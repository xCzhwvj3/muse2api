"""muse.ai 纯协议生成引擎：脱离 Chromium/CDP，通过 Noise_XX + HTTP-over-Noise 完成对话、生图、生视频与额度查询。"""
from __future__ import annotations

import base64
import copy
import datetime
import hashlib
import json
import logging
import os
import re
import struct
import threading
import time
import uuid
from dataclasses import dataclass, field
from urllib.parse import quote, urlencode, urljoin

import requests

from engine import (
    ESSENTIAL_COOKIES,
    MAX_REFERENCE_IMAGES,
    MAX_REFERENCE_TOTAL_BYTES,
    REFERENCE_MIME_EXT,
    MuseAuthError,
    MuseEngine,
    MuseGenerationError,
    MuseModelRefusalError,
    MuseProxyError,
    MuseSessionUnavailable,
    _MIB,
    _sniff_mime,
    reference_kind,
)
from noise_transport import (
    DEFAULT_NOISE_WS_URL,
    NoiseConnection,
    NoiseHttpError,
    NoiseProxyError,
    NoiseSubscription,
    NoiseTransportError,
)
from proxy import request_proxy_context

log = logging.getLogger("muse2api")

_CHROME_UA = (
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/135.0.0.0 Safari/537.36"
)
_CHAT_STREAM_CAPABILITIES = [
    "hotel_results",
    "chat_cancel",
    "delta_stream",
    "custom_reactions",
    "custom_reactions_facebook_thumbs_up_v1",
]
_CHAT_SUBSCRIBE_CAPABILITIES = [
    *_CHAT_STREAM_CAPABILITIES,
    "voice_reply_captions",
    "voice_user_live_transcript",
]
_FS_WRITE_CHUNK_BYTES = 512 * 1024
_INLINE_IMAGE_MAX_BYTES = 8 * 1024 * 1024
_DEFAULT_QUOTA_ACTION_ID = "40e0249eeae158685b6a8d0c3b203f53dd4f2c7d63"
_QUOTA_ACTION_RE = re.compile(
    r'createServerReference\)\("([0-9a-f]{40,})",[^)]{0,160}"fetchSubscriptionAction"'
)
_SANDBOX_MD_RE = re.compile(r"!\[[^\]]*\]\((sandbox://[^)\s]+)\)")
_SANDBOX_RAW_RE = re.compile(r"(sandbox://workspace/[^\s)\"'<>]+)")
_EXT_TO_MIME = {
    ".png": "image/png",
    ".jpg": "image/jpeg",
    ".jpeg": "image/jpeg",
    ".gif": "image/gif",
    ".webp": "image/webp",
    ".heic": "image/heic",
    ".heif": "image/heif",
    ".avif": "image/avif",
    ".mp4": "video/mp4",
    ".mov": "video/quicktime",
    ".webm": "video/webm",
    ".mkv": "video/x-matroska",
}


def _proxy_fingerprint(proxy: dict | None) -> str:
    if not proxy:
        return ""
    return json.dumps(proxy, sort_keys=True, ensure_ascii=False)


def _cookie_header(cookies: dict) -> str:
    return "; ".join(f"{k}={v}" for k, v in (cookies or {}).items() if v)


def _same_origin_headers(cookies: dict, accept: str = "*/*",
                         content_type: str | None = None,
                         referer: str = "https://muse.ai/thread/new") -> dict[str, str]:
    """构造带同源 Fetch 元数据的请求头，满足 /api/hatch/token 与 Server Action 的 CSRF 校验。"""
    headers = {
        "Cookie": _cookie_header(cookies),
        "User-Agent": _CHROME_UA,
        "Origin": "https://muse.ai",
        "Referer": referer,
        "Accept": accept,
        "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
        "Sec-Fetch-Site": "same-origin",
        "Sec-Fetch-Mode": "cors",
        "Sec-Fetch-Dest": "empty",
    }
    if content_type:
        headers["Content-Type"] = content_type
    return headers


def _harvest_cookies(resp_cookies, cur_cookies: dict, cur_exp: dict) -> bool:
    """从 HTTP 响应合并轮换后的 Cookie；如有变化返回 True。"""
    changed = False
    for cookie in resp_cookies:
        if cookie.value and cur_cookies.get(cookie.name) != cookie.value:
            cur_cookies[cookie.name] = cookie.value
            changed = True
        if cookie.expires:
            exp_int = int(float(cookie.expires))
            if cur_exp.get(cookie.name) != exp_int:
                cur_exp[cookie.name] = exp_int
                changed = True
    return changed


def _normalize_workspace_uri(path: str) -> str:
    """将 VM 路径统一规范为 sandbox://workspace/... 形式用于去重。"""
    p = (path or "").strip()
    if p.startswith("sandbox://"):
        return p
    for prefix in ("/home/hatch/workspace/", "workspace/"):
        if p.startswith(prefix):
            return f"sandbox://workspace/{p[len(prefix):]}"
    if p.startswith("/home/hatch/"):
        return f"sandbox://workspace/{p[12:]}"
    return f"sandbox://workspace/{p.lstrip('/')}"


def _to_fs_raw_path(uri: str) -> str:
    """将 sandbox:// 或 VM 绝对路径转换为 GET /fs/raw/{*path} 的 URL 编码路径。"""
    cleaned = (uri or "").strip().split("?", 1)[0].split("#", 1)[0]
    for prefix in ("sandbox://", "file://"):
        if cleaned.startswith(prefix):
            cleaned = cleaned[len(prefix):]
            break
    cleaned = cleaned.replace("\\", "/")
    segments = [seg for seg in cleaned.split("/") if seg and seg not in (".", "..")]
    if "workspace" in segments:
        segments = segments[segments.index("workspace"):]
    elif len(segments) >= 3 and segments[0] in ("home", "Users"):
        segments = segments[2:]
    return "/".join(quote(seg, safe="") for seg in segments)


def _guess_mime_from_path(path: str) -> str:
    clean = (path or "").split("?", 1)[0].split("#", 1)[0].lower()
    dot = clean.rfind(".")
    return _EXT_TO_MIME.get(clean[dot:], "") if dot >= 0 else ""


def _probe_image_dims(data: bytes) -> tuple[int | None, int | None]:
    """纯 Python 解析 PNG / GIF / JPEG / WEBP 文件头尺寸，无需第三方图像库。"""
    try:
        if len(data) >= 24 and data.startswith(b"\x89PNG\r\n\x1a\n"):
            w, h = struct.unpack(">II", data[16:24])
            return int(w), int(h)
        if len(data) >= 10 and data[:6] in (b"GIF87a", b"GIF89a"):
            w, h = struct.unpack("<HH", data[6:10])
            return int(w), int(h)
        if len(data) >= 30 and data[:4] == b"RIFF" and data[8:12] == b"WEBP":
            chunk = data[12:16]
            if chunk == b"VP8X" and len(data) >= 30:
                w = 1 + int.from_bytes(data[24:27], "little")
                h = 1 + int.from_bytes(data[27:30], "little")
                return w, h
            if chunk == b"VP8 " and len(data) >= 30:
                w = struct.unpack("<H", data[26:28])[0] & 0x3FFF
                h = struct.unpack("<H", data[28:30])[0] & 0x3FFF
                return int(w), int(h)
            if chunk == b"VP8L" and len(data) >= 25:
                bits = struct.unpack("<I", data[21:25])[0]
                return (bits & 0x3FFF) + 1, ((bits >> 14) & 0x3FFF) + 1
        if data.startswith(b"\xff\xd8"):
            idx = 2
            total = len(data)
            while idx + 4 <= total:
                if data[idx] != 0xFF:
                    idx += 1
                    continue
                while idx < total and data[idx] == 0xFF:
                    idx += 1
                if idx >= total:
                    break
                marker = data[idx]
                idx += 1
                if marker in (0xD8, 0xD9, 0x01) or 0xD0 <= marker <= 0xD7:
                    continue
                if idx + 2 > total:
                    break
                seg_len = struct.unpack(">H", data[idx:idx + 2])[0]
                if marker in (0xC0, 0xC1, 0xC2, 0xC3, 0xC5, 0xC6, 0xC7, 0xC9, 0xCA, 0xCB, 0xCD, 0xCE, 0xCF):
                    if idx + 7 <= total:
                        h, w = struct.unpack(">HH", data[idx + 3:idx + 7])
                        return int(w), int(h)
                    break
                idx += max(seg_len, 2)
    except Exception:
        pass
    return None, None


def _extract_transcript_text(payload: dict) -> str:
    """从 delta.message_done / message.assistant 的 transcript 中提取最新助手文本。"""
    transcript = payload.get("transcript")
    if isinstance(transcript, str):
        try:
            transcript = json.loads(transcript)
        except ValueError:
            transcript = None
    if not isinstance(transcript, dict):
        return ""
    messages = transcript.get("messages")
    if not isinstance(messages, list):
        return ""
    for msg in reversed(messages):
        if isinstance(msg, dict) and msg.get("role") == "assistant":
            content = msg.get("content")
            if isinstance(content, list):
                parts = [
                    block.get("text", "")
                    for block in content
                    if isinstance(block, dict) and block.get("type") == "text" and isinstance(block.get("text"), str)
                ]
                joined = "".join(parts).strip()
                if joined:
                    return joined
    return ""


def _extract_static_refusal(payload: dict) -> str | None:
    """按 muse.ai 前端规则识别协议级静默拒答（override_source == 'static_response'）。"""
    if payload.get("override_source") != "static_response":
        return None
    return _extract_transcript_text(payload) or "请求已被上游安全策略拒绝"


def _collect_media_candidates(obj: dict, out: dict[str, dict]):
    """从实时事件或历史消息中提取所有图片/视频候选 URI（覆盖 resources、tool_call 与 markdown）。"""
    if not isinstance(obj, dict):
        return

    def add_uri(uri: str, mime: str = "", kind: str = ""):
        if not isinstance(uri, str) or not uri.strip():
            return
        norm = uri.strip()
        if not norm.startswith(("sandbox://", "http://", "https://")):
            norm = _normalize_workspace_uri(norm)
        inferred_mime = mime.strip().lower() if isinstance(mime, str) and mime.strip() else _guess_mime_from_path(norm)
        inferred_kind = kind.strip().lower() if isinstance(kind, str) and kind.strip() else ""
        if not inferred_kind:
            if inferred_mime.startswith("video/"):
                inferred_kind = "video"
            elif inferred_mime.startswith("image/"):
                inferred_kind = "image"
        if inferred_kind not in ("image", "video", "media") and not inferred_mime.startswith(("image/", "video/")):
            return
        if norm not in out:
            out[norm] = {"uri": norm, "mime": inferred_mime, "kind": inferred_kind or "media"}

    def scan_text(text: str):
        if not isinstance(text, str) or "sandbox://" not in text:
            return
        for match in _SANDBOX_MD_RE.finditer(text):
            add_uri(match.group(1))
        for match in _SANDBOX_RAW_RE.finditer(text):
            add_uri(match.group(1).rstrip(".,;:"))

    def scan_resources(res_list):
        if not isinstance(res_list, list):
            return
        for res in res_list:
            if not isinstance(res, dict):
                continue
            add_uri(res.get("uri") or res.get("path") or "", res.get("mime_type") or "", res.get("kind") or "")

    def scan_metadata(meta):
        if isinstance(meta, str):
            try:
                meta = json.loads(meta)
            except ValueError:
                scan_text(meta)
                return
        if not isinstance(meta, dict):
            return
        if meta.get("missing") is True:
            return
        file_type = meta.get("file_type") or meta.get("media_type") or ""
        if not file_type and meta.get("kind") in ("image", "video"):
            file_type = meta["kind"]
        for key in ("file_paths", "media_paths", "paths"):
            paths = meta.get(key)
            if isinstance(paths, list):
                for item in paths:
                    if isinstance(item, str):
                        add_uri(item, kind=file_type)
                    elif isinstance(item, dict):
                        if item.get("missing") is True:
                            continue
                        add_uri(
                            item.get("path") or item.get("uri") or "",
                            item.get("mime_type") or item.get("mime") or "",
                            file_type,
                        )
        for list_key, default_kind in (("images", "image"), ("videos", "video"), ("items", file_type)):
            entries = meta.get(list_key)
            if isinstance(entries, list):
                for item in entries:
                    if isinstance(item, str):
                        add_uri(item, kind=default_kind)
                    elif isinstance(item, dict):
                        if item.get("missing") is True:
                            continue
                        add_uri(
                            item.get("path") or item.get("uri") or item.get("image_path") or item.get("video_path") or "",
                            item.get("mime_type") or item.get("mime") or "",
                            item.get("kind") or default_kind,
                        )
        for single_key, key_kind in (
            ("image_path", "image"),
            ("video_path", "video"),
            ("path", file_type),
            ("file_path", file_type),
            ("media_path", file_type),
            ("uri", file_type),
        ):
            val = meta.get(single_key)
            if isinstance(val, str):
                add_uri(val, meta.get("mime_type") or meta.get("mime") or "", key_kind)
        scan_text(meta.get("fallback_text") or "")
        output = meta.get("output")
        if output is not None:
            scan_metadata(output)
        for sub_key in ("result", "data", "artifact", "artifacts", "media", "video", "image"):
            sub = meta.get(sub_key)
            if isinstance(sub, dict):
                scan_metadata(sub)
            elif isinstance(sub, list):
                for elem in sub:
                    if isinstance(elem, dict):
                        scan_metadata(elem)

    def scan_content_blocks(blocks):
        if not isinstance(blocks, list):
            return
        for blk in blocks:
            if not isinstance(blk, dict):
                continue
            btype = blk.get("type")
            if btype == "tool_call":
                res = blk.get("result")
                if isinstance(res, dict):
                    scan_metadata(res.get("metadata"))
                    scan_metadata(res)
                scan_resources(blk.get("resources"))
            elif btype == "text":
                scan_text(blk.get("text") or "")
            elif btype == "sub_agent":
                scan_content_blocks(blk.get("content"))

    scan_resources(obj.get("resources"))
    scan_metadata(obj.get("result"))
    scan_metadata(obj.get("metadata"))
    scan_metadata(obj.get("data"))
    for single_key, key_kind in (("image_path", "image"), ("video_path", "video"), ("media_path", "")):
        val = obj.get(single_key)
        if isinstance(val, str):
            add_uri(val, obj.get("mime_type") or obj.get("mime") or "", key_kind or (obj.get("kind") or ""))
    scan_text(obj.get("display_text") or "")
    scan_text(obj.get("content") or "")
    scan_text(obj.get("text") or "")
    scan_text(obj.get("fallback_text") or "")
    for list_key in ("presentations", "widgets"):
        entries = obj.get(list_key)
        if isinstance(entries, list):
            for elem in entries:
                if isinstance(elem, dict):
                    _collect_media_candidates(elem, out)

    transcript = obj.get("transcript")
    if isinstance(transcript, str):
        try:
            transcript = json.loads(transcript)
        except ValueError:
            transcript = None
    if isinstance(transcript, dict):
        for msg in transcript.get("messages") or []:
            if isinstance(msg, dict):
                scan_content_blocks(msg.get("content"))

    nested = obj.get("payload")
    if isinstance(nested, dict):
        _collect_media_candidates(nested, out)


@dataclass
class _AccountSession:
    """单账号持久协议上下文与 Noise 长连接槽位。"""
    account_id: str
    lock: threading.Lock = field(default_factory=threading.Lock)
    conn: NoiseConnection | None = None
    vm_id: str = ""
    endpoint_url: str = ""
    vm_name: str = ""
    auth_token: str = ""
    notary_token: str = ""
    token_at: float = 0.0
    proxy_key: str = ""
    cookies: dict = field(default_factory=dict)
    cookies_exp: dict = field(default_factory=dict)
    device_id: str = field(default_factory=lambda: str(uuid.uuid4()))


class ProtocolEngine:
    """muse.ai 纯协议引擎，与 MuseEngine 保持完全一致的外部接口契约。"""

    def __init__(self, cfg):
        self.cfg = cfg
        self.proc = None  # 保持与 app.py 旧字段兼容（协议模式下不启动浏览器子进程）
        self.proxy_resolver = None
        self.cookie_sink = None
        self._last_http_renew: dict[str, float] = {}
        self._local = threading.local()
        self._started = False
        self._sessions_lock = threading.Lock()
        self._sessions: dict[str, _AccountSession] = {}
        self._quota_action_lock = threading.Lock()
        self._quota_action_id = _DEFAULT_QUOTA_ACTION_ID
        self._noise_url = getattr(cfg, "noise_url", DEFAULT_NOISE_WS_URL) or DEFAULT_NOISE_WS_URL

    def _ensure_local(self):
        if not hasattr(self._local, "proxy_snapshot"):
            self._local.proxy_snapshot = None
        if not hasattr(self._local, "current_acc_id"):
            self._local.current_acc_id = None
        if not hasattr(self._local, "page"):
            self._local.page = None
        if not hasattr(self._local, "cookies"):
            self._local.cookies = {}
        if not hasattr(self._local, "cookies_exp"):
            self._local.cookies_exp = {}
        return self._local

    @property
    def page(self):
        return self._ensure_local().page

    @property
    def current_acc_id(self):
        return self._ensure_local().current_acc_id

    def is_running(self) -> bool:
        return self._started

    def start(self):
        self.cfg.ensure_dirs()
        self._started = True

    def stop(self):
        self._started = False
        with self._sessions_lock:
            sessions = list(self._sessions.values())
            self._sessions.clear()
        for sess in sessions:
            with sess.lock:
                if sess.conn is not None:
                    sess.conn.close()
                    sess.conn = None
        self.close_current_page()

    def close_current_page(self):
        """解绑当前工作线程的会话引用；账号级 Noise 长连接保留在连接池供后续复用。"""
        local = self._ensure_local()
        local.page = None
        local.current_acc_id = None
        local.cookies = {}
        local.cookies_exp = {}

    def reset_thread(self, for_chat: bool = False):
        """协议模式下每次请求自带独立新 session_id，无需页面级重置。"""
        return None

    def _get_session(self, account_id: str | None) -> _AccountSession:
        key = account_id or "__anonymous__"
        with self._sessions_lock:
            sess = self._sessions.get(key)
            if sess is None:
                sess = _AccountSession(account_id=key)
                self._sessions[key] = sess
            return sess

    def _resolve_proxy(self, account_id: str | None) -> dict | None:
        local = self._ensure_local()
        if local.proxy_snapshot is not None:
            return copy.deepcopy(local.proxy_snapshot)
        if account_id and callable(self.proxy_resolver):
            resolved = self.proxy_resolver(account_id)
            return copy.deepcopy(resolved) if resolved else None
        return None

    def _persist_cookies(self, account_id: str | None, cookies: dict, cookies_exp: dict):
        local = self._ensure_local()
        local.cookies = dict(cookies)
        local.cookies_exp = dict(cookies_exp)
        if account_id and callable(self.cookie_sink):
            try:
                self.cookie_sink(account_id, dict(cookies), dict(cookies_exp))
            except Exception as exc:  # noqa: BLE001
                log.warning("协议引擎落盘轮换 Cookie 失败 (%s): %s", account_id, exc)

    def read_cookies(self) -> dict[str, dict]:
        """返回当前线程绑定账号的最新内存 Cookie（兼容 app._sync_cookies 契约）。"""
        local = self._ensure_local()
        acc_id = local.current_acc_id
        cookies = dict(local.cookies or {})
        cookies_exp = dict(local.cookies_exp or {})
        if acc_id:
            sess = self._get_session(acc_id)
            if sess.cookies:
                cookies.update(sess.cookies)
                cookies_exp.update(sess.cookies_exp)
        out: dict[str, dict] = {}
        for name, val in cookies.items():
            if not val:
                continue
            exp = cookies_exp.get(name, -1)
            try:
                exp_val = int(float(exp)) if exp is not None else -1
            except (TypeError, ValueError):
                exp_val = -1
            out[name] = {"value": str(val), "expires": exp_val}
        return out

    @staticmethod
    def renew_session_http(cookies: dict, expires: dict | None = None,
                           wake_vm: bool = True, proxy: dict | None = None) -> dict:
        return MuseEngine.renew_session_http(cookies, expires=expires, wake_vm=wake_vm, proxy=proxy)

    def _normalize_image(self, img: str) -> tuple[str, str]:
        return MuseEngine._normalize_image(self, img)

    # ---------------- 换票与长连池 ----------------

    def _exchange_noise_token(self, cookies: dict, cookies_exp: dict,
                              endpoint_url: str, vm_name: str,
                              proxy: dict | None, account_id: str | None) -> tuple[str, str]:
        """调用 POST /api/hatch/token 换取 Noise 鉴权 JWT 与 notary_token。"""
        headers = _same_origin_headers(cookies, accept="application/json", content_type="application/json")
        try:
            with request_proxy_context(proxy) as proxy_options:
                session = requests.Session()
                session.trust_env = False
                resp = session.post(
                    "https://muse.ai/api/hatch/token",
                    headers=headers,
                    json={"vmAddress": endpoint_url, "vmName": vm_name},
                    timeout=15,
                    allow_redirects=False,
                    **proxy_options,
                )
        except requests.RequestException as exc:
            if proxy:
                raise MuseProxyError(f"经账号代理请求 /api/hatch/token 失败 ({type(exc).__name__})；未回退直连") from None
            raise MuseGenerationError(f"请求 /api/hatch/token 失败: {exc}") from exc

        if proxy and resp.status_code == 407:
            raise MuseProxyError("账号代理认证失败 (HTTP 407)，未回退直连")
        if _harvest_cookies(resp.cookies, cookies, cookies_exp):
            self._persist_cookies(account_id, cookies, cookies_exp)
        if resp.status_code in (401, 403):
            raise MuseAuthError(f"/api/hatch/token 返回 HTTP {resp.status_code}，Cookie 已失效或被拒绝")
        if resp.status_code != 200:
            raise MuseGenerationError(f"/api/hatch/token 返回 HTTP {resp.status_code}: {resp.text[:200]}")
        try:
            data = resp.json()
        except ValueError as exc:
            raise MuseGenerationError("/api/hatch/token 返回非 JSON 响应") from exc
        token = (data.get("token") or "").strip()
        notary = (data.get("notary_token") or "").strip()
        if not token or not notary:
            raise MuseGenerationError("/api/hatch/token 缺少 token 或 notary_token")
        return token, notary

    def _evict_connection(self, account_id: str | None):
        sess = self._get_session(account_id)
        with sess.lock:
            if sess.conn is not None:
                sess.conn.close()
                sess.conn = None
            sess.auth_token = ""
            sess.notary_token = ""
            sess.token_at = 0.0

    def _ensure_connection(self, cookies: dict, expires: dict | None = None,
                           account_id: str | None = None,
                           force_refresh: bool = False) -> tuple[_AccountSession, NoiseConnection]:
        """为账号获取健康的 Noise 长连接；自动完成会话续签、VM 唤醒、换票与断线重连。"""
        if not cookies or not any(cookies.get(k) for k in ESSENTIAL_COOKIES):
            raise MuseAuthError("账号缺少必需的 hatch_sess Cookie")
        self.start()
        proxy = self._resolve_proxy(account_id)
        proxy_key = _proxy_fingerprint(proxy)
        sess = self._get_session(account_id)

        with sess.lock:
            # 合并最新传入的 Cookie（保留内存中可能刚轮换更新的值，但外部显式导入的新值优先）
            cur_cookies = dict(cookies)
            cur_exp = dict(expires or {})
            if not force_refresh and sess.cookies:
                for k, v in sess.cookies.items():
                    if v and k not in cur_cookies:
                        cur_cookies[k] = v
            sess.cookies = cur_cookies
            sess.cookies_exp = cur_exp

            # 若已有存活连接且代理未变更，做轻量保活复用
            if not force_refresh and sess.conn is not None and sess.conn.is_alive() and sess.proxy_key == proxy_key:
                idle_sec = time.monotonic() - sess.conn._last_activity
                if idle_sec < 25.0:
                    self._bind_local(account_id, sess, sess.conn)
                    return sess, sess.conn
                try:
                    sess.conn.ping(timeout=6.0)
                    self._bind_local(account_id, sess, sess.conn)
                    return sess, sess.conn
                except Exception:
                    log.info("账号 %s Noise 连接探活失败，准备重建", account_id)
                    sess.conn.close()
                    sess.conn = None

            if sess.conn is not None:
                sess.conn.close()
                sess.conn = None

            # Step 1: 获取或刷新会话信息，确保工作区已分配且 VM 处于 RUNNING 状态
            need_session = force_refresh or not (sess.vm_id and sess.endpoint_url and sess.vm_name) or sess.proxy_key != proxy_key
            if need_session:
                info = self._fetch_running_session(cur_cookies, cur_exp, proxy, account_id, wake_if_unknown=False)
                sess.vm_id = info["vm_id"]
                sess.endpoint_url = info["endpoint_url"]
                sess.vm_name = info["vm_name"]
                cur_cookies = info["cookies"]
                cur_exp = info["cookies_exp"]
                sess.cookies = cur_cookies
                sess.cookies_exp = cur_exp

            # Step 2: 换票并建立 Noise_XX WebSocket；若首连因旧票或 VM 休眠失败则唤醒并重试一次
            last_exc: Exception | None = None
            for attempt in range(2):
                try:
                    if attempt == 1:
                        info = self._fetch_running_session(cur_cookies, cur_exp, proxy, account_id, wake_if_unknown=True)
                        sess.vm_id = info["vm_id"]
                        sess.endpoint_url = info["endpoint_url"]
                        sess.vm_name = info["vm_name"]
                        cur_cookies = info["cookies"]
                        cur_exp = info["cookies_exp"]
                        sess.cookies = cur_cookies
                        sess.cookies_exp = cur_exp
                    token, notary = self._exchange_noise_token(
                        cur_cookies, cur_exp, sess.endpoint_url, sess.vm_name, proxy, account_id
                    )
                    conn = NoiseConnection.connect(
                        vm_id=sess.vm_id,
                        auth_token=token,
                        notary_token=notary,
                        proxy=proxy,
                        base_url=self._noise_url,
                        timeout=20.0,
                    )
                    conn.ping(timeout=8.0)
                    sess.auth_token = token
                    sess.notary_token = notary
                    sess.token_at = time.monotonic()
                    sess.proxy_key = proxy_key
                    sess.conn = conn
                    self._bind_local(account_id, sess, conn)
                    return sess, conn
                except (MuseAuthError, MuseProxyError, MuseSessionUnavailable):
                    raise
                except NoiseProxyError as exc:
                    raise MuseProxyError(str(exc)) from None
                except Exception as exc:  # noqa: BLE001
                    last_exc = exc
                    log.warning("账号 %s Noise 建连第 %d 次尝试失败: %s", account_id, attempt + 1, exc)
            raise MuseGenerationError(f"建立 Noise 加密隧道失败: {last_exc}") from last_exc

    def _fetch_running_session(self, cur_cookies: dict, cur_exp: dict,
                               proxy: dict | None, account_id: str | None,
                               wake_if_unknown: bool = False) -> dict:
        """获取已分配会话；仅当明确休眠或首连失败重试时触发 VM 唤醒，避免 vm_state=UNKNOWN 导致无谓盲等。"""
        res = self.renew_session_http(cur_cookies, cur_exp, wake_vm=wake_if_unknown, proxy=proxy)
        cur_cookies = res["cookies"]
        cur_exp = res["cookies_exp"]
        self._persist_cookies(account_id, cur_cookies, cur_exp)
        if account_id:
            self._last_http_renew[account_id] = time.time()

        vm_id = res.get("vm_id") or ""
        endpoint_url = res.get("endpoint_url") or ""
        vm_name = res.get("vm_name") or ""
        vm_state = (res.get("vm_state") or "").upper()
        if not vm_id or not endpoint_url or not vm_name:
            raise MuseGenerationError("/api/session 缺少 vm_id / endpoint_url / vm_name")

        # 仅当上游明确返回停机/启动中状态时主动唤醒并轮询；vm_state 为 UNKNOWN 时直接尝试建连，失败后再进入重试唤醒
        sleeping_states = ("STOPPED", "SUSPENDED", "TERMINATED", "OFFLINE", "STARTING", "PROVISIONING", "PENDING", "WAKING")
        if vm_state in sleeping_states:
            if not res.get("wake_requested"):
                wake_res = self.renew_session_http(cur_cookies, cur_exp, wake_vm=True, proxy=proxy)
                cur_cookies = wake_res["cookies"]
                cur_exp = wake_res["cookies_exp"]
                self._persist_cookies(account_id, cur_cookies, cur_exp)
                vm_state = (wake_res.get("vm_state") or "").upper()
            if vm_state in sleeping_states:
                deadline = time.monotonic() + 25.0
                while time.monotonic() < deadline:
                    time.sleep(2.0)
                    check = self.renew_session_http(cur_cookies, cur_exp, wake_vm=False, proxy=proxy)
                    cur_cookies = check["cookies"]
                    cur_exp = check["cookies_exp"]
                    self._persist_cookies(account_id, cur_cookies, cur_exp)
                    vm_state = (check.get("vm_state") or "").upper()
                    endpoint_url = check.get("endpoint_url") or endpoint_url
                    vm_name = check.get("vm_name") or vm_name
                    if vm_state not in sleeping_states:
                        break
        elif wake_if_unknown:
            # 首连失败重试：已触发一次 wake_vm=True，短暂停顿等待容器拉起
            time.sleep(2.5)
        return {
            "vm_id": vm_id,
            "endpoint_url": endpoint_url,
            "vm_name": vm_name,
            "vm_state": vm_state,
            "cookies": cur_cookies,
            "cookies_exp": cur_exp,
        }

    def _bind_local(self, account_id: str | None, sess: _AccountSession, conn: NoiseConnection):
        local = self._ensure_local()
        local.current_acc_id = account_id
        local.page = conn
        local.cookies = dict(sess.cookies)
        local.cookies_exp = dict(sess.cookies_exp)

    def ensure_page(self, cookies: dict, expires: dict | None = None,
                    account_id: str | None = None):
        """建立或校验账号的 Noise 加密连接（替代浏览器标签页预热）。"""
        _, conn = self._ensure_connection(cookies, expires, account_id=account_id, force_refresh=False)
        return conn

    def refresh(self, cookies: dict, expires: dict | None = None,
                account_id: str | None = None):
        """强制重新验证 Cookie 并重建 Noise 隧道（用于 /admin/accounts/{id}/test）。"""
        _, conn = self._ensure_connection(cookies, expires, account_id=account_id, force_refresh=True)
        return conn

    # ---------------- 纯 HTTP 额度查询 ----------------

    def _discover_quota_action_id(self, cookies: dict, cookies_exp: dict,
                                  proxy: dict | None, account_id: str | None) -> str | None:
        """上游前端发版变更 Server Action 哈希时，从 /thread/new 静态脚本动态刷新 fetchSubscriptionAction ID。"""
        headers = _same_origin_headers(cookies, accept="text/html,application/xhtml+xml,*/*")
        try:
            with request_proxy_context(proxy) as proxy_options:
                session = requests.Session()
                session.trust_env = False
                html_resp = session.get(
                    "https://muse.ai/thread/new",
                    headers=headers,
                    timeout=15,
                    allow_redirects=False,
                    **proxy_options,
                )
                if _harvest_cookies(html_resp.cookies, cookies, cookies_exp):
                    self._persist_cookies(account_id, cookies, cookies_exp)
                if html_resp.status_code != 200:
                    return None
                html_body = html_resp.content.decode("utf-8", errors="replace")
                script_paths = re.findall(r'src="(/_next/static/[^"]+\.js)"', html_body)
                seen: set[str] = set()
                for rel in script_paths:
                    if rel in seen:
                        continue
                    seen.add(rel)
                    js_resp = session.get(
                        urljoin("https://muse.ai", rel),
                        headers={"User-Agent": _CHROME_UA},
                        timeout=10,
                        **proxy_options,
                    )
                    if js_resp.status_code != 200:
                        continue
                    js_body = js_resp.content.decode("utf-8", errors="replace")
                    if "fetchSubscriptionAction" in js_body:
                        m = _QUOTA_ACTION_RE.search(js_body)
                        if m:
                            return m.group(1)
        except Exception as exc:  # noqa: BLE001
            log.warning("动态刷新 fetchSubscriptionAction ID 失败: %s", exc)
        return None

    @staticmethod
    def _parse_subscription_rsc(body: str) -> dict | None:
        """解析 Next.js Server Action 返回的 RSC 行，提取 subscription 字典。"""
        # 使用 \n 切行，避免 Unicode 行分隔符（如 U+0085 / U+2028）截断 JSON 内容
        for line in (body or "").split("\n"):
            idx = line.find("{")
            if idx < 0:
                continue
            try:
                obj = json.loads(line[idx:])
            except ValueError:
                continue
            if isinstance(obj, dict) and isinstance(obj.get("subscription"), dict):
                return obj["subscription"]
        return None

    @staticmethod
    def _format_quota_from_subscription(sub: dict) -> dict:
        """将 muse.ai subscription 对象转换为与 MuseEngine.quota() 完全一致的返回结构。"""
        tier = sub.get("tier") if isinstance(sub.get("tier"), dict) else {}
        usage = sub.get("usage") if isinstance(sub.get("usage"), dict) else {}
        out: dict = {}

        plan = (tier.get("name") or sub.get("usageRowLabel") or "").strip()
        if plan:
            out["plan"] = plan

        pct = usage.get("percentUsed")
        if isinstance(pct, (int, float)) and 0 <= pct <= 100:
            out["weekly_used_pct"] = int(pct) if float(pct).is_integer() else round(float(pct), 2)

        subtitle = (sub.get("statusSubtitle") or "").strip()
        reset_text = ""
        if subtitle:
            m = re.search(r"(?:重置时间[：:]\s*|resets?\s+on\s+)(.+)$", subtitle, re.I)
            reset_text = m.group(1).strip() if m else subtitle
        elif isinstance(usage.get("resetsAt"), (int, float)) and usage["resetsAt"] > 0:
            dt = datetime.datetime.fromtimestamp(float(usage["resetsAt"]), tz=datetime.timezone.utc)
            reset_text = dt.strftime("%Y-%m-%d")
        if reset_text:
            out["weekly_reset"] = reset_text

        topup_balance = sub.get("topupBalance")
        topup_total = sub.get("topupTotal")
        topup_val_label = (sub.get("topupRowValueLabel") or "").strip()
        if isinstance(topup_total, (int, float)) and topup_total > 0 and isinstance(topup_balance, (int, float)):
            used_ratio = max(0.0, min(100.0, (topup_total - topup_balance) / topup_total * 100.0))
            out["extra_used_pct"] = int(round(used_ratio)) if abs(used_ratio - round(used_ratio)) < 0.05 else round(used_ratio, 1)
            out["extra_expires"] = "never"
        if topup_val_label:
            m_left = re.search(r"[（(]([^）)]+)[）)]", topup_val_label)
            if m_left:
                out["extra_left"] = m_left.group(1).replace("\xa0", " ").strip()
        elif isinstance(topup_balance, (int, float)):
            out["extra_left"] = f"{int(topup_balance):,}"

        raw_lines = [
            x for x in (
                plan,
                subtitle,
                sub.get("usageRowValueLabel"),
                sub.get("topupRowLabel"),
                topup_val_label,
            ) if x
        ]
        out["raw"] = "\n".join(raw_lines)
        out["found"] = "weekly_used_pct" in out
        return out

    def quota(self, cookies: dict, expires: dict | None = None,
              account_id: str | None = None) -> dict:
        """通过 Next.js Server Action 纯 HTTP 读取账号用量，无需浏览器弹窗点击。"""
        if not cookies or not any(cookies.get(k) for k in ESSENTIAL_COOKIES):
            raise MuseAuthError("账号缺少必需的 hatch_sess Cookie")
        proxy = self._resolve_proxy(account_id)
        cur_cookies = dict(cookies)
        cur_exp = dict(expires or {})

        for attempt in range(2):
            with self._quota_action_lock:
                action_id = self._quota_action_id
            headers = _same_origin_headers(
                cur_cookies,
                accept="text/x-component",
                content_type="text/plain;charset=UTF-8",
            )
            headers["Next-Action"] = action_id
            try:
                with request_proxy_context(proxy) as proxy_options:
                    session = requests.Session()
                    session.trust_env = False
                    resp = session.post(
                        "https://muse.ai/thread/new",
                        headers=headers,
                        data="[]",
                        timeout=15,
                        allow_redirects=False,
                        **proxy_options,
                    )
            except requests.RequestException as exc:
                if proxy:
                    raise MuseProxyError(f"经账号代理查询额度失败 ({type(exc).__name__})；未回退直连") from None
                raise MuseGenerationError(f"查询额度请求失败: {exc}") from exc

            if proxy and resp.status_code == 407:
                raise MuseProxyError("账号代理认证失败 (HTTP 407)，未回退直连")
            if _harvest_cookies(resp.cookies, cur_cookies, cur_exp):
                self._persist_cookies(account_id, cur_cookies, cur_exp)
            if resp.status_code in (401, 403):
                raise MuseAuthError(f"查询额度返回 HTTP {resp.status_code}，会话已失效")
            if resp.status_code in (301, 302, 303, 307, 308):
                loc = resp.headers.get("Location") or ""
                if any(k in loc.lower() for k in ("login", "signin", "auth")):
                    raise MuseAuthError("查询额度被重定向至登录页，会话已失效")

            if resp.status_code == 200:
                # Next.js text/x-component 默认不带 charset，需显式按 UTF-8 解码，防止 requests 按 ISO-8859-1 破坏中文与切行
                rsc_body = resp.content.decode("utf-8", errors="replace")
                sub = self._parse_subscription_rsc(rsc_body)
                if sub is not None:
                    parsed = self._format_quota_from_subscription(sub)
                    if parsed.get("found"):
                        return parsed
                    raise MuseGenerationError("额度接口未返回有效用量百分比；旧缓存未覆盖")

            # 首次解析失败时，尝试从前端静态包刷新 fetchSubscriptionAction ID 后重试一次
            if attempt == 0:
                new_id = self._discover_quota_action_id(cur_cookies, cur_exp, proxy, account_id)
                if new_id and new_id != action_id:
                    with self._quota_action_lock:
                        self._quota_action_id = new_id
                    log.info("已动态刷新 fetchSubscriptionAction ID: %s", new_id[:12])
                    continue
            break
        raise MuseGenerationError("未能从协议接口读取有效用量；旧缓存未覆盖")

    # ---------------- 隧道内公共操作：取消、文件上传、原文件直取 ----------------

    @staticmethod
    def _cancel_session(conn: NoiseConnection, session_id: str):
        try:
            if conn.is_alive():
                conn.request_json("POST", "/chat/cancel", payload={"session_id": session_id}, timeout=5.0)
        except Exception:
            pass

    @staticmethod
    def _upload_file_to_vm(conn: NoiseConnection, raw_bytes: bytes, filename: str) -> str:
        """按 muse.ai 前端 512KB 分片协议调用 POST /fs/write 上传参考素材，返回工作区相对路径。"""
        safe_name = re.sub(r"[^a-zA-Z0-9._-]+", "_", filename or "upload.bin").strip("._") or "upload.bin"
        rel_path = f"workspace/uploads/{uuid.uuid4().hex[:12]}-{safe_name}"
        total = len(raw_bytes)
        if total == 0:
            conn.request_json(
                "POST",
                "/fs/write",
                payload={
                    "path": rel_path,
                    "data_base64": "",
                    "overwrite": True,
                    "append": False,
                    "create_parent": True,
                },
                timeout=30.0,
            )
            return rel_path
        offset = 0
        part_index = 0
        while offset < total:
            chunk = raw_bytes[offset:offset + _FS_WRITE_CHUNK_BYTES]
            conn.request_json(
                "POST",
                "/fs/write",
                payload={
                    "path": rel_path,
                    "data_base64": base64.b64encode(chunk).decode("ascii"),
                    "overwrite": part_index == 0,
                    "append": part_index != 0,
                    "create_parent": part_index == 0,
                },
                timeout=60.0,
            )
            offset += len(chunk)
            part_index += 1
        return rel_path

    @staticmethod
    def _download_raw_file(conn: NoiseConnection, uri: str, timeout: float = 120.0) -> tuple[bytes, str]:
        """调用 GET /fs/raw/{*path} 直接拉取云端 VM 原图/原视频原始字节。"""
        raw_path = _to_fs_raw_path(uri)
        if not raw_path:
            raise MuseGenerationError(f"无法解析云端媒体路径: {uri}")
        status, headers, data = conn.request_bytes("GET", f"/fs/raw/{raw_path}", timeout=timeout)
        if status >= 400:
            raise MuseGenerationError(f"下载云端原文件失败 (HTTP {status}): {uri}")
        if not data:
            raise MuseGenerationError(f"云端原文件为空: {uri}")
        mime = (headers.get("content-type") or "").split(";", 1)[0].strip().lower()
        return data, mime

    @staticmethod
    def _open_chat_session(conn: NoiseConnection, session_id: str,
                           items: list[dict], device_id: str) -> tuple[str, NoiseSubscription]:
        """先通过 POST /chat/stream 创建独立隔离线程并投递消息，再订阅该线程的事件流（避免新建线程先 subscribe 报 404）。"""
        ack = conn.request_json(
            "POST",
            "/chat/stream",
            payload={
                "items": items,
                "node_id": device_id,
                "session_id": session_id,
                "capabilities": _CHAT_STREAM_CAPABILITIES,
                "timezone": "UTC",
            },
            timeout=45.0,
        )
        actual_sid = (ack.get("session_id") if isinstance(ack, dict) else None) or session_id
        sub_events = conn.open_subscription(
            "POST",
            "/chat/subscribe",
            payload={
                "session_id": actual_sid,
                "after_stream_seq": 0,
                "after_chat_event_seq": 0,
                "capabilities": _CHAT_SUBSCRIBE_CAPABILITIES,
            },
            timeout=30.0,
        )
        return actual_sid, sub_events

    @staticmethod
    def _next_unique_record(sub: NoiseSubscription, seen_keys: set[tuple],
                            timeout: float = 0.25) -> tuple[dict | None, bool]:
        """从订阅流读取下一条去重后的 NDJSON 事件记录，返回 (record, ended)。"""
        rec = sub.next_record(timeout=timeout)
        if rec is None:
            return None, sub._ended
        if rec.get("_eof"):
            return None, True
        if rec.get("type") == "event":
            ev_name = rec.get("event") or ""
            seq = rec.get("seq")
            payload = rec.get("payload") if isinstance(rec.get("payload"), dict) else {}
            msg_id = payload.get("message_id") or ""
            if seq is not None:
                dedup_key = (ev_name, seq, msg_id)
                if dedup_key in seen_keys:
                    return None, sub._ended
                seen_keys.add(dedup_key)
        return rec, sub._ended

    # ---------------- 流式文本对话 ----------------

    def chat_stream(self, cookies: dict, prompt: str, expires: dict | None = None,
                    timeout: int | None = None, account_id: str | None = None,
                    stop_event=None):
        """纯协议流式文本对话，逐片 yield 增量文本，支持 stop_event 即时取消云端生成。"""
        if not (prompt or "").strip():
            raise MuseGenerationError("对话提示词为空")
        total_timeout = float(timeout or self.cfg.chat_timeout)
        sess, conn = self._ensure_connection(cookies, expires, account_id=account_id)
        session_id = str(uuid.uuid4())
        items = [{"type": "text", "text": prompt}]
        sub_events: NoiseSubscription | None = None
        try:
            try:
                session_id, sub_events = self._open_chat_session(conn, session_id, items, sess.device_id)
            except NoiseHttpError as exc:
                if exc.status in (401, 403):
                    self._evict_connection(account_id)
                    raise MuseAuthError(f"对话鉴权失败 (HTTP {exc.status})") from None
                raise MuseGenerationError(str(exc)) from exc
            except NoiseTransportError as exc:
                self._evict_connection(account_id)
                raise MuseGenerationError(f"Noise 隧道异常: {exc}") from exc

            deadline = time.monotonic() + total_timeout
            seen_keys: set[tuple] = set()
            emitted_len = 0
            active_tools = 0
            done = False
            while time.monotonic() < deadline and not done:
                if stop_event is not None and stop_event.is_set():
                    self._cancel_session(conn, session_id)
                    return
                try:
                    rec, ended = self._next_unique_record(sub_events, seen_keys, timeout=0.25)
                except NoiseTransportError as exc:
                    self._evict_connection(account_id)
                    if emitted_len > 0:
                        return
                    raise MuseGenerationError(f"流式接收中断: {exc}") from exc

                if rec is not None:
                    if rec.get("ok") is False or (rec.get("type") != "event" and rec.get("error")):
                        err = rec.get("error")
                        msg = err.get("message") if isinstance(err, dict) else str(err)
                        raise MuseGenerationError(f"对话失败: {msg}")
                    if rec.get("type") != "event":
                        if ended:
                            break
                        continue
                    ev = rec.get("event") or ""
                    payload = rec.get("payload") if isinstance(rec.get("payload"), dict) else {}
                    ev_sid = payload.get("session_id")
                    if ev_sid and ev_sid != session_id:
                        if ended:
                            break
                        continue

                    if ev == "agent.status":
                        if payload.get("activity_code") == "out_of_credits":
                            raise MuseGenerationError("账号额度不足")
                    elif ev == "delta.tool_start":
                        active_tools += 1
                    elif ev == "delta.tool_done":
                        active_tools = max(0, active_tools - 1)
                    elif ev == "delta.text_append":
                        delta = payload.get("text")
                        if isinstance(delta, str) and delta:
                            emitted_len += len(delta)
                            yield delta
                    elif ev in ("delta.message_done", "message.assistant"):
                        status = payload.get("status")
                        if status == "failed":
                            raise MuseGenerationError("模型生成失败 (status=failed)")
                        refusal = _extract_static_refusal(payload)
                        if refusal:
                            if emitted_len == 0:
                                emitted_len += len(refusal)
                                yield refusal
                            done = True
                            break
                        final_text = payload.get("display_text") or payload.get("content") or _extract_transcript_text(payload)
                        if isinstance(final_text, str) and final_text and emitted_len == 0:
                            emitted_len += len(final_text)
                            yield final_text
                        # 仅当无未完成工具调用且已有正文或最终消息完成时结束对话
                        if active_tools == 0 and (ev == "delta.message_done" or payload.get("role") in (None, "assistant")):
                            done = True
                            break
                if ended:
                    break
            if emitted_len == 0 and not done:
                raise MuseGenerationError(f"对话在 {int(total_timeout)}s 内未收到模型回复")
        finally:
            if sub_events is not None:
                sub_events.close("chat_stream finished")

    # ---------------- 生图 / 生视频 ----------------

    def _prepare_reference_items(self, conn: NoiseConnection,
                                 refs: list[str]) -> tuple[list[dict], set[str], set[str]]:
        """校验并组装参考素材项：小图片内联 base64，大文件/视频/音频/文档走 /fs/write 上传为 file_ref。"""
        if len(refs) > MAX_REFERENCE_IMAGES:
            raise MuseGenerationError(f"参考素材最多 {MAX_REFERENCE_IMAGES} 个，当前传入 {len(refs)} 个")
        items: list[dict] = []
        upload_hashes: set[str] = set()
        uploaded_uris: set[str] = set()
        total_bytes = 0
        for idx, raw_ref in enumerate(refs, start=1):
            b64, mime = self._normalize_image(raw_ref)
            if not b64:
                continue
            raw_bytes = base64.b64decode(b64)
            total_bytes += len(raw_bytes)
            if total_bytes > MAX_REFERENCE_TOTAL_BYTES:
                raise MuseGenerationError(
                    f"参考素材总大小超过 {MAX_REFERENCE_TOTAL_BYTES // _MIB} MiB 限制"
                )
            upload_hashes.add(hashlib.sha256(raw_bytes).hexdigest())
            ext = REFERENCE_MIME_EXT.get(mime, ".bin")
            filename = f"ref_{idx}{ext}"
            kind = reference_kind(mime)
            if kind == "image" and len(raw_bytes) <= _INLINE_IMAGE_MAX_BYTES:
                items.append({
                    "type": "image",
                    "mime_type": mime,
                    "data_base64": b64,
                    "filename": filename,
                })
            else:
                vm_path = self._upload_file_to_vm(conn, raw_bytes, filename)
                uploaded_uris.add(_normalize_workspace_uri(vm_path))
                items.append({
                    "type": "file_ref",
                    "mime_type": mime,
                    "path": vm_path,
                    "filename": filename,
                })
        return items, upload_hashes, uploaded_uris

    def _fetch_history_media(self, conn: NoiseConnection, session_id: str,
                             candidates: dict[str, dict]):
        """实时流结束仍未拿到候选媒体时，通过 GET /chat/history 兜底检索该会话最新助手消息。"""
        try:
            query = urlencode({"session_id": session_id, "limit": 10})
            hist = conn.request_json("GET", f"/chat/history?{query}", timeout=15.0)
        except Exception as exc:  # noqa: BLE001
            log.debug("兜底查询 /chat/history 失败 (%s): %s", session_id, exc)
            return
        messages = hist.get("chat_events") or hist.get("messages") or hist.get("events") or []
        if isinstance(messages, list):
            for msg in messages:
                if isinstance(msg, dict):
                    role = msg.get("role")
                    ev_name = msg.get("event_name") or ""
                    if role == "user" or ev_name in ("message.user", "message.user_metadata_updated"):
                        continue
                    if role == "assistant" or ev_name in ("message.assistant", "delta.message_done", "delta.presentation"):
                        _collect_media_candidates(msg, candidates)

    def generate(self, cookies: dict, prompt: str, expect: str = "image",
                 timeout: int = 240, expires: dict | None = None,
                 account_id: str | None = None, on_progress=None,
                 reference_image: str | None = None,
                 reference_images: list[str] | None = None,
                 stop_event=None) -> dict:
        """纯协议驱动 muse.ai 生图/生视频并通过 /fs/raw 直取无损原图/原视频落盘。"""
        refs = [r for r in (reference_images or ([reference_image] if reference_image else [])) if r]
        sess, conn = self._ensure_connection(cookies, expires, account_id=account_id)
        items, upload_hashes, uploaded_uris = self._prepare_reference_items(conn, refs)
        items.append({"type": "text", "text": prompt})

        def report_progress(milestone: int):
            if callable(on_progress):
                try:
                    on_progress(milestone)
                except Exception:
                    pass

        session_id = str(uuid.uuid4())
        sub_events: NoiseSubscription | None = None
        try:
            try:
                session_id, sub_events = self._open_chat_session(conn, session_id, items, sess.device_id)
            except NoiseHttpError as exc:
                if exc.status in (401, 403):
                    self._evict_connection(account_id)
                    raise MuseAuthError(f"生成请求鉴权失败 (HTTP {exc.status})") from None
                raise MuseGenerationError(str(exc)) from exc
            except NoiseTransportError as exc:
                self._evict_connection(account_id)
                raise MuseGenerationError(f"Noise 隧道异常: {exc}") from exc

            deadline = time.monotonic() + float(timeout)
            seen_keys: set[tuple] = set()
            candidates: dict[str, dict] = {}
            text_chunks: list[str] = []
            final_text = ""
            milestone = 0
            active_tools = 0
            agent_busy = False
            turn_done = False
            done_at: float | None = None

            while time.monotonic() < deadline:
                if stop_event is not None and stop_event.is_set():
                    self._cancel_session(conn, session_id)
                    raise MuseGenerationError("任务已取消")
                try:
                    rec, ended = self._next_unique_record(sub_events, seen_keys, timeout=0.3)
                except NoiseTransportError as exc:
                    self._evict_connection(account_id)
                    raise MuseGenerationError(f"等待生成结果时 Noise 连接断开: {exc}") from exc

                if rec is not None:
                    if rec.get("ok") is False or (rec.get("type") != "event" and rec.get("error")):
                        err = rec.get("error")
                        msg = err.get("message") if isinstance(err, dict) else str(err)
                        raise MuseGenerationError(f"云端拒绝生成请求: {msg}")
                    if rec.get("type") == "event":
                        ev = rec.get("event") or ""
                        payload = rec.get("payload") if isinstance(rec.get("payload"), dict) else {}
                        ev_sid = payload.get("session_id")
                        if not (ev_sid and ev_sid != session_id) and ev not in ("message.user", "message.user_metadata_updated"):
                            _collect_media_candidates(rec, candidates)
                            for up_uri in uploaded_uris:
                                candidates.pop(up_uri, None)
                            if ev == "agent.status":
                                code = payload.get("activity_code")
                                if code == "out_of_credits":
                                    raise MuseGenerationError("账号额度不足")
                                if code in ("online", "idle", "ready", "completed", "disconnected", "offline", "connection_error"):
                                    agent_busy = False
                                elif code:
                                    agent_busy = True
                                if code == "making_something" and milestone < 25:
                                    milestone = 25
                                    report_progress(25)
                            elif ev == "task.status":
                                t_status = payload.get("status")
                                sub_cnt = payload.get("active_subagent_count") or 0
                                if t_status in ("completed", "failed", "cancelled") and sub_cnt == 0:
                                    agent_busy = False
                            elif ev == "delta.message_start":
                                turn_done = False
                                done_at = None
                                if milestone < 20:
                                    milestone = 20
                                    report_progress(20)
                            elif ev == "delta.tool_start":
                                active_tools += 1
                                turn_done = False
                                done_at = None
                                if milestone < 25:
                                    milestone = 25
                                    report_progress(25)
                            elif ev == "delta.tool_done":
                                active_tools = max(0, active_tools - 1)
                                if not self._has_matching_candidate(candidates, expect):
                                    turn_done = False
                                    done_at = None
                            elif ev == "delta.text_append":
                                delta = payload.get("text")
                                if isinstance(delta, str) and delta:
                                    text_chunks.append(delta)
                            elif ev in ("delta.message_done", "message.assistant"):
                                if payload.get("status") == "failed":
                                    raise MuseGenerationError("模型媒体生成失败 (status=failed)")
                                refusal = _extract_static_refusal(payload)
                                if refusal and not candidates:
                                    raise MuseModelRefusalError(f"模型未生成媒体，仅返回文本: {MuseEngine._clean_model_text(refusal)}")
                                txt = payload.get("display_text") or payload.get("content") or _extract_transcript_text(payload)
                                if isinstance(txt, str) and txt:
                                    final_text = txt
                                if ev == "delta.message_done" or payload.get("role") in (None, "assistant"):
                                    turn_done = True
                                    done_at = time.monotonic()

                # 已拿到匹配目标类型的媒体候选则立即进入原文件拉取
                if self._has_matching_candidate(candidates, expect):
                    break
                if turn_done and active_tools == 0 and not agent_busy:
                    # 若模型说“正在生成”等中间态文本，多等片刻以防后续工具/媒体事件延迟到达
                    combined_text = final_text or "".join(text_chunks)
                    wait_grace = 12.0 if MuseEngine._media_status_pending(combined_text) else 2.5
                    if ended or (done_at is not None and time.monotonic() - done_at >= wait_grace):
                        break
                if ended:
                    break

            if not self._has_matching_candidate(candidates, expect):
                self._fetch_history_media(conn, session_id, candidates)
                for up_uri in uploaded_uris:
                    candidates.pop(up_uri, None)

            # 排序：期望类型优先，后生成的候选优先（最新成品常在列表尾部）
            ordered = list(candidates.values())
            ordered.reverse()
            if expect == "video":
                ordered.sort(key=lambda item: 0 if item["kind"] == "video" or item["mime"].startswith("video/") else 1)
            else:
                ordered.sort(key=lambda item: 0 if item["kind"] == "image" or item["mime"].startswith("image/") else 1)

            if ordered:
                report_progress(40)

            matched_upload_only = False
            wrong_kind_ext: str | None = None
            for item in ordered:
                uri = item["uri"]
                if uri.startswith(("http://", "https://")):
                    continue
                data, header_mime = self._download_raw_file(conn, uri, timeout=120.0)
                if hashlib.sha256(data).hexdigest() in upload_hashes:
                    matched_upload_only = True
                    log.warning("命中的云端媒体是本次上传的参考素材，忽略: %s", uri)
                    continue
                mime = _sniff_mime(data) or header_mime or item["mime"] or ""
                ext = MuseEngine._pick_ext(mime, uri, expect)
                kind = "video" if ext in (".mp4", ".webm", ".mov") else "image"
                if expect == "video" and kind != "video":
                    wrong_kind_ext = ext
                    continue
                out_w, out_h = _probe_image_dims(data) if kind == "image" else (None, None)
                filename = f"{uuid.uuid4().hex}{ext}"
                dst = os.path.join(self.cfg.media_dir, filename)
                with open(dst, "wb") as fp:
                    fp.write(data)
                return {
                    "path": dst,
                    "filename": filename,
                    "size": len(data),
                    "ext": ext,
                    "mime": mime or _guess_mime_from_path(filename) or ("video/mp4" if kind == "video" else "image/png"),
                    "kind": kind,
                    "via": "noise_raw",
                    "attachment": uri,
                    "w": out_w,
                    "h": out_h,
                }

            if wrong_kind_ext is not None:
                raise MuseGenerationError(
                    f"期望生成视频，但提取成品类型为图片 ({wrong_kind_ext})，拒绝以图片冒充视频交付"
                )
            if matched_upload_only:
                raise MuseGenerationError("云端只返回了本次上传的参考素材，未出现新的生成结果")

            combined_text = (final_text or "".join(text_chunks)).strip()
            if combined_text:
                refusal_line = MuseEngine._media_refusal_text(combined_text, expect)
                clean = refusal_line or MuseEngine._clean_model_text(combined_text)
                if re.search(r"额度不足|积分不足|out of credits|达到上限|token limit", combined_text, re.I):
                    raise MuseGenerationError("账号额度不足")
                raise MuseModelRefusalError(f"模型未生成媒体，仅返回文本: {clean}")
            raise MuseGenerationError(f"等待生成结果超时 ({timeout}s)，未收到可用媒体文件")
        finally:
            if sub_events is not None:
                sub_events.close("generate finished")

    @staticmethod
    def _has_matching_candidate(candidates: dict[str, dict], expect: str) -> bool:
        for item in candidates.values():
            if expect == "video":
                if item["kind"] == "video" or item["mime"].startswith("video/"):
                    return True
            else:
                if item["kind"] == "image" or item["mime"].startswith("image/"):
                    return True
        return False
