"""muse.ai 纯协议传输层：Noise_XX 加密握手、Protobuf 帧编解码与多路复用 WebSocket。"""
from __future__ import annotations

import base64
import hashlib
import hmac
import ipaddress
import json
import logging
import os
import queue
import socket
import ssl
import struct
import threading
import time
import uuid
from dataclasses import dataclass, field
from urllib.parse import urlencode, urlsplit

import websocket
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.x25519 import (
    X25519PrivateKey,
    X25519PublicKey,
)
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

from proxy import normalize_server

log = logging.getLogger("muse2api")

DEFAULT_NOISE_WS_URL = "wss://hatch.metaaivm.com/v1/noise"
NOISE_PROTOCOL_NAME = b"Noise_XX_25519_AESGCM_SHA256"
MAX_NOISE_CHUNK_BYTES = 65489
MAX_NOISE_CHUNKS = 256
MAX_ASSEMBLED_BYTES = MAX_NOISE_CHUNK_BYTES * MAX_NOISE_CHUNKS
MAX_REQUEST_BODY_CHUNK = 512 * 1024
SERVICE_DAEMON = 0
STREAM_RESET_CANCELLED = 1
_UINT64_MASK = (1 << 64) - 1
_FRAME_EOF = object()


class NoiseTransportError(RuntimeError):
    """Noise 隧道底层通信、握手或协议解码错误。"""


class NoiseProxyError(NoiseTransportError):
    """经账号代理建连或认证失败，严禁回退直连。"""


class NoiseHttpError(NoiseTransportError):
    """隧道内 HTTP-over-Noise 返回 4xx/5xx 状态码。"""

    def __init__(self, status: int, message: str, body: str = ""):
        super().__init__(message)
        self.status = status
        self.body = body


# ---------------- 极简 Protobuf Wire 编解码 ----------------

def _pb_varint_bytes(value: int) -> bytes:
    """编码无符号或 64 位补码 varint。"""
    n = value & _UINT64_MASK if value < 0 else value
    out = bytearray()
    while True:
        byte = n & 0x7F
        n >>= 7
        if n:
            out.append(byte | 0x80)
        else:
            out.append(byte)
            return bytes(out)


def _pb_varint(field_num: int, value: int) -> bytes:
    return _pb_varint_bytes((field_num << 3) | 0) + _pb_varint_bytes(value)


def _pb_bytes(field_num: int, data: bytes) -> bytes:
    return _pb_varint_bytes((field_num << 3) | 2) + _pb_varint_bytes(len(data)) + data


def _pb_str(field_num: int, text: str) -> bytes:
    return _pb_bytes(field_num, text.encode("utf-8"))


def _pb_decode(buf: bytes) -> list[tuple[int, int, int | bytes]]:
    """按 protobuf wire format 解码字段列表 [(field_num, wire_type, value)]。"""
    idx = 0
    total = len(buf)
    fields: list[tuple[int, int, int | bytes]] = []

    def read_varint() -> int:
        nonlocal idx
        result = 0
        shift = 0
        while idx < total:
            byte = buf[idx]
            idx += 1
            result |= (byte & 0x7F) << shift
            if (byte & 0x80) == 0:
                return result
            shift += 7
            if shift > 70:
                raise NoiseTransportError("protobuf varint 溢出")
        raise NoiseTransportError("protobuf varint 意外截断")

    while idx < total:
        tag = read_varint()
        field_num = tag >> 3
        wire_type = tag & 7
        if wire_type == 0:
            fields.append((field_num, 0, read_varint()))
        elif wire_type == 2:
            length = read_varint()
            end = idx + length
            if end > total:
                raise NoiseTransportError("protobuf length-delimited 字段越界")
            fields.append((field_num, 2, buf[idx:end]))
            idx = end
        elif wire_type == 5:
            end = idx + 4
            if end > total:
                raise NoiseTransportError("protobuf fixed32 字段越界")
            fields.append((field_num, 5, buf[idx:end]))
            idx = end
        elif wire_type == 1:
            end = idx + 8
            if end > total:
                raise NoiseTransportError("protobuf fixed64 字段越界")
            fields.append((field_num, 1, buf[idx:end]))
            idx = end
        else:
            raise NoiseTransportError(f"不支持的 protobuf wire_type={wire_type}")
    return fields


def _encode_header(key: str, value: str) -> bytes:
    return _pb_str(1, key) + _pb_str(2, value)


def _decode_headers(raw_list: list[bytes]) -> list[tuple[str, str]]:
    headers: list[tuple[str, str]] = []
    for raw in raw_list:
        key = ""
        val = ""
        for fn, wt, v in _pb_decode(raw):
            if wt == 2 and isinstance(v, bytes):
                if fn == 1:
                    key = v.decode("utf-8", errors="replace")
                elif fn == 2:
                    val = v.decode("utf-8", errors="replace")
        if key:
            headers.append((key, val))
    return headers


def _encode_noise_chunks(service_req_bytes: bytes, chunk_id: int) -> list[bytes]:
    """按 65489 字节上限切分 NoiseTransportFrame，最多 256 片。"""
    total = max(1, (len(service_req_bytes) + MAX_NOISE_CHUNK_BYTES - 1) // MAX_NOISE_CHUNK_BYTES)
    if total > MAX_NOISE_CHUNKS:
        raise NoiseTransportError(f"单条 Noise 载荷过大 ({len(service_req_bytes)} 字节，分片数 {total} > 256)")
    frames: list[bytes] = []
    for index in range(total):
        start = index * MAX_NOISE_CHUNK_BYTES
        part = service_req_bytes[start:start + MAX_NOISE_CHUNK_BYTES]
        frames.append(
            _pb_varint(1, chunk_id)
            + _pb_varint(2, index)
            + _pb_varint(3, total)
            + _pb_bytes(4, part)
        )
    return frames


class _FrameAssembler:
    """重组服务端可能拆成多片的 NoiseTransportFrame。"""

    def __init__(self):
        self._pending: dict[int, tuple[int, dict[int, bytes], int]] = {}

    def feed(self, plaintext: bytes) -> bytes | None:
        chunk_id = 0
        chunk_index = 0
        total_chunks = 1
        payload = b""
        for fn, wt, val in _pb_decode(plaintext):
            if fn == 1 and wt == 0 and isinstance(val, int):
                chunk_id = val
            elif fn == 2 and wt == 0 and isinstance(val, int):
                chunk_index = val
            elif fn == 3 and wt == 0 and isinstance(val, int):
                total_chunks = val
            elif fn == 4 and wt == 2 and isinstance(val, bytes):
                payload = val
        if total_chunks < 1 or total_chunks > MAX_NOISE_CHUNKS:
            raise NoiseTransportError(f"非法 total_chunks={total_chunks}")
        if chunk_index < 0 or chunk_index >= total_chunks:
            raise NoiseTransportError(f"非法 chunk_index={chunk_index}/{total_chunks}")
        if total_chunks == 1:
            return payload
        entry = self._pending.get(chunk_id)
        if entry is None:
            if len(self._pending) >= 32:
                oldest = next(iter(self._pending))
                self._pending.pop(oldest, None)
            parts: dict[int, bytes] = {}
            acc_bytes = 0
        else:
            expected_total, parts, acc_bytes = entry
            if expected_total != total_chunks:
                self._pending.pop(chunk_id, None)
                raise NoiseTransportError("分片 total_chunks 不一致")
        if chunk_index in parts:
            self._pending.pop(chunk_id, None)
            raise NoiseTransportError(f"重复分片 chunk_index={chunk_index}")
        acc_bytes += len(payload)
        if acc_bytes > MAX_ASSEMBLED_BYTES:
            self._pending.pop(chunk_id, None)
            raise NoiseTransportError("重组帧超出长度上限")
        parts[chunk_index] = payload
        if len(parts) < total_chunks:
            self._pending[chunk_id] = (total_chunks, parts, acc_bytes)
            return None
        self._pending.pop(chunk_id, None)
        return b"".join(parts[i] for i in range(total_chunks))


# ---------------- Noise_XX_25519_AESGCM_SHA256 ----------------

def _sha256(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()


def _hmac_sha256(key: bytes, data: bytes) -> bytes:
    return hmac.new(key, data, hashlib.sha256).digest()


def _hkdf2(chaining_key: bytes, ikm: bytes) -> tuple[bytes, bytes]:
    temp = _hmac_sha256(chaining_key, ikm)
    out1 = _hmac_sha256(temp, b"\x01")
    out2 = _hmac_sha256(temp, out1 + b"\x02")
    return out1, out2


def _noise_nonce(counter: int) -> bytes:
    return struct.pack(">IQ", 0, counter)


def _x25519_pub_bytes(priv: X25519PrivateKey) -> bytes:
    return priv.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw,
    )


class _NoiseCipher:
    """Noise_XX 握手后的对称传输加解密状态。"""

    def __init__(self, send_key: bytes, recv_key: bytes):
        self._send_aes = AESGCM(send_key)
        self._recv_aes = AESGCM(recv_key)
        self._send_nonce = 0
        self._recv_nonce = 0

    def encrypt(self, plaintext: bytes) -> bytes:
        nonce = _noise_nonce(self._send_nonce)
        self._send_nonce += 1
        return self._send_aes.encrypt(nonce, plaintext, b"")

    def decrypt(self, ciphertext: bytes) -> bytes:
        nonce = _noise_nonce(self._recv_nonce)
        self._recv_nonce += 1
        return self._recv_aes.decrypt(nonce, ciphertext, b"")


def _run_noise_xx_handshake(ws: websocket.WebSocket, timeout: float) -> _NoiseCipher:
    """在已建立的二进制 WebSocket 上执行 Noise_XX 三步握手。"""
    ws.settimeout(timeout)
    h_state = NOISE_PROTOCOL_NAME.ljust(32, b"\x00")
    ck = h_state
    h_state = _sha256(h_state)  # 空 prologue
    key: bytes | None = None
    nonce_counter = 0

    def mix_hash(data: bytes):
        nonlocal h_state
        h_state = _sha256(h_state + data)

    def mix_key(ikm: bytes):
        nonlocal ck, key, nonce_counter
        ck, key = _hkdf2(ck, ikm)
        nonce_counter = 0

    def encrypt_and_hash(plaintext: bytes) -> bytes:
        nonlocal nonce_counter
        if key is None:
            mix_hash(plaintext)
            return plaintext
        ct = AESGCM(key).encrypt(_noise_nonce(nonce_counter), plaintext, h_state)
        nonce_counter += 1
        mix_hash(ct)
        return ct

    def decrypt_and_hash(ciphertext: bytes) -> bytes:
        nonlocal nonce_counter
        if key is None:
            mix_hash(ciphertext)
            return ciphertext
        pt = AESGCM(key).decrypt(_noise_nonce(nonce_counter), ciphertext, h_state)
        nonce_counter += 1
        mix_hash(ciphertext)
        return pt

    # msg1: 客户端临时公钥 + ClientHello{nonce: 32 bytes}
    ephemeral = X25519PrivateKey.generate()
    ephemeral_pub = _x25519_pub_bytes(ephemeral)
    mix_hash(ephemeral_pub)
    client_hello = b"\x0a\x20" + os.urandom(32)
    ws.send_binary(ephemeral_pub + encrypt_and_hash(client_hello))

    # msg2: 服务端临时公钥(32B) + 加密静态公钥(48B) + 加密载荷
    msg2 = ws.recv()
    if isinstance(msg2, str):
        raise NoiseTransportError(f"Noise 握手 msg2 收到非二进制帧: {msg2[:120]}")
    if not isinstance(msg2, (bytes, bytearray)) or len(msg2) < 80:
        raise NoiseTransportError(f"Noise 握手 msg2 长度无效: {len(msg2) if msg2 else 0}")
    msg2_bytes = bytes(msg2)
    remote_ephemeral = msg2_bytes[:32]
    mix_hash(remote_ephemeral)
    remote_ephemeral_key = X25519PublicKey.from_public_bytes(remote_ephemeral)
    mix_key(ephemeral.exchange(remote_ephemeral_key))
    remote_static = decrypt_and_hash(msg2_bytes[32:80])
    if len(remote_static) != 32:
        raise NoiseTransportError("Noise 握手服务端静态公钥长度无效")
    mix_key(ephemeral.exchange(X25519PublicKey.from_public_bytes(remote_static)))
    decrypt_and_hash(msg2_bytes[80:])

    # msg3: 客户端静态公钥 + 空载荷
    static_key = X25519PrivateKey.generate()
    enc_static = encrypt_and_hash(_x25519_pub_bytes(static_key))
    mix_key(static_key.exchange(remote_ephemeral_key))
    enc_empty = encrypt_and_hash(b"")
    ws.send_binary(enc_static + enc_empty)

    send_key, recv_key = _hkdf2(ck, b"")
    return _NoiseCipher(send_key, recv_key)


# ---------------- 代理隧道与 TLS Socket 建连 ----------------

def _read_exact(sock: socket.socket, size: int) -> bytes:
    buf = bytearray()
    while len(buf) < size:
        chunk = sock.recv(size - len(buf))
        if not chunk:
            raise OSError("代理连接在握手阶段关闭")
        buf.extend(chunk)
    return bytes(buf)


def _dial_tcp(target_host: str, target_port: int, proxy: dict | None, timeout: float) -> socket.socket:
    """建立到目标主机的 TCP 套接字；配置代理时强制走代理隧道，绝不回退直连。"""
    if not proxy:
        return socket.create_connection((target_host, target_port), timeout=timeout)

    try:
        parsed = urlsplit(normalize_server(proxy["server"]))
    except ValueError as exc:
        raise NoiseProxyError(f"账号代理配置无效: {exc}") from None

    proxy_host = parsed.hostname
    proxy_port = parsed.port
    scheme = parsed.scheme
    username = (proxy.get("username") or "").encode("latin-1")
    password = (proxy.get("password") or "").encode("latin-1")
    try:
        sock = socket.create_connection((proxy_host, proxy_port), timeout=timeout)
    except OSError as exc:
        raise NoiseProxyError(f"无法连接账号代理 ({type(exc).__name__})；未回退直连") from None

    try:
        sock.settimeout(timeout)
        if scheme in ("socks5", "socks5h"):
            if len(username) > 255 or len(password) > 255:
                raise NoiseProxyError("SOCKS5 代理凭据长度超过 255 字节")
            method = 2 if (username or password) else 0
            sock.sendall(bytes((5, 1, method)))
            if _read_exact(sock, 2) != bytes((5, method)):
                raise NoiseProxyError("SOCKS5 代理拒绝认证方式")
            if method == 2:
                sock.sendall(bytes((1, len(username))) + username + bytes((len(password),)) + password)
                if _read_exact(sock, 2) != bytes((1, 0)):
                    raise NoiseProxyError("SOCKS5 代理认证失败")
            try:
                addr = ipaddress.ip_address(target_host)
                dest = bytes((1 if addr.version == 4 else 4,)) + addr.packed
            except ValueError:
                # 始终让代理端解析域名，防止本地 DNS 泄漏。
                domain = target_host.encode("idna")
                dest = bytes((3, len(domain))) + domain
            sock.sendall(bytes((5, 1, 0)) + dest + int(target_port).to_bytes(2, "big"))
            reply = _read_exact(sock, 4)
            if reply[:3] != bytes((5, 0, 0)):
                raise NoiseProxyError(f"SOCKS5 代理拒绝建立隧道 (code={reply[1]})")
            atyp = reply[3]
            if atyp == 1:
                _read_exact(sock, 4 + 2)
            elif atyp == 4:
                _read_exact(sock, 16 + 2)
            elif atyp == 3:
                domain_len = _read_exact(sock, 1)[0]
                _read_exact(sock, domain_len + 2)
            else:
                raise NoiseProxyError("SOCKS5 代理返回非法地址类型")
            return sock

        # HTTP CONNECT 隧道
        authority = f"[{target_host}]:{target_port}" if ":" in target_host else f"{target_host}:{target_port}"
        lines = [f"CONNECT {authority} HTTP/1.1", f"Host: {authority}", "Proxy-Connection: Keep-Alive"]
        if username or password:
            token = base64.b64encode(username + b":" + password).decode("ascii")
            lines.append(f"Proxy-Authorization: Basic {token}")
        sock.sendall(("\r\n".join(lines) + "\r\n\r\n").encode("latin-1"))
        head = bytearray()
        while not head.endswith(b"\r\n\r\n"):
            chunk = sock.recv(1)
            if not chunk:
                raise NoiseProxyError("HTTP 代理在 CONNECT 握手阶段断开连接")
            head.extend(chunk)
            if len(head) > 65536:
                raise NoiseProxyError("HTTP 代理响应头过大")
        status_line = bytes(head).split(b"\r\n", 1)[0].decode("latin-1", errors="replace")
        parts = status_line.split(" ", 2)
        code = int(parts[1]) if len(parts) >= 2 and parts[1].isdigit() else 0
        if code == 407:
            raise NoiseProxyError("账号代理认证失败 (HTTP 407)，未回退直连")
        if code != 200:
            raise NoiseProxyError(f"HTTP 代理拒绝 CONNECT 隧道 (HTTP {code})；未回退直连")
        return sock
    except NoiseProxyError:
        sock.close()
        raise
    except OSError as exc:
        sock.close()
        raise NoiseProxyError(f"经账号代理建立隧道失败 ({type(exc).__name__})；未回退直连") from None


# ---------------- 多路复用 NoiseConnection ----------------

@dataclass
class _StreamInbox:
    queue: queue.Queue = field(default_factory=queue.Queue)


@dataclass
class _DecodedFrame:
    kind: str  # "response" | "body_chunk" | "reset"
    stream_id: int
    status: int = 0
    headers: list[tuple[str, str]] = field(default_factory=list)
    data: bytes = b""
    end_body: bool = False
    reset_code: int = 0
    reset_reason: str = ""


def _decode_service_response(raw: bytes) -> _DecodedFrame | None:
    sf_bytes = b""
    for fn, wt, val in _pb_decode(raw):
        if fn == 1 and wt == 2 and isinstance(val, bytes):
            sf_bytes = val
    if not sf_bytes:
        return None
    stream_id = 0
    resp_bytes: bytes | None = None
    chunk_bytes: bytes | None = None
    reset_bytes: bytes | None = None
    for fn, wt, val in _pb_decode(sf_bytes):
        if fn == 1 and wt == 0 and isinstance(val, int):
            stream_id = val
        elif fn == 3 and wt == 2 and isinstance(val, bytes):
            resp_bytes = val
        elif fn == 4 and wt == 2 and isinstance(val, bytes):
            chunk_bytes = val
        elif fn == 5 and wt == 2 and isinstance(val, bytes):
            reset_bytes = val

    if resp_bytes is not None:
        status = 0
        raw_headers: list[bytes] = []
        body = b""
        end_body = False
        for fn, wt, val in _pb_decode(resp_bytes):
            if fn == 1 and wt == 0 and isinstance(val, int):
                status = val
            elif fn == 2 and wt == 2 and isinstance(val, bytes):
                raw_headers.append(val)
            elif fn == 3 and wt == 2 and isinstance(val, bytes):
                body = val
            elif fn == 4 and wt == 0 and isinstance(val, int):
                end_body = val != 0
        return _DecodedFrame(
            kind="response",
            stream_id=stream_id,
            status=status,
            headers=_decode_headers(raw_headers),
            data=body,
            end_body=end_body,
        )
    if chunk_bytes is not None:
        data = b""
        end_body = False
        for fn, wt, val in _pb_decode(chunk_bytes):
            if fn == 1 and wt == 2 and isinstance(val, bytes):
                data = val
            elif fn == 2 and wt == 0 and isinstance(val, int):
                end_body = val != 0
        return _DecodedFrame(
            kind="body_chunk",
            stream_id=stream_id,
            data=data,
            end_body=end_body,
        )
    if reset_bytes is not None:
        code = 0
        reason = ""
        for fn, wt, val in _pb_decode(reset_bytes):
            if fn == 1 and wt == 0 and isinstance(val, int):
                code = val
            elif fn == 2 and wt == 2 and isinstance(val, bytes):
                reason = val.decode("utf-8", errors="replace")
        return _DecodedFrame(
            kind="reset",
            stream_id=stream_id,
            reset_code=code,
            reset_reason=reason,
        )
    return None


class NoiseSubscription:
    """一条持续接收 NDJSON 事件的 Noise 订阅流。"""

    def __init__(self, conn: NoiseConnection, stream_id: int, inbox: _StreamInbox,
                 ack: dict, pending_lines: list[str], ended: bool):
        self._conn = conn
        self.stream_id = stream_id
        self._inbox = inbox
        self.ack = ack
        self._buffer = ""
        self._queued_records: list[dict] = []
        self._ended = ended
        self._closed = False
        for line in pending_lines:
            rec = self._parse_line(line)
            if rec is not None:
                self._queued_records.append(rec)

    @staticmethod
    def _parse_line(line: str) -> dict | None:
        text = line.strip()
        if not text:
            return None
        try:
            obj = json.loads(text)
        except ValueError:
            return None
        return obj if isinstance(obj, dict) else None

    def next_record(self, timeout: float = 1.0) -> dict | None:
        """阻塞读取下一条 NDJSON 事件；超时返回 None，流结束返回 {'_eof': True}。"""
        if self._queued_records:
            return self._queued_records.pop(0)
        if self._ended:
            return {"_eof": True}
        deadline = time.monotonic() + max(0.05, timeout)
        while True:
            remain = deadline - time.monotonic()
            if remain <= 0:
                return None
            try:
                item = self._inbox.queue.get(timeout=min(remain, 0.5))
            except queue.Empty:
                if self._ended or not self._conn.is_alive():
                    self._ended = True
                    return {"_eof": True}
                continue
            if item is _FRAME_EOF:
                self._ended = True
                if self._buffer.strip():
                    rec = self._parse_line(self._buffer)
                    self._buffer = ""
                    if rec is not None:
                        return rec
                return {"_eof": True}
            if isinstance(item, Exception):
                self._ended = True
                raise item
            frame: _DecodedFrame = item
            if frame.kind == "reset":
                self._ended = True
                return {"_eof": True, "_reset": frame.reset_reason, "_reset_code": frame.reset_code}
            if frame.data:
                self._buffer += frame.data.decode("utf-8", errors="replace")
                if "\n" in self._buffer:
                    lines = self._buffer.split("\n")
                    self._buffer = lines.pop()
                    for ln in lines:
                        rec = self._parse_line(ln)
                        if rec is not None:
                            self._queued_records.append(rec)
            if frame.end_body:
                self._ended = True
                if self._buffer.strip():
                    rec = self._parse_line(self._buffer)
                    self._buffer = ""
                    if rec is not None:
                        self._queued_records.append(rec)
            if self._queued_records:
                return self._queued_records.pop(0)
            if self._ended:
                return {"_eof": True}

    def close(self, reason: str = "client closed"):
        if self._closed:
            return
        self._closed = True
        if not self._ended and self._conn.is_alive():
            try:
                self._conn.send_reset(self.stream_id, reason)
            except Exception:
                pass
        self._conn._drop_stream(self.stream_id)


class NoiseConnection:
    """单条已握手的 Noise 加密 WebSocket 连接，支持多线程多路复用 stream_id。"""

    def __init__(self, ws_url: str, proxy: dict | None = None,
                 connect_timeout: float = 20.0):
        self.ws_url = ws_url
        self._send_lock = threading.Lock()
        self._streams_lock = threading.Lock()
        self._streams: dict[int, _StreamInbox] = {}
        self._next_stream_id = 1
        self._next_chunk_id = 1
        self._closed = False
        self._fatal_error: Exception | None = None
        self._last_activity = time.monotonic()
        self._assembler = _FrameAssembler()

        parsed = urlsplit(ws_url)
        is_secure = parsed.scheme == "wss"
        host = parsed.hostname or "hatch.metaaivm.com"
        port = parsed.port or (443 if is_secure else 80)

        raw_sock = _dial_tcp(host, port, proxy, timeout=connect_timeout)
        sock: socket.socket = raw_sock
        try:
            if is_secure:
                ctx = ssl.create_default_context()
                sock = ctx.wrap_socket(raw_sock, server_hostname=host)
            self._ws = websocket.create_connection(
                ws_url,
                socket=sock,
                timeout=connect_timeout,
                origin="https://muse.ai",
                header=[
                    "User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/135.0.0.0 Safari/537.36",
                ],
                skip_utf8_validation=True,
            )
            self._cipher = _run_noise_xx_handshake(self._ws, timeout=connect_timeout)
        except NoiseProxyError:
            try:
                sock.close()
            except OSError:
                pass
            raise
        except Exception as exc:
            try:
                sock.close()
            except OSError:
                pass
            if proxy and isinstance(exc, OSError):
                raise NoiseProxyError(f"经账号代理完成 Noise 握手失败: {exc}") from None
            raise NoiseTransportError(f"Noise WebSocket 建连或握手失败: {exc}") from exc

        self._ws.settimeout(1.0)
        self._recv_thread = threading.Thread(
            target=self._recv_loop, name="noise-recv", daemon=True
        )
        self._recv_thread.start()

    @classmethod
    def connect(cls, vm_id: str, auth_token: str, notary_token: str,
                proxy: dict | None = None, base_url: str = DEFAULT_NOISE_WS_URL,
                timeout: float = 20.0) -> NoiseConnection:
        query = urlencode({
            "vm_id": vm_id,
            "auth_token": auth_token,
            "notary_token": notary_token,
            "app_id": "hatch-web",
            "app_version": "1",
            "request_id": str(uuid.uuid4()),
        })
        sep = "&" if "?" in base_url else "?"
        return cls(f"{base_url}{sep}{query}", proxy=proxy, connect_timeout=timeout)

    def is_alive(self) -> bool:
        return not self._closed and self._fatal_error is None

    def _drop_stream(self, stream_id: int):
        with self._streams_lock:
            self._streams.pop(stream_id, None)

    def _fail_all(self, exc: Exception | None):
        with self._streams_lock:
            if self._closed and self._fatal_error is not None:
                return
            self._closed = True
            if exc is not None:
                self._fatal_error = exc
            inboxes = list(self._streams.values())
            self._streams.clear()
        sentinel = exc if exc is not None else _FRAME_EOF
        for inbox in inboxes:
            inbox.queue.put(sentinel)

    def _recv_loop(self):
        while not self._closed:
            try:
                raw = self._ws.recv()
            except websocket.WebSocketTimeoutException:
                continue
            except websocket.WebSocketConnectionClosedException:
                self._fail_all(NoiseTransportError("Noise WebSocket 连接已关闭"))
                return
            except OSError as exc:
                if self._closed:
                    return
                self._fail_all(NoiseTransportError(f"Noise WebSocket 读取异常: {exc}"))
                return
            except Exception as exc:  # noqa: BLE001
                if self._closed:
                    return
                self._fail_all(NoiseTransportError(f"Noise WebSocket 意外错误: {exc}"))
                return

            if not raw:
                self._fail_all(NoiseTransportError("Noise WebSocket 收到空关闭帧"))
                return
            if isinstance(raw, str):
                continue
            try:
                plaintext = self._cipher.decrypt(bytes(raw))
                assembled = self._assembler.feed(plaintext)
                if assembled is None:
                    continue
                frame = _decode_service_response(assembled)
            except Exception as exc:  # noqa: BLE001
                self._fail_all(NoiseTransportError(f"Noise 帧解密或解码失败: {exc}"))
                return
            if frame is None:
                continue
            self._last_activity = time.monotonic()
            with self._streams_lock:
                inbox = self._streams.get(frame.stream_id)
            if inbox is not None:
                inbox.queue.put(frame)

    def _send_service_frame(self, service_frame_bytes: bytes):
        """加密并按顺序发出 ServiceRequest；加密与发送共享同一锁保证 nonce 严格递增。"""
        service_req = _pb_varint(1, SERVICE_DAEMON) + _pb_bytes(2, service_frame_bytes)
        with self._send_lock:
            if self._closed:
                raise self._fatal_error or NoiseTransportError("Noise 连接已关闭")
            chunk_id = self._next_chunk_id
            self._next_chunk_id += 1
            chunks = _encode_noise_chunks(service_req, chunk_id)
            for chunk in chunks:
                ct = self._cipher.encrypt(chunk)
                self._ws.send_binary(ct)

    def send_reset(self, stream_id: int, reason: str = ""):
        reset_msg = _pb_varint(1, STREAM_RESET_CANCELLED) + (_pb_str(2, reason) if reason else b"")
        sf = _pb_varint(1, stream_id) + _pb_bytes(5, reset_msg)
        self._send_service_frame(sf)

    def _start_request(self, verb: str, path: str, body: bytes = b"",
                       headers: list[tuple[str, str]] | None = None) -> tuple[int, _StreamInbox]:
        """注册 stream_id 并发送 HTTP-over-Noise 请求（大请求体自动拆分为 BodyChunk）。"""
        if not self.is_alive():
            raise self._fatal_error or NoiseTransportError("Noise 连接不可用")
        req_headers: list[tuple[str, str]] = [
            ("x-request-id", str(uuid.uuid4())),
            ("x-app-id", "hatch-web"),
            ("Accept-Encoding", "identity"),
            ("Accept-Language", "zh-CN"),
        ]
        if headers:
            existing = {k.lower() for k, _ in headers}
            req_headers = [pair for pair in req_headers if pair[0].lower() not in existing]
            req_headers.extend(headers)

        with self._streams_lock:
            stream_id = self._next_stream_id
            self._next_stream_id += 1
            inbox = _StreamInbox()
            self._streams[stream_id] = inbox

        try:
            first_body = body[:MAX_REQUEST_BODY_CHUNK]
            rest_offset = len(first_body)
            end_first = rest_offset >= len(body)

            app_parts = [_pb_str(1, verb), _pb_str(2, path)]
            for k, v in req_headers:
                app_parts.append(_pb_bytes(3, _encode_header(k, v)))
            if first_body:
                app_parts.append(_pb_bytes(4, first_body))
            app_parts.append(_pb_varint(5, 1 if end_first else 0))
            app_req = b"".join(app_parts)
            self._send_service_frame(_pb_varint(1, stream_id) + _pb_bytes(2, app_req))

            while rest_offset < len(body):
                part = body[rest_offset:rest_offset + MAX_REQUEST_BODY_CHUNK]
                rest_offset += len(part)
                is_last = rest_offset >= len(body)
                body_chunk = _pb_bytes(1, part) + _pb_varint(2, 1 if is_last else 0)
                self._send_service_frame(_pb_varint(1, stream_id) + _pb_bytes(4, body_chunk))
        except Exception:
            self._drop_stream(stream_id)
            raise
        return stream_id, inbox

    def request_bytes(self, verb: str, path: str, body: bytes = b"",
                      headers: list[tuple[str, str]] | None = None,
                      timeout: float = 60.0) -> tuple[int, dict[str, str], bytes]:
        """发送单次 HTTP-over-Noise 请求并完整收集响应字节。"""
        stream_id, inbox = self._start_request(verb, path, body=body, headers=headers)
        deadline = time.monotonic() + timeout
        status = 0
        resp_headers: dict[str, str] = {}
        parts: list[bytes] = []
        try:
            while True:
                remain = deadline - time.monotonic()
                if remain <= 0:
                    try:
                        self.send_reset(stream_id, "client timeout")
                    except Exception:
                        pass
                    raise TimeoutError(f"Noise 请求超时 ({verb} {path})")
                try:
                    item = inbox.queue.get(timeout=min(remain, 1.0))
                except queue.Empty:
                    if not self.is_alive():
                        raise self._fatal_error or NoiseTransportError("Noise 连接在等待响应期间断开")
                    continue
                if item is _FRAME_EOF:
                    raise NoiseTransportError(f"Noise 连接提前断开 ({verb} {path})")
                if isinstance(item, Exception):
                    raise item
                frame: _DecodedFrame = item
                if frame.kind == "reset":
                    raise NoiseTransportError(
                        f"Noise 流被对端重置 ({verb} {path}: code={frame.reset_code} {frame.reset_reason})"
                    )
                if frame.kind == "response":
                    status = frame.status
                    resp_headers = {k.lower(): v for k, v in frame.headers}
                    if frame.data:
                        parts.append(frame.data)
                    if frame.end_body:
                        break
                elif frame.kind == "body_chunk":
                    if frame.data:
                        parts.append(frame.data)
                    if frame.end_body:
                        break
            return status, resp_headers, b"".join(parts)
        finally:
            self._drop_stream(stream_id)

    def request_json(self, verb: str, path: str, payload: dict | None = None,
                     timeout: float = 30.0,
                     headers: list[tuple[str, str]] | None = None) -> dict:
        """发送 JSON RPC 请求并自动解包 {ok: true, result: ...} 或原始对象。"""
        req_headers = list(headers or [])
        body = b""
        if payload is not None:
            body = json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
            req_headers.append(("Content-Type", "application/json"))
        status, _, raw = self.request_bytes(verb, path, body=body, headers=req_headers, timeout=timeout)
        text = raw.decode("utf-8", errors="replace")
        if status >= 400:
            raise NoiseHttpError(status, f"Noise HTTP {status} ({verb} {path}): {text[:240]}", body=text)
        if not text.strip():
            return {}
        data = json.loads(text)
        if isinstance(data, dict):
            if data.get("ok") is False or ("error" in data and data.get("error")):
                err = data.get("error")
                msg = err.get("message") if isinstance(err, dict) else str(err)
                raise NoiseHttpError(status or 500, f"Noise RPC 错误 ({verb} {path}): {msg}", body=text)
            if data.get("ok") is True and "result" in data and isinstance(data["result"], dict):
                return data["result"]
            return data
        return {"value": data}

    def open_subscription(self, verb: str, path: str, payload: dict | None = None,
                          timeout: float = 30.0) -> NoiseSubscription:
        """打开一条 NDJSON 订阅流（如 /chat/subscribe 或 /chat/stream），等待首包或 ack。"""
        req_headers: list[tuple[str, str]] = []
        body = b""
        if payload is not None:
            body = json.dumps(payload, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
            req_headers.append(("Content-Type", "application/json"))
        stream_id, inbox = self._start_request(verb, path, body=body, headers=req_headers)
        deadline = time.monotonic() + timeout
        status = 0
        text_buf = ""
        ended = False
        try:
            while True:
                remain = deadline - time.monotonic()
                if remain <= 0:
                    try:
                        self.send_reset(stream_id, "subscription ack timeout")
                    except Exception:
                        pass
                    raise TimeoutError(f"Noise 订阅握手超时 ({verb} {path})")
                try:
                    item = inbox.queue.get(timeout=min(remain, 0.5))
                except queue.Empty:
                    if not self.is_alive():
                        raise self._fatal_error or NoiseTransportError("Noise 连接在等待订阅响应时断开")
                    continue
                if item is _FRAME_EOF:
                    raise NoiseTransportError(f"Noise 订阅在收到确认前断开 ({verb} {path})")
                if isinstance(item, Exception):
                    raise item
                frame: _DecodedFrame = item
                if frame.kind == "reset":
                    raise NoiseTransportError(
                        f"Noise 订阅流被重置 ({verb} {path}: code={frame.reset_code} {frame.reset_reason})"
                    )
                if frame.kind == "response":
                    status = frame.status
                    if frame.data:
                        text_buf += frame.data.decode("utf-8", errors="replace")
                    ended = frame.end_body
                    if status >= 400:
                        # 读完残余错误体以便定位原因
                        while not ended and time.monotonic() < deadline:
                            try:
                                more = inbox.queue.get(timeout=0.3)
                            except queue.Empty:
                                break
                            if isinstance(more, _DecodedFrame):
                                if more.data:
                                    text_buf += more.data.decode("utf-8", errors="replace")
                                if more.end_body or more.kind == "reset":
                                    break
                        raise NoiseHttpError(status, f"Noise HTTP {status} ({verb} {path}): {text_buf[:240]}", body=text_buf)
                elif frame.kind == "body_chunk":
                    if frame.data:
                        text_buf += frame.data.decode("utf-8", errors="replace")
                    ended = frame.end_body

                # 判断是否已拿到首个完整 JSON（可能是 ack，也可能直接是 type=="event"）
                if status and ("\n" in text_buf or ended):
                    lines = text_buf.split("\n")
                    if not ended:
                        tail = lines.pop()
                    else:
                        tail = ""
                    non_empty = [ln for ln in lines if ln.strip()]
                    if not non_empty and not ended:
                        text_buf = tail
                        continue
                    ack: dict = {}
                    pending_lines: list[str] = []
                    if non_empty:
                        first_obj = None
                        try:
                            first_obj = json.loads(non_empty[0])
                        except ValueError:
                            first_obj = None
                        if isinstance(first_obj, dict) and first_obj.get("type") == "event":
                            pending_lines = non_empty
                        elif isinstance(first_obj, dict):
                            if first_obj.get("ok") is False or first_obj.get("error"):
                                err = first_obj.get("error")
                                msg = err.get("message") if isinstance(err, dict) else str(err)
                                raise NoiseHttpError(status, f"Noise 订阅被拒 ({verb} {path}): {msg}", body=non_empty[0])
                            ack = first_obj.get("result") if (first_obj.get("ok") is True and isinstance(first_obj.get("result"), dict)) else first_obj
                            pending_lines = non_empty[1:]
                    sub = NoiseSubscription(self, stream_id, inbox, ack, pending_lines, ended)
                    sub._buffer = tail
                    return sub
                # 部分接口首包 response(200, body=b"", end_body=False) 后直接等事件，无需死等首行
                if status and 200 <= status < 300 and not text_buf and frame.kind == "response" and not ended:
                    return NoiseSubscription(self, stream_id, inbox, {}, [], False)
        except Exception:
            self._drop_stream(stream_id)
            raise

    def ping(self, timeout: float = 8.0) -> dict:
        return self.request_json("POST", "/api/ping", timeout=timeout)

    def close(self):
        self._fail_all(None)
        try:
            self._ws.close()
        except Exception:
            pass
