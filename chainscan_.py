from __future__ import annotations
import argparse
import hashlib
import json
import os
import re
import struct
import sys
import threading
import time
import types
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple
P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G = (GX, GY)
def _inv_mod(a: int, m: int = P) -> int:
    return pow(a % m, m - 2, m)
def point_add(p: Optional[Tuple[int, int]], q: Optional[Tuple[int, int]]) -> Optional[Tuple[int, int]]:
    if p is None:
        return q
    if q is None:
        return p
    if p[0] == q[0]:
        if (p[1] + q[1]) % P == 0:
            return None  # p == -q
        lam = (3 * p[0] * p[0]) * _inv_mod(2 * p[1]) % P  # doubling
    else:
        lam = (q[1] - p[1]) * _inv_mod(q[0] - p[0]) % P
    x = (lam * lam - p[0] - q[0]) % P
    y = (lam * (p[0] - x) - p[1]) % P
    return (x, y)
def point_mul(k: int, p: Optional[Tuple[int, int]] = G) -> Optional[Tuple[int, int]]:
    k %= N
    if k == 0 or p is None:
        return None
    result = None
    addend = p
    while k:
        if k & 1:
            result = point_add(result, addend)
        addend = point_add(addend, addend)
        k >>= 1
    return result
def public_key_bytes(priv_int: int, compressed: bool = True) -> bytes:
    if not (0 < priv_int < N):
        raise ValueError("private key out of secp256k1 range")
    pt = point_mul(priv_int)
    if pt is None:
        raise ValueError("invalid private key (point at infinity)")
    x = pt[0].to_bytes(32, "big")
    y = pt[1].to_bytes(32, "big")
    if compressed:
        return (b"\x02" if pt[1] % 2 == 0 else b"\x03") + x
    return b"\x04" + x + y
_RL = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
    7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
    3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
    1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
    4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13,
]
_RR = [
    5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
    6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
    15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
    8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
    12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11,
]
_SL = [
    11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
    7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
    11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
    11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
    9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6,
]
_SR = [
    8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
    9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
    9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
    15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
    8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11,
]
_KL = (0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E)
_KR = (0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000)
_M32 = 0xFFFFFFFF
def _rol32(x: int, n: int) -> int:
    return ((x << n) | (x >> (32 - n))) & _M32
def _rmd_f(j: int, x: int, y: int, z: int) -> int:
    if j < 16:
        return x ^ y ^ z
    if j < 32:
        return (x & y) | ((~x & _M32) & z)
    if j < 48:
        return (x | (~y & _M32)) ^ z
    if j < 64:
        return (x & z) | (y & (~z & _M32))
    return x ^ (y | (~z & _M32))
def ripemd160(data: bytes) -> bytes:
    h = [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]
    bit_len = (len(data) * 8) & 0xFFFFFFFFFFFFFFFF
    padded = data + b"\x80" + b"\x00" * ((56 - (len(data) + 1) % 64) % 64) + struct.pack("<Q", bit_len)
    for off in range(0, len(padded), 64):
        x = struct.unpack("<16L", padded[off:off + 64])
        al, bl, cl, dl, el = h
        ar, br, cr, dr, er = h
        for j in range(80):
            t = (al + _rmd_f(j, bl, cl, dl) + x[_RL[j]] + _KL[j >> 4]) & _M32
            t = (_rol32(t, _SL[j]) + el) & _M32
            al, el, dl, cl, bl = el, dl, _rol32(cl, 10), bl, t
            t = (ar + _rmd_f(79 - j, br, cr, dr) + x[_RR[j]] + _KR[j >> 4]) & _M32
            t = (_rol32(t, _SR[j]) + er) & _M32
            ar, er, dr, cr, br = er, dr, _rol32(cr, 10), br, t
        t = (h[1] + cl + dr) & _M32
        h[1] = (h[2] + dl + er) & _M32
        h[2] = (h[3] + el + ar) & _M32
        h[3] = (h[4] + al + br) & _M32
        h[4] = (h[0] + bl + cr) & _M32
        h[0] = t
    return struct.pack("<5L", *h)
def sha256(b: bytes) -> bytes:
    return hashlib.sha256(b).digest()
def hash160(b: bytes) -> bytes:
    return ripemd160(sha256(b))
_B58_ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
_B58_INDEX = {c: i for i, c in enumerate(_B58_ALPHABET)}
def b58encode(data: bytes) -> str:
    n = int.from_bytes(data, "big")
    out = ""
    while n > 0:
        n, rem = divmod(n, 58)
        out = _B58_ALPHABET[rem] + out
    pad = 0
    for byte in data:
        if byte != 0:
            break
        pad += 1
    return "1" * pad + out
def b58decode(s: str) -> bytes:
    n = 0
    for ch in s:
        if ch not in _B58_INDEX:
            raise ValueError(f"invalid Base58 character: {ch!r}")
        n = n * 58 + _B58_INDEX[ch]
    body = n.to_bytes((n.bit_length() + 7) // 8, "big") if n else b""
    pad = 0
    for ch in s:
        if ch != "1":
            break
        pad += 1
    return b"\x00" * pad + body
def b58check_encode(version: bytes, payload: bytes) -> str:
    raw = version + payload
    checksum = sha256(sha256(raw))[:4]
    return b58encode(raw + checksum)
def b58check_decode(s: str) -> bytes:
    raw = b58decode(s)
    if len(raw) < 5:
        raise ValueError("Base58Check string too short")
    body, checksum = raw[:-4], raw[-4:]
    if sha256(sha256(body))[:4] != checksum:
        raise ValueError("Base58Check checksum mismatch")
    return body
_BECH32_CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
_BECH32_CONST = 1
_BECH32M_CONST = 0x2BC830A3
def _bech32_polymod(values: List[int]) -> int:
    gen = (0x3B6A57B2, 0x26508E6D, 0x1EA119FA, 0x3D4233DD, 0x2A1462B3)
    chk = 1
    for v in values:
        top = chk >> 25
        chk = ((chk & 0x1FFFFFF) << 5) ^ v
        for i in range(5):
            if (top >> i) & 1:
                chk ^= gen[i]
    return chk
def _bech32_hrp_expand(hrp: str) -> List[int]:
    return [ord(c) >> 5 for c in hrp] + [0] + [ord(c) & 31 for c in hrp]
def _bech32_checksum(hrp: str, data: List[int], const: int) -> List[int]:
    values = _bech32_hrp_expand(hrp) + data
    polymod = _bech32_polymod(values + [0] * 6) ^ const
    return [(polymod >> 5 * (5 - i)) & 31 for i in range(6)]
def _convertbits(data, from_bits: int, to_bits: int, pad: bool = True) -> List[int]:
    acc = 0
    bits = 0
    ret = []
    maxv = (1 << to_bits) - 1
    for value in data:
        acc = (acc << from_bits) | value
        bits += from_bits
        while bits >= to_bits:
            bits -= to_bits
            ret.append((acc >> bits) & maxv)
    if pad and bits:
        ret.append((acc << (to_bits - bits)) & maxv)
    return ret
def segwit_encode(hrp: str, witver: int, witprog: bytes) -> str:
    if not 0 <= witver <= 16:
        raise ValueError("witness version must be 0..16")
    if not 2 <= len(witprog) <= 40:
        raise ValueError("witness program must be 2..40 bytes")
    const = _BECH32_CONST if witver == 0 else _BECH32M_CONST
    data = [witver] + _convertbits(list(witprog), 8, 5)
    combined = data + _bech32_checksum(hrp, data, const)
    return hrp + "1" + "".join(_BECH32_CHARSET[d] for d in combined)
MAINNET = {
    "p2pkh": b"\x00",   # 1...
    "p2sh": b"\x05",    # 3...
    "hrp": "bc",        # bc1...
}
def _tagged_hash(tag: str, msg: bytes) -> bytes:
    th = sha256(tag.encode())
    return sha256(th + th + msg)
def p2pkh_address(pubkey: bytes, version: bytes = MAINNET["p2pkh"]) -> str:
    return b58check_encode(version, hash160(pubkey))
def p2sh_p2wpkh_address(pubkey: bytes, version: bytes = MAINNET["p2sh"]) -> str:
    redeem_script = b"\x00\x14" + hash160(pubkey)
    return b58check_encode(version, hash160(redeem_script))
def p2wpkh_address(pubkey: bytes, hrp: str = MAINNET["hrp"]) -> str:
    return segwit_encode(hrp, 0, hash160(pubkey))
def point_from_bytes(pub: bytes) -> Tuple[int, int]:
    if len(pub) == 33 and pub[0] in (2, 3):
        x = int.from_bytes(pub[1:], "big")
        y_sq = (pow(x, 3, P) + 7) % P
        y = pow(y_sq, (P + 1) // 4, P)  # p % 4 == 3, so this is the square root
        if pow(y, 2, P) != y_sq:
            raise ValueError("public key is not a point on secp256k1")
        if (y % 2) != (pub[0] % 2):
            y = P - y
        return (x, y)
    if len(pub) == 65 and pub[0] == 4:
        return (int.from_bytes(pub[1:33], "big"), int.from_bytes(pub[33:], "big"))
    raise ValueError("unsupported public key encoding")
def p2tr_address_from_pubkey(pub: bytes, hrp: str = MAINNET["hrp"]) -> str:
    pt = point_from_bytes(pub)
    if pt[1] % 2 != 0:  # lift_x: force even Y
        pt = (pt[0], P - pt[1])
    x_only = pt[0].to_bytes(32, "big")
    tweak = int.from_bytes(_tagged_hash("TapTweak", x_only), "big")
    if tweak >= N:
        raise ValueError("invalid taproot tweak")
    q = point_add(pt, point_mul(tweak))
    if q is None:
        raise ValueError("taproot tweak produced infinity")
    return segwit_encode(hrp, 1, q[0].to_bytes(32, "big"))
def p2tr_address(priv_int: int, hrp: str = MAINNET["hrp"]) -> str:
    return p2tr_address_from_pubkey(public_key_bytes(priv_int, True), hrp)
@dataclass
class WifKey:
    wif: str
    priv_int: int
    priv_hex: str
    compressed: bool
    testnet: bool
    pubkey_compressed_hex: str
    pubkey_uncompressed_hex: str
def decode_wif(wif: str) -> WifKey:
    wif = wif.strip()
    if not wif:
        raise ValueError("empty WIF")
    body = b58check_decode(wif)
    version, payload = body[0], body[1:]
    if version == 0x80:
        testnet = False
    elif version == 0xEF:
        testnet = True
    else:
        raise ValueError(f"unsupported WIF version byte 0x{version:02x}")
    if len(payload) == 33 and payload[-1] == 0x01:
        compressed = True
        key = payload[:32]
    elif len(payload) == 32:
        compressed = False
        key = payload
    else:
        raise ValueError("malformed WIF payload length")
    priv = int.from_bytes(key, "big")
    if not (0 < priv < N):
        raise ValueError("private key out of secp256k1 range")
    return WifKey(
        wif=wif,
        priv_int=priv,
        priv_hex=key.hex(),
        compressed=compressed,
        testnet=testnet,
        pubkey_compressed_hex=public_key_bytes(priv, True).hex(),
        pubkey_uncompressed_hex=public_key_bytes(priv, False).hex(),
    )
def encode_wif(priv_int: int, compressed: bool = True, testnet: bool = False) -> str:
    if not (0 < priv_int < N):
        raise ValueError("private key out of secp256k1 range")
    payload = priv_int.to_bytes(32, "big") + (b"\x01" if compressed else b"")
    return b58check_encode(b"\xef" if testnet else b"\x80", payload)
def addresses_for_privkey(key: WifKey) -> Dict[str, str]:
    pub_c = bytes.fromhex(key.pubkey_compressed_hex)
    pub_u = bytes.fromhex(key.pubkey_uncompressed_hex)
    hrp = "tb" if key.testnet else "bc"
    p2pkh = p2pkh_address(pub_u if not key.compressed else pub_c,
                          b"\x6f" if key.testnet else b"\x00")
    return {
        "p2pkh": p2pkh,
        "p2sh_p2wpkh": p2sh_p2wpkh_address(pub_c, b"\xc4" if key.testnet else b"\x05"),
        "p2wpkh": p2wpkh_address(pub_c, hrp),
        "p2tr": p2tr_address(key.priv_int, hrp),
    }
class RateLimiter:
    def __init__(self, min_interval: float = 0.0) -> None:
        self.min_interval = max(0.0, float(min_interval))
        self._lock = threading.Lock()
        self._next_free = 0.0
    def acquire(self) -> None:
        interval = self.min_interval
        if interval <= 0:
            return
        with self._lock:
            now = time.monotonic()
            wait = self._next_free - now
            self._next_free = max(now, self._next_free) + interval
        if wait > 0:
            time.sleep(wait)
    def cooldown(self, seconds: float) -> None:
        if seconds <= 0:
            return
        with self._lock:
            self._next_free = max(self._next_free, time.monotonic() + seconds)
HTTP_LIMITER = RateLimiter(0.0)
def set_rate_limit(min_interval: float) -> None:
    HTTP_LIMITER.min_interval = max(0.0, float(min_interval))
wbc = types.SimpleNamespace(
    N=N, P=P, point_add=point_add, point_mul=point_mul,
    point_from_bytes=point_from_bytes, public_key_bytes=public_key_bytes,
    decode_wif=decode_wif, addresses_for_privkey=addresses_for_privkey,
    b58check_decode=b58check_decode, b58check_encode=b58check_encode,
    HTTP_LIMITER=HTTP_LIMITER, set_rate_limit=set_rate_limit,
)
import argparse
import hashlib
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple
HERE = Path(__file__).resolve().parent
__version__ = "1.0.0"
CONFIG_PATH = HERE / ".chainscan" / "config.json"
SESSION_PATH = HERE / ".chainscan" / "session.json"
REPORT_DIR = HERE / "reports"
DEFAULT_ENDPOINT = "https://mempool.space"
USER_AGENT = f"chainscan/{__version__} (read-only chain analysis)"
CONFIG: Dict[str, Any] = {
    "endpoint": DEFAULT_ENDPOINT,
    "rate": 0.35,          # seconds between requests (token bucket)
    "timeout": 25,
    "usd": True,
}
def load_config() -> None:
    try:
        if CONFIG_PATH.exists():
            CONFIG.update(json.loads(CONFIG_PATH.read_text()))
    except Exception:
        pass
def save_config() -> None:
    CONFIG_PATH.parent.mkdir(parents=True, exist_ok=True)
    CONFIG_PATH.write_text(json.dumps(CONFIG, indent=2))
W = 78
def rule(char: str = "=") -> str:
    return char * W
def box_title(title: str) -> List[str]:
    inner = W - 2
    return ["+" + "-" * inner + "+", "|" + title.center(inner) + "|", "+" + "-" * inner + "+"]
def section(n: int, title: str) -> str:
    return f"\n[{n}] {title.upper()} " + "-" * max(0, W - len(title) - 6)
def kv(label: str, value: Any, width: int = 22) -> str:
    return f"  {label + ' ':.<{width}} {value}"
def banner() -> List[str]:
    return [
        "  ____ _   _    _    ___ _   _ ____   ____    _    _   _ ",
        " / ___| | | |  / \\  |_ _| \\ | / ___| / ___|  / \\  | \\ | |",
        "| |   | |_| | / _ \\  | ||  \\| \\___ \\| |     / _ \\ |  \\| |",
        "| |___|  _  |/ ___ \\ | || |\\  |___) | |___ / ___ \\| |\\  |",
        " \\____|_| |_/_/   \\_\\___|_| \\_|____/ \\____/_/   \\_\\_| \\_|",
        f"  v{__version__}  ·  read-only chain analysis  ·  no key material is ever exported",
    ]
BECH32_CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
BECH32_CONST = 1
BECH32M_CONST = 0x2BC830A3
def _polymod(values: Sequence[int]) -> int:
    gen = (0x3B6A57B2, 0x26508E6D, 0x1EA119FA, 0x3D4233DD, 0x2A1462B3)
    chk = 1
    for value in values:
        top = chk >> 25
        chk = ((chk & 0x1FFFFFF) << 5) ^ value
        for i in range(5):
            if (top >> i) & 1:
                chk ^= gen[i]
    return chk
def _hrp_expand(hrp: str) -> List[int]:
    return [ord(c) >> 5 for c in hrp] + [0] + [ord(c) & 31 for c in hrp]
def _convertbits(data: Sequence[int], frombits: int, tobits: int, pad: bool) -> Optional[List[int]]:
    acc = bits = 0
    out: List[int] = []
    maxv = (1 << tobits) - 1
    for value in data:
        if value < 0 or (value >> frombits):
            return None
        acc = (acc << frombits) | value
        bits += frombits
        while bits >= tobits:
            bits -= tobits
            out.append((acc >> bits) & maxv)
    if pad:
        if bits:
            out.append((acc << (tobits - bits)) & maxv)
    elif bits >= frombits or ((acc << (tobits - bits)) & maxv):
        return None
    return out
def bech32_decode(address: str) -> Dict[str, Any]:
    if not address:
        raise ValueError("empty string")
    if address.lower() != address and address.upper() != address:
        raise ValueError("mixed case is not permitted")
    addr = address.lower()
    pos = addr.rfind("1")
    if pos < 1:
        raise ValueError("missing human-readable part separator")
    if pos + 7 > len(addr):
        raise ValueError("data part too short")
    hrp, data_part = addr[:pos], addr[pos + 1:]
    try:
        data = [BECH32_CHARSET.index(c) for c in data_part]
    except ValueError:
        raise ValueError("character outside the bech32 alphabet") from None
    const = _polymod(_hrp_expand(hrp) + data)
    if const == BECH32_CONST:
        spec = "bech32"
    elif const == BECH32M_CONST:
        spec = "bech32m"
    else:
        raise ValueError("checksum mismatch")
    payload = data[:-6]
    if not payload:
        raise ValueError("empty witness payload")
    witver = payload[0]
    if witver > 16:
        raise ValueError("witness version above 16")
    prog = _convertbits(payload[1:], 5, 8, False)
    if prog is None:
        raise ValueError("invalid witness program padding")
    program = bytes(prog)
    if not (2 <= len(program) <= 40):
        raise ValueError(f"witness program length {len(program)} outside 2..40")
    if witver == 0 and len(program) not in (20, 32):
        raise ValueError("v0 witness program must be 20 or 32 bytes")
    expected = "bech32" if witver == 0 else "bech32m"
    if spec != expected:
        raise ValueError(f"wrong checksum variant: {spec} used for v{witver}, expected {expected}")
    if witver == 0 and len(program) == 20:
        kind = "P2WPKH"
    elif witver == 0 and len(program) == 32:
        kind = "P2WSH"
    elif witver == 1 and len(program) == 32:
        kind = "P2TR"
    else:
        kind = f"witness_v{witver}"
    return {
        "hrp": hrp,
        "witness_version": witver,
        "program": program.hex(),
        "checksum": spec,
        "kind": kind,
        "network": "mainnet" if hrp == "bc" else ("testnet" if hrp == "tb" else "regtest/other"),
    }
TXID_RE = re.compile(r"^[0-9a-fA-F]{64}$")
OUTPOINT_RE = re.compile(r"^([0-9a-fA-F]{64}):(\d{1,7})$")
@dataclass
class Target:
    raw: str
    kind: str                     # address | txid | blockhash | height | outpoint
    valid: bool
    detail: Dict[str, Any] = field(default_factory=dict)
    error: str = ""
    @property
    def summary(self) -> str:
        if not self.valid:
            return f"{self.kind} INVALID ({self.error})"
        return f"{self.kind} OK"
def classify(raw: str) -> Target:
    s = (raw or "").strip()
    if not s:
        return Target(s, "empty", False, {}, "no input")
    m = OUTPOINT_RE.match(s)
    if m:
        return Target(s, "outpoint", True, {"txid": m.group(1).lower(), "vout": int(m.group(2))})
    if TXID_RE.match(s):
        return Target(s, "hex64", True, {"hex": s.lower()})
    if s.isdigit():
        height = int(s)
        if 0 < height < 100_000_000:
            return Target(s, "height", True, {"height": height})
        return Target(s, "height", False, {}, "numeric input is not a plausible block height")
    if s.lower().startswith(("bc1", "tb1")):
        try:
            info = bech32_decode(s)
            return Target(s, "address", True, info)
        except ValueError as exc:
            return Target(s, "address", False, {}, str(exc))
    try:
        payload = wbc.b58check_decode(s)
    except Exception as exc:
        return Target(s, "unknown", False, {}, f"not Base58Check ({exc})")
    if len(payload) != 21:
        return Target(s, "unknown", False, {}, f"unexpected payload length {len(payload)}")
    version = payload[0]
    if version in (0x00, 0x6F):
        kind, network = "P2PKH", "mainnet" if version == 0 else "testnet"
    elif version in (0x05, 0xC4):
        kind, network = "P2SH", "mainnet" if version == 5 else "testnet"
    else:
        return Target(s, "unknown", False, {}, f"version byte 0x{version:02x} is not an address prefix")
    return Target(s, "address", True, {
        "kind": kind, "network": network, "hash160": payload[1:].hex(),
        "checksum": "base58check",
    })
class NetworkError(RuntimeError):
    pass
def _set_rate() -> None:
    wbc.set_rate_limit(float(CONFIG.get("rate", 0.35)))
def http_get(path: str, raw_text: bool = False) -> Any:
    _set_rate()
    url = CONFIG["endpoint"].rstrip("/") + path
    wbc.HTTP_LIMITER.acquire()
    req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    try:
        with urllib.request.urlopen(req, timeout=float(CONFIG.get("timeout", 25))) as resp:
            body = resp.read().decode("utf-8", "replace")
    except urllib.error.HTTPError as exc:
        if exc.code == 404:
            raise NetworkError(f"not found (404): {path}") from None
        if exc.code == 429:
            retry = 0.0
            try:
                retry = float(exc.headers.get("Retry-After") or 0.0)
            except (TypeError, ValueError):
                retry = 0.0
            wbc.HTTP_LIMITER.cooldown(retry or 3.0)
            raise NetworkError("rate limited by the endpoint (429) - backing off") from None
        raise NetworkError(f"HTTP {exc.code}: {path}") from None
    except Exception as exc:  # noqa: BLE001 - network layer
        raise NetworkError(f"{type(exc).__name__}: {exc}") from None
    if raw_text:
        return body.strip()
    try:
        return json.loads(body)
    except json.JSONDecodeError:
        raise NetworkError(f"non-JSON response from {path}") from None
def btc_price() -> Optional[float]:
    if not CONFIG.get("usd", True):
        return None
    try:
        data = http_get("/api/v1/prices")
        return float(data.get("USD")) if isinstance(data, dict) else None
    except Exception:
        return None
def sats(v: Optional[int]) -> str:
    if v is None:
        return "-"
    return f"{v:,} sat ({v / 1e8:.8f} BTC)"
def ts(unix: Optional[int]) -> str:
    if not unix:
        return "-"
    return datetime.fromtimestamp(unix, tz=timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
def script_type(spk: Optional[str]) -> str:
    if not spk:
        return "unknown"
    s = spk.lower()
    if s.startswith("76a914") and s.endswith("88ac"):
        return "P2PKH"
    if s.startswith("a914") and s.endswith("87"):
        return "P2SH"
    if s.startswith("0014"):
        return "P2WPKH"
    if s.startswith("0020"):
        return "P2WSH"
    if s.startswith("5120"):
        return "P2TR"
    if s.startswith("6a"):
        return "OP_RETURN"
    if s.startswith("21") or s.startswith("41"):
        return "P2PK"
    if s.startswith("51") or s.startswith("52"):
        return "nulldata/sigop"
    return "non-standard"
def analyse_address(target: Target) -> Dict[str, Any]:
    s = target.raw if target.raw.lower() == target.raw else target.raw
    addr = s.strip()
    info = http_get(f"/api/address/{urllib.parse.quote(addr)}")
    utxo_status = "ok"
    try:
        utxos = http_get(f"/api/address/{urllib.parse.quote(addr)}/utxo")
    except NetworkError as exc:
        utxos = []
        utxo_status = str(exc)
    tx_status = "ok"
    try:
        txs = http_get(f"/api/address/{urllib.parse.quote(addr)}/txs")
    except NetworkError as exc:
        txs = []
        tx_status = str(exc)
    chain = info.get("chain_stats", {})
    mem = info.get("mempool_stats", {})
    funded = int(chain.get("funded_txo_sum", 0))
    spent = int(chain.get("spent_txo_sum", 0))
    balance = funded - spent
    mem_delta = int(mem.get("funded_txo_sum", 0)) - int(mem.get("spent_txo_sum", 0))
    utxo_values = sorted((int(u["value"]) for u in utxos), reverse=True)
    dust = [v for v in utxo_values if v < 546]
    types: Dict[str, int] = {}
    for u in utxos:
        t = script_type(u.get("scriptpubkey"))
        types[t] = types.get(t, 0) + 1
    times = [t.get("status", {}).get("block_time") for t in txs if t.get("status", {}).get("block_time")]
    return {
        "address": addr,
        "identity": target.detail,
        "chain_stats": chain,
        "mempool_stats": mem,
        "funded_sat": funded,
        "spent_sat": spent,
        "balance_sat": balance,
        "mempool_delta_sat": mem_delta,
        "tx_count": int(chain.get("tx_count", 0)),
        "utxo_status": utxo_status,
        "utxo_count": len(utxos) if utxo_status == "ok" else None,
        "utxo_total_sat": sum(utxo_values) if utxo_status == "ok" else None,
        "largest_utxo_sat": (utxo_values[0] if utxo_values else 0) if utxo_status == "ok" else None,
        "dust_utxos": len(dust) if utxo_status == "ok" else None,
        "utxo_script_types": types if utxo_status == "ok" else {},
        "tx_status": tx_status,
        "window_size": len(txs),
        "latest_activity": max(times) if times else None,
        "earliest_in_window": min(times) if times else None,
        "recent_txids": [t.get("txid") for t in txs[:5]],
        "spent_ratio": (spent / funded) if funded else 0.0,
    }
def analyse_tx(target: Target) -> Dict[str, Any]:
    txid = target.detail.get("hex", target.raw.strip())
    tx = http_get(f"/api/tx/{txid}")
    vins = tx.get("vin", []) or []
    vouts = tx.get("vout", []) or []
    in_total = 0
    in_known = True
    script_in: Dict[str, int] = {}
    sequences = []
    for vin in vins:
        prev = vin.get("prevout") or {}
        if prev.get("value") is not None:
            in_total += int(prev["value"])
        else:
            in_known = False
        t = script_type(prev.get("scriptpubkey"))
        script_in[t] = script_in.get(t, 0) + 1
        sequences.append(vin.get("sequence"))
    out_total = sum(int(v.get("value", 0)) for v in vouts)
    script_out: Dict[str, int] = {}
    for v in vouts:
        t = script_type(v.get("scriptpubkey"))
        script_out[t] = script_out.get(t, 0) + 1
    weight = int(tx.get("weight", 0))
    vsize = int(tx.get("vsize") or (weight + 3) // 4)
    fee = (in_total - out_total) if in_known else None
    is_coinbase = bool(vins) and vins[0].get("is_coinbase", False)
    segwit = any(bool(v.get("witness")) for v in vins)
    rbf = any(seq is not None and int(seq) < 0xFFFFFFFE for seq in sequences)
    return {
        "txid": txid,
        "version": tx.get("version"),
        "locktime": tx.get("locktime"),
        "status": tx.get("status", {}),
        "size": tx.get("size"),
        "weight": weight,
        "vsize": vsize,
        "input_count": len(vins),
        "output_count": len(vouts),
        "input_total_sat": in_total if in_known else None,
        "output_total_sat": out_total,
        "fee_sat": fee,
        "fee_rate": (fee / vsize) if (fee is not None and vsize) else None,
        "coinbase": is_coinbase,
        "segwit": segwit,
        "rbf_signalled": rbf,
        "input_script_types": script_in,
        "output_script_types": script_out,
        "outputs": [
            {
                "n": v.get("n", idx),
                "value": int(v.get("value", 0)),
                "address": v.get("scriptpubkey_address") or "(no address form)",
                "type": script_type(v.get("scriptpubkey")),
            }
            for idx, v in enumerate(vouts)
        ],
    }
def analyse_block(target: Target) -> Dict[str, Any]:
    if target.kind == "height":
        block_hash = http_get(f"/api/block-height/{target.detail['height']}", raw_text=True)
        block_hash = block_hash.strip().strip('"')
    else:
        block_hash = target.detail.get("hex", target.raw.strip())
    block = http_get(f"/api/block/{block_hash}")
    return {
        "hash": block.get("id", block_hash),
        "height": block.get("height"),
        "timestamp": block.get("timestamp"),
        "tx_count": block.get("tx_count"),
        "size": block.get("size"),
        "weight": block.get("weight"),
        "version": block.get("version"),
        "nonce": block.get("nonce"),
        "bits": block.get("bits"),
        "difficulty": block.get("difficulty"),
        "merkle_root": block.get("merkle_root"),
        "previousblockhash": block.get("previousblockhash"),
        "mediantime": block.get("mediantime"),
    }
def analyse_outpoint(target: Target) -> Dict[str, Any]:
    txid, vout = target.detail["txid"], target.detail["vout"]
    tx = http_get(f"/api/tx/{txid}")
    outs = tx.get("vout", []) or []
    if vout >= len(outs):
        raise NetworkError(f"transaction has no output #{vout}")
    o = outs[vout]
    try:
        spend = http_get(f"/api/tx/{txid}/outspend/{vout}")
    except NetworkError:
        spend = {"spent": None}
    return {
        "txid": txid,
        "vout": vout,
        "value_sat": int(o.get("value", 0)),
        "address": o.get("scriptpubkey_address") or "(no address form)",
        "type": script_type(o.get("scriptpubkey")),
        "scriptpubkey": o.get("scriptpubkey"),
        "confirmed": bool(tx.get("status", {}).get("confirmed")),
        "block_time": tx.get("status", {}).get("block_time"),
        "spent": spend.get("spent"),
        "spent_by": spend.get("txid"),
        "spent_at_index": spend.get("vin"),
        "spent_status": spend.get("status", {}).get("block_time"),
    }
def parse_der(hexstr: str) -> Tuple[int, int, Optional[int]]:
    raw = bytes.fromhex(hexstr.strip().removeprefix("0x"))
    if len(raw) < 8 or raw[0] != 0x30:
        raise ValueError("not a DER-encoded signature")
    total = raw[1]
    body = raw[2:2 + total]
    if len(body) != total:
        raise ValueError("truncated DER body")
    i = 0
    if body[i] != 0x02:
        raise ValueError("expected INTEGER for r")
    i += 1
    rlen = body[i]
    i += 1
    r = int.from_bytes(body[i:i + rlen], "big")
    i += rlen
    if i >= len(body) or body[i] != 0x02:
        raise ValueError("expected INTEGER for s")
    i += 1
    slen = body[i]
    i += 1
    s = int.from_bytes(body[i:i + slen], "big")
    i += slen
    sighash = raw[2 + total] if len(raw) > 2 + total else None
    return r, s, sighash
def ecdsa_verify(pub_point: Tuple[int, int], r: int, s: int, z: int) -> bool:
    n = wbc.N
    if not (1 <= r < n and 1 <= s < n):
        return False
    w = pow(s, n - 2, n)
    u1, u2 = (z * w) % n, (r * w) % n
    point = wbc.point_add(wbc.point_mul(u1), wbc.point_mul(u2, pub_point))
    return point is not None and (point[0] % n) == r
def nonce_reuse_proof(pub_point: Tuple[int, int], r: int,
                      s1: int, z1: int, s2: int, z2: int) -> Tuple[bool, str]:
    n = wbc.N
    ds = (s1 - s2) % n
    if ds == 0:
        return False, "identical s values - not a nonce reuse pattern"
    k = ((z1 - z2) * pow(ds, n - 2, n)) % n
    if k == 0:
        return False, "recovered k is zero"
    d = ((s1 * k - z1) * pow(r, n - 2, n)) % n
    if d == 0:
        return False, "recovered scalar is zero"
    matched = wbc.point_mul(d) == pub_point
    if matched:
        return True, "COMPROMISED: recovered scalar reproduces the signer's public key"
    return False, "no match - signatures do not share a recoverable nonce"
def audit_signatures(entries: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    results = []
    for entry in entries:
        label = str(entry.get("label") or "set")
        pub_hex = str(entry.get("pubkey", "")).strip()
        sigs_in = entry.get("signatures") or []
        row: Dict[str, Any] = {
            "label": label,
            "pubkey": pub_hex,
            "count": len(sigs_in),
            "parsed": 0,
            "valid": 0,
            "invalid": 0,
            "errors": [],
            "reuse_groups": [],
            "compromised": False,
            "verdict": "",
        }
        try:
            pub_point = wbc.point_from_bytes(bytes.fromhex(pub_hex))
        except Exception as exc:  # noqa: BLE001
            row["verdict"] = f"unusable public key: {exc}"
            results.append(row)
            continue
        parsed: List[Tuple[int, int, int, str]] = []
        for idx, sig in enumerate(sigs_in):
            try:
                r, s, _sighash = parse_der(str(sig.get("sig", "")))
                if isinstance(sig.get("z"), int):
                    z = int(sig["z"])
                else:
                    z_hex = str(sig.get("z", "")).strip().removeprefix("0x")
                    z = int(z_hex, 16) if z_hex else 0
                ok = ecdsa_verify(pub_point, r, s, z)
                parsed.append((r, s, z, f"#{idx}"))
                row["parsed"] += 1
                if ok:
                    row["valid"] += 1
                else:
                    row["invalid"] += 1
                    row["errors"].append(f"#{idx}: signature does not verify against this public key")
            except Exception as exc:  # noqa: BLE001
                row["errors"].append(f"#{idx}: {exc}")
        by_r: Dict[int, List[Tuple[int, int, int, str]]] = {}
        for item in parsed:
            by_r.setdefault(item[0], []).append(item)
        for r_value, group in by_r.items():
            if len(group) < 2:
                continue
            a, b = group[0], group[1]
            matched, reason = nonce_reuse_proof(pub_point, r_value, a[1], a[2], b[1], b[2])
            row["reuse_groups"].append({
                "r": f"{r_value:064x}",
                "signatures": [a[3], b[3]],
                "recovered": matched,
                "reason": reason,
            })
            if matched:
                row["compromised"] = True
        if row["compromised"]:
            row["verdict"] = "HIGH RISK - nonce reuse confirmed, key is compromised"
        elif row["count"] == 0:
            row["verdict"] = "no signatures supplied"
        elif row["invalid"]:
            row["verdict"] = "REVIEW - some signatures failed verification"
        else:
            row["verdict"] = "OK - no repeated nonce detected in this sample"
        results.append(row)
    return {
        "sets": results,
        "compromised_sets": sum(1 for r in results if r["compromised"]),
        "audited": len(results),
    }
DISCLAIMER = (
    "Read-only analysis produced from public chain data. No private key material is "
    "derived, exported or transmitted by this tool."
)
def _header(title: str, target: str) -> List[str]:
    lines = banner()
    lines.append("")
    lines.extend(box_title(title))
    lines.append(kv("generated", ts(int(time.time()))))
    lines.append(kv("endpoint", CONFIG["endpoint"]))
    lines.append(kv("target", target))
    return lines
def _footer(lines: List[str], extra: Optional[Dict[str, Any]] = None) -> List[str]:
    lines.append("")
    lines.append(rule("-"))
    if extra:
        for k, v in extra.items():
            lines.append(kv(k, v))
    lines.append("  " + DISCLAIMER)
    lines.append(rule("-"))
    return lines
def render_address_report(data: Dict[str, Any], price: Optional[float]) -> List[str]:
    bal = data["balance_sat"]
    lines = _header("ADDRESS REPORT", data["address"])
    lines.append(section(1, "identity & validation"))
    ident = data["identity"]
    lines.append(kv("address", data["address"]))
    lines.append(kv("script type", ident.get("kind", "?")))
    lines.append(kv("network", ident.get("network", "?")))
    lines.append(kv("checksum", ident.get("checksum", "?")))
    if ident.get("hash160"):
        lines.append(kv("hash160", ident["hash160"]))
    if ident.get("witness_version") is not None:
        lines.append(kv("witness version", ident["witness_version"]))
        lines.append(kv("witness program", ident.get("program", "")))
    lines.append(kv("validation", "PASS (validated locally before any request)"))
    lines.append(section(2, "balance"))
    lines.append(kv("confirmed", sats(bal)))
    lines.append(kv("mempool delta", sats(data["mempool_delta_sat"])))
    if price:
        lines.append(kv("fiat (BTC/USD)", f"${price:,.2f}  ->  ${bal / 1e8 * price:,.2f}"))
    lines.append(kv("total received", sats(data["funded_sat"])))
    lines.append(kv("total spent", sats(data["spent_sat"])))
    lines.append(kv("spent ratio", f"{data['spent_ratio'] * 100:.1f}%"))
    lines.append(section(3, "activity"))
    lines.append(kv("transactions", f"{data['tx_count']:,}"))
    lines.append(kv("latest activity", ts(data["latest_activity"])))
    lines.append(kv("oldest in window",
                    f"{ts(data['earliest_in_window'])}  ({data['window_size']} txs examined)"))
    stats = data["chain_stats"]
    lines.append(kv("funded outputs", f"{stats.get('funded_txo_count', 0):,}"))
    lines.append(kv("spent outputs", f"{stats.get('spent_txo_count', 0):,}"))
    lines.append(section(4, "utxo set"))
    if data["utxo_status"] != "ok":
        lines.append(kv("status", "UNAVAILABLE"))
        lines.append(kv("reason", data["utxo_status"]))
        lines.append("  note: Esplora refuses full UTXO listings above its output limit.")
        lines.append("        The balance above is still authoritative, taken from chain_stats.")
    else:
        lines.append(kv("utxos", data["utxo_count"]))
        lines.append(kv("utxo total", sats(data["utxo_total_sat"])))
        lines.append(kv("largest utxo", sats(data["largest_utxo_sat"])))
        lines.append(kv("dust (<546 sat)", data["dust_utxos"]))
        if data["utxo_script_types"]:
            lines.append(kv("script mix", ", ".join(f"{k}:{v}" for k, v in sorted(data["utxo_script_types"].items()))))
    lines.append(section(5, "assessment"))
    observations = []
    if data["tx_count"] == 0:
        observations.append("address has never transacted (zero funded outputs)")
    if bal > 0 and data["utxo_status"] != "ok":
        observations.append("utxo detail unavailable from this endpoint - balance taken from chain_stats")
    if bal > 0 and data["utxo_status"] == "ok" and data["utxo_count"] == 0:
        observations.append("positive balance without confirmed utxos - explorer inconsistency")
    if data["dust_utxos"]:
        observations.append(f"{data['dust_utxos']} dust-level utxo(s) present")
    if data["utxo_count"] and data["utxo_count"] > 100:
        observations.append("large utxo set - consolidation may be costly")
    if data["spent_ratio"] >= 0.99 and bal == 0:
        observations.append("fully swept: everything received has been spent")
    if not observations:
        observations.append("no anomalies detected in this pass")
    for obs in observations:
        lines.append(f"  - {obs}")
    lines.append(section(6, "data provenance"))
    lines.append(kv("chain_stats", "ok"))
    lines.append(kv("utxo listing", "ok" if data["utxo_status"] == "ok" else f"unavailable ({data['utxo_status']})"))
    lines.append(kv("tx listing", "ok" if data["tx_status"] == "ok" else f"unavailable ({data['tx_status']})"))
    lines.append(kv("fiat price", "ok" if price else "unavailable"))
    if data["recent_txids"]:
        lines.append(section(7, "recent transactions"))
        for txid in data["recent_txids"]:
            lines.append(f"  {txid}")
    return _footer(lines, {"mode": "address", "engine": f"chainscan {__version__}"})
def render_tx_report(data: Dict[str, Any], price: Optional[float]) -> List[str]:
    lines = _header("TRANSACTION REPORT", data["txid"])
    status = data.get("status", {})
    lines.append(section(1, "identity"))
    lines.append(kv("txid", data["txid"]))
    lines.append(kv("confirmed", status.get("confirmed")))
    lines.append(kv("block height", status.get("block_height", "-")))
    lines.append(kv("block time", ts(status.get("block_time"))))
    lines.append(kv("version", data["version"]))
    lines.append(kv("locktime", data["locktime"]))
    lines.append(section(2, "size & fee"))
    lines.append(kv("size", f"{data['size']:,} bytes" if data["size"] else "-"))
    lines.append(kv("vsize", f"{data['vsize']:,} vbytes"))
    lines.append(kv("weight", f"{data['weight']:,}"))
    lines.append(kv("fee", sats(data["fee_sat"])))
    if data["fee_rate"] is not None:
        lines.append(kv("fee rate", f"{data['fee_rate']:.2f} sat/vB"))
    if price and data["fee_sat"] is not None:
        lines.append(kv("fee (USD)", f"${data['fee_sat'] / 1e8 * price:,.4f}"))
    lines.append(section(3, "structure"))
    lines.append(kv("inputs", data["input_count"]))
    lines.append(kv("outputs", data["output_count"]))
    lines.append(kv("input total", sats(data["input_total_sat"])))
    lines.append(kv("output total", sats(data["output_total_sat"])))
    lines.append(kv("segwit", data["segwit"]))
    lines.append(kv("rbf signalled", data["rbf_signalled"]))
    lines.append(kv("coinbase", data["coinbase"]))
    if data["input_script_types"]:
        lines.append(kv("input scripts", ", ".join(f"{k}:{v}" for k, v in sorted(data["input_script_types"].items()))))
    if data["output_script_types"]:
        lines.append(kv("output scripts", ", ".join(f"{k}:{v}" for k, v in sorted(data["output_script_types"].items()))))
    lines.append(section(4, "outputs"))
    for o in data["outputs"][:40]:
        index = "-" if o.get("n") is None else str(o["n"])
        value = int(o.get("value") or 0)
        lines.append(f"  #{index:<3} {value:>14,} sat  {o['type']:<12} {o['address']}")
    if len(data["outputs"]) > 40:
        lines.append(f"  ... {len(data['outputs']) - 40} more outputs")
    return _footer(lines, {"mode": "transaction", "engine": f"chainscan {__version__}"})
def render_block_report(data: Dict[str, Any], price: Optional[float]) -> List[str]:
    lines = _header("BLOCK REPORT", str(data.get("height")))
    lines.append(section(1, "identity"))
    lines.append(kv("hash", data["hash"]))
    lines.append(kv("height", data["height"]))
    lines.append(kv("time", ts(data.get("timestamp"))))
    lines.append(kv("previous", data.get("previousblockhash") or "-"))
    lines.append(kv("merkle root", data.get("merkle_root") or "-"))
    lines.append(section(2, "contents"))
    lines.append(kv("transactions", f"{data.get('tx_count', 0):,}"))
    lines.append(kv("size", f"{data.get('size', 0):,} bytes"))
    lines.append(kv("weight", f"{data.get('weight', 0):,}"))
    lines.append(section(3, "consensus"))
    lines.append(kv("version", data.get("version")))
    lines.append(kv("nonce", data.get("nonce")))
    lines.append(kv("bits", data.get("bits")))
    lines.append(kv("difficulty", f"{data.get('difficulty', 0):,.0f}"))
    return _footer(lines, {"mode": "block", "engine": f"chainscan {__version__}"})
def render_outpoint_report(data: Dict[str, Any], price: Optional[float]) -> List[str]:
    lines = _header("OUTPOINT REPORT", f"{data['txid']}:{data['vout']}")
    lines.append(section(1, "output"))
    lines.append(kv("txid", data["txid"]))
    lines.append(kv("vout", data["vout"]))
    lines.append(kv("value", sats(data["value_sat"])))
    lines.append(kv("address", data["address"]))
    lines.append(kv("script type", data["type"]))
    lines.append(kv("confirmed", data["confirmed"]))
    lines.append(section(2, "spend status"))
    if data["spent"] is None:
        lines.append(kv("spent", "unknown (explorer unavailable)"))
    elif data["spent"]:
        lines.append(kv("spent", True))
        lines.append(kv("spending txid", data["spent_by"]))
        lines.append(kv("spent at input", data["spent_at_index"]))
        lines.append(kv("spent block time", ts(data["spent_status"])))
    else:
        lines.append(kv("spent", False))
        lines.append(kv("status", "UNSPENT - live utxo"))
    return _footer(lines, {"mode": "outpoint", "engine": f"chainscan {__version__}"})
def render_audit_report(data: Dict[str, Any]) -> List[str]:
    lines = _header("SIGNATURE AUDIT", f"{data['audited']} set(s)")
    lines.append(section(1, "summary"))
    lines.append(kv("sets audited", data["audited"]))
    lines.append(kv("compromised sets", data["compromised_sets"]))
    lines.append(kv("method", "ECDSA nonce (k) reuse detection + public-key proof"))
    for i, s in enumerate(data["sets"], 1):
        lines.append(section(i + 1, f"set {i}: {s['label']}"))
        lines.append(kv("public key", s["pubkey"] or "-"))
        lines.append(kv("signatures", s["count"]))
        lines.append(kv("verified", s["valid"]))
        lines.append(kv("failed", s["invalid"]))
        lines.append(kv("verdict", s["verdict"]))
        for group in s["reuse_groups"]:
            lines.append("  ! repeated r detected:")
            lines.append(kv("r", group["r"]))
            lines.append(kv("signatures", ", ".join(group["signatures"])))
            lines.append(kv("recovery proof", group["reason"]))
        for err in s["errors"][:5]:
            lines.append(f"  - {err}")
    return _footer(lines, {"mode": "audit", "note": "private keys are never printed",
                           "engine": f"chainscan {__version__}"})
def load_session() -> Dict[str, Any]:
    try:
        if SESSION_PATH.exists():
            return json.loads(SESSION_PATH.read_text())
    except Exception:
        pass
    return {"started": ts(int(time.time())), "stats": {"scans": 0, "reports": 0}, "targets": []}
def save_session(session: Dict[str, Any]) -> None:
    SESSION_PATH.parent.mkdir(parents=True, exist_ok=True)
    SESSION_PATH.write_text(json.dumps(session, indent=2))
def record(session: Dict[str, Any], raw: str, kind: str, report_path: Optional[str], status: str) -> None:
    session["targets"].append({
        "input": raw, "kind": kind, "status": status,
        "report": report_path, "at": ts(int(time.time())),
    })
    session["stats"]["scans"] = session["stats"].get("scans", 0) + 1
    if report_path:
        session["stats"]["reports"] = session["stats"].get("reports", 0) + 1
    save_session(session)
def write_report(lines: List[str], kind: str, slug: str) -> Path:
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now().strftime("%Y%m%d-%H%M%S")
    safe = re.sub(r"[^A-Za-z0-9._-]", "_", slug)[:40] or "target"
    path = REPORT_DIR / f"{stamp}_{kind}_{safe}.txt"
    path.write_text("\n".join(lines) + "\n")
    return path
def run_target(raw: str, session: Optional[Dict[str, Any]] = None,
               render: bool = True) -> Dict[str, Any]:
    target = classify(raw)
    if not target.valid:
        return {"ok": False, "target": target, "error": target.error}
    price = btc_price()
    try:
        if target.kind == "address":
            data = analyse_address(target)
            lines = render_address_report(data, price)
            kind = "address"
        elif target.kind == "hex64":
            try:
                data = analyse_tx(target)
                lines = render_tx_report(data, price)
                kind = "tx"
            except NetworkError:
                data = analyse_block(target)
                lines = render_block_report(data, price)
                kind = "block"
        elif target.kind == "height":
            data = analyse_block(target)
            lines = render_block_report(data, price)
            kind = "block"
        elif target.kind == "outpoint":
            data = analyse_outpoint(target)
            lines = render_outpoint_report(data, price)
            kind = "outpoint"
        else:
            return {"ok": False, "target": target, "error": f"unsupported input kind {target.kind}"}
    except NetworkError as exc:
        return {"ok": False, "target": target, "error": str(exc)}
    except Exception as exc:  # noqa: BLE001 - the CLI must never dump a traceback
        if os.environ.get("CHAINSCAN_DEBUG"):
            raise
        return {"ok": False, "target": target,
                "error": f"internal error while analysing {target.kind}: {type(exc).__name__}: {exc}"}
    path = write_report(lines, kind, raw) if render else None
    if session is not None:
        record(session, raw, kind, str(path) if path else None, "ok")
    return {"ok": True, "target": target, "kind": kind, "data": data,
            "lines": lines, "report": str(path) if path else None}
def stats_footer() -> str:
    s = load_session()
    st = s.get("stats", {})
    reports = len(list(REPORT_DIR.glob("*.txt"))) if REPORT_DIR.exists() else 0
    return (f"  today: {st.get('scans', 0)} scans  |  results: {reports} files  |  "
            f"endpoint: {CONFIG['endpoint'].split('//')[-1]}")
MENU_ITEMS = [
    ("1", "scan one target          (address / txid / block hash / height / txid:vout)"),
    ("2", "batch scan from file"),
    ("3", "reports manager"),
    ("4", "settings"),
    ("5", "key tools               (WIF decode / address inspection)"),
    ("6", "signature audit         (ECDSA nonce-reuse detection)"),
    ("7", "resume session"),
    ("8", "watch loop              (re-scan on interval, diff balances)"),
    ("9", "self-test"),
    ("0", "exit"),
]
def print_menu() -> None:
    print()
    for line in banner():
        print(line)
    print()
    print("--[ main menu ]--" + "-" * (W - 17))
    for key, label in MENU_ITEMS:
        print(f"  [{key}] {label}")
    print("-" * W)
    print(stats_footer())
    print("  keys: q quit  h help  c clear  r reports  s session")
def prompt(text: str) -> str:
    try:
        return input(text).strip()
    except (EOFError, KeyboardInterrupt):
        print()
        return "0"
def show_report(result: Dict[str, Any]) -> None:
    if not result["ok"]:
        print(f"  ! {result['error']}")
        return
    print()
    for line in result["lines"]:
        print(line)
    print(f"\n  report saved -> {result['report']}")
def key_tools() -> None:
    while True:
        print("\n--[ key tools ]" + "-" * (W - 15))
        print("  [1] decode WIF -> all address forms")
        print("  [2] inspect an address (local validation only)")
        print("  [0] back")
        choice = prompt("keytools> ")
        if choice in ("0", "q", ""):
            return
        if choice == "1":
            wif = prompt("WIF: ")
            try:
                key = wbc.decode_wif(wif)
                forms = wbc.addresses_for_privkey(key)
                print(kv("private key", key.priv_hex))
                print(kv("compressed", key.compressed))
                print(kv("network", key.network))
                for name, addr in forms.items():
                    print(kv(name, addr))
            except Exception as exc:  # noqa: BLE001
                print(f"  ! invalid WIF: {exc}")
        elif choice == "2":
            raw = prompt("address: ")
            target = classify(raw)
            if target.valid:
                for k, v in target.detail.items():
                    print(kv(k, v))
            else:
                print(f"  ! {target.error}")
def reports_manager() -> None:
    if not REPORT_DIR.exists():
        print("  no reports yet")
        return
    files = sorted(REPORT_DIR.glob("*.txt"), reverse=True)
    if not files:
        print("  no reports yet")
        return
    for i, path in enumerate(files[:20], 1):
        print(f"  [{i:>2}] {path.name}  ({path.stat().st_size:,} bytes)")
    choice = prompt("open which number (enter to cancel)? ")
    if choice.isdigit() and 1 <= int(choice) <= min(20, len(files)):
        print()
        print(files[int(choice) - 1].read_text())
def batch_scan(path: str, resume: bool = False, limit: Optional[int] = None) -> int:
    try:
        raw_lines = Path(path).read_text().splitlines()
    except OSError as exc:
        print(f"  ! cannot read {path}: {exc}")
        return 2
    targets = [ln.split("#")[0].strip() for ln in raw_lines]
    targets = [t for t in targets if t]
    if limit:
        targets = targets[:limit]
    session = load_session()
    done = {t["input"] for t in session["targets"] if t.get("status") == "ok"}
    ok = fail = skipped = 0
    for i, target in enumerate(targets, 1):
        if resume and target in done:
            skipped += 1
            print(f"  [{i}/{len(targets)}] skip (already done): {target[:24]}...")
            continue
        result = run_target(target, session)
        if result["ok"]:
            ok += 1
            print(f"  [{i}/{len(targets)}] {result['kind']:<9} ok  -> {Path(result['report']).name}")
        else:
            fail += 1
            print(f"  [{i}/{len(targets)}] FAILED  {target[:24]}...  {result['error']}")
    print(f"\n  batch complete: {ok} ok, {fail} failed, {skipped} skipped")
    return 0 if fail == 0 else 1
def signature_audit(path: str) -> int:
    try:
        payload = json.loads(Path(path).read_text())
    except Exception as exc:  # noqa: BLE001
        print(f"  ! cannot read {path}: {exc}")
        return 2
    entries = payload if isinstance(payload, list) else payload.get("sets", [])
    if not isinstance(entries, list) or not entries:
        print("  ! expected a list of {pubkey, signatures:[{z,sig}]}")
        return 2
    data = audit_signatures(entries)
    lines = render_audit_report(data)
    path_out = write_report(lines, "audit", Path(path).stem)
    for line in lines:
        print(line)
    print(f"\n  report saved -> {path_out}")
    return 0
def menu() -> int:
    session = load_session()
    while True:
        print_menu()
        choice = prompt("chainscan> ").lower()
        if choice in ("0", "q", "quit", "exit"):
            print("  bye")
            return 0
        if choice == "h":
            print("""
  Inputs are auto-detected and validated locally before any request:
    address     Base58Check (P2PKH/P2SH) or Bech32/Bech32m (P2WPKH/P2WSH/P2TR)
    txid        64 hex characters
    block hash  64 hex characters (resolved after the tx lookup misses)
    height      integer
    outpoint    <txid>:<vout>
  Every report is written to ./reports/ as .txt and logged in the session file.
""")
        elif choice == "c":
            os.system("cls" if os.name == "nt" else "clear")
        elif choice == "r":
            reports_manager()
        elif choice == "s":
            s = load_session()
            print(kv("started", s.get("started", "-")))
            print(kv("scans", s.get("stats", {}).get("scans", 0)))
            print(kv("targets", len(s.get("targets", []))))
        elif choice == "1":
            raw = prompt("target: ")
            if raw:
                show_report(run_target(raw, session))
        elif choice == "2":
            path = prompt("file with one target per line: ")
            if path:
                batch_scan(path, resume=False)
        elif choice == "3":
            reports_manager()
        elif choice == "4":
            print(kv("endpoint", CONFIG["endpoint"]))
            print(kv("rate (s/req)", CONFIG["rate"]))
            print(kv("timeout", CONFIG["timeout"]))
            edit = prompt("change rate in seconds (enter to keep)? ")
            if edit:
                try:
                    CONFIG["rate"] = max(0.0, float(edit))
                    save_config()
                    print("  saved")
                except ValueError:
                    print("  ! not a number")
            ep = prompt("change endpoint (enter to keep)? ")
            if ep:
                CONFIG["endpoint"] = ep.rstrip("/")
                save_config()
                print("  saved")
        elif choice == "5":
            key_tools()
        elif choice == "6":
            path = prompt("signature JSON path: ")
            if path:
                signature_audit(path)
        elif choice == "7":
            s = load_session()
            pending = [t["input"] for t in s["targets"] if t.get("status") != "ok"]
            if not pending:
                print("  nothing to resume")
            else:
                print(f"  {len(pending)} pending target(s)")
                for target in pending:
                    show_report(run_target(target, s))
        elif choice == "8":
            path = prompt("file with one target per line: ")
            if not path:
                continue
            try:
                raw_lines = Path(path).read_text().splitlines()
            except OSError as exc:
                print(f"  ! cannot read {path}: {exc}")
                continue
            targets = [ln.split("#")[0].strip() for ln in raw_lines]
            targets = [t for t in targets if t]
            interval_raw = prompt(f"interval seconds (default {CONFIG.get('watch_interval', 60)})? ")
            try:
                interval = float(interval_raw) if interval_raw else float(CONFIG.get("watch_interval", 60))
            except ValueError:
                interval = 60.0
            CONFIG["watch_interval"] = interval
            save_config()
            cycles_raw = prompt("cycles (blank or 0 = until interrupted)? ")
            cycles = int(cycles_raw) if cycles_raw.isdigit() else 0
            watch_loop(targets, interval=interval, cycles=cycles)
        elif choice == "9":
            selftest()
        else:
            print("  ! unknown option")
def _sign(priv: int, z: int, k: int) -> Tuple[int, int]:
    n = wbc.N
    point = wbc.point_mul(k)
    r = point[0] % n
    s = (pow(k, n - 2, n) * (z + r * priv)) % n
    return r, s
def _der(r: int, s: int) -> str:
    def enc(x: int) -> bytes:
        raw = x.to_bytes(max(1, (x.bit_length() + 7) // 8), "big")
        if raw[0] & 0x80:
            raw = b"\x00" + raw
        return b"\x02" + bytes([len(raw)]) + raw
    body = enc(r) + enc(s)
    return (b"\x30" + bytes([len(body)]) + body).hex()
def selftest() -> int:
    print()
    print(rule("="))
    print("  CHAINSCAN SELF-TEST")
    print(rule("="))
    failures: List[str] = []
    def check(name: str, got: Any, want: Any) -> None:
        ok = got == want
        print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + ("" if ok else f"   got={got!r} want={want!r}"))
        if not ok:
            failures.append(name)
    t = classify("1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa")
    check("genesis address accepted", (t.kind, t.valid, t.detail.get("kind")), ("address", True, "P2PKH"))
    check("corrupted Base58 checksum rejected", classify("1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNx").valid, False)
    t = classify("bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4")
    check("bech32 v0 P2WPKH accepted", (t.valid, t.detail.get("kind"), t.detail.get("checksum")),
          (True, "P2WPKH", "bech32"))
    check("uppercase bech32 accepted", classify("BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4").valid, True)
    check("mixed-case bech32 rejected",
          classify("bc1QW508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4").valid, False)
    check("bech32 bad checksum rejected",
          classify("bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t5").valid, False)
    t = classify("bc1p5cyxnuxmeuwuvkwfem96lqzszd02n6xdcjrs20cac6yqjjwudpxqkedrcr")
    check("bech32m v1 P2TR accepted", (t.valid, t.detail.get("kind"), t.detail.get("checksum")),
          (True, "P2TR", "bech32m"))
    check("bech32m bad checksum rejected",
          classify("bc1p5cyxnuxmeuwuvkwfem96lqzszd02n6xdcjrs20cac6yqjjwudpxqkedrcx").valid, False)
    check("txid recognised", classify("aa" * 32).kind, "hex64")
    check("outpoint parsed", classify("aa" * 32 + ":3").detail["vout"], 3)
    check("block height parsed", classify("800000").detail["height"], 800000)
    check("absurd height rejected", classify("999999999999").valid, False)
    check("script P2WPKH", script_type("0014" + "11" * 20), "P2WPKH")
    check("script P2WSH", script_type("0020" + "11" * 32), "P2WSH")
    check("script P2TR", script_type("5120" + "11" * 32), "P2TR")
    check("script OP_RETURN", script_type("6a0b68656c6c6f"), "OP_RETURN")
    priv = int("f" * 16, 16)
    pub_point = wbc.point_mul(priv)
    pub_hex = wbc.public_key_bytes(priv, True).hex()
    z1, z2, nonce = 0x1111, 0x2222, 0xABCDEF0123456789
    r1, s1 = _sign(priv, z1, nonce)
    r2, s2 = _sign(priv, z2, nonce)
    check("identical nonce reproduces r", r1, r2)
    parsed = parse_der(_der(r1, s1))
    check("DER round-trip", (parsed[0], parsed[1]), (r1, s1))
    check("signature verifies", ecdsa_verify(pub_point, r1, s1, z1), True)
    check("wrong z fails verification", ecdsa_verify(pub_point, r1, s1, z1 + 1), False)
    matched, _reason = nonce_reuse_proof(pub_point, r1, s1, z1, s2, z2)
    check("nonce reuse proof succeeds", matched, True)
    reuse_case = [{
        "label": "synthetic-reuse", "pubkey": pub_hex,
        "signatures": [{"z": f"{z1:064x}", "sig": _der(r1, s1)},
                       {"z": f"{z2:064x}", "sig": _der(r2, s2)}],
    }]
    audit = audit_signatures(reuse_case)
    check("auditor flags compromise", audit["compromised_sets"], 1)
    audit_text = "\n".join(render_audit_report(audit))
    check("auditor never prints the private key", f"{priv:064x}" in audit_text, False)
    check("audit report has evidence", "COMPROMISED" in audit_text, True)
    r3, s3 = _sign(priv, z2, nonce + 1)
    clean_case = [{
        "label": "synthetic-clean", "pubkey": pub_hex,
        "signatures": [{"z": f"{z1:064x}", "sig": _der(r1, s1)},
                       {"z": f"{z2:064x}", "sig": _der(r3, s3)}],
    }]
    check("no false positive on distinct nonces",
          audit_signatures(clean_case)["compromised_sets"], 0)
    check("watch: first observation is a baseline",
          diff_snapshots(None, {"ok": True, "kind": "address", "balance_sat": 5,
                                "tx_count": 1, "recent": []})[0]["type"], "baseline")
    steady = {"ok": True, "kind": "address", "balance_sat": 1000, "tx_count": 2,
              "utxo_count": 1, "recent": ["a"]}
    check("watch: no movement produces no changes", diff_snapshots(steady, dict(steady)), [])
    moved = dict(steady, balance_sat=1500, tx_count=3, utxo_count=2, recent=["b", "a"])
    kinds = [c["type"] for c in diff_snapshots(steady, moved)]
    check("watch: balance / count / new-tx / utxo detected",
          ("balance" in kinds, "tx_count" in kinds, "new_tx" in kinds, "utxo" in kinds),
          (True, True, True, True))
    check("watch: outpoint spend transition",
          [c["type"] for c in diff_snapshots({"ok": True, "kind": "outpoint", "spent": False},
                                             {"ok": True, "kind": "outpoint", "spent": True,
                                              "spent_by": "ff"})],
          ["outpoint_spent"])
    check("watch: scan failure surfaces", diff_snapshots(steady, {"ok": False, "error": "boom"})[0]["type"],
          "error")
    path = write_report(["chainscan self-test report"], "selftest", "selftest")
    check("report file written", path.exists() and path.stat().st_size > 0, True)
    path.unlink(missing_ok=True)
    print(rule("-"))
    if failures:
        print(f"  {len(failures)} FAILURE(S): {', '.join(failures)}")
        return 1
    print("  ALL PASS")
    return 0
WATCH_STATE_PATH = HERE / ".chainscan" / "watch_state.json"
WATCH_LOG_PATH = REPORT_DIR / "watch_log.txt"
def load_watch_state() -> Dict[str, Any]:
    try:
        if WATCH_STATE_PATH.exists():
            return json.loads(WATCH_STATE_PATH.read_text())
    except Exception:
        pass
    return {"targets": {}, "cycles": 0, "started": ts(int(time.time()))}
def save_watch_state(state: Dict[str, Any]) -> None:
    WATCH_STATE_PATH.parent.mkdir(parents=True, exist_ok=True)
    WATCH_STATE_PATH.write_text(json.dumps(state, indent=2))
def snapshot(result: Dict[str, Any]) -> Dict[str, Any]:
    if not result.get("ok"):
        return {"ok": False, "error": result.get("error", "scan failed")}
    data, kind = result["data"], result["kind"]
    if kind == "address":
        return {
            "ok": True, "kind": kind,
            "balance_sat": data["balance_sat"],
            "tx_count": data["tx_count"],
            "utxo_count": data["utxo_count"],
            "mempool_delta_sat": data["mempool_delta_sat"],
            "latest_activity": data["latest_activity"],
            "recent": data.get("recent_txids") or [],
        }
    if kind == "outpoint":
        return {
            "ok": True, "kind": kind,
            "spent": data.get("spent"),
            "value_sat": data.get("value_sat"),
            "spent_by": data.get("spent_by"),
        }
    return {"ok": True, "kind": kind}
def diff_snapshots(prev: Optional[Dict[str, Any]], cur: Dict[str, Any]) -> List[Dict[str, Any]]:
    if not cur.get("ok"):
        return [{"type": "error", "text": cur.get("error", "scan failed")}]
    if not prev or not prev.get("ok"):
        return [{"type": "baseline", "text": "baseline recorded (first observation)"}]
    changes: List[Dict[str, Any]] = []
    if cur["kind"] == "address":
        delta = cur.get("balance_sat", 0) - prev.get("balance_sat", 0)
        if delta:
            changes.append({
                "type": "balance", "delta": delta,
                "text": f"balance {delta:+,} sat ({delta / 1e8:+.8f} BTC)",
            })
        dt = cur.get("tx_count", 0) - prev.get("tx_count", 0)
        if dt:
            changes.append({"type": "tx_count", "delta": dt,
                            "text": f"transaction count {dt:+d}"})
        seen = set(prev.get("recent") or [])
        for txid in cur.get("recent") or []:
            if txid not in seen:
                changes.append({"type": "new_tx", "txid": txid, "text": f"new tx {txid}"})
        if cur.get("utxo_count") is not None and prev.get("utxo_count") is not None:
            du = cur["utxo_count"] - prev["utxo_count"]
            if du:
                changes.append({"type": "utxo", "delta": du,
                                "text": f"utxo count {du:+d}"})
        if cur.get("mempool_delta_sat") and not prev.get("mempool_delta_sat"):
            changes.append({"type": "mempool", "text":
                            f"unconfirmed inflow {cur['mempool_delta_sat']:,} sat"})
    elif cur["kind"] == "outpoint":
        if prev.get("spent") is False and cur.get("spent") is True:
            changes.append({"type": "outpoint_spent", "text":
                            f"OUTPOINT SPENT by {cur.get('spent_by')}"})
        elif prev.get("spent") is None and cur.get("spent") is not None:
            changes.append({"type": "outpoint_state", "text":
                            f"spend state now known: spent={cur.get('spent')}"})
    return changes
def render_watch_cycle(cycle: int, observations: List[Dict[str, Any]],
                       interval: float) -> List[str]:
    lines = _header("WATCH CYCLE REPORT", f"cycle {cycle}")
    lines.append(section(1, "cycle"))
    lines.append(kv("cycle", cycle))
    lines.append(kv("interval", f"{interval:g}s"))
    lines.append(kv("targets", len(observations)))
    changed = [o for o in observations if o["changes"] and o["changes"][0]["type"] != "baseline"]
    lines.append(kv("targets changed", len(changed)))
    lines.append(section(2, "targets"))
    for obs in observations:
        tag = "CHANGED" if any(c["type"] not in ("baseline",) for c in obs["changes"]) else "steady"
        if obs["changes"] and obs["changes"][0]["type"] == "baseline":
            tag = "baseline"
        lines.append(f"  [{tag:<8}] {obs['target']}")
        snap = obs.get("snapshot") or {}
        if snap.get("kind") == "address":
            lines.append(kv("balance", sats(snap.get("balance_sat"))))
            lines.append(kv("transactions", snap.get("tx_count")))
        elif snap.get("kind") == "outpoint":
            lines.append(kv("value", sats(snap.get("value_sat"))))
            lines.append(kv("spent", snap.get("spent")))
    if changed:
        lines.append(section(3, "alerts"))
        for obs in changed:
            for change in obs["changes"]:
                if change["type"] == "baseline":
                    continue
                lines.append(f"  ! {obs['target'][:34]:<34} {change['text']}")
    return _footer(lines, {"mode": "watch", "engine": f"chainscan {__version__}"})
def log_watch_cycle(cycle: int, observations: List[Dict[str, Any]]) -> None:
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    rows = []
    for obs in observations:
        for change in obs["changes"]:
            if change["type"] in ("baseline",):
                continue
            rows.append(f"{ts(int(time.time()))}\tcycle={cycle}\t{obs['target']}\t{change['type']}\t{change['text']}")
    if rows:
        with WATCH_LOG_PATH.open("a") as handle:
            handle.write("\n".join(rows) + "\n")
def watch_loop(targets: Sequence[str], interval: float = 60.0,
               cycles: int = 0, always: bool = False,
               quiet: bool = False) -> int:
    if not targets:
        print("  ! no targets to watch")
        return 2
    interval = max(1.0, float(interval))
    state = load_watch_state()
    cycle = int(state.get("cycles", 0))
    alerts_total = 0
    started = time.time()
    print()
    for line in banner():
        print(line)
    print()
    print(f"  watch mode: {len(targets)} target(s), interval {interval:g}s, "
          f"cycles {'until interrupted' if cycles == 0 else cycles}")
    print(rule("-"))
    try:
        while True:
            cycle += 1
            cycle_start = time.time()
            observations: List[Dict[str, Any]] = []
            for target in targets:
                result = run_target(target, session=None, render=False)
                cur = snapshot(result)
                prev = (state["targets"] or {}).get(target)
                changes = diff_snapshots(prev, cur)
                state.setdefault("targets", {})[target] = cur
                observations.append({
                    "target": target,
                    "snapshot": cur,
                    "changes": changes,
                })
                if cur.get("ok"):
                    label = cur.get("kind", "?")
                    if cur["kind"] == "address":
                        detail = f"{cur['balance_sat']:,} sat | tx {cur['tx_count']}"
                    elif cur["kind"] == "outpoint":
                        detail = f"spent={cur.get('spent')}"
                    else:
                        detail = "tracked"
                else:
                    label, detail = "error", cur.get("error", "")[:60]
                marker = " " if not changes or changes[0]["type"] == "baseline" else "!"
                if not quiet:
                    print(f"  {marker} [{cycle:>3}] {label:<9} {target[:40]:<40} {detail}")
                    for change in changes:
                        if change["type"] != "baseline":
                            print(f"          -> {change['text']}")
                    if changes and changes[0]["type"] == "baseline":
                        print("          -> baseline recorded")
            real_changes = sum(
                1 for o in observations
                for c in o["changes"] if c["type"] not in ("baseline",)
            )
            alerts_total += real_changes
            log_watch_cycle(cycle, observations)
            if real_changes or always:
                path = write_report(render_watch_cycle(cycle, observations, interval),
                                    "watch", f"cycle{cycle}")
                if not quiet:
                    print(f"        cycle report -> {path.name}")
            state["cycles"] = cycle
            state["last_cycle_at"] = ts(int(time.time()))
            save_watch_state(state)
            if cycles and cycle >= cycles:
                break
            elapsed = time.time() - cycle_start
            sleep_for = interval - elapsed
            if sleep_for > 0:
                if not quiet:
                    print(f"        sleeping {sleep_for:.1f}s "
                          f"(cycle took {elapsed:.1f}s) - ctrl-c to stop")
                time.sleep(sleep_for)
    except KeyboardInterrupt:
        print("\n  interrupted by user")
    total = time.time() - started
    print(rule("-"))
    print(f"  watch summary: {cycle} cycle(s) this run | {alerts_total} change(s) detected "
          f"| {total:.0f}s elapsed")
    print(f"  state: {WATCH_STATE_PATH}")
    print(f"  log:   {WATCH_LOG_PATH}")
    return 0
def main(argv: Optional[Sequence[str]] = None) -> int:
    load_config()
    parser = argparse.ArgumentParser(
        prog="chainscan",
        description="CHAINSCAN - read-only Bitcoin chain analysis with full .txt reporting",
    )
    parser.add_argument("--version", action="version", version=f"chainscan {__version__}")
    sub = parser.add_subparsers(dest="cmd")
    p_scan = sub.add_parser("scan", help="analyse one target")
    p_scan.add_argument("target")
    p_scan.add_argument("--json", action="store_true", help="emit machine-readable JSON")
    p_scan.add_argument("--no-save", action="store_true", help="do not write a report file")
    p_batch = sub.add_parser("batch", help="scan a file of targets")
    p_batch.add_argument("file")
    p_batch.add_argument("--resume", action="store_true", help="skip targets already completed")
    p_batch.add_argument("--limit", type=int, default=None)
    p_audit = sub.add_parser("audit", help="audit ECDSA signatures for nonce reuse")
    p_audit.add_argument("file")
    p_watch = sub.add_parser("watch", help="re-scan targets on an interval and report changes")
    p_watch.add_argument("file", help="file with one target per line")
    p_watch.add_argument("--interval", type=float, default=60.0, help="seconds between cycles")
    p_watch.add_argument("--cycles", type=int, default=0, help="number of cycles, 0 = until interrupted")
    p_watch.add_argument("--always", action="store_true", help="write a report every cycle, not only on change")
    p_watch.add_argument("--quiet", action="store_true", help="only print alerts")
    sub.add_parser("menu", help="interactive menu")
    sub.add_parser("selftest", help="run the built-in test suite")
    p_cfg = sub.add_parser("config", help="show or change settings")
    p_cfg.add_argument("--endpoint")
    p_cfg.add_argument("--rate", type=float)
    args = parser.parse_args(argv)
    if args.cmd == "scan":
        result = run_target(args.target, load_session(), render=not args.no_save)
        if args.json:
            print(json.dumps({
                "ok": result["ok"],
                "kind": result.get("kind"),
                "error": result.get("error"),
                "report": result.get("report"),
                "data": result.get("data"),
            }, indent=2, default=str))
        else:
            show_report(result)
        return 0 if result["ok"] else 1
    if args.cmd == "batch":
        return batch_scan(args.file, resume=args.resume, limit=args.limit)
    if args.cmd == "audit":
        return signature_audit(args.file)
    if args.cmd == "watch":
        try:
            raw_lines = Path(args.file).read_text().splitlines()
        except OSError as exc:
            print(f"  ! cannot read {args.file}: {exc}")
            return 2
        targets = [ln.split("#")[0].strip() for ln in raw_lines]
        targets = [t for t in targets if t]
        return watch_loop(targets, interval=args.interval, cycles=args.cycles,
                          always=args.always, quiet=args.quiet)
    if args.cmd == "selftest":
        return selftest()
    if args.cmd == "config":
        if args.endpoint:
            CONFIG["endpoint"] = args.endpoint.rstrip("/")
        if args.rate is not None:
            CONFIG["rate"] = max(0.0, args.rate)
        save_config()
        for key, value in CONFIG.items():
            print(kv(key, value))
        return 0
    return menu()
if __name__ == "__main__":
    sys.exit(main())
