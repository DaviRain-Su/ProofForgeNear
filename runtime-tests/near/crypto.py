#!/usr/bin/env python3
"""NearCrypto sandbox scenes for sha256/keccak/ripemd160/ecrecover/ed25519_verify.

Honesty: not testnet/mainnet, not formal. Requires PF_NEAR_RPC / PF_NEAR_HOME /
PF_NEAR_WASM. Missing sandbox → the wrapping crypto.sh skips.
"""

from __future__ import annotations

import hashlib
import os
import struct
import sys
from pathlib import Path

from cryptography.hazmat.primitives.asymmetric import ec
from cryptography.hazmat.primitives.asymmetric.utils import decode_dss_signature
from cryptography.hazmat.primitives import hashes
from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    v = os.environ.get(name, "").strip()
    if not v:
        raise SystemExit(f"near-crypto: missing env {name}")
    return v


def _u64s(*words: int) -> bytes:
    return b"".join(struct.pack("<Q", w & ((1 << 64) - 1)) for w in words)


def _words_le(data: bytes) -> list[int]:
    out: list[int] = []
    for i in range(0, len(data), 8):
        chunk = data[i : i + 8]
        if len(chunk) < 8:
            chunk = chunk + b"\x00" * (8 - len(chunk))
        out.append(int.from_bytes(chunk, "little"))
    return out


def _call_u64(client: NearClient, method: str, args: bytes = b"") -> int:
    res = client.call(method, args)
    value = NearClient.success_value_bytes(res)
    if value is None or len(value) < 8:
        raise AssertionError(f"{method} SuccessValue expected >=8 bytes, got {value!r}")
    return NearClient.decode_u64_le(value, 0)


def _ripemd160(data: bytes) -> bytes:
    return hashlib.new("ripemd160", data).digest()


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearCrypto (hash / ecrecover / ed25519_verify) ===")
    client.deploy(wasm)
    client.call("initialize", b"")
    got = client.view_u64("get")
    if got != 0:
        raise AssertionError(f"after initialize: get() expected 0, got {got}")
    print("nearcrypto: initialize() -> get()==0 ok")

    abc = b"abc"
    sha = hashlib.sha256(abc).digest()
    sha_w0, _, _, sha_w3 = _words_le(sha)
    got = client.view_u64("sha256W0")
    if got != sha_w0:
        raise AssertionError(f"sha256W0 expected {sha_w0:#x}, got {got:#x}")
    got = client.view_u64("sha256W3")
    if got != sha_w3:
        raise AssertionError(f"sha256W3 expected {sha_w3:#x}, got {got:#x}")
    print(f"nearcrypto: sha256(abc)={sha.hex()} LE windows ok")

    keccak = bytes.fromhex(
        "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"
    )
    keccak_w0 = _words_le(keccak)[0]
    got = client.view_u64("keccak256W0")
    if got != keccak_w0:
        raise AssertionError(f"keccak256W0 expected {keccak_w0:#x}, got {got:#x}")
    print(f"nearcrypto: keccak256(abc)={keccak.hex()} w0 ok")

    ripe = _ripemd160(abc)
    ripe_w0, ripe_w1, ripe_w2 = _words_le(ripe)
    got = client.view_u64("ripemd160W0")
    if got != ripe_w0:
        raise AssertionError(f"ripemd160W0 expected {ripe_w0:#x}, got {got:#x}")
    got = client.view_u64("ripemd160W2")
    if got != ripe_w2:
        raise AssertionError(f"ripemd160W2 expected {ripe_w2:#x}, got {got:#x}")
    print(f"nearcrypto: ripemd160(abc)={ripe.hex()} LE windows ok")

    # keccak-512("abc") first 8 bytes 18587dc2ea106b9a; LE window 0x9a6b10eac27d5818.
    # (sha3_512("abc") starts with b751850b — different algorithm.)
    try:
        from Crypto.Hash import keccak as _keccak_mod

        _k512 = _keccak_mod.new(digest_bits=512)
        _k512.update(abc)
        k512 = _k512.digest()
    except ImportError:
        k512 = bytes.fromhex(
            "18587dc2ea106b9a1563e32b3312421ca164c7f1f07bc922a9c83d77cea3a1e5"
            "d0c69910739025372dc14ac9642629379540c17e2a65b19d77aa511a9d00bb96"
        )
    k512_w0 = _words_le(k512)[0]
    got = _call_u64(client, "keccak512W0")
    if got != k512_w0:
        raise AssertionError(f"keccak512W0 expected {k512_w0:#x}, got {got:#x}")
    print(f"nearcrypto: keccak512(abc)[:8]={k512[:8].hex()} LE w0 ok")

    # secp256k1 priv=1 = G; sha256("hello"); recovery id v=1 (nearcore 0..3, not 27/28).
    pub_words = [
        0xACBBDCF97E66BE79,
        0x070B87CE9562A055,
        0xD928CE2DDBFC9B02,
        0x9817F8165B81F259,
        0x65C4A32677DA3A48,
        0xA808110EFCFBA45D,
        0x195485A648B417FD,
        0xB8D410FB8FD0479C,
    ]
    status1 = _call_u64(client, "ecrecoverStatus1")
    if status1 != 0:
        raise AssertionError(f"ecrecover v=1 expected status 0, got {status1}")
    w0 = _call_u64(client, "ecrecoverW0v1")
    w7 = _call_u64(client, "ecrecoverW7v1")
    if w0 != pub_words[0] or w7 != pub_words[7]:
        raise AssertionError(
            f"ecrecover v=1 pubkey mismatch w0 {w0:#x} vs {pub_words[0]:#x}, "
            f"w7 {w7:#x} vs {pub_words[7]:#x}"
        )
    print("nearcrypto: ecrecover v=1 recovered secp256k1 G 64B windows ok")

    ok = _call_u64(client, "ed25519Abc")
    if ok != 1:
        raise AssertionError(f"ed25519Abc expected 1, got {ok}")
    bad = _call_u64(client, "ed25519Abd")
    if bad != 0:
        raise AssertionError(f"ed25519Abd (tampered message) expected 0, got {bad}")
    print("nearcrypto: ed25519_verify abc ok==1, abd ok==0")

    print("suite NearCrypto: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-crypto: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
