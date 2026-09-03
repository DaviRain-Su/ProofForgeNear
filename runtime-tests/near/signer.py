#!/usr/bin/env python3
"""NearSigner sandbox scenes for signer_account_id / signer_account_pk (engineering only).

Scenes:
  initialize() → get()==0
  signerId() == first 8 UTF-8 bytes of test.near (little-endian)
  signerIdLength() == 9
  checkDirectCall()==1 (signer == predecessor on a direct transaction)
  signerKeyLo() == curve tag 0 (ed25519) followed by key bytes 0..6, little-endian
  signerKeyTop() == key byte 31

Honesty: not testnet/mainnet, not formal. Requires PF_NEAR_RPC / PF_NEAR_HOME /
PF_NEAR_WASM. Missing sandbox → the wrapping signer.sh skips.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    v = os.environ.get(name, "").strip()
    if not v:
        raise SystemExit(f"near-signer: missing env {name}")
    return v


def _call_u64(client: NearClient, method: str) -> int:
    res = client.call(method, b"")
    value = NearClient.success_value_bytes(res)
    if value is None or len(value) < 8:
        raise AssertionError(f"{method} SuccessValue expected >=8 bytes, got {value!r}")
    return NearClient.decode_u64_le(value, 0)


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearSigner (signer account id / public key) ===")
    client.deploy(wasm)

    client.call("initialize", b"")
    got = client.view_u64("get")
    if got != 0:
        raise AssertionError(f"after initialize: get() expected 0, got {got}")
    print("nearsigner: initialize() -> get()==0 ok")

    signer_id = _call_u64(client, "signerId")
    expected = int.from_bytes(b"test.nea", "little")
    if signer_id != expected:
        raise AssertionError(
            f"signerId() expected first 8 UTF-8 bytes of test.near "
            f"({expected:#x}), got {signer_id:#x}"
        )
    signer_len = _call_u64(client, "signerIdLength")
    if signer_len != len(b"test.near"):
        raise AssertionError(f"signerIdLength() expected 9, got {signer_len}")
    print("nearsigner: signer AccountId == len(9) + test.nea words ok")

    direct = _call_u64(client, "checkDirectCall")
    if direct != 1:
        raise AssertionError(f"checkDirectCall expected 1 on a direct transaction, got {direct}")
    print("nearsigner: signer == predecessor on direct call ok")

    pub = client._pub
    key_lo = _call_u64(client, "signerKeyLo")
    expected_lo = int.from_bytes(bytes([0]) + pub[:7], "little")
    if key_lo != expected_lo:
        raise AssertionError(
            f"signerKeyLo() expected ed25519 tag + key bytes 0..6 "
            f"({expected_lo:#x}), got {key_lo:#x}"
        )
    key_top = _call_u64(client, "signerKeyTop")
    if key_top != pub[31]:
        raise AssertionError(f"signerKeyTop() expected {pub[31]:#x}, got {key_top:#x}")
    print("nearsigner: signer_account_pk 33-byte windows match the sandbox key ok")

    print("suite NearSigner: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-signer: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
