#!/usr/bin/env python3
"""NearLazy sandbox scenes for Lazy/LazyOption cells (engineering only).

Scenes:
  initialize(7) → get()==7
  lazySet(41) → lazyGet()==41 (bare-prefix cell, exact 8-byte Borsh value)
  lazyGetOrSet on absent cell initializes and returns the seed
  lazyGetOrSet on present cell returns the stored value without writing
  optIsSome()==0 before, ==1 after optSet; optGet returns the value
  optTake removes the cell and returns the previous value; optIsSome()==0 after

Honesty: not testnet/mainnet, not formal. Requires PF_NEAR_RPC / PF_NEAR_HOME /
PF_NEAR_WASM. Missing sandbox → the wrapping lazy.sh skips.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    v = os.environ.get(name, "").strip()
    if not v:
        raise SystemExit(f"near-lazy: missing env {name}")
    return v


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearLazy (Lazy / LazyOption cells) ===")
    client.deploy(wasm)

    client.call("initialize", NearClient.encode_u64_le(7))
    got = client.view_u64("get")
    if got != 7:
        raise AssertionError(f"after initialize(7): get() expected 7, got {got}")
    print("nearlazy: initialize(7) → get()==7 ok")

    # absent cell reads the explicit fallback
    if client.view_u64("lazyGet") != 0:
        raise AssertionError("lazyGet on absent cell expected fallback 0")
    print("nearlazy: absent lazyGet fallback 0 ok")

    client.call("lazySet", NearClient.encode_u64_le(41))
    if client.view_u64("lazyGet") != 41:
        raise AssertionError("lazyGet after lazySet(41) expected 41")
    print("nearlazy: lazySet(41) → lazyGet()==41 ok")

    # getOrSet on a present cell must not overwrite
    client.call("lazyGetOrSet", NearClient.encode_u64_le(99))
    if client.view_u64("lazyGet") != 41:
        raise AssertionError("lazyGetOrSet must not overwrite a present cell")
    print("nearlazy: lazyGetOrSet keeps present value ok")

    # absent-cell initialization runs on a fresh subaccount (init is once-only)
    fresh = "lazy-fresh.test.near"
    client.create_subaccount_with_key(fresh, 10**25)
    client.deploy_to(fresh, wasm)
    client.call_on(fresh, "initialize", NearClient.encode_u64_le(0))
    got = client.call_on(fresh, "lazyGetOrSet", NearClient.encode_u64_le(33))
    used = NearClient.decode_u64_le(NearClient.success_value_bytes(got) or b"\x00" * 8)
    if used != 33:
        raise AssertionError(f"lazyGetOrSet on absent cell expected 33, got {used}")
    if client.view_u64_on(fresh, "lazyGet") != 33:
        raise AssertionError("lazyGet after lazyGetOrSet(33) expected 33")
    print("nearlazy: lazyGetOrSet initializes absent cell ok")

    # LazyOption: absent → isSome 0, fallback read
    if client.view_u64("optIsSome") != 0:
        raise AssertionError("fresh optIsSome expected 0")
    if client.view_u64("optGet") != 0:
        raise AssertionError("fresh optGet expected fallback 0")
    print("nearlazy: absent LazyOption fallback ok")

    client.call("optSet", NearClient.encode_u64_le(0x123456789ABCDEF0))
    if client.view_u64("optIsSome") != 1:
        raise AssertionError("optIsSome after optSet expected 1")
    if client.view_u64("optGet") != 0x123456789ABCDEF0:
        raise AssertionError("optGet after optSet value mismatch")
    print("nearlazy: optSet → optIsSome/optGet ok")

    got = client.call("optTake")
    taken = NearClient.decode_u64_le(NearClient.success_value_bytes(got) or b"\x00" * 8)
    if taken != 0x123456789ABCDEF0:
        raise AssertionError(f"optTake expected previous value, got {taken:#x}")
    if client.view_u64("optIsSome") != 0:
        raise AssertionError("optIsSome after optTake expected 0")
    print("nearlazy: optTake removes cell ok")

    print("suite NearLazy: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-lazy: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)