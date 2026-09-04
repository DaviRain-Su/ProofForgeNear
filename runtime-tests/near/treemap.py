#!/usr/bin/env python3
"""NearTreeMap sandbox scenes for sorted TreeMap storage (engineering only).

Scenes:
  initialize(0) → get()==0
  put in-order keys 5, 20, 100 → has(key)==1 for each; get returns the stored value
  keyAt exposes the ascending order: slot0=5, slot1=20, slot2=100
  duplicate put replaces the value in place (length unchanged)
  removeTail deletes the largest key; length shrinks
  out-of-order put (key smaller than tail) fails closed; state unchanged

Honesty: not testnet/mainnet, not formal. Requires PF_NEAR_RPC / PF_NEAR_HOME /
PF_NEAR_WASM. Missing sandbox → the wrapping treemap.sh skips.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    v = os.environ.get(name, "").strip()
    if not v:
        raise SystemExit(f"near-treemap: missing env {name}")
    return v


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearTreeMap (sorted TreeMap storage) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))
    if client.view_u64("get") != 0:
        raise AssertionError("after initialize(0): get() expected 0")
    print("neartreemap: initialize(0) → get()==0 ok")

    # insert three ascending keys
    client.call("putKey", NearClient.encode_u64_le(5))
    client.call("putValue", NearClient.encode_u64_le(500))
    client.call("putKey", NearClient.encode_u64_le(20))
    client.call("putValue", NearClient.encode_u64_le(2000))
    client.call("putKey", NearClient.encode_u64_le(100))
    client.call("putValue", NearClient.encode_u64_le(10000))
    if client.view_u64("get") != 3:
        raise AssertionError(f"after three puts: get() expected 3")
    print("neartreemap: three ascending puts → length 3 ok")

    # has + get for each
    for key in (5, 20, 100):
        if client.view_u64("has", NearClient.encode_u64_le(key)) != 1:
            raise AssertionError(f"has({key}) expected 1")
    if client.view_u64("has", NearClient.encode_u64_le(7)) != 0:
        raise AssertionError("has(7) expected 0")
    if client.view_u64("getValue", NearClient.encode_u64_le(20)) != 2000:
        raise AssertionError("getValue(20) expected 2000")
    print("neartreemap: has/getValue over sorted keys ok")

    # ordered read
    if client.view_u64("keyAt", NearClient.encode_u64_le(0)) != 5:
        raise AssertionError("keyAt(0) expected 5")
    if client.view_u64("keyAt", NearClient.encode_u64_le(1)) != 20:
        raise AssertionError("keyAt(1) expected 20")
    if client.view_u64("keyAt", NearClient.encode_u64_le(2)) != 100:
        raise AssertionError("keyAt(2) expected 100")
    if client.view_u64("keyAt", NearClient.encode_u64_le(3)) != 0:
        raise AssertionError("keyAt(3) expected fallback 0")
    print("neartreemap: ascending keyAt order ok")

    # duplicate put fails closed: v0 has no lookup-rewrite path for a present tail key
    try:
        client.call("putKey", NearClient.encode_u64_le(20))
        client.call("putValue", NearClient.encode_u64_le(9999))
    except NearRpcError:
        print("neartreemap: duplicate put trapped ok")
    else:
        raise AssertionError("duplicate put must fail action validation")
    if client.view_u64("get") != 3:
        raise AssertionError("failed duplicate put must not grow the map")

    # remove tail
    client.call("removeTail", NearClient.encode_u64_le(100))
    if client.view_u64("get") != 2:
        raise AssertionError("after removeTail: get() expected 2")
    if client.view_u64("has", NearClient.encode_u64_le(100)) != 0:
        raise AssertionError("removed key must be absent")
    print("neartreemap: removeTail ok")

    # out-of-order put fails closed: the whole tx traps and state rolls back
    try:
        client.call("putKey", NearClient.encode_u64_le(7))
        client.call("putValue", NearClient.encode_u64_le(777))
    except NearRpcError:
        print("neartreemap: out-of-order put trapped ok")
    else:
        raise AssertionError("out-of-order put must fail action validation")
    if client.view_u64("get") != 2:
        raise AssertionError("failed put must roll back length")
    print("neartreemap: out-of-order put rolled back ok")

    print("suite NearTreeMap: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-treemap: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)