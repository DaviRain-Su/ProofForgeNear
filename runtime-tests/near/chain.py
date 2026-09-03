#!/usr/bin/env python3
"""NearChain sandbox scenes for epoch/gas/locked/random_seed (engineering only).

Scenes:
  initialize(0) → get()==0
  epoch() is stable within one block
  lockedLo()/lockedHigh() == 0 (sandbox account never stakes)
  seedLo()/seedTop() agree across two reads pinned to one block
  prepaid() > 0 and burnt() > 0 with burnt() <= prepaid() (gas meters live)

Honesty: not testnet/mainnet, not formal. Requires PF_NEAR_RPC / PF_NEAR_HOME /
PF_NEAR_WASM. Missing sandbox → the wrapping chain.sh skips.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    v = os.environ.get(name, "").strip()
    if not v:
        raise SystemExit(f"near-chain: missing env {name}")
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

    print("=== suite: NearChain (epoch / gas / locked balance / random seed) ===")
    client.deploy(wasm)

    client.call("initialize", NearClient.encode_u64_le(0))
    got = client.view_u64("get")
    if got != 0:
        raise AssertionError(f"after initialize(0): get() expected 0, got {got}")
    print("nearchain: initialize(0) -> get()==0 ok")

    e0 = client.view_u64("epoch")
    e1 = client.view_u64("epoch")
    if e0 != e1:
        raise AssertionError(f"epoch() advanced between sibling views ({e0} -> {e1})")
    print(f"nearchain: epoch() stable at {e0} ok")

    locked = client.view_account_locked(client.account_id)
    locked_lo = client.view_u64("lockedLo")
    locked_hi = client.view_u64("lockedHigh")
    if locked_lo != locked & ((1 << 64) - 1):
        raise AssertionError(
            f"lockedLo() expected locked balance low word "
            f"{locked & ((1 << 64) - 1)}, got {locked_lo}"
        )
    if locked_hi != locked >> 64:
        raise AssertionError(
            f"lockedHigh() expected locked balance high word "
            f"{locked >> 64}, got {locked_hi}"
        )
    print(f"nearchain: account_locked_balance u128 == ({locked_hi:#x}, {locked_lo:#x}) ok")

    h0 = client.latest_block_height()
    seed_lo = client.view_u64("seedLo")
    seed_top = client.view_u64("seedTop")
    h1 = client.latest_block_height()
    if h0 != h1:
        h0 = h1
        seed_lo = client.view_u64("seedLo")
        seed_top = client.view_u64("seedTop")
        h1 = client.latest_block_height()
        if h0 != h1:
            raise AssertionError(
                f"block still advancing under sole-client views (h0={h0}, h1={h1})"
            )
    seed_lo2 = client.view_u64("seedLo")
    seed_top2 = client.view_u64("seedTop")
    if client.latest_block_height() != h1:
        raise AssertionError("seed views crossed a block boundary")
    if (seed_lo, seed_top) != (seed_lo2, seed_top2):
        raise AssertionError(
            f"random_seed must be constant within one block: "
            f"({seed_lo:#x}, {seed_top:#x}) != ({seed_lo2:#x}, {seed_top2:#x})"
        )
    print(f"nearchain: random_seed constant within block {h1} ok")

    prepaid = _call_u64(client, "prepaid")
    burnt = _call_u64(client, "burnt")
    if prepaid == 0:
        raise AssertionError("prepaid() returned 0; transaction gas must be prepaid")
    if burnt == 0:
        raise AssertionError("burnt() returned 0; the call itself burns gas")
    if burnt > prepaid:
        raise AssertionError(f"burnt() {burnt} exceeds prepaid() {prepaid}")
    print(f"nearchain: 0 < burnt() ({burnt}) <= prepaid() ({prepaid}) ok")

    print("suite NearChain: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-chain: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
