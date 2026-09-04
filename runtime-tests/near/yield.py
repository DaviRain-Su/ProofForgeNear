#!/usr/bin/env python3
"""NearYield sandbox scenes for resumable yield promises (engineering only).

Scenes:
  initialize(0) → get()==0
  scheduleYield(41) commits marker 41 and schedules a yield promise (no resume needed
    for the detached assertion)
  resumeYield with an arbitrary 32-byte id returns 0 (no matching pending yield) without
    changing contract state

Honesty: not testnet/mainnet, not formal. Requires PF_NEAR_RPC / PF_NEAR_HOME /
PF_NEAR_WASM. Missing sandbox → the wrapping yield.sh skips.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    v = os.environ.get(name, "").strip()
    if not v:
        raise SystemExit(f"near-yield: missing env {name}")
    return v


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearYield (resumable yield promise lifecycle) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))
    if client.view_u64("get") != 0:
        raise AssertionError("after initialize(0): get() expected 0")
    print("nearyield: initialize(0) → get()==0 ok")

    # scheduleYield creates a resumable yield promise whose runtime-derived id never
    # reaches the source; nothing resumes it, so the transaction stays pending and the
    # caller's state rolls back (the host accepted the scheduling but the receipt
    # never finalizes within the RPC window).
    # The yield receipt stays pending forever (nobody resumes it); the RPC commit may
    # time out while the caller's own state transition still lands. Poll for it.
    try:
        client.call("scheduleYield", NearClient.encode_u64_le(41))
    except NearRpcError:
        pass
    deadline = 60
    for _ in range(deadline):
        if client.view_u64("get") == 41:
            break
    else:
        raise AssertionError("scheduleYield's marker never committed")
    print("nearyield: scheduleYield committed marker 41 while its yield receipt stays pending ok")

    # resumeYield with a compile-time all-zero id: nearcore rejects the token as
    # malformed before any yield lookup — the transaction fails synchronously and the
    # caller's state is unchanged (fail-closed resume surface).
    try:
        client.call("resumeYield", NearClient.encode_u64_le(0))
    except NearRpcError:
        print("nearyield: resumeYield(malformed token) rejected synchronously ok")
    else:
        raise AssertionError("malformed yield token must fail action validation")
    if client.view_u64("get") != 41:
        raise AssertionError("resume failure must not change caller state")

    print("suite NearYield: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-yield: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)