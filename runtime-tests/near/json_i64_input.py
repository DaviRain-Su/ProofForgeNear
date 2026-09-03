#!/usr/bin/env python3
"""Canonical unquoted JSON integer (i64) input scenes."""

from __future__ import annotations

import os
import sys
from pathlib import Path

from near_rpc import NearClient, NearRpcError


def _require(name: str) -> str:
    value = os.environ.get(name, "").strip()
    if not value:
        raise SystemExit(f"near-json-i64-input: missing env {name}")
    return value


def _expect(client: NearClient, method: str, wire: bytes, value: int) -> None:
    got = client.view(method, wire)
    expected = NearClient.encode_u64_le(value & ((1 << 64) - 1))
    if got != expected:
        raise AssertionError(
            f"{method}({wire!r}): expected {expected.hex()}, got {got.hex()}"
        )


def _expect_failure(client: NearClient, wire: bytes, scene: str) -> None:
    try:
        client.view("echoValue", wire)
    except NearRpcError:
        print(f"near-json-i64-input: {scene} trapped ok")
        return
    raise AssertionError(f"{scene}: expected view failure")


def main() -> None:
    rpc = _require("PF_NEAR_RPC")
    home = Path(_require("PF_NEAR_HOME"))
    wasm = Path(_require("PF_NEAR_WASM"))
    client = NearClient(rpc, home)

    print("=== suite: NearJsonI64Input (canonical integer subset) ===")
    client.deploy(wasm)
    client.call("initialize", NearClient.encode_u64_le(0))

    accepted = [
        (0, b"0"),
        (1, b"1"),
        (-1, b"-1"),
        (123, b"123"),
        (-123, b"-123"),
        (1 << 62, str(1 << 62).encode()),
        ((1 << 63) - 1, str((1 << 63) - 1).encode()),
        (-(1 << 63), str(-(1 << 63)).encode()),
        (-((1 << 63) - 1), str(-((1 << 63) - 1)).encode()),
    ]
    for value, digits in accepted:
        wire = b" " + b"{" + b'"value"' + b":" + digits + b"}" + b" "
        _expect(client, "echoValue", wire, value)

    # mutating use persists and returns
    got = client.call("commitValue", b'{"value": -5}')
    used = NearClient.decode_u64_le(NearClient.success_value_bytes(got) or b"\x00" * 8)
    if used != (-5) & ((1 << 64) - 1):
        raise AssertionError(f"commitValue(-5) expected two's complement, got {used:#x}")
    print("near-json-i64-input: commitValue(-5) two's complement ok")

    failures = [
        (b"+1", "plus sign"),
        (b"007", "leading zeros"),
        (b"-0", "negative zero"),
        (b"1.0", "float"),
        (b"9223372036854775808", "max+1 positive"),
        (b"-9223372036854775809", "min-1 negative"),
        (b"99999999999999999999", "21 digits"),
        (b"true", "boolean"),
        (b'"123"', "quoted string"),
        (b"{} ", "missing field"),
        (b'{"value":1,"extra":2}', "unknown field"),
    ]
    for digits, scene in failures:
        _expect_failure(client, b'{"value":' + digits + b"}", scene)

    print("suite NearJsonI64Input: PASS")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, NearRpcError) as exc:
        print(f"near-json-i64-input: FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)