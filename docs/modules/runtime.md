# ProofForge.Wasm.Near.Runtime

## Purpose

普通 Lean 名，抽出后变成 NEAR `env` host import。不是新 DSL。

合约 `open ProofForge.Wasm.Near.Sdk`。抽出器只识别具名 Runtime stub（SDK 名字经
`@[pf_inline]` 消去）。根层不再提供混合 façade。

## Surface

宿主 stub `@[irreducible]`。NEAR 走 `env`。

摘：`nearPredecessor` / `nearCurrentAccount` / storage / Promise / log。

抽出器认这些具名 stub；外来叶子 fail closed。

## Tests

`Tests/NearCtxSpec.lean` + `runtime-tests/near/context.sh`。
