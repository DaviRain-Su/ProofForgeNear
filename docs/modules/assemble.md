# ProofForge.Wasm.Near.Assemble

## Purpose

把 NEAR IR 先编成 WAT，再调用本机锁定的 `wat2wasm 1.0.41` 写出 `.wasm`。

## Boundary

子进程，不是 FFI。PATH 上随便一个 `wat2wasm` 不算：版本必须是 `1.0.41`。
写出 `{name}.wat` / `{name}.wasm`。WAT 头含 `;; digest=`（target IR digest）。

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Near.Assemble` | NEAR WAT 头 `PROOF-FORGE-NEAR-RAW-U64`；调 wat2wasm | rustc / cargo / near-sandbox |

## API

- `assembleProgram outDir program : IO Result`
- `Result`：`watPath` / `wasmPath` / `watSource`

## Tests

`runtime-tests/near/check.sh`：import 表 + wasm magic。
sandbox 门见 [near.md](near.md)。
