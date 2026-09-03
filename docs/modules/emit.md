# ProofForge.Wasm.Emit

## Purpose

把 Wasm 家族 IR 编成 WAT 文本。公开入口先假定程序已经过 `Wasm.IR` 子集检查；
每个 method 再经 `Core.CFG` 降成显式 basic block。Emitter 遍历 checked terminator
和 exit，不重新递归解释 source `ite` / `forBody`。

## Boundary

`Wasm.Emit` 共享 Core 标量 / 控制流到 WAT 的 lowering。NEAR 的 import 表与 KV
布局由 `Near.Emit` 注入。

| 模块 | 拥有 |
|---|---|
| `Wasm.Emit` | Core checked 算术、`ite`、`storeField`、`okState` / `errorOverflow` → WAT |
| `Near.Emit` | `env` import、KV 8-byte LE、bounded Borsh/JSON、arena、Promise |

WAT 头含 digest。空 `entries` 失败。外来叶子 fail closed，发射器不再认。

## Tests

`Tests/NearSpec.lean`：Counter WAT 含 module / digest / `env` import。
`Tests/EmitSpec.lean` 只挂载模块。
