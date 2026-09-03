# ProofForge.Wasm（NEAR lowering）

## Purpose

本仓库把 Lean 直接 lowering 到 WAT / `.wasm`，目标是 **NEAR Protocol**。
host import 表钉 `env`，存储是 KV raw-u64。CLI 不接受泛名 `wasm`。

调研背景见 [research/06-wasm-feasibility.md](../research/06-wasm-feasibility.md)。

## 结构

```text
ProofForge/Wasm/
  Host.lean       -- host import 表 + 存储布局 + 入口 ABI
  IR.lean         -- 程序形状、v0 子集、canonical 拼写（域由 NEAR 注入）
  Emit.lean       -- Core → WAT
  Near/           -- NEAR raw-u64/Borsh + guest arena + bounded raw storage
```

- digest 域：`near-raw-u64|`
- runtime 叶子不跨链：抽取期即被拒绝
- 锁定组装器是 `wat2wasm` 1.0.41。链上产物是 `.wat` / `.wasm`

成员合同见 [`Wasm/Near`](near.md)。
