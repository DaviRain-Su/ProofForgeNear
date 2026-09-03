# ProofForge NEAR

[![CI](https://github.com/DaviRain-Su/ProofForgeNear/actions/workflows/ci.yml/badge.svg)](https://github.com/DaviRain-Su/ProofForgeNear/actions/workflows/ci.yml)

[English](README.md)

Lean 4 → NEAR 合约编译器：用 `@[pf_entry]` 标记普通 Lean 入口；ProofForge 抽出受检 IR，
发射 WAT，再由 **钉死的 wat2wasm**（wabt 1.0.41）汇编 `.wasm`。
表面是 **NEAR raw-u64**，配 near-sdk 式 SDK 与 **near-sandbox** 工程门。
本仓库是 ProofForge 的 NEAR 单目标分支。

产品契约：[`docs/product/support-matrix.md`](docs/product/support-matrix.md)。
写合约指南：[`docs/product/writing-contracts.md`](docs/product/writing-contracts.md)。

## 布局

- `ProofForge/Core/` — 目标无关的值/效果 IR、CFG、codec、schema
- `ProofForge/Extract/` — Lean 表达式 → IR 抽取器（仅 NEAR）
- `ProofForge/Wasm/` — 家族 Host / IR / Emit，以及 `Near/`
- `ProofForge/Cli.lean` — `pf` CLI（`pf build`）
- `Examples/` — NEAR 示例（digest 钉在 `ProofForge/Wasm/Near/Registry.lean`）
- `Tests/` — elaboration 期规格（`#guard` / `example`）
- `runtime-tests/near/` — near-sandbox 2.13.0 集成门禁
- `docs/product/` — 能力矩阵、写合约指南、路线图
- `docs/research/` — **历史**决策笔记（已归档）
- `docs/modules/` — 各模块合同

## 构建与测试

```text
./.agents/setup        # 钉死工具链：elan/Lake v4.31.0、wat2wasm 1.0.41、near-sandbox 2.13.0
lake build             # 编译器库
lake build pf          # CLI 可执行文件
lake build Tests       # 测试套件
lake build Examples    # 示例合约
```

本地 CI 镜像：`scripts/ci_local.sh`（`--fast` 只跑 Python 守卫）。

## CLI

```text
pf build [--out DIR] [--module MOD] [Program ...]
pf --version
```

`pf build` 写出 `Name.wat` / `Name.wasm`（NEAR raw-u64；锁定 wat2wasm）。
裸名映射到仓内 `Examples`；用户工程传 `--module` 或在 `pf.toml` 写 `[[program]]`。

## 链上门禁

```text
runtime-tests/near/check.sh      # NEAR import 表 + wasm magic
runtime-tests/near/counter.sh    # near-sandbox Counter（缺 sandbox 则跳过）
```

## 用户合约

合约只 import `ProofForge.Attr` 加上 NEAR SDK，不要 import `ProofForge` 伞模块：

```lean
import ProofForge.Attr
import ProofForge.Wasm.Near.Sdk
```

SDK 传递闭包不得触及 Emit/Assemble/Registry（CI：`scripts/check_sdk_import_closure.py`）。
Lake lib：`ProofForgeNearSdk`。

## 信任边界

- Kernel 定理钉的是用户 `def` / 静态字段，**不是** `.wasm` 精化。
- near-sandbox 变绿是**工程**门，不是证明。
- NEAR JSON / NEP 形导出是**有界规范子集**，不是完整标准 ABI。
