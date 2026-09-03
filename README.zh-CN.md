# ProofForge NEAR

[![CI](https://github.com/DaviRain-Su/ProofForgeNear/actions/workflows/ci.yml/badge.svg)](https://github.com/DaviRain-Su/ProofForgeNear/actions/workflows/ci.yml)
[![Lean 4.31.0](https://img.shields.io/badge/Lean-v4.31.0-blue)](https://lean-lang.org)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

[English](README.md)

**用 Lean 4 写 NEAR 智能合约，用 Lean 内核证明，再编译到 WebAssembly。**
ProofForge NEAR 是 Lean 4 → NEAR Wasm 合约编译器：在普通 Lean 源码里用
`@[pf_entry]` 标记入口，抽出器将其降级为受检查 IR，发射 WAT，再经**锁定版
wat2wasm**(wabt 1.0.41）汇编为 `.wasm`。目标面是 **NEAR raw-u64**，配
near-sdk 风格 SDK，所有 fixture 都过 **near-sandbox 2.13.0** 链上门禁。
本仓是 [ProofForge](https://github.com/DaviRain-Su/ProofForge) 的 NEAR
单目标 fork。

## 特性

- **Lean 4 即合约语言**——入口、状态记录、错误类型都是普通 Lean
  `def`/`structure`/`inductive`；相关定理写在同一文件里（见
  `Examples/Counter.lean`)。
- **受检查抽取管线**——`@[pf_entry]` → profile 门禁 → 目标无关 IR/CFG →
  NEAR 方言 IR → WAT → `.wasm`。Registry 钉住的 digest 在抽取输出漂移时
  直接拒绝构建。
- **near-sdk 风格 SDK**(`ProofForgeNearSdk`)——有界存储
  (`Vector`/`Lookup`/`Iterable`/`Queue`)、NEP-141 同质化代币账本与注册
  经济学、跨合约 **Promise**（有序 N 路 join、回调）、带钉死旧 schema
  digest 的迁移，以及 JSON 边界 codec(NEP 形状参数/返回）。
- **链上工程门禁**——near-sandbox 对每个 fixture 做部署与调用：计数器
  生命周期、schema 迁移、promise join、存储、NEP-141 事件。
- **锁定工具链**——Lean/Lake v4.31.0、wabt wat2wasm 1.0.41、
  near-sandbox 2.13.0(`.agents/setup`)。

## 示例

```lean
import ProofForge

namespace MyCounter

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (initial : UInt64) : State :=
  { value := initial }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

@[pf_entry]
def increment (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if s.value ≤ u64Max - delta then
    let next := s.value + delta
    .ok ({ value := next }, next)
  else
    .error .overflow

end MyCounter
```

```text
lake exe pf -- build --module MyCounter.Counter   # 产出 Counter.wat / Counter.wasm
```

## 构建与测试

```text
./.agents/setup        # 锁定工具链：elan/Lake v4.31.0、wat2wasm 1.0.41、near-sandbox 2.13.0
lake build             # 编译器库
lake build pf          # CLI 可执行
lake build Tests       # 测试套件（elaboration 期断言）
lake build Examples    # 示例合约
```

本地 CI 镜像：`scripts/ci_local.sh`(`--fast` 只跑 Python 守卫）。

## CLI

```text
pf build [--out DIR] [--module MOD] [Program ...]
pf --version
```

`pf build` 写出 `Name.wat` / `Name.wasm`(NEAR raw-u64；锁定 wat2wasm)。
裸名字映射到仓内 `Examples` fixture；用户项目传 `--module` 或在
`pf.toml` 里列 `[[program]]`。

## 链上门禁

```text
runtime-tests/near/check.sh      # NEAR import 表 + wasm magic
runtime-tests/near/counter.sh    # near-sandbox Counter（无沙箱时跳过）
```

## 布局

- `ProofForge/Core/` — 目标无关的 value/effect IR、CFG、codec、schema
- `ProofForge/Extract/` — Lean 表达式 → IR 抽出器（仅 NEAR)
- `ProofForge/Wasm/` — 家族 Host / IR / Emit 加 `Near/`
- `ProofForge/Cli.lean` — `pf` CLI(`pf build`)
- `Examples/` — NEAR fixture(digest 钉在 `ProofForge/Wasm/Near/Registry.lean`)
- `Tests/` — elaboration 期规格(`#guard` / `example`)
- `runtime-tests/near/` — near-sandbox 2.13.0 集成门禁
- `docs/product/` — 支撑矩阵、写作指南、路线图
- `docs/research/` — **历史**决策记录（归档）
- `docs/modules/` — 逐模块契约

## 用户合约

合约只 import `ProofForge.Attr` 与 NEAR SDK——绝不 import `ProofForge`
伞包：

```lean
import ProofForge.Attr
import ProofForge.Wasm.Near.Sdk
```

SDK 传递闭包不得触及 Emit/Assemble/Registry(CI 由
`scripts/check_sdk_import_closure.py` 强制）。Lake lib:`ProofForgeNearSdk`。

## 信任边界

- 内核定理覆盖的是用户 `def` / 静态字段——**不是** `.wasm` 精化。
- near-sandbox 绿是**工程**门禁，不是证明。
- NEAR JSON / NEP 形状导出是**有界规范子集**，不是完整标准 ABI。

## 相关仓库

- [ProofForge](https://github.com/DaviRain-Su/ProofForge) — 多目标上游 monorepo
- [ProofForgeEvm](https://github.com/DaviRain-Su/ProofForgeEvm) — EVM 单目标 fork
- [ProofForgeXrpl](https://github.com/DaviRain-Su/ProofForgeXrpl) — XRPL 单目标 fork

## 许可证

[MIT](LICENSE) © 2026 DaviRain-Su
