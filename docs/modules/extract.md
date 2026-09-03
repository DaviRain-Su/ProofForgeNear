# ProofForge.Extract

## Purpose

从 elaborated `Expr` 抽出 `Extract.IR.Program`（`Core.IR.Program` 配上抽出器方言）。前端先从 `init` 的结果类型建立 typed state schema，再抽方法 Ops；物理槽表只是 schema 的兼容视图。

## State schema

`ProofForge.Core.Schema` 是状态布局的 source of truth：

- `Place` / `PathStep` 保存稳定的源位置身份。structure 字段由 owner type + 声明序号标识，
  字段名不参与身份判定，只用于诊断和兼容叶名；Vector 元素用 index；Option 的 tag /
  payload 是显式路径步骤。
- `Leaf` 保存 source scalar type；`VectorLayout` 保存长度、每元素字节数和每元素叶子数。
- `IR.Program.slots` 由 `IR.slotsOfSchema` 生成，继续保留 `nodes_0_value`、`slot_tag`
  这类显示名。抽出的程序必须满足 `IR.schemaMatchesSlots`。

`Wasm.Near.IR.fromExtracted` 只调用 typed layout 查询，不扫描 `_0_left`、`_tag`、`_p0`
猜 Vector / Option 布局。

## Core evaluation and writeback

`ProofForge.Core.Eval` 在 schema 和规范化 Ops 都可用后，为每个抽出方法建立
`IR.Method.evaluation`：

- checked add/sub/mul/div/mod 变成显式 `ValueRef.checked kind lhs rhs`，状态写入不再依赖
  emitter 的“最近一次计算结果”寄存器。
- 静态状态写入使用 typed `Place`；Option 成功结果明确列出 tag 和 payload 两次写入；
  多叶 record diff 的每个 `storeField` 也有对应 typed write event。
- lexical scalar let、branch / bounded loop 保留为结构化 state-effect tree，不依赖 emitter
  的遍历游标。
- 运行时 Vector 下标写入使用 `DynamicPlace(vector Place, index, elementPath)`。
- `Evaluation.explicit = false` 只用于没有 schema 的旧手写 fixture。

当前 `Ops` 仍是前端 compatibility lowering，但 emitter 不再直接消费抽出方言：
`Core.Target.projectProgram` 按 `Near.IR.extractRegistration` 递归投影公共 Core，并把
extension conversion 留在 NEAR 模块。`Core.Evaluation` 随 method 保留。这里刻意不让
旧写回规则进入 Core：把任一物理布局特判塞回 Core 都会污染 source 语义。

## Source-form normalization

抽出器承诺对已测试的 syntax-only 写法保持同一 Core：直接 record constructor 与等价的
外层 pure `let` + record update 会抽成相同 schema、slots、方法 Ops 和 evaluation。规范化刻意很窄：
窄整数 alias 和包住 `if` 的 pure head `let` 做 zeta-reduction；`UInt64` pure let 保留成
`letLocal`，纯值 `if` 保留成 `Val.select`，避免把同一 mutation continuation 复制到两个
分支。NEAR 效应经 `mentionsNearEffect` 识别；循环仍交给专用 decoder。这里不做全局 `whnf`。

公开入口：`decodeExpr (env : Environment) → Nat → Expr → …`（可选 `preserveLocals`）与
`mentionsNearEffect (env : Environment) → Nat → Expr → Bool`。

方法完成规范化后会递归检查所有 Val、branch 和 loop 的 `.arg`。init 只允许
`arg < paramCount`；mutate/view 另允许 `arg == paramCount` 表示隐式 state。任何 proof / let /
callback binder 泄漏都会在 lowering 之前 fail closed。

## Boundary

递归下降 `Expr`。`x ≤ u64Max - y` → `checkedAddU64`；`y ≤ x` → `checkedSubU64`；
`y = 0 ∨ x ≤ u64Max / y` → `checkedMulU64`；`y ≠ 0` 后 `/` `%` →
`checkedDivU64` / `checkedModU64`。比较认 `=` `≠` `<` `≤` `>` `≥`。假支不必是
overflow。`match opt with | none => a | some n => b` 抽成 `ite (eq tag 0)`。

`ProofForge.Wasm.Near.Runtime` 的具名 stub 抽成 `.near` 叶子。位运算 /
有界 `forIn [:N]` / 运行时 `Vector` 下标 / 命名 `Error` 构造子 /
`UInt64 × UInt64` view 也抽。外来叶子 fail closed。

`@[pf_entry]` 只是标记。种类从返回类型推断：structure → init；`Except` → mutate；
标量 / `Prod` / 有界容器 / `@[pf_boundary]` 类型 → view。Lean `init` 的链上名是
`initialize`。允许多个 init / mutate / view；槽表从名为 `init` 的那个收。

`Extract.IR.ValKind` / `OpExt` 只含 `.near`，并提供 `ValKind.arity`、
`OpExt.mapValues/values/wellFormed`、`cfgDialect`、`toCFG`、`methodToCFG`、`Op.wellFormed`。

## API

- `inferSchema env initName : Except String Core.Schema`
- `inferSlots env initName : Except String (Array Core.IR.Slot)`（schema 的兼容视图）
- `inferFields env initName : Except String (Array String)`
- `decodeExpr env n e`（可选 `preserveLocals`）
- `mentionsNearEffect env n e : Bool`
- `extractModuleIR env ns (fields?)`（收 `@[pf_entry]`）
- `#pf_near_build`

## Tests

`Tests/BuildSpec.lean`：收入口；无标记 fail closed。
`Tests/CounterSpec.lean` / `PairSpec.lean` / `FlagSpec.lean` / `WindowSpec.lean` /
`PhaseSpec.lean`：对应 fixture 的源语义与抽出形状。
