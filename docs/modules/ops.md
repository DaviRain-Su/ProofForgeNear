# ProofForge.Core.Ops / Extract.Ops / Near.Ops

## Purpose

抽出器与 backend 共享一套可扩展操作树。公共构造子在 `ProofForge.Core.Ops`；
抽出器方言是 `Extract.IR.ValKind` / `OpExt`（`.near`）；链叶子和效应在
`Wasm.Near.Ops`。

新的抽出链路走 `Core.Ops`、`Extract.IR` 和 NEAR Ops。发射 overflow 路径的依据是
checked 算术，不是方法名。

## Types

`Core.Ops.Val`：`arg` / `local` / `field` / `lit` / 位运算 `bitAnd` `bitOr` `bitXor`
`bitNot` `shiftL` `shiftR` / `indexGet` / `loopIx` / `select` / wrapping `*U64` /
`ext kind operands`。

`Core.Ops.Cmp`：`eq` / `ne` / `lt` / `le` / `gt` / `ge`。

`Core.Ops.Op`：`letLocal` / `joinLocal` / `setLocal`、checked 四则、`ite`、
`forAccum` / `forBody` / `indexSetLeaf` / `indexSet`、`storeField` / `okState` /
`errorOverflow` / `errorNamed` / `errorTyped` / `returnU64` / `returnState` /
`ext payload`。

`storeField name v`：写一个已摊平的状态叶。mutate 槽 diff 一次可发多条；单叶仍压成
`okState`。

`Extract.Ops` 只是抽出器方言上的 decoder-facing 名字（`Val.near*`、`Op.near*` 等），
不再另建一棵 Ops 树。`opValuesAny` 只认核心构造器、`.ext (.near _)`、`.errorTyped`
与 false 兜底。

## Tests

`Tests/CounterSpec.lean`：`increment` 抽出 `checkedAddU64`。
`Tests/TargetOpsSpec.lean`：NEAR value/op well-formed。
