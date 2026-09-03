# ProofForge.Cli

## Purpose

`pf`：把源模块抽出后编成 NEAR 制品。`Wasm.Near.Registry` 只登记源码模块名并钉
target IR digest，不能替代源模块 IR。

## Surface

```
pf build [--out DIR] [--module MOD] [Name ...]
pf --version
```

- 写出 `.wat` / `.wasm`（NEAR raw-u64），锁定 wat2wasm 1.0.41
- 裸名字映射到仓内 `Examples` fixture（`Counter` → `Examples.Counter`，其余多数在
  `Examples.Near.*`）；`--module` 接受点分 Lean 模块（可重复）
- 用户工程应使用 `--module` 或 `pf.toml` 的 `[[program]]` 条目；不写名字 = 全部登记源模块
- 每次运行重新抽取 IR；fixture digest 必须与 `Near.Registry` 钉值一致，否则 fail-closed（`ir/mismatch`）
- `--target near` 可显式给出；其它 target 名（含 `wasm`）被拒绝

## Tests

`Tests/CliSpec.lean` 钉参数解析与 usage。CLI 本身用 `lake exe pf -- --help`。
