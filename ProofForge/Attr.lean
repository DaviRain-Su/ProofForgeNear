import Lean

open Lean

namespace ProofForge.Attr

/-- Declare the exact prior NEAR state-schema digest accepted by one migration entry. -/
syntax (name := pf_near_migrate)
  "pf_near_migrate" num : attr

private partial def syntaxNatLiterals (node : Syntax) : Array Nat :=
  match node.isNatLit? with
  | some value => #[value]
  | none => node.getArgs.flatMap syntaxNatLiterals

/-- 只标记可编译根。种类由返回类型推断。 -/
initialize pfEntryAttr : TagAttribute ←
  registerTagAttribute `pf_entry
    "mark a Lean definition as a ProofForge compile root"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_entry is not a definition"

/-- 显式允许抽出器在控制流边界 β 展开的已检查、有界 helper。 -/
initialize pfInlineAttr : TagAttribute ←
  registerTagAttribute `pf_inline
    "allow the ProofForge extractor to inline a bounded helper definition"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_inline is not a definition"

/-- Mark a compiler-owned structure or inductive as an ordinary logical contract-boundary
value. This is intentionally representation-free: the shared codec still derives and validates
its complete field/variant schema, while the target owns its wire layout. The marker exists so
reusable SDK value types under the reserved `ProofForge` namespace do not need one-off extractor
or emitter cases. -/
initialize pfBoundaryAttr : TagAttribute ←
  registerTagAttribute `pf_boundary
    "allow a compiler-owned datatype to use the generic ProofForge boundary codec"
    fun decl => do
      unless decl.toString.startsWith "ProofForge." do
        throwError "extract/unsupported: pf_boundary is reserved for compiler-owned ProofForge datatypes"
      let env ← getEnv
      match env.find? decl with
      | some (.inductInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_boundary is not a structure or inductive"

/-- Mark one NEAR entry as callable only when predecessor and current AccountId are equal. -/
initialize pfNearPrivateAttr : TagAttribute ←
  registerTagAttribute `pf_near_private
    "declare a NEAR private entry wrapper"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_near_private is not a definition"

/-- Mark one mutating NEAR entry or initializer as accepting an attached deposit. -/
initialize pfNearPayableAttr : TagAttribute ←
  registerTagAttribute `pf_near_payable
    "declare a NEAR payable entry wrapper"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_near_payable is not a definition"

/-- Mark one exact zero-parameter NEAR method as matching near-sdk's generated no-args wrapper:
the request body is not read or validated. Other zero-parameter methods retain exact-empty input. -/
initialize pfNearNoArgsAttr : TagAttribute ←
  registerTagAttribute `pf_near_no_args
    "declare a NEAR zero-parameter wrapper that ignores request bytes"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_near_no_args is not a definition"

/-- Mark one explicit logical-Unit NEAR mutator as matching near-sdk's omitted-return wrapper:
persist state but do not call `value_return`. Without this marker explicit Unit remains JSON null. -/
initialize pfNearVoidAttr : TagAttribute ←
  registerTagAttribute `pf_near_void
    "declare a NEAR mutator with an empty success return"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_near_void is not a definition"

/-- Mark an exact mutating U128 result as a dual terminal: immediate quoted JSON when no returned
Promise was staged on the branch, otherwise `promise_return` of that one Promise. -/
initialize pfNearPromiseOrValueAttr : TagAttribute ←
  registerTagAttribute `pf_near_promise_or_value
    "declare a NEAR mutator returning either quoted U128 or one Promise"
    fun decl => do
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure ()
      | _ => throwError "extract/unsupported: pf_near_promise_or_value is not a definition"

/-- Mark one NEAR mutator as an explicit migration from one exact prior schema digest. Target
binding additionally requires an explicit private attribute and rejects payable migration. -/
initialize pfNearMigrateAttr : ParametricAttribute Nat ←
  registerParametricAttribute {
    name := `pf_near_migrate
    descr := "declare an authenticated NEAR migration from one exact state-schema digest"
    getParam := fun decl stx => do
      let values := syntaxNatLiterals stx
      unless values.size == 1 do
        throwError "invalid pf_near_migrate syntax"
      let digest := values[0]!
      unless digest ≤ 18446744073709551615 do
        throwError "extract/unsupported: pf_near_migrate digest must fit UInt64"
      let env ← getEnv
      match env.find? decl with
      | some (.defnInfo _) => pure digest
      | _ => throwError "extract/unsupported: pf_near_migrate is not a definition"
  }

def isEntry (env : Environment) (decl : Name) : Bool :=
  pfEntryAttr.hasTag env decl

def isInline (env : Environment) (decl : Name) : Bool :=
  pfInlineAttr.hasTag env decl

def isBoundary (env : Environment) (decl : Name) : Bool :=
  pfBoundaryAttr.hasTag env decl

def isNearPrivate (env : Environment) (decl : Name) : Bool :=
  pfNearPrivateAttr.hasTag env decl

def isNearPayable (env : Environment) (decl : Name) : Bool :=
  pfNearPayableAttr.hasTag env decl

def isNearNoArgs (env : Environment) (decl : Name) : Bool :=
  pfNearNoArgsAttr.hasTag env decl

def isNearVoid (env : Environment) (decl : Name) : Bool :=
  pfNearVoidAttr.hasTag env decl

def isNearPromiseOrValue (env : Environment) (decl : Name) : Bool :=
  pfNearPromiseOrValueAttr.hasTag env decl

def nearMigrationDigest? (env : Environment) (decl : Name) : Option Nat :=
  pfNearMigrateAttr.getParam? env decl

/-- Opaque source metadata. Only the NEAR target may decode these strings. -/
def nearEntryAnnotations (env : Environment) (decl : Name) : Array String := Id.run do
  let mut annotations := #[]
  if isNearPrivate env decl then
    annotations := annotations.push "near.private.v1"
  if isNearPayable env decl then
    annotations := annotations.push "near.payable.v1"
  if isNearNoArgs env decl then
    annotations := annotations.push "near.no-args-ignore-input.v1"
  if isNearVoid env decl then
    annotations := annotations.push "near.void.v1"
  if isNearPromiseOrValue env decl then
    annotations := annotations.push "near.promise-or-value-u128.v1"
  if let some digest := nearMigrationDigest? env decl then
    annotations := annotations.push s!"near.migrate.v1:{digest}"
  return annotations

/-- 当前环境里、恰好挂在 `ns` 下的入口（不含子名字空间）。 -/
def entriesIn (env : Environment) (ns : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if n.getPrefix == ns && isEntry env n then acc.push n else acc

end ProofForge.Attr
