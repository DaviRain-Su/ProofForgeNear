import Lean
import ProofForge.Extract.Ops
import ProofForge.Profile
import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Core.Except
import ProofForge.Wasm.Near.Runtime
import ProofForge.Wasm.Near.Sdk.Promise
import ProofForge.Wasm.Near.Sdk.Store.AccountTokenLookup
import ProofForge.Wasm.Near.Sdk.Transient
import ProofForge.Wasm.Near.Sdk.Storage
import ProofForge.Extract.Lexical

open Lean

namespace ProofForge.Extract

/-- Recognize std `Except` and `Core.Except` result constructors interchangeably. -/
private def isExceptOkHead (e : Expr) : Bool :=
  isConstNamed e ``Except.ok || isConstNamed e ``ProofForge.Core.Except.ok

private def isExceptErrorHead (e : Expr) : Bool :=
  isConstNamed e ``Except.error || isConstNamed e ``ProofForge.Core.Except.err

/-- NEAR Runtime host reads. Matched by const name before any empty-arg UInt64
unfold that would bake the irreducible stub body `0` into a literal. -/
private def nearRuntimeLeaf? (e : Expr) : Option Ops.Val :=
  if isConstNamed e ``ProofForge.Wasm.Near.Runtime.blockIndex then
    some Ops.Val.nearBlockIndex
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.blockTimestamp then
    some Ops.Val.nearBlockTimestamp
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageUsage then
    some Ops.Val.nearStorageUsage
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessor then
    some Ops.Val.nearPredecessor
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorLen then
    some Ops.Val.nearPredecessorLen
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorW1 then
    some Ops.Val.nearPredecessorW1
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorW2 then
    some Ops.Val.nearPredecessorW2
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorW3 then
    some Ops.Val.nearPredecessorW3
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorW4 then
    some Ops.Val.nearPredecessorW4
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorW5 then
    some Ops.Val.nearPredecessorW5
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorW6 then
    some Ops.Val.nearPredecessorW6
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorW7 then
    some Ops.Val.nearPredecessorW7
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.attachedDeposit then
    some Ops.Val.nearAttachedDeposit
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.attachedDepositW0 then
    some Ops.Val.nearAttachedDepositW0
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.attachedDepositW1 then
    some Ops.Val.nearAttachedDepositW1
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.accountBalance then
    some Ops.Val.nearAccountBalance
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.accountBalanceW0 then
    some Ops.Val.nearAccountBalanceW0
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.accountBalanceW1 then
    some Ops.Val.nearAccountBalanceW1
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountId then
    some Ops.Val.nearCurrentAccountId
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdLen then
    some Ops.Val.nearCurrentAccountIdLen
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdW1 then
    some Ops.Val.nearCurrentAccountIdW1
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdW2 then
    some Ops.Val.nearCurrentAccountIdW2
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdW3 then
    some Ops.Val.nearCurrentAccountIdW3
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdW4 then
    some Ops.Val.nearCurrentAccountIdW4
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdW5 then
    some Ops.Val.nearCurrentAccountIdW5
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdW6 then
    some Ops.Val.nearCurrentAccountIdW6
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdW7 then
    some Ops.Val.nearCurrentAccountIdW7
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.epochHeight then
    some Ops.Val.nearEpochHeight
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.prepaidGas then
    some Ops.Val.nearPrepaidGas
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.usedGas then
    some Ops.Val.nearUsedGas
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.accountLockedBalance then
    some Ops.Val.nearAccountLockedBalance
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.accountLockedBalanceW0 then
    some Ops.Val.nearAccountLockedBalanceW0
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.accountLockedBalanceW1 then
    some Ops.Val.nearAccountLockedBalanceW1
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.signer then
    some Ops.Val.nearSigner
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.signerLen then
    some Ops.Val.nearSignerLen
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.signerW1 then
    some Ops.Val.nearSignerW1
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.signerW2 then
    some Ops.Val.nearSignerW2
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.signerW3 then
    some Ops.Val.nearSignerW3
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.signerW4 then
    some Ops.Val.nearSignerW4
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.signerW5 then
    some Ops.Val.nearSignerW5
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.signerW6 then
    some Ops.Val.nearSignerW6
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.signerW7 then
    some Ops.Val.nearSignerW7
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.signerPk then
    some Ops.Val.nearSignerPk
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.signerPkW1 then
    some Ops.Val.nearSignerPkW1
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.signerPkW2 then
    some Ops.Val.nearSignerPkW2
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.signerPkW3 then
    some Ops.Val.nearSignerPkW3
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.signerPkW4 then
    some Ops.Val.nearSignerPkW4
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.randomSeed then
    some Ops.Val.nearRandomSeed
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.randomSeedW1 then
    some Ops.Val.nearRandomSeedW1
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.randomSeedW2 then
    some Ops.Val.nearRandomSeedW2
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.randomSeedW3 then
    some Ops.Val.nearRandomSeedW3
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultsCount then
    some Ops.Val.nearPromiseResultsCount
  else none

set_option maxRecDepth 2048 in
mutual
private partial def asVal (env : Environment) (fuel : Nat) (e : Expr) : Option Ops.Val :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    match e with
    | .letE _ _ value body _ => asVal env fuel' (body.instantiate1 value)
    | .bvar i => some (.arg i)
    | _ =>
      if let some reduced := reduceCtorProjection? env e then
        asVal env fuel' reduced
      else if let some reduced := reducePureInlineMatch? env e then
        asVal env fuel' reduced
      else if let some reduced := reduceInlineProjection? env e then
        asVal env fuel' reduced
      else if let some reduced := reduceUInt64NewtypeMatch? env e then
        asVal env fuel' reduced
      else if let some v := asLit fuel' e then some v
      else if let some payload := uint64NewtypeCtorPayload? env e then
        asVal env fuel' payload
      else if isConstNamed e ``localRef && e.getAppArgs.size ≥ 1 then
        match asLit fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
        | some (.lit i) => some (.local i.toNat)
        | _ => none
      else if isConstNamed e ``methodArgRef && e.getAppArgs.size ≥ 1 then
        match asLit fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
        | some (.lit i) => some (.local (methodArgLocalBase + i.toNat))
        | _ => none
      else if isConstNamed e ``ite && e.getAppArgs.size ≥ 4 then
        let args := e.getAppArgs
        let rawCond := strip args[args.size - 4]!
        let (cond, negate) :=
          if isConstNamed rawCond ``Not && rawCond.getAppArgs.size ≥ 1 then
            (strip rawCond.getAppArgs[rawCond.getAppArgs.size - 1]!, true)
          else
            (rawCond, false)
        let cmp? : Option Ops.Cmp :=
          if isConstNamed cond ``Eq || isConstNamed cond ``BEq.beq then some .eq
          else if isConstNamed cond ``Ne then some .ne
          else if isConstNamed cond ``LT.lt then some .lt
          else if isConstNamed cond ``LE.le then some .le
          else if isConstNamed cond ``GT.gt then some .gt
          else if isConstNamed cond ``GE.ge || endsWith cond ".ge" || endsWith cond ".hGe" then
            some .ge
          else none
        let invert : Ops.Cmp → Option Ops.Cmp
          | .eq => some .ne | .ne => some .eq
          | .lt => some .ge | .le => some .gt
          | .gt => some .le | .ge => some .lt
        let condArgs := cond.getAppArgs
        match cmp? with
        | some cmp =>
          if h : condArgs.size ≥ 2 then
            let lhs := condArgs[condArgs.size - 2]
            let rhs := condArgs[condArgs.size - 1]
            let cmp? := if negate then invert cmp else some cmp
            match cmp?, asVal env fuel' lhs, asVal env fuel' rhs,
                asVal env fuel' args[args.size - 2]!, asVal env fuel' args[args.size - 1]! with
            | some cmp, some lv, some rv, some thn, some els =>
                some (.select cmp lv rv thn els)
            | _, _, _, _, _ => none
          else none
        | none =>
          match asVal env fuel' rawCond,
              asVal env fuel' args[args.size - 2]!, asVal env fuel' args[args.size - 1]! with
          | some cond, some thn, some els => some (.select .ne cond (.lit 0) thn els)
          | _, _, _ => none
      else
        match e.getAppFn.constName? with
        | some n => asValNamed env fuel' n e
        | none => none

/-- The `constName` dispatch arm of `asVal`, extracted so the recursive value decoder
stays navigable. `fuel` here is the caller's already-decremented budget. -/
private partial def asValNamed (env : Environment) (fuel : Nat) (n : Name) (e : Expr) :
    Option Ops.Val :=
  let field := n.toString
  let user := isUserName env n || isBoundaryProjectionName env n
  if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenMulU64Ok ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenMulU64W0 ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenMulU64W1) &&
      e.getAppArgs.size ≥ 3 then
    let args := e.getAppArgs
    match asVal env fuel args[args.size - 3]!, asVal env fuel args[args.size - 2]!,
        asVal env fuel args[args.size - 1]! with
    | some valueLo, some valueHi, some factor =>
        if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenMulU64Ok then
          some (.nearTokenMulU64Ok valueLo valueHi factor)
        else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenMulU64W0 then
          some (.nearTokenMulU64W0 valueLo valueHi factor)
        else
          some (.nearTokenMulU64W1 valueLo valueHi factor)
    | _, _, _ => none
  else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenAddOk ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenAddW0 ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenAddW1 ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenSubOk ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenSubW0 ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenSubW1) &&
      e.getAppArgs.size ≥ 4 then
    let args := e.getAppArgs
    match asVal env fuel args[args.size - 4]!, asVal env fuel args[args.size - 3]!,
        asVal env fuel args[args.size - 2]!, asVal env fuel args[args.size - 1]! with
    | some leftLo, some leftHi, some rightLo, some rightHi =>
        if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenAddOk then
          some (.nearTokenAddOk leftLo leftHi rightLo rightHi)
        else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenAddW0 then
          some (.nearTokenAddW0 leftLo leftHi rightLo rightHi)
        else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenAddW1 then
          some (.nearTokenAddW1 leftLo leftHi rightLo rightHi)
        else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenSubOk then
          some (.nearTokenSubOk leftLo leftHi rightLo rightHi)
        else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nearTokenSubW0 then
          some (.nearTokenSubW0 leftLo leftHi rightLo rightHi)
        else
          some (.nearTokenSubW1 leftLo leftHi rightLo rightHi)
    | _, _, _, _ => none
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.transientBuffer64Get &&
      e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    let capacityExpr := unfoldUserHelpers env 8 args[args.size - 2]!
    match asStaticLit env fuel capacityExpr, asVal env fuel args[args.size - 1]! with
    | some (.lit capacity), some index =>
        if ProofForge.Wasm.Near.Memory.buffer64CapacityValid capacity.toNat then
          some (.nearTransientBuffer64Get capacity.toNat index)
        else none
    | _, _ => none
  else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageResultStatus ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageResultLength ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageResultFits) &&
      e.getAppArgs.size ≥ 1 then
    let args := e.getAppArgs
    let capacityExpr := unfoldUserHelpers env 8 args[args.size - 1]!
    match asStaticLit env fuel capacityExpr with
    | some (.lit capacity) =>
        let capacity := capacity.toNat
        if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
          if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageResultStatus then
            some (.nearStorageResultStatus capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageResultLength then
            some (.nearStorageResultLength capacity)
          else
            some (.nearStorageResultFits capacity)
        else none
    | _ => none
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageResultByte &&
      e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    let capacityExpr := unfoldUserHelpers env 8 args[args.size - 2]!
    match asStaticLit env fuel capacityExpr, asVal env fuel args[args.size - 1]! with
    | some (.lit capacity), some index =>
        let capacity := capacity.toNat
        if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
          some (.nearStorageResultByte capacity index)
        else none
    | _, _ => none
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageResultNearTokenW0Strict then
    some .nearStorageResultNearTokenW0Strict
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageResultNearTokenW1Strict then
    some .nearStorageResultNearTokenW1Strict
  else if e.getAppArgs.size ≥ 1 &&
      (isConstNamed e ``ProofForge.Wasm.Near.Runtime.sha256ResultW0 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.sha256ResultW1 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.sha256ResultW2 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.sha256ResultW3 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak256ResultW0 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak256ResultW1 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak256ResultW2 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak256ResultW3 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW0 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW1 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW2 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW3 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW4 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW5 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW6 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW7 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.ripemd160ResultW0 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.ripemd160ResultW1 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.ripemd160ResultW2 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverStatus ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW0 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW1 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW2 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW3 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW4 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW5 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW6 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW7 ||
        isConstNamed e ``ProofForge.Wasm.Near.Runtime.ed25519VerifyOk) then
    let args := e.getAppArgs
    let capacityExpr := unfoldUserHelpers env 8 args[args.size - 1]!
    match asStaticLit env fuel capacityExpr with
    | some (.lit capacity) =>
        let capacity := capacity.toNat
        if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
          if isConstNamed e ``ProofForge.Wasm.Near.Runtime.sha256ResultW0 then
            some (.nearSha256ResultW0 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.sha256ResultW1 then
            some (.nearSha256ResultW1 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.sha256ResultW2 then
            some (.nearSha256ResultW2 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.sha256ResultW3 then
            some (.nearSha256ResultW3 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak256ResultW0 then
            some (.nearKeccak256ResultW0 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak256ResultW1 then
            some (.nearKeccak256ResultW1 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak256ResultW2 then
            some (.nearKeccak256ResultW2 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak256ResultW3 then
            some (.nearKeccak256ResultW3 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW0 then
            some (.nearKeccak512ResultW0 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW1 then
            some (.nearKeccak512ResultW1 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW2 then
            some (.nearKeccak512ResultW2 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW3 then
            some (.nearKeccak512ResultW3 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW4 then
            some (.nearKeccak512ResultW4 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW5 then
            some (.nearKeccak512ResultW5 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW6 then
            some (.nearKeccak512ResultW6 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512ResultW7 then
            some (.nearKeccak512ResultW7 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.ripemd160ResultW0 then
            some (.nearRipemd160ResultW0 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.ripemd160ResultW1 then
            some (.nearRipemd160ResultW1 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.ripemd160ResultW2 then
            some (.nearRipemd160ResultW2 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverStatus then
            some (.nearEcrecoverStatus capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW0 then
            some (.nearEcrecoverResultW0 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW1 then
            some (.nearEcrecoverResultW1 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW2 then
            some (.nearEcrecoverResultW2 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW3 then
            some (.nearEcrecoverResultW3 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW4 then
            some (.nearEcrecoverResultW4 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW5 then
            some (.nearEcrecoverResultW5 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW6 then
            some (.nearEcrecoverResultW6 capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecoverResultW7 then
            some (.nearEcrecoverResultW7 capacity)
          else
            some (.nearEd25519VerifyOk capacity)
        else none
    | _ => none
  else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultStatus ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultLength ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultFits) &&
      e.getAppArgs.size ≥ 1 then
    let args := e.getAppArgs
    let capacityExpr := unfoldUserHelpers env 8 args[args.size - 1]!
    match asStaticLit env fuel capacityExpr with
    | some (.lit capacity) =>
        let capacity := capacity.toNat
        if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
          if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultStatus then
            some (.nearPromiseResultStatus capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultLength then
            some (.nearPromiseResultLength capacity)
          else
            some (.nearPromiseResultFits capacity)
        else none
    | _ => none
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultByte &&
      e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    let capacityExpr := unfoldUserHelpers env 8 args[args.size - 2]!
    match asStaticLit env fuel capacityExpr, asVal env fuel args[args.size - 1]! with
    | some (.lit capacity), some index =>
        let capacity := capacity.toNat
        if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
          some (.nearPromiseResultByte capacity index)
        else none
    | _, _ => none
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultBorshUInt64D &&
      e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    let capacityExpr := unfoldUserHelpers env 8 args[args.size - 2]!
    match asStaticLit env fuel capacityExpr, asVal env fuel args[args.size - 1]! with
    | some (.lit capacity), some fallback =>
        let capacity := capacity.toNat
        if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
          some (.nearPromiseResultBorshUInt64D capacity fallback)
        else none
    | _, _ => none
  else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultQuotedU128Valid ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultQuotedU128W0 ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultQuotedU128W1) &&
      e.getAppArgs.size ≥ 1 then
    let args := e.getAppArgs
    let capacityExpr := unfoldUserHelpers env 8 args[args.size - 1]!
    match asStaticLit env fuel capacityExpr with
    | some (.lit capacity) =>
        let capacity := capacity.toNat
        if capacity == 41 then
          if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultQuotedU128Valid then
            some (.nearPromiseResultQuotedU128Valid capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultQuotedU128W0 then
            some (.nearPromiseResultQuotedU128W0 capacity)
          else
            some (.nearPromiseResultQuotedU128W1 capacity)
        else none
    | _ => none
  else if let some leaf := nearRuntimeLeaf? e then
    some leaf
  else if (isConstNamed e ``Eq || isConstNamed e ``BEq.beq || isConstNamed e ``Ne ||
      isConstNamed e ``bne ||
      isConstNamed e ``LT.lt || isConstNamed e ``LE.le || isConstNamed e ``GT.gt ||
      isConstNamed e ``GE.ge || endsWith e ".ge" || endsWith e ".hGe") &&
      e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    let cmp : Ops.Cmp :=
      if isConstNamed e ``Eq || isConstNamed e ``BEq.beq then .eq
      else if isConstNamed e ``Ne || isConstNamed e ``bne then .ne
      else if isConstNamed e ``LT.lt then .lt
      else if isConstNamed e ``LE.le then .le
      else if isConstNamed e ``GT.gt then .gt
      else .ge
    let lhsE := args[args.size - 2]!
    let rhsE := args[args.size - 1]!
    match asVal env fuel lhsE, asVal env fuel rhsE with
    | some lhs, some rhs => some (.select cmp lhs rhs (.lit 1) (.lit 0))
    | _, _ => none
  else if isConstNamed e ``Bool.or && e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    match asVal env fuel args[args.size - 2]!,
        asVal env fuel args[args.size - 1]! with
    | some lhs, some rhs => some (.bitOr lhs rhs)
    | _, _ => none
  else if isConstNamed e ``Bool.and && e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    match asVal env fuel args[args.size - 2]!,
        asVal env fuel args[args.size - 1]! with
    | some lhs, some rhs => some (.bitAnd lhs rhs)
    | _, _ => none
  else if isConstNamed e ``Bool.not && e.getAppArgs.size ≥ 1 then
    (asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]!).map fun value =>
      .select .eq value (.lit 0) (.lit 1) (.lit 0)
  else if (isConstNamed e ``Prod.fst || isConstNamed e ``Prod.snd) &&
      e.getAppArgs.size ≥ 1 then
    let leaf := if isConstNamed e ``Prod.fst then "fst" else "snd"
    (asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]!).map (flattenField · leaf)
  else if isConstNamed e ``Decidable.decide && e.getAppArgs.size ≥ 2 then
    asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!
  else if let some (_, unfolded) := unfoldUserHelper env e then
    match env.find? n with
    | some (.defnInfo info) =>
      if isScalarResult env info.type || isUInt256Type (resultType 16 info.type) ||
          isBytes32Type (resultType 16 info.type) then
        asVal env fuel unfolded
      else none
    | _ => none
  else if let some leaf := uint256ProjLeaf n then
    let args := e.getAppArgs
    if args.isEmpty then none
    else
      let rawBase := args[args.size - 1]!
      let baseE := unfoldUserHelpers env 8 rawBase
      let limbConst : String → Name
        | "w0" => ``ProofForge.Core.Value.UInt256.w0
        | "w1" => ``ProofForge.Core.Value.UInt256.w1
        | "w2" => ``ProofForge.Core.Value.UInt256.w2
        | _ => ``ProofForge.Core.Value.UInt256.w3
      if isConstNamed baseE ``ProofForge.Wasm.Near.Runtime.attachedDeposit128 then
        if leaf == "w0" then some Ops.Val.nearAttachedDepositW0
        else if leaf == "w1" then some Ops.Val.nearAttachedDepositW1
        else none
      else if isConstNamed baseE ``ProofForge.Wasm.Near.Runtime.accountBalance128 then
        if leaf == "w0" then some Ops.Val.nearAccountBalanceW0
        else if leaf == "w1" then some Ops.Val.nearAccountBalanceW1
        else none
      else if isConstNamed baseE ``ProofForge.Wasm.Near.Runtime.accountLockedBalance128 then
        if leaf == "w0" then some Ops.Val.nearAccountLockedBalanceW0
        else if leaf == "w1" then some Ops.Val.nearAccountLockedBalanceW1
        else none
      else
        let projected := mkApp (mkConst (limbConst leaf)) baseE
        match reduceCtorProjection? env projected with
        | some reduced => asVal env fuel reduced
        | none =>
          match asVal env fuel baseE with
          | some b => some (flattenField b leaf)
          | none =>
            match strip baseE with
            | .bvar i => some (flattenField (.arg i) leaf)
            | _ => none
  else if let some leaf := nearAccountIdProjLeaf n then
    let args := e.getAppArgs
    if args.isEmpty then none
    else
      let baseE := unfoldUserHelpers env 8 args[args.size - 1]!
      if isConstNamed baseE ``ProofForge.Wasm.Near.Runtime.predecessorAccountId ||
          endsWith baseE ".predecessorAccountId" then
        some (match leaf with
          | "length" => .nearPredecessorLen
          | "w0" => .nearPredecessor
          | "w1" => .nearPredecessorW1 | "w2" => .nearPredecessorW2
          | "w3" => .nearPredecessorW3 | "w4" => .nearPredecessorW4
          | "w5" => .nearPredecessorW5 | "w6" => .nearPredecessorW6
          | _ => .nearPredecessorW7)
      else if isConstNamed baseE ``ProofForge.Wasm.Near.Runtime.selfAccountId ||
          endsWith baseE ".selfAccountId" then
        some (match leaf with
          | "length" => .nearCurrentAccountIdLen
          | "w0" => .nearCurrentAccountId
          | "w1" => .nearCurrentAccountIdW1 | "w2" => .nearCurrentAccountIdW2
          | "w3" => .nearCurrentAccountIdW3 | "w4" => .nearCurrentAccountIdW4
          | "w5" => .nearCurrentAccountIdW5 | "w6" => .nearCurrentAccountIdW6
          | _ => .nearCurrentAccountIdW7)
      else if isConstNamed baseE ``ProofForge.Wasm.Near.Runtime.signerAccountId ||
          endsWith baseE ".signerAccountId" then
        some (match leaf with
          | "length" => .nearSignerLen
          | "w0" => .nearSigner
          | "w1" => .nearSignerW1 | "w2" => .nearSignerW2
          | "w3" => .nearSignerW3 | "w4" => .nearSignerW4
          | "w5" => .nearSignerW5 | "w6" => .nearSignerW6
          | _ => .nearSignerW7)
      else
        match asVal env fuel baseE with
        | some b => some (flattenField b leaf)
        | none =>
          match strip baseE with
          | .bvar i => some (flattenField (.arg i) leaf)
          | _ => none
  else if user && field.contains "." && e.getAppArgs.size ≥ 1 then
    let proj :=
      match field.splitOn "." with
      | [] => field
      | parts => parts.getLast!
    if proj == "mk" || proj == "ok" || proj == "error" ||
        proj.startsWith "_proof" || proj == "rfl" then none
    else if match env.find? n with
        | some (.ctorInfo _) => true
        | some (.inductInfo _) => true
        | _ => false then none
    else
      -- 整个 Vector 投影本身不是叶。下标 / 元素字段再展开。
      let skipVector :=
        match env.find? n with
        | some info =>
          info.type.getUsedConstantsAsSet.toList.any (· == ``Vector)
        | none => false
      if skipVector then none
      else
        match asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
        | some b =>
          let leaf := if looksLikeOptionProj env n then s!"{proj}_tag" else proj
          -- `s.nodes[0]!.value`：基是 `nodes_0`，叶是 `value`。
          some (flattenField b leaf)
        | none =>
          match e.getAppArgs[e.getAppArgs.size - 1]! with
          | .bvar i =>
            let leaf := if looksLikeOptionProj env n then s!"{proj}_tag" else proj
            some (flattenField (.arg i) leaf)
          | _ => none
  else if (isConstNamed e ``UInt8.toUInt64 || isConstNamed e ``UInt64.toUInt8 ||
      isConstNamed e ``UInt16.toUInt64 || isConstNamed e ``UInt64.toUInt16 ||
      isConstNamed e ``UInt32.toUInt64 || isConstNamed e ``UInt64.toUInt32 ||
      isConstNamed e ``UInt64.toNat || isConstNamed e ``UInt64.ofNat) &&
      e.getAppArgs.size ≥ 1 then
    asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]!
    else if (isConstNamed e ``HAdd.hAdd || endsWith e ".hAdd") && e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.addU64 l r)
    | _, _ => none
    else if (isConstNamed e ``Nat.sub ||
        (isConstNamed e ``HSub.hSub && e.getAppArgs.size ≥ 3 &&
          isConstNamed e.getAppArgs[0]! ``Nat &&
          isConstNamed e.getAppArgs[1]! ``Nat &&
          isConstNamed e.getAppArgs[2]! ``Nat)) && e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.select .ge l r (.subU64 l r) (.lit 0))
    | _, _ => none
    else if (isConstNamed e ``HSub.hSub || endsWith e ".hSub") &&
        e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.subU64 l r)
    | _, _ => none
    else if (isConstNamed e ``HMul.hMul || endsWith e ".hMul") &&
        e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.mulU64 l r)
    | _, _ => none
    else if (isConstNamed e ``HDiv.hDiv || endsWith e ".hDiv" ||
        isConstNamed e ``UInt64.div) && e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.divU64 l r)
    | _, _ => none
    else if (isConstNamed e ``HMod.hMod || endsWith e ".hMod" ||
        isConstNamed e ``UInt64.mod) && e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.modU64 l r)
    | _, _ => none
    else if (isConstNamed e ``HAnd.hAnd || endsWith e ".hAnd") && e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.bitAnd l r)
    | _, _ => none
  else if (isConstNamed e ``HOr.hOr || endsWith e ".hOr") && e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.bitOr l r)
    | _, _ => none
  else if (isConstNamed e ``HXor.hXor || endsWith e ".hXor") && e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.bitXor l r)
    | _, _ => none
  else if (isConstNamed e ``Complement.complement || endsWith e ".complement") &&
      e.getAppArgs.size ≥ 1 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some v => some (.bitNot v)
    | none => none
  else if (isConstNamed e ``HShiftLeft.hShiftLeft || endsWith e ".hShiftLeft") &&
      e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.shiftL l r)
    | _, _ => none
  else if (isConstNamed e ``HShiftRight.hShiftRight || endsWith e ".hShiftRight") &&
      e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.shiftR l r)
    | _, _ => none
  else if (isConstNamed e ``Option.isSome || endsWith e ".isSome") && e.getAppArgs.size ≥ 1 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.field b n) =>
      if n.endsWith "_tag" then some (.field b n)
      else some (.field b s!"{n}_tag")
    | some b => some (.field b s!"slot_tag")
    | none => none
  else if let some leaf := nearRuntimeLeaf? e then
    some leaf
  else if isConstNamed e ``Bool.true || endsWith e ".true" then
    some (.lit 1)
  else if isConstNamed e ``Bool.false || endsWith e ".false" then
    some (.lit 0)
  else if user && e.getAppArgs.isEmpty then
    match e.getAppFn.constName? with
    | some ctor =>
      match env.find? ctor with
      | some (.ctorInfo c) =>
        match enumCtorIndex env c.induct ctor with
        | some i => some (.lit (UInt64.ofNat i))
        | none => none
      | _ => none
    | none => none
  else if isConstNamed e ``Option.none || endsWith e ".none" then
    some (.lit 0)
  else if (isConstNamed e ``Option.some || endsWith e ".some") && e.getAppArgs.size ≥ 1 then
    asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]!
  else if (isConstNamed e ``GetElem.getElem || isConstNamed e ``GetElem?.getElem! ||
      isConstNamed e ``Vector.get ||
      endsWith e ".getElem" || endsWith e ".getElem!" || endsWith e ".get") &&
      e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    -- Do not recursively search proof/type arguments for an index: their local binders
    -- are not source values. The collection/index positions are fixed by GetElem.
    let collIndex? : Option (Expr × Expr) :=
      if isConstNamed e ``GetElem.getElem || endsWith e ".getElem" then
        if h : args.size ≥ 3 then some (args[args.size - 3], args[args.size - 2])
        else none
      else if h : args.size ≥ 2 then
        some (args[args.size - 2], args[args.size - 1])
      else none
    let rec findState (fuel : Nat) (e : Expr) : Option Ops.Val :=
      match fuel with
      | 0 => none
      | fuel + 1 =>
        match strip e with
        | .bvar j => some (.arg j)
        | e =>
          if isConstNamed e ``methodArgRef && e.getAppArgs.size ≥ 1 then
            match asLit fuel e.getAppArgs[e.getAppArgs.size - 1]! with
            | some (.lit i) => some (.local (methodArgLocalBase + i.toNat))
            | _ => none
          else e.getAppArgs.findSome? (findState fuel)
    match collIndex?.bind fun pair => (asVal env fuel pair.2).map (pair.1, ·) with
    | some (collection, .lit n) =>
      let i := n.toNat
      let baseField :=
        match asVal env fuel collection with
        | some (.field _ fname) => some fname
        | _ => none
      match findState fuel collection, baseField with
      | some base, some fname =>
        let suf := s!"_{i}"
        let baseName :=
          if fname.endsWith suf then fname.dropEnd suf.length |>.copy else fname
        some (.field base s!"{baseName}_{i}")
      | some base, none =>
        match vectorBaseName env 8 collection with
        | some fname => some (.field base s!"{fname}_{i}")
        | none =>
            if isConstNamed collection ``methodArgRef then some (.field base s!"_{i}")
            else none
      | _, _ => none
    | some (collection, idx) =>
      let lits := args.filterMap (asLit fuel)
      let len :=
        if h : lits.size > 0 then
          match lits[0] with
          | .lit n => n.toNat
          | _ => 0
        else 0
      match findState fuel collection, vectorBaseName env 8 collection with
      | some base, some fname => some (.indexGet base fname idx len)
      | _, _ => none
    | none => none

  else if e.getAppArgs.isEmpty then
    match env.find? n with
    | some (.defnInfo info) =>
      if info.type.consumeMData.getAppFn.constName? == some ``UInt64 then
        match asVal env fuel info.value with
        | some value =>
            match staticUInt64? value with
            | some literal => some (.lit literal)
            | none => some value
        | none => none
      else none
    | _ => none
  else none
end
private def val (env : Environment) (e : Expr) : Option Ops.Val :=
  -- Bounded tree algorithms naturally compose several parent/child projections. Their elaborated
  -- `GetElem`/`toNat` wrappers are deeper than ordinary scalar expressions, but still finite.
  asVal env 32 e


/-- Decode a scalar binding through pure explicitly-inline facade layers before substituting it.
This preserves shared target reads without increasing the global value-decoder fuel or recognizing
the facade's namespace. -/
private partial def valNodeCount : Ops.Val → Nat
  | .arg _ | .local _ | .lit _ | .loopIx => 1
  | .field base _ | .bitNot base => 1 + valNodeCount base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs | .addU64 lhs rhs | .subU64 lhs rhs
  | .mulU64 lhs rhs | .divU64 lhs rhs | .modU64 lhs rhs =>
      1 + valNodeCount lhs + valNodeCount rhs
  | .indexGet base _ index _ _ => 1 + valNodeCount base + valNodeCount index
  | .select _ lhs rhs thn els =>
      1 + valNodeCount lhs + valNodeCount rhs + valNodeCount thn + valNodeCount els
  | .ext _ operands =>
      1 + operands.foldl (init := 0) fun total operand => total + valNodeCount operand

private partial def readsMutableNearResult : Ops.Val → Bool
  | .arg _ | .local _ | .lit _ | .loopIx => false
  | .field base _ | .bitNot base => readsMutableNearResult base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs | .addU64 lhs rhs | .subU64 lhs rhs
  | .mulU64 lhs rhs | .divU64 lhs rhs | .modU64 lhs rhs =>
      readsMutableNearResult lhs || readsMutableNearResult rhs
  | .indexGet base _ index _ _ =>
      readsMutableNearResult base || readsMutableNearResult index
  | .select _ lhs rhs thn els =>
      readsMutableNearResult lhs || readsMutableNearResult rhs ||
        readsMutableNearResult thn || readsMutableNearResult els
  | .ext (.near (.storageResultStatus _)) _
  | .ext (.near (.storageResultLength _)) _
  | .ext (.near (.storageResultFits _)) _
  | .ext (.near (.storageResultByte _)) _
  | .ext (.near (.promiseResultStatus _)) _
  | .ext (.near (.promiseResultLength _)) _
  | .ext (.near (.promiseResultFits _)) _
  | .ext (.near (.promiseResultByte _)) _
  | .ext (.near (.promiseResultBorshUInt64D _)) _
  | .ext (.near (.promiseResultQuotedU128Valid _)) _
  | .ext (.near (.promiseResultQuotedU128W0 _)) _
  | .ext (.near (.promiseResultQuotedU128W1 _)) _ => true
  | .ext _ operands => operands.any readsMutableNearResult

/-- Materialize scalar source values whose substitution would duplicate bounded control flow or
re-evaluate a target read after a later effect. -/
private def shouldMaterializeLocal (_type : Expr) (value : Ops.Val) : Bool :=
  match value with
  | .field .. | .indexGet .. | .select .. | .ext .. => true
  | value => readsMutableNearResult value || valNodeCount value ≥ 1024

private def localScalarValue? (env : Environment) (fuel : Nat) (value : Expr) : Option Ops.Val :=
  let rec go (fuel : Nat) (value : Expr) : Option Ops.Val :=
    let value := substLets 64 value
    asVal env 64 value <|>
      match fuel with
      | 0 => none
      | fuel' + 1 =>
        if let some reduced := reducePureInlineMatch? env value then
          go fuel' reduced
        else if let some (helper, unfolded) := unfoldUserHelper env value then
          if inlineHelperPreservesUserType env helper then none else go fuel' unfolded
        else
          none
  go fuel value

private def asUInt64VariantCtor (env : Environment) (e : Expr) :
    Option (UInt64 × Array Ops.Val × Nat) := do
  let ctorName ← e.getAppFn.constName?
  let .ctorInfo ctor ← env.find? ctorName | none
  let payloadWidth ← uint64VariantPayloadWidth? env ctor.induct
  let index ← enumCtorIndex env ctor.induct ctorName
  let args := e.getAppArgs
  if args.size < ctor.numFields then none else pure ()
  let mut payloads : Array Ops.Val := #[]
  for offset in [:ctor.numFields] do
    let payloadExpr ← args[args.size - ctor.numFields + offset]?
    let payload ← val env payloadExpr
    payloads := payloads.push payload
  return (UInt64.ofNat index, payloads, payloadWidth)

private def asSubFromMax (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``HSub.hSub then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match val env args[args.size - 2]! >>= staticUInt64? with
      | some max => if max == ~~~(0 : UInt64) then val env args[args.size - 1]! else none
      | none => none
    else none
  else none

/-- `x ≤ u64Max - y`  →  checked add x y。单独的 `x ≤ u64Max` 不是 add。 -/
private def asCheckedAddGuard (env : Environment) (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``LE.le then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match val env args[args.size - 2]!, asSubFromMax env args[args.size - 1]! with
      | some lhs, some rhs => some (lhs, rhs)
      | _, _ => none
    else none
  else none

private def asDivFromMax (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``HDiv.hDiv then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match val env args[args.size - 2]! >>= staticUInt64? with
      | some max => if max == ~~~(0 : UInt64) then val env args[args.size - 1]! else none
      | none => none
    else none
  else none

/-- `x ≤ u64Max / y`  →  checked mul x y -/
private def asCheckedMulGuard (env : Environment) (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``LE.le then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match val env args[args.size - 2]!, asDivFromMax env args[args.size - 1]! with
      | some lhs, some rhs => some (lhs, rhs)
      | _, _ => none
    else none
  else none

private def binArgs (e : Expr) : Option (Expr × Expr) :=
  let args := e.getAppArgs
  if args.size ≥ 2 then some (args[args.size - 2]!, args[args.size - 1]!) else none

private def asCmpCoreWithFuel (env : Environment) (fuel : Nat) (e : Expr) :
    Option (Ops.Cmp × Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``Eq || isConstNamed e ``BEq.beq then
    match binArgs e with
    | some (l, r) =>
      match asVal env fuel l, asVal env fuel r with
      | some lv, some rv => some (.eq, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``Ne || isConstNamed e ``bne then
    match binArgs e with
    | some (l, r) =>
      match asVal env fuel l, asVal env fuel r with
      | some lv, some rv => some (.ne, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``LT.lt then
    match binArgs e with
    | some (l, r) =>
      match asVal env fuel l, asVal env fuel r with
      | some lv, some rv => some (.lt, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``LE.le then
    match binArgs e with
    | some (l, r) =>
      match asVal env fuel l, asVal env fuel r with
      | some lv, some rv => some (.le, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``GT.gt then
    match binArgs e with
    | some (l, r) =>
      match asVal env fuel l, asVal env fuel r with
      | some lv, some rv => some (.gt, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``GE.ge || endsWith e ".ge" || endsWith e ".hGe" then
    match binArgs e with
    | some (l, r) =>
      match asVal env fuel l, asVal env fuel r with
      | some lv, some rv => some (.ge, lv, rv)
      | _, _ => none
    | none => none
  else none

private def asCmpCore (env : Environment) (e : Expr) : Option (Ops.Cmp × Ops.Val × Ops.Val) :=
  asCmpCoreWithFuel env 32 e

private def asCmp (env : Environment) (e : Expr) : Option (Ops.Cmp × Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``Not then
    let args := e.getAppArgs
    if args.size ≥ 1 then
      match asCmpCore env args[args.size - 1]! with
      | some (.eq, l, r) => some (.ne, l, r)
      | some (.ne, l, r) => some (.eq, l, r)
      | _ => none
    else none
  else
    match asCmpCore env e with
    | some t => some t
    | none =>
      if isConstNamed e ``Eq then
        match binArgs e with
        | some (l, r) =>
          let l := strip l
          let r := strip r
          let trueR := isConstNamed r ``Bool.true || endsWith r ".true"
          let noneR := isConstNamed r ``Option.none || endsWith r ".none"
          let noneL := isConstNamed l ``Option.none || endsWith l ".none"
          if trueR && (isConstNamed l ``Option.isSome || endsWith l ".isSome") then
            match val env l with
            | some (.field b n) =>
              let tag := if n.endsWith "_tag" then n else s!"{n}_tag"
              some (.ne, .field b tag, .lit 0)
            | some b => some (.ne, .field b "slot_tag", .lit 0)
            | none => some (.ne, .field (.arg 0) "slot_tag", .lit 0)
          else if noneR then
            match val env l with
            | some lv => some (.eq, lv, .lit 0)
            | none => none
          else if noneL then
            match val env r with
            | some rv => some (.eq, rv, .lit 0)
            | none => none
          else none
        | none => none
      else if isConstNamed e ``Option.isSome || endsWith e ".isSome" then
        let args := e.getAppArgs
        if args.size ≥ 1 then
          match val env args[args.size - 1]! with
          | some (.field b n) =>
            let tag := if n.endsWith "_tag" then n else s!"{n}_tag"
            some (.ne, .field b tag, .lit 0)
          | some b => some (.ne, .field b "slot_tag", .lit 0)
          | none => none
        else none
      else none

/-- Normalize pure Boolean syntax to a 0/1 value so compound guards do not duplicate branches. -/
private def asBoolVal (env : Environment) (fuel : Nat) (e : Expr) : Option Ops.Val :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    if let .letE _ _ value body _ := e then
      asBoolVal env fuel' (body.instantiate1 value)
    else
    let args := e.getAppArgs
    let last? := if h : args.size > 0 then some args[args.size - 1] else none
    if isConstNamed e ``Bool.true then some (.lit 1)
    else if isConstNamed e ``Bool.false then some (.lit 0)
    else if isConstNamed e ``Bool.or && args.size ≥ 2 then
      match asBoolVal env fuel' args[args.size - 2]!, asBoolVal env fuel' args[args.size - 1]! with
      | some lhs, some rhs => some (.bitOr lhs rhs)
      | _, _ => none
    else if isConstNamed e ``Bool.and && args.size ≥ 2 then
      match asBoolVal env fuel' args[args.size - 2]!, asBoolVal env fuel' args[args.size - 1]! with
      | some lhs, some rhs => some (.bitAnd lhs rhs)
      | _, _ => none
    else if isConstNamed e ``Bool.not then
      last?.bind fun value =>
        (asBoolVal env fuel' value).map fun v => .select .eq v (.lit 0) (.lit 1) (.lit 0)
    else if (isConstNamed e ``ite || isConstNamed e ``dite) && args.size ≥ 4 then
      let peelProofLam (value : Expr) : Expr :=
        match strip value with
        | .lam _ _ body _ => body.lowerLooseBVars 1 1
        | value => value
      match asBoolVal env fuel' args[args.size - 4]!,
          asBoolVal env fuel' (peelProofLam args[args.size - 2]!),
          asBoolVal env fuel' (peelProofLam args[args.size - 1]!) with
      | some cond, some thn, some els => some (.select .ne cond (.lit 0) thn els)
      | _, _, _ => none
    else if isConstNamed e ``Decidable.decide && args.size ≥ 2 then
      asBoolVal env fuel' args[args.size - 2]!
    else if isConstNamed e ``Eq && args.size ≥ 2 then
      let lhs := strip args[args.size - 2]!
      let rhs := strip args[args.size - 1]!
      if isConstNamed rhs ``Bool.true then asBoolVal env fuel' lhs
      else if isConstNamed lhs ``Bool.true then asBoolVal env fuel' rhs
      else if isConstNamed rhs ``Bool.false then
        (asBoolVal env fuel' lhs).map fun v => .select .eq v (.lit 0) (.lit 1) (.lit 0)
      else if isConstNamed lhs ``Bool.false then
        (asBoolVal env fuel' rhs).map fun v => .select .eq v (.lit 0) (.lit 1) (.lit 0)
      else
        (asCmp env e).map fun (cmp, lhs, rhs) => .select cmp lhs rhs (.lit 1) (.lit 0)
    else
      match asCmp env e with
      | some (cmp, lhs, rhs) => some (.select cmp lhs rhs (.lit 1) (.lit 0))
      | none =>
        match unfoldUserHelper env e with
        | some (_, unfolded) => asBoolVal env fuel' unfolded
        | none => none

private def asCondition (env : Environment) (e : Expr) : Option (Ops.Cmp × Ops.Val × Ops.Val) :=
  -- Bounded tree guards can contain several nested projected lookups. Keep ordinary value
  -- decoding conservative, but let an explicit control-flow boundary finish that finite tree.
  asCmp env e <|> asCmpCoreWithFuel env 128 e <|>
    (asBoolVal env 64 e).map fun value => (.ne, value, .lit 0)

/-- `x ≥ y` / `y ≤ x`  →  checked sub x y。`x ≤ lit` 是上界（255 / u64Max），不是 sub。 -/
private def asCheckedSubGuard (env : Environment) (e : Expr) : Option (Ops.Val × Ops.Val) :=
  match asCmp env e with
  | some (.le, _, .lit _) => none
  | some (.le, rhs, lhs) => some (lhs, rhs)
  | some (.ge, lhs, rhs) => some (lhs, rhs)
  | _ => none

/-- `den ≠ 0` 才是除法守卫。两边都是字面量的 `0 ≠ 1` 不算。 -/
private def asNeZero (env : Environment) (e : Expr) : Option Ops.Val :=
  match asCmp env e with
  | some (.ne, .lit _, .lit _) => none
  | some (.ne, v, .lit 0) => some v
  | some (.ne, .lit 0, v) => some v
  | _ => none

private def asEqZero (env : Environment) (e : Expr) : Option Ops.Val :=
  match asCmp env e with
  | some (.eq, v, .lit 0) => some v
  | some (.eq, .lit 0, v) => some v
  | _ => none

/-- 多字段 `State.mk a b …`：init 用第一个显式参数；checked 更新用最后一个。 -/
private def asStateMk (env : Environment) (e : Expr) (preferLast := false) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``Prod.mk || endsWith e ".Prod.mk" then none
  else if endsWith e ".State.mk" || endsWith e ".mk" then
    let args := e.getAppArgs
    if args.size = 0 then none
    else if preferLast then val env args[args.size - 1]!
    else
      match args.findSome? (val env) with
      | some v => some v
      | none => val env args[args.size - 1]!
  else none

private def asOptionPayload (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``Option.none || endsWith e ".none" then
    some (.lit 0)
  else if isConstNamed e ``Option.some || endsWith e ".some" then
    let args := e.getAppArgs
    if args.size ≥ 1 then val env args[args.size - 1]! else none
  else
    match e.getAppFn.constName? with
    | some ctor =>
      match env.find? ctor with
      | some (.ctorInfo c) =>
        if isOptionLikeInductive env c.induct || isEnumLeaf env c.induct then
          match enumCtorIndex env c.induct ctor with
          | some 0 => some (.lit 0)
          | some _ =>
            if c.numFields == 0 then some (.lit 1)
            else if e.getAppArgs.size ≥ 1 then val env e.getAppArgs[e.getAppArgs.size - 1]!
            else none
          | none => none
        else none
      | _ => none
    | none => none

/-- Preserve the constructor discriminant when an Option-like value becomes storage leaves. -/
private def asOptionStorage (env : Environment) (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``Option.none || endsWith e ".none" then
    some (.lit 0, .lit 0)
  else if isConstNamed e ``Option.some || endsWith e ".some" then
    let args := e.getAppArgs
    if args.size ≥ 1 then
      (val env args[args.size - 1]!).map fun payload => (.lit 1, payload)
    else none
  else
    match e.getAppFn.constName? with
    | some ctor =>
      match env.find? ctor with
      | some (.ctorInfo info) =>
        if isOptionLikeInductive env info.induct then
          match enumCtorIndex env info.induct ctor with
          | some 0 => some (.lit 0, .lit 0)
          | some _ =>
            if info.numFields == 0 then some (.lit 1, .lit 1)
            else if e.getAppArgs.size ≥ 1 then
              (val env e.getAppArgs[e.getAppArgs.size - 1]!).map fun payload =>
                (.lit 1, payload)
            else none
          | none => none
        else none
      | _ => none
    | none => none

/-- Unwrap only sequencing carriers around a returned Option. `peelControl` intentionally erases
`Option.some` for payload-oriented consumers, so fixed result framing must inspect it first. -/
private def asConstructedOptionResult (env : Environment) : Nat → Expr →
    Option (Ops.Val × Ops.Val)
  | 0, e => asOptionStorage env e
  | fuel' + 1, e =>
      let e := peelLets (strip e)
      if (isConstNamed e ``Pure.pure || endsWith e ".pure" ||
          isConstNamed e ``ForInStep.done || endsWith e ".done") &&
          e.getAppArgs.size ≥ 1 then
        asConstructedOptionResult env fuel' e.getAppArgs[e.getAppArgs.size - 1]!
      else
        asOptionStorage env e

/-- Flatten one `#v[…]` / `List.cons` element into ABI leaves. Static `Prod.mk` trees become
ordered scalar limbs so a constructed `BoundedVec (α × β) n` publishes the same
`length ‖ leaf₀ ‖ …` frame codecs already pack for `(α,β)[]`. -/
private partial def flattenListElementVals (env : Environment) (fuel : Nat) (e : Expr) :
    Array Ops.Val :=
  match fuel with
  | 0 => #[]
  | fuel' + 1 =>
    let e := strip e
    if isConstNamed e ``Prod.mk && e.getAppArgs.size ≥ 2 then
      let args := e.getAppArgs
      flattenListElementVals env fuel' args[args.size - 2]! ++
        flattenListElementVals env fuel' args[args.size - 1]!
    else
      match val env e with
      | some v => #[v]
      | none => #[]

/-- `#v[a, b, …]` = `Vector.mk (List.toArray (a :: b :: []))`。 -/
private def collectListVals (env : Environment) (fuel : Nat) (e : Expr) : Array Ops.Val :=
  match fuel with
  | 0 => #[]
  | fuel' + 1 =>
    let e := strip e
    if isConstNamed e ``List.nil || endsWith e ".nil" then
      #[]
    else if isConstNamed e ``List.cons || endsWith e ".cons" then
      let args := e.getAppArgs
      if args.size ≥ 2 then
        let head := args[args.size - 2]!
        let tail := args[args.size - 1]!
        let headVals := flattenListElementVals env 8 head
        if headVals.isEmpty then collectListVals env fuel' tail
        else headVals ++ collectListVals env fuel' tail
      else #[]
    else if isConstNamed e ``List.toArray || endsWith e ".toArray" then
      let args := e.getAppArgs
      if args.size ≥ 1 then collectListVals env fuel' args[args.size - 1]! else #[]
    else
      flattenListElementVals env 8 e

private def findListVals (env : Environment) (fuel : Nat) (e : Expr) : Option (Array Ops.Val) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    if isConstNamed e ``List.cons || endsWith e ".cons" then
      -- Recognition may traverse the largest internal raw-storage key literal. Acceptance remains
      -- owned by each consumer's capacity predicate after this syntax-only flattening step.
      some (collectListVals env 80 e)
    else
      e.getAppArgs.findSome? (findListVals env fuel')

private def asVectorLits (env : Environment) (e : Expr) : Option (Array Ops.Val) :=
  let e := strip e
  if isConstNamed e ``Vector.mk || endsWith e "Vector.mk" then
    match findListVals env 16 e with
    | some vs => if vs.isEmpty then none else some vs
    | none => none
  else none

/-- A constructed bounded boundary value already has the target-neutral fixed frame expected by
the codec adapters: one length followed by every compile-time-capacity slot. Keep this recognition
separate from ordinary user structures because these compiler-owned polymorphic carriers are not
persistent state and their capacity parameter is erased after extraction. -/
private def asBoundedCtorFields (env : Environment) (e : Expr) : Option (Array Ops.Val) := do
  let e := substLets 32 (strip e)
  let ctor ← e.getAppFn.constName?
  let .ctorInfo info ← env.find? ctor | none
  unless info.induct == boundedVecName || info.induct == boundedBytesName ||
      info.induct == boundedStringName do none
  let args := e.getAppArgs
  unless args.size ≥ 2 do none
  let length ← val env args[args.size - 2]!
  let values ← asVectorLits env args[args.size - 1]!
  return #[length] ++ values

/-- Compiler-owned fixed-width scalar constructors are boundary values, not persistent State.
Expose their ordered limbs directly so target codecs see the same frame as projected wide values. -/
private def asWideCtorFields (env : Environment) (e : Expr) : Option (Array Ops.Val) := do
  let e := substLets 32 (strip e)
  let ctor ← e.getAppFn.constName?
  let .ctorInfo info ← env.find? ctor | none
  unless info.induct == uint128Name ||
      info.induct == uint256Name || info.induct == fixedBytesName do none
  let args := e.getAppArgs
  unless info.numFields ≤ args.size do none
  let fields := args.extract (args.size - info.numFields) args.size
  let values ← fields.mapM (val env)
  unless values.size == info.numFields do none
  return values

/-- A reusable compiler-owned `@[pf_boundary]` value is source data, not persistent State.
Unfold only explicitly bounded helpers to its constructor and expose every scalar field through
the ordinary fixed return frame. Schema validation and target codecs still decide whether that
frame is admissible and how it is serialized. -/
private def asRegisteredBoundaryCtorFields (env : Environment) (e : Expr) :
    Option (Array Ops.Val) := do
  let e := substLets 32 (strip (unfoldUserHelpers env 16 e))
  let ctor ← e.getAppFn.constName?
  let .ctorInfo info ← env.find? ctor | none
  unless Attr.isBoundary env info.induct do none
  let args := e.getAppArgs
  unless info.numFields ≤ args.size do none
  let fields := args.extract (args.size - info.numFields) args.size
  let mut values : Array Ops.Val := #[]
  for field in fields do
    -- Boundary records may contain an exact compiler-owned wide scalar. Preserve every ordered
    -- limb instead of letting generic `val` turn the nested constructor into a field projection
    -- rooted at persistent State (for example `total_w0`).
    match asWideCtorFields env field with
    | some limbs => values := values ++ limbs
    | none =>
        let value ← val env field
        values := values.push value
  return values

/-- `xs.set i v`：只抽出被改的那一叶。 -/
private def asVectorSet (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isVectorSet e then
    let args := e.getAppArgs
    -- 只认编译期常量下标。运行时下标走 `asIndexSet`。
    -- `Vector.set.{u} α n xs i v h` 里 `n` 是长度，不能当 index。
    let idx? : Option Nat :=
      Id.run do
        let mut seenLen := false
        for a in args do
          match asLit 8 a with
          | some (.lit n) =>
            if !seenLen then
              seenLen := true
            else
              return some n.toNat
          | _ => pure ()
        return none
    -- `Vector.set xs i v h`：值在字面量下标之后。
    -- 嵌套 `Node.mk` 时取被改的那一叶（preferLast）。
    let payload :=
      Id.run do
        let mut seenIdx := false
        for a in args do
          match asLit 8 a with
          | some (.lit _) =>
            seenIdx := true
          | _ =>
            if seenIdx then
              -- `{ s.nodes[0]! with value := v }` 展开成 `have __src := …; Node.mk …`。
              let a := peelLets (strip a)
              match asStateMk env a true with
              | some v => return some (true, v)
              | none =>
                match val env a with
                | some v => return some (false, v)
                | none => pure ()
        return none
    match idx?, payload, vectorBaseName env 16 e with
    | some i, some (true, v), some n => some (.field v s!"{n}_{i}_value")
    | some i, some (false, v), some n => some (.field v s!"{n}_{i}")
    | _, _, _ => none
  else none

/-- `State.mk` 每个字段一个值。`Option` 展开成 tag + payload；`Vector` 展开成各叶。 -/
private def asIndexSets (env : Environment) (e0 : Expr) : Option (Array Ops.Op) :=
  let rec go (fuel : Nat) (e : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      match e with
      | .letE _ _ value body _ => go fuel' value <|> go fuel' body
      | .lam _ _ body _ => go fuel' body
      | _ =>
        if isExceptOkHead e && e.getAppArgs.size ≥ 1 then
          go fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else if isConstNamed e ``Prod.mk && e.getAppArgs.size ≥ 2 then
          go fuel' e.getAppArgs[e.getAppArgs.size - 2]!
        else if isVectorSet e then
          some e
        else
          e.getAppArgs.findSome? (go fuel')
  match go 8 e0 with
  | none => none
  | some e =>
  if isVectorSet e then
    let args := e.getAppArgs
    let lits := args.filterMap (asLit 8)
    let len :=
      if h : lits.size > 0 then
        match lits[0] with
        | .lit n => n.toNat
        | _ => 0
      else 0
    -- `Vector.set α n xs i v h`：最后四项固定为 xs、下标、新元素、证明。
    -- 不要扫描证明参数；其中的局部 binder 不是源程序的动态下标。
    let parsed :=
      Id.run do
        if h : args.size ≥ 4 then
          let idx? := val env args[args.size - 3]
          let payload := substLets 8 (peelLets (strip args[args.size - 2]))
          let isCtor :=
            match payload.getAppFn.constName? with
            | some n =>
              match env.find? n with
              | some (.ctorInfo _) => true
              | _ => false
            | none => false
          if isCtor || isIteExpr payload then return (false, idx?, some payload, none)
          else return (false, idx?, none, val env payload)
        else
          return (false, none, none, none)
    let rec changedLeaves (selfIdx : Option Ops.Val) (fuel : Nat) (e : Expr) :
        Array (String × Ops.Val) :=
      match fuel with
      | 0 => #[]
      | fuel' + 1 =>
        let e := substLets 16 (strip e)
        match e.getAppFn.constName? with
        | some n =>
          match env.find? n with
          | some (.ctorInfo c) =>
            if isUserType env c.induct && isStructure env c.induct then
              let names := getStructureFields env c.induct
              let args := e.getAppArgs
              let nF := names.size
              if nF == 0 || args.size < nF then #[]
              else
                -- `{ src with left := a, parent := b }`：叶来自别的节点 / 别的字段就算改了。
                -- `y.parent := x.parent` 两边都叫 parent，不能只看字段名。
                Id.run do
                  let mut acc : Array (String × Ops.Val) := #[]
                  for i in [0:nF] do
                    if h : i < nF ∧ i < args.size then
                      let fname := names[i].toString
                      let arg := substLets 8 (strip args[args.size - nF + i])
                      let looksSame :=
                        match val env arg with
                        | some (.field (.arg _) n) =>
                          n == fname || n.endsWith ("_" ++ fname)
                        | some (.field (.indexGet _ _ i _ _) leaf) =>
                          -- 同一下标上的同一逻辑叶才算没改。
                          (leaf == fname || leaf.endsWith ("_" ++ fname)) &&
                            (match selfIdx with
                             | some j => i == j
                             | none => true)
                        | _ => false
                      unless looksSame do
                        match val env arg with
                        | some v => acc := acc.push (fname, v)
                        | none => pure ()
                  return acc
            else
              e.getAppArgs.foldl (init := #[]) fun a x =>
                a ++ changedLeaves selfIdx fuel' x
          | _ => e.getAppArgs.foldl (init := #[]) fun a x =>
              a ++ changedLeaves selfIdx fuel' x
        | none => e.getAppArgs.foldl (init := #[]) fun a x =>
            a ++ changedLeaves selfIdx fuel' x
    match parsed with
    | (true, _, _, _) => none
    | (false, some idx, some payloadE, _) =>
      match idx with
      | .lit _ => none
      | _ =>
        match vectorBaseName env 16 e with
        | none => none
        | some name =>
          let payloadOps (payload : Expr) : Array Ops.Op :=
            match asUInt64VariantCtor env payload with
            | some (tag, payloads, payloadWidth) => Id.run do
              let mut ops : Array Ops.Op := #[.indexSetLeaf name idx (.lit tag) len "tag"]
              for offset in [:payloadWidth] do
                ops := ops.push (.indexSetLeaf name idx
                  (payloads[offset]?.getD (.lit 0)) len s!"p{offset}")
              return ops
            | none =>
              let leaves := changedLeaves (some idx) 8 payload
              let leaves :=
                if leaves.isEmpty then
                  match val env payload with
                  | some v => #[("", v)]
                  | none => #[]
                else leaves
              leaves.map fun p => (.indexSetLeaf name idx p.2 len p.1 : Ops.Op)
          if isIteExpr payloadE then
            let args := payloadE.getAppArgs
            let peelProofLam (branch : Expr) : Expr :=
              match strip branch with
              | .lam _ _ body _ => substLets 16 (body.lowerLooseBVars 1 1)
              | branch => substLets 16 branch
            if args.size < 2 then none
            else
              match args.findSome? (asCondition env) with
              | none => none
              | some (cmp, lhs, rhs) =>
                let thn := payloadOps (peelProofLam args[args.size - 2]!)
                let els := payloadOps (peelProofLam args[args.size - 1]!)
                if thn.isEmpty && els.isEmpty then none else some #[.ite cmp lhs rhs thn els]
          else
            let ops := payloadOps payloadE
            if ops.isEmpty then none else some ops
    | (false, some idx, none, some payload) =>
      match idx with
      | .lit _ => none
      | _ =>
        match vectorBaseName env 16 e with
        | some name => some #[.indexSetLeaf name idx payload len]
        | none => none
    | _ => none
  else none

private def asIndexSet (env : Environment) (e0 : Expr) : Option Ops.Op :=
  match asIndexSets env e0 with
  | some ops => ops[0]?
  | none => none

def peelForalls (e : Expr) : Expr :=
  let rec go (fuel : Nat) (e : Expr) : Expr :=
    match fuel with
    | 0 => e
    | fuel' + 1 =>
      match strip e with
      | .forallE _ _ body _ => go fuel' body
      | e => e
  go 32 e

def fieldTypeExpr (env : Environment) (structName fieldName : Name) : Option Expr :=
  match getProjFnForField? env structName fieldName with
  | none => none
  | some proj =>
    match env.find? proj with
    | none => none
    | some info => some (peelForalls info.type)

private partial def collectListExprs (fuel : Nat) (e : Expr) : Option (Array Expr) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    if isConstNamed e ``List.nil || endsWith e ".nil" then
      some #[]
    else if isConstNamed e ``List.cons || endsWith e ".cons" then
      let args := e.getAppArgs
      if args.size < 2 then none
      else do
        let tail ← collectListExprs fuel' args[args.size - 1]!
        return #[args[args.size - 2]!] ++ tail
    else if isConstNamed e ``List.toArray || endsWith e ".toArray" then
      let args := e.getAppArgs
      if args.isEmpty then none else collectListExprs fuel' args[args.size - 1]!
    else
      e.getAppArgs.findSome? (collectListExprs fuel')

private def vectorElements (e : Expr) : Option (Array Expr) :=
  let e := strip e
  if isConstNamed e ``Vector.mk || endsWith e "Vector.mk" then
    collectListExprs 32 e
  else none

private def unfoldNullaryValue? (env : Environment) (e : Expr) : Option Expr :=
  let e := strip e
  if !e.getAppArgs.isEmpty then none
  else do
    let name ← e.getAppFn.constName?
    -- Keep `@[irreducible]` runtime leaves (predecessor/current account) as named constants.
    -- Unfolding them here would turn `nearPredecessor` into the host stub `0`.
    if Lean.getReducibilityStatusCore env name == .irreducible then none
    else
      let .defnInfo info ← env.find? name | none
      return info.value

/-- Explicit source fields of one user-defined structure constructor. -/
private def userCtorFields (env : Environment) (e : Expr) : Option (Array Expr) :=
  let e := peelLets (strip e)
  match e.getAppFn.constName? with
  | none => none
  | some n =>
    match env.find? n with
    | some (.ctorInfo c) =>
      if isUserType env c.induct && isStructure env c.induct then
        let args := e.getAppArgs
        if args.size ≥ c.numFields then
          some (args.extract (args.size - c.numFields) args.size)
        else none
      else none
    | _ => none

/-- Flatten an initializer from its source type, producing exactly one value per schema leaf. -/
private partial def flattenInitValue (env : Environment) (fuel : Nat) (ty e : Expr) :
    Option (Array Ops.Val) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := substLets 32 (strip e)
    match unfoldNullaryValue? env e with
    | some body => flattenInitValue env fuel' ty body
    | none =>
      let ty := strip ty
      let tyName? := ty.getAppFn.constName?
      if tyName? == some ``UInt64 || tyName? == some ``UInt32 ||
          tyName? == some ``UInt16 || tyName? == some ``UInt8 then
        (val env e).map (#[·])
      else if isUInt256Type ty || isUInt128Type ty || isBytes32Type ty then
        asWideCtorFields env e
      else if tyName? == some ``Bool then
        if isConstNamed e ``Bool.true || endsWith e ".true" then some #[.lit 1]
        else if isConstNamed e ``Bool.false || endsWith e ".false" then some #[.lit 0]
        else (val env e).map (#[·])
      else if tyName? == some ``Option then
        (asOptionStorage env e).map fun (tag, payload) => #[tag, payload]
      else if tyName? == some ``Vector then
        let tyArgs := ty.getAppArgs
        if tyArgs.size < 2 then none
        else
          match asLit 8 tyArgs[tyArgs.size - 1]!, vectorElements e with
          | some (.lit length), some elements =>
            if elements.size != length.toNat then none
            else Id.run do
              let mut values : Array Ops.Val := #[]
              for h : i in [:elements.size] do
                let some item := flattenInitValue env fuel' tyArgs[tyArgs.size - 2]! elements[i]
                  | return none
                values := values ++ item
              return some values
          | _, _ => none
      else if let some tyName := tyName? then
        if isEnumLeaf env tyName then
          match e.getAppFn.constName? with
          | some ctor => (enumCtorIndex env tyName ctor).map fun index => #[.lit (UInt64.ofNat index)]
          | none => none
        else if isUInt64Newtype env tyName then
          (val env e).map (#[·])
        else if isOptionLikeInductive env tyName then
          (asOptionStorage env e).map fun (tag, payload) => #[tag, payload]
        else if let some payloadWidth := uint64VariantPayloadWidth? env tyName then
          match asUInt64VariantCtor env e with
          | none => none
          | some (tag, payloads, _) =>
            Id.run do
              let mut values := #[.lit tag]
              for index in [:payloadWidth] do
                values := values.push (payloads[index]?.getD (.lit 0))
              return some values
        else if isUserName env tyName && isStructure env tyName then
          match userCtorFields env e with
          | none => none
          | some fields =>
            let names := getStructureFields env tyName
            if fields.size != names.size then none
            else Id.run do
              let mut values : Array Ops.Val := #[]
              for h : i in [:fields.size] do
                let some fieldTy := fieldTypeExpr env tyName names[i]! | return none
                let some fieldValues := flattenInitValue env fuel' fieldTy fields[i] | return none
                values := values ++ fieldValues
              return some values
        else none
      else none

private def asStateFields (env : Environment) (e : Expr) : Option (Array Ops.Val) := do
  let fields ← userCtorFields env (substLets 32 e)
  let ctor ← (substLets 32 e).getAppFn.constName?
  let .ctorInfo info ← env.find? ctor | none
  if info.induct == uint128Name ||
      info.induct == uint256Name || info.induct == fixedBytesName then none else pure ()
  let names := getStructureFields env info.induct
  if fields.size != names.size then none else pure ()
  let mut values : Array Ops.Val := #[]
  for h : i in [:fields.size] do
    let fieldTy ← fieldTypeExpr env info.induct names[i]!
    let fieldValues ← flattenInitValue env 32 fieldTy fields[i]
    values := values ++ fieldValues
  return values

private def looksUnchangedField (v : Ops.Val) (leaf : String) : Bool :=
  match v with
  | .field _ n =>
    n == leaf || n.endsWith ("_" ++ leaf) || leaf.endsWith ("_" ++ n)
  | _ => false

/-- 把一个值摊成账户叶。`Vector.set` / 嵌套 `with` 只展开被改的那些。 -/
private partial def flattenLeaves (env : Environment) (base : String) (e : Expr)
    (appliedBases : Array Expr := #[]) : Array (String × Ops.Val) :=
  let e := peelLets (strip e)
  if isVectorSet e then
    let args := e.getAppArgs
    -- `Vector.set α n xs i v h`：第一个字面量是长度，第二个是下标。
    -- 长度之后的第一个非字面量是旧向量，两下标之后才是新元素。
    let parsed :=
      Id.run do
        let mut nLits : Nat := 0
        let mut xs? : Option Expr := none
        let mut idx? : Option Nat := none
        let mut payload? : Option Expr := none
        for a in args do
          if endsWith a "._proof_1" || endsWith a "._proof_2" || endsWith a ".rfl" then
            pure ()
          else
            match asLit 8 a with
            | some (.lit n) =>
              if nLits == 0 then
                nLits := 1
              else if nLits == 1 then
                nLits := 2
                idx? := some n.toNat
              else
                pure ()
            | some _ =>
              pure ()
            | none =>
              if nLits == 1 && xs?.isNone then
                xs? := some (peelLets (strip a))
              else if nLits ≥ 2 && payload?.isNone then
                payload? := some (peelLets (strip a))
        return (idx?, xs?, payload?)
    match parsed with
    | (some i, xs?, some payload) =>
      let pre := if base.isEmpty then s!"{i}" else s!"{base}_{i}"
      let here := flattenLeaves env pre payload appliedBases
      let here :=
        if here.isEmpty then
          match val env payload with
          | some v => #[(pre, v)]
          | none => #[]
        else here
      let prev :=
        match xs? with
        | some xs => flattenLeaves env base xs appliedBases
        | none => #[]
      prev ++ here
    | _ => #[]
  else if let some fields := userCtorFields env e then
    match e.getAppFn.constName? with
    | none => #[]
    | some n =>
      match env.find? n with
      | some (.ctorInfo c) =>
        let names := getStructureFields env c.induct
        Id.run do
          let mut acc : Array (String × Ops.Val) := #[]
          for i in [0:fields.size] do
            if h : i < names.size ∧ i < fields.size then
              let fname := names[i].toString
              let child := if base.isEmpty then fname else s!"{base}_{fname}"
              let arg := fields[i]
              let inheritedFromAppliedBase :=
                match (peelLets (strip arg)).getAppFn.constName? with
                | some projection =>
                  match env.getProjectionFnInfo? projection with
                  | some info =>
                    let args := (peelLets (strip arg)).getAppArgs
                    info.ctorName == n && info.i == i &&
                      (args[args.size - 1]?.map appliedBases.contains).getD false
                  | none => false
                | none => false
              -- A payload constructor is one typed variant field, not a nested scalar
              -- expression whose first argument can stand in for the whole field.
              -- `{ { s with locked := e } with seats := xs.set … }.locked` elaborates as a
              -- projection of the inner constructor; reduce that projection before treating
              -- the field as an inherited `s.locked` leaf.
              let nestedArg := (reduceCtorProjection? env (peelLets (strip arg))).getD arg
              let nested :=
                if (asUInt64VariantCtor env arg).isSome || (asOptionStorage env arg).isSome then #[]
                else flattenLeaves env child nestedArg appliedBases
              let isVectorField :=
                match env.find? (c.induct.str fname) with
                | some info => info.type.getUsedConstantsAsSet.toList.any (· == ``Vector)
                | none => false
              -- Inner transitions represented by `appliedBases` were already lowered. A direct
              -- projection only inherits that field; reducing it through the constructor would
              -- replay a transition rather than describe an outer write.
              if inheritedFromAppliedBase then
                pure ()
              else if !nested.isEmpty then
                acc := acc ++ nested.filter fun p => !looksUnchangedField p.2 p.1
              else if isVectorField then
                -- A runtime-indexed vector is represented only by typed indexSet writes.
                -- Its root projection is not a scalar account leaf.
                pure ()
              else
                match asUInt64VariantCtor env arg with
                | some (tag, payloads, payloadWidth) =>
                  acc := acc.push (s!"{child}_tag", .lit tag)
                  for index in [:payloadWidth] do
                    acc := acc.push
                      (s!"{child}_p{index}", payloads[index]?.getD (.lit 0))
                | none =>
                  match asOptionStorage env arg with
                  | some (tag, payload) =>
                    acc := acc.push (s!"{child}_tag", tag) |>.push (s!"{child}_p0", payload)
                  | none =>
                    -- Record-update fields can close over bounded tree walks (Phoenix
                    -- `oldSize` / `maxBookAddress`). The ordinary scalar decoder fuel is
                    -- too low and used to drop those aggregate stores silently.
                    match val env nestedArg <|> asVal env 128 nestedArg <|>
                        localScalarValue? env 128 nestedArg with
                    | some v =>
                      unless looksUnchangedField v child || looksUnchangedField v fname do
                        acc := acc.push (child, v)
                    | none =>
                      if isConstNamed nestedArg ``Bool.true || endsWith nestedArg ".true" then
                        acc := acc.push (child, .lit 1)
                      else if isConstNamed nestedArg ``Bool.false || endsWith nestedArg ".false" then
                        acc := acc.push (child, .lit 0)
                      else
                        match nestedArg.getAppFn.constName? with
                        | some ctor =>
                          match env.find? ctor with
                          | some (.ctorInfo info) =>
                            -- A payload variant must be flattened into its typed tag/payload
                            -- leaves. Falling back to the constructor index would create a raw
                            -- store for the non-leaf parent and silently discard its payload.
                            if (uint64VariantPayloadWidth? env info.induct).isNone then
                              match enumCtorIndex env info.induct ctor with
                              | some k => acc := acc.push (child, .lit (UInt64.ofNat k))
                              | none => pure ()
                          | _ => pure ()
                        | none =>
                          match asLit 8 nestedArg with
                          | some v => acc := acc.push (child, v)
                          | none => pure ()
          acc
      | _ => #[]
  else
    match val env e with
    | some v =>
      if base.isEmpty || looksUnchangedField v base then #[] else #[(base, v)]
    | none => #[]

/-- Flatten a statically shaped scalar result. Products are protocol tuples, not heap containers:
each leaf must already lower to one target-neutral scalar value. -/
private def scalarResultValues (env : Environment) (fuel : Nat) (e : Expr) :
    Option (Array Ops.Val) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    if let .letE _ _ value body _ := e then
      scalarResultValues env fuel' (body.instantiate1 value)
    else if isConstNamed e ``Unit.unit || isConstNamed e ``PUnit.unit then
      some #[]
    else if isConstNamed e ``Prod.mk && e.getAppArgs.size ≥ 2 then do
      let args := e.getAppArgs
      let left ← scalarResultValues env fuel' args[args.size - 2]!
      let right ← scalarResultValues env fuel' args[args.size - 1]!
      return left ++ right
    else
      let unfolded := strip (unfoldUserHelpers env 16 e)
      asWideCtorFields env unfolded <|> asWideCtorFields env e
        <|> asRegisteredBoundaryCtorFields env unfolded
        <|> asRegisteredBoundaryCtorFields env e <|>
        (asBoolVal env fuel e <|> val env e).map (#[·])

/-- Keep the historical scalar `okState` shorthand, but spell multi-leaf effectful results as the
existing sequence of scalar returns. CFG lowering already joins that sequence into `returnU64s`. -/
private def effectfulResultOps (env : Environment) (e : Expr) : Option (Array Ops.Op) := do
  let values ← scalarResultValues env 16 e
  if values.size == 1 then
    return #[.okState values[0]!]
  else if values.size > 1 then
    return values.map fun value => .returnU64 value
  else
    -- Core's historical success terminal carries one scalar even when the logical result has no
    -- leaves. This zero is control-only: target output codecs must use the retained `.unit` schema
    -- rather than exposing it as a public result.
    return #[.okState (.lit 0)]

/-- `Except.ok` carrying a fixed-width boundary value (for example `NearToken` / `UInt128`). -/
private def asExceptOkBoundaryReturns (env : Environment) (e : Expr) : Option (Array Ops.Op) :=
  let e := peelControl 8 (dropUnusedHeadLets 32 e)
  if !isExceptOkHead e || e.getAppArgs.size < 1 then none else
  let payload := strip (unfoldUserHelpers env 16 (strip e.getAppArgs[e.getAppArgs.size - 1]!))
  if isConstNamed payload ``Prod.mk then none else
  match asWideCtorFields env payload <|> asRegisteredBoundaryCtorFields env payload with
  | some values => some (values.map fun value => (.returnU64 value : Ops.Op))
  | none =>
      match scalarResultValues env 16 payload with
      | some values =>
          if values.size > 1 then some (values.map fun value => (.returnU64 value : Ops.Op)) else none
      | none => none

/-- `Except.ok (State.mk …, ret)`：按叶 diff，改了几个槽就写几条。 -/
private def asStoreFields (env : Environment) (e : Expr)
    (includeSingle : Bool := false) : Option (Array Ops.Op) :=
  -- Preserve the RHS of `let next := ...` before peeling the state constructor. Dropping a used
  -- scalar binder turns `next` into an unrelated outer `.arg` and silently stores the wrong value.
  let e := peelControl 8 (substUInt64Lets 64 (dropUnusedHeadLets 32 e))
  if isExceptOkHead e then
    let args := e.getAppArgs
    if args.size ≥ 1 then
      let pair := strip args[args.size - 1]!
      if isConstNamed pair ``Prod.mk && pair.getAppArgs.size ≥ 2 then
        let st := pair.getAppArgs[pair.getAppArgs.size - 2]!
        let ret := pair.getAppArgs[pair.getAppArgs.size - 1]!
        -- Bare `.ok (methodArgRef, scalar)` must stay opaque here: `asStoreFields` is also consulted
        -- from `ite` arms before the recursively decoded then-branch, and succeeding with a lone
        -- `.okState` would erase preceding ignored Wasm effects (fifo cancel / CPI). Wide boundary
        -- returns (NearToken / UInt128 limbs as `.returnU64`) still need this short path.
        if isConstNamed (strip st) ``methodArgRef then
          match effectfulResultOps env ret with
          | some returns =>
              if returns.any fun op => match op with | .returnU64 _ => true | _ => false then
                some returns
              else none
          | none => none
        else
        let vectorBase := vectorBaseName env 32 st
        let leaves := (flattenLeaves env "" st).filter fun p => some p.1 != vectorBase
        let explicitSingle := includeSingle || containsUInt64NewtypeCtor env 16 st
        if leaves.isEmpty then none
        else if !explicitSingle && leaves.size == 1 then
          match effectfulResultOps env ret with
          | some returns =>
              if returns.any fun op => match op with | .returnU64 _ => true | _ => false then
                some returns
              else none
          | none => none
        else
          let stores := leaves.map fun p => (.storeField p.1 p.2 : Ops.Op)
          match effectfulResultOps env ret with
          | some returns => some (stores ++ returns)
          | none => some stores
      else none
    else none
  else none

private def asOkStateCore (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := peelControl 8 (dropUnusedHeadLets 32 e)
  if isExceptOkHead e then
    let args := e.getAppArgs
    if args.size ≥ 1 then
      let pair := strip args[args.size - 1]!
      if isConstNamed pair ``Prod.mk then
        let pargs := pair.getAppArgs
        if pargs.size ≥ 2 then
          let st := pargs[pargs.size - 2]!
          let boolLit :=
            (strip st).getAppArgs.findSome? fun a =>
              if isConstNamed a ``Bool.true || endsWith a ".true" then some (.lit 1)
              else if isConstNamed a ``Bool.false || endsWith a ".false" then some (.lit 0)
              else none
          match boolLit with
          | some v => some v
          | none =>
          match asOptionPayload env st with
          | some v => some v
          | none =>
            -- `{ s with nodes := s.nodes.set i { … with value := v } }`
            -- 展开成 `State.mk s.root s.size (Vector.set …)`。`val` 会先吃到
            -- `s.root`，必须先认嵌套 Vector.set，否则 dest 落到错误槽。
            match asVectorSet env (strip st) <|>
                (strip st).getAppArgs.findSome? (asVectorSet env) with
            | some v => some v
            | none =>
            match val env st with
            | some v =>
              match v with
              | .ext (.near _) _ => some v
              | v =>
                if Ops.isLangLeaf v then some v else none
            | _ =>
              match asVectorSet env (strip st) <|>
                  (strip st).getAppArgs.findSome? (asVectorSet env) with
              | some v => some v
              | none =>
                match asStateMk env st true with
                | some v => some v
                | none =>
                  let args := (strip st).getAppArgs
                  args.findSome? (asOptionPayload env) <|> asStateMk env st true
        else none
      else asStateMk env pair true
    else none
  else none

private def asOkState (env : Environment) (e : Expr) : Option Ops.Val :=
  match asOkStateCore env e with
  | result@(some (.field _ field)) =>
      let projectionScalar? := e.getUsedConstantsAsSet.toList.findSome? fun name =>
        if Core.IR.lastName name.toString != field || (env.getProjectionFnInfo? name).isNone then none
        else (env.find? name).map fun info => isScalarResult env info.type
      -- A structure/variant projection cannot be the scalar result of a mutating method. Let the
      -- full state decoder handle that branch instead of selecting an arbitrary constructor field.
      if projectionScalar? == some false then none else result
  | result => result

/-- Scalar `Except.ok` is an intermediate value producer, not a state commit. -/
private def asOkScalar (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := peelControl 8 (dropUnusedHeadLets 32 e)
  if isExceptOkHead e then
    let args := e.getAppArgs
    if h : args.size > 0 then
      let payload := strip args[args.size - 1]
      if isConstNamed payload ``Prod.mk then none else val env payload
    else none
  else none

/-- `.ok (s, value)` with the original state is a successful no-op, not an implicit write. The
result may be one scalar or a statically bounded product of scalar leaves. -/
private def asOkNoop (env : Environment) (e : Expr) : Option (Array Ops.Val) :=
  let e := peelControl 8 (dropUnusedHeadLets 32 e)
  if isExceptOkHead e then
    let args := e.getAppArgs
    if h : args.size > 0 then
      let pair := strip args[args.size - 1]
      if isConstNamed pair ``Prod.mk then
        let pairArgs := pair.getAppArgs
        if h : pairArgs.size ≥ 2 then
          match strip pairArgs[pairArgs.size - 2] with
          | .bvar _ => scalarResultValues env 16 pairArgs[pairArgs.size - 1]
          | state =>
            if isConstNamed state ``methodArgRef then
              scalarResultValues env 16 pairArgs[pairArgs.size - 1]
            else
              let reconstructedFromOneBinder :=
                match userCtorFields env state with
                | some fields =>
                    !fields.isEmpty && fields.all fun value =>
                      let args := (strip value).getAppArgs
                      if h : args.size > 0 then
                        match strip args[args.size - 1] with
                        | .bvar _ => true
                        | _ => false
                      else false
                | none => false
              let retValues? := scalarResultValues env 16 pairArgs[pairArgs.size - 1]!
              let reconstructedUnchanged :=
                let leaves := flattenLeaves env "" state
                match userCtorFields env state, retValues? with
                | some fields, some retValues =>
                  !fields.isEmpty && leaves.isEmpty && retValues.size > 1
                | _, _ => false
              if reconstructedFromOneBinder || reconstructedUnchanged then
                scalarResultValues env 16 pairArgs[pairArgs.size - 1]
              else none
        else none
      else none
    else none
  else none

private inductive DecodedError where
  | notError
  | overflow
  | named (name : String)
  | typed (frame : Core.Ops.ErrorFrame Ops.Val)
  | unsupported (reason : String)

/-- Preserve direct parameterized source-error constructors as one target-neutral fixed frame.
The first safe slice accepts one through four explicitly named UInt64 fields. Unsupported payloads
must not silently degrade to selector-only errors. -/
private def decodeErrorCtor (env : Environment) (e : Expr) : DecodedError :=
  let e := peelControl 8 e
  if isExceptErrorHead e then
    let args := e.getAppArgs
    if h : args.size > 0 then
      let applied := strip args[args.size - 1]
      match applied.getAppFn.constName? with
      | none => .notError
      | some ctorName =>
        let name := Core.IR.lastName ctorName.toString
        match env.find? ctorName with
        | some (.ctorInfo ctor) =>
          if ctor.numFields == 0 then
            if name == "overflow" then .overflow else .named name
          else if name == "overflow" then
            .unsupported "overflow error constructor cannot carry fields"
          else if ctor.numFields > 4 then
            .unsupported "parameterized source error supports at most four UInt64 fields"
          else
            match env.find? ctor.induct with
            | some (.inductInfo info) =>
              if info.numParams != 0 || info.numIndices != 0 || info.isRec then
                .unsupported "parameterized source error must be a nonrecursive monomorphic enum"
              else if applied.getAppArgs.size < ctor.numFields then
                .unsupported "parameterized source error lost constructor fields"
              else Id.run do
                let mut type := ctor.type
                let mut errorArgs : Array (Core.Ops.ErrorArg Ops.Val) := #[]
                let mut names : Array String := #[]
                for fieldIndex in [:ctor.numFields] do
                  let .forallE fieldName domain body binderInfo := strip type
                    | return .unsupported "parameterized source error lost field metadata"
                  if fieldName.isAnonymous || binderInfo != .default then
                    return .unsupported "parameterized source error fields must be explicitly named"
                  if domain.consumeMData.getAppFn.constName? != some ``UInt64 then
                    return .unsupported "parameterized source error currently supports only UInt64 fields"
                  let fieldName := fieldName.toString
                  if fieldName.isEmpty || names.contains fieldName then
                    return .unsupported "parameterized source error field names must be unique"
                  let some fieldExpr := applied.getAppArgs[applied.getAppArgs.size - ctor.numFields + fieldIndex]?
                    | return .unsupported "parameterized source error lost field value"
                  let some value := val env fieldExpr
                    | return .unsupported "parameterized source error field is not a scalar value"
                  names := names.push fieldName
                  errorArgs := errorArgs.push { name := fieldName, type := .uint64, parts := #[value] }
                  type := body
                let frame : Core.Ops.ErrorFrame Ops.Val := { constructor := name, args := errorArgs }
                if frame.wellFormed (·.wellFormed IR.ValKind.arity) then .typed frame
                else .unsupported "parameterized source error frame is malformed"
            | _ => .unsupported "parameterized source error has no enum metadata"
        | _ => if name == "overflow" then .overflow else .named name
    else .notError
  else .notError

private def isErrorOverflow (e : Expr) : Bool :=
  let e := peelControl 8 e
  if isExceptErrorHead e then
    let args := e.getAppArgs
    if h : args.size > 0 then
      endsWith (strip args[args.size - 1]) ".overflow"
    else false
  else false

private def returnStatesOf (vs : Array Ops.Val) : Array Ops.Op :=
  vs.map fun value => .returnState value

private def natOfVal : Ops.Val → Option Nat
  | .lit n => some n.toNat
  | _ => none

private partial def staticNatTerm? (env : Environment) (fuel : Nat) (e : Expr) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      let e := substLets fuel' (strip e)
      if let some value := natLiteral? e then
        some value
      else if let some reduced := reduceCtorProjectionFuel? env fuel' e then
        staticNatTerm? env fuel' reduced
      else
        match unfoldUserHelper env e with
        | some (_, unfolded) => staticNatTerm? env fuel' (substLets fuel' unfolded)
        | none => none

private def staticNatVal? (env : Environment) (e : Expr) : Option Nat :=
  staticNatTerm? env 64 e <|> (val env e >>= natOfVal) <|> do
    let .lit value ← asStaticLit env 64 e | none
    some value.toNat

private partial def staticString? (env : Environment) (fuel : Nat) (e : Expr) : Option String :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      let e := substLets fuel' (strip e)
      match e with
      | .lit (.strVal value) => some value
      | _ =>
          if let some reduced := reduceCtorProjectionFuel? env fuel' e then
            staticString? env fuel' reduced
          else if let some (helper, unfolded) := unfoldUserHelper env e then
            if inlineHelperPreservesUserType env helper then none
            else staticString? env fuel' (substLets fuel' unfolded)
          else none

/-- `.ok (state, ret)` 的第二元。找不到就 none。 -/
private def findOkRet (env : Environment) (e : Expr) : Option Ops.Val :=
  let rec go (fuel : Nat) (e : Expr) : Option Ops.Val :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if isExceptOkHead e && e.getAppArgs.size ≥ 1 then
        let pair := strip e.getAppArgs[e.getAppArgs.size - 1]!
        if isConstNamed pair ``Prod.mk && pair.getAppArgs.size ≥ 2 then
          let ret := pair.getAppArgs[pair.getAppArgs.size - 1]!
          val env ret
        else none
      else
        match e with
        | .letE _ _ value body _ => go fuel' (body.instantiate1 value)
        | .lam _ _ body _ => go fuel' body
        | .app f a => go fuel' f <|> go fuel' a
        | _ => none
  go 16 e

private def forRangeEnd (env : Environment) (e : Expr) : Option Nat :=
  let rec rangeEnd (fuel : Nat) (e : Expr) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if endsWith e ".mk" || e.getAppFn.constName?.isSome then
        let rargs := e.getAppArgs
        if rargs.size ≥ 2 then
          match asStaticLit env 16 rargs[1]! with
          | some (.lit n) => some n.toNat
          | _ => rargs.findSome? (rangeEnd fuel')
        else rargs.findSome? (rangeEnd fuel')
      else e.getAppArgs.findSome? (rangeEnd fuel')
  rangeEnd 8 e

/-- `forAccum` / `forBody`：下标位的 `.arg` 是循环变量。不要改 payload。 -/
private partial def rewriteLoopIx : Ops.Val → Ops.Val
  | .indexGet b n i k off => .indexGet b n (rewriteLoopIx i) k off
  -- State-loop callbacks expose the mutable accumulator and index as their two innermost
  -- binders. Depending on zeta/proof reduction, the scalar index is decoded as either one;
  -- captured method parameters remain at indices ≥ 2 and are normalized later.
  | .arg 0 | .arg 1 => .loopIx
  | .field b n => .field (rewriteLoopIx b) n
  | .bitAnd l r => .bitAnd (rewriteLoopIx l) (rewriteLoopIx r)
  | .bitOr l r => .bitOr (rewriteLoopIx l) (rewriteLoopIx r)
  | .bitXor l r => .bitXor (rewriteLoopIx l) (rewriteLoopIx r)
  | .bitNot v => .bitNot (rewriteLoopIx v)
  | .shiftL l r => .shiftL (rewriteLoopIx l) (rewriteLoopIx r)
  | .shiftR l r => .shiftR (rewriteLoopIx l) (rewriteLoopIx r)
  | .select c l r t f =>
      .select c (rewriteLoopIx l) (rewriteLoopIx r) (rewriteLoopIx t) (rewriteLoopIx f)
  | .addU64 l r => .addU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .subU64 l r => .subU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .mulU64 l r => .mulU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .divU64 l r => .divU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .modU64 l r => .modU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .ext kind operands => .ext kind (operands.map rewriteLoopIx)
  | v => v

private partial def rewriteLoopOp : Ops.Op → Ops.Op
  | .letLocal i v => .letLocal i (rewriteLoopIx v)
  | .joinLocal i => .joinLocal i
  | .setLocal i v => .setLocal i (rewriteLoopIx v)
  | .checkedAddU64 l r => .checkedAddU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .checkedSubU64 l r => .checkedSubU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .checkedMulU64 l r => .checkedMulU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .checkedDivU64 l r => .checkedDivU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .checkedModU64 l r => .checkedModU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .ite c l r t f =>
      .ite c (rewriteLoopIx l) (rewriteLoopIx r)
        (t.map rewriteLoopOp) (f.map rewriteLoopOp)
  | .indexSetLeaf n i v k leaf =>
      .indexSetLeaf n (rewriteLoopIx i) (rewriteLoopIx v) k leaf
  | .indexSet n i v k off =>
      .indexSet n (rewriteLoopIx i) (rewriteLoopIx v) k off
  | .storeField n v => .storeField n (rewriteLoopIx v)
  | .okState v => .okState (rewriteLoopIx v)
  | .returnU64 v => .returnU64 (rewriteLoopIx v)
  | .returnState _ => .errorOverflow
  | .forAccum n v resultLocal => .forAccum n (rewriteLoopIx v) resultLocal
  | .forBody n body => .forBody n (body.map rewriteLoopOp)
  | op => op

/--
普通 accumulator / early-return 循环沿用原来的 callback 归一化：账户参数落到
`.arg 0`，动态索引就是 `loopIx`，而 `indexSet` payload 仍是外层方法参数。
State-carrying loop 不能用这条宽松规则，继续走上面的精确 binder 重写。
-/
private partial def rewritePlainLoopIx : Ops.Val → Ops.Val
  | .indexGet b n i k off =>
      let b' := match b with | .arg _ => .arg 0 | _ => rewritePlainLoopIx b
      let i' := match i with | .lit _ => i | _ => .loopIx
      .indexGet b' n i' k off
  | .field b n => .field (rewritePlainLoopIx b) n
  | .bitAnd l r => .bitAnd (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .bitOr l r => .bitOr (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .bitXor l r => .bitXor (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .bitNot x => .bitNot (rewritePlainLoopIx x)
  | .shiftL l r => .shiftL (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .shiftR l r => .shiftR (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .select c l r t f =>
      .select c (rewritePlainLoopIx l) (rewritePlainLoopIx r)
        (rewritePlainLoopIx t) (rewritePlainLoopIx f)
  | .addU64 l r => .addU64 (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .subU64 l r => .subU64 (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .mulU64 l r => .mulU64 (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .divU64 l r => .divU64 (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .modU64 l r => .modU64 (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .ext kind operands => .ext kind (operands.map rewritePlainLoopIx)
  | v => v

private partial def rewritePlainLoopOp (op : Ops.Op) : Ops.Op :=
  let rv := rewritePlainLoopIx
  match op with
  | .letLocal i v => .letLocal i (rv v)
  | .joinLocal i => .joinLocal i
  | .setLocal i v => .setLocal i (rv v)
  | .checkedAddU64 l r => .checkedAddU64 (rv l) (rv r)
  | .checkedSubU64 l r => .checkedSubU64 (rv l) (rv r)
  | .checkedMulU64 l r => .checkedMulU64 (rv l) (rv r)
  | .checkedDivU64 l r => .checkedDivU64 (rv l) (rv r)
  | .checkedModU64 l r => .checkedModU64 (rv l) (rv r)
  | .ite c l r t f =>
      let l' := match l with | .arg _ => .loopIx | _ => rv l
      let r' := match r with | .arg _ => .loopIx | _ => rv r
      .ite c l' r' (t.map rewritePlainLoopOp) (f.map rewritePlainLoopOp)
  | .indexSetLeaf n i v k leaf =>
      let i' := match i with | .lit _ => i | _ => .loopIx
      let v' := match v with | .arg _ => .arg 0 | _ => v
      .indexSetLeaf n i' v' k leaf
  | .indexSet n i v k off =>
      let i' := match i with | .lit _ => i | _ => .loopIx
      let v' := match v with | .arg _ => .arg 0 | _ => v
      .indexSet n i' v' k off
  | .storeField n v => .storeField n v
  | .okState v => .okState (match v with | .arg _ => .arg 0 | _ => v)
  | .returnU64 v => .returnU64 (rv v)
  | .returnState _ => .errorOverflow
  | .forAccum n v resultLocal => .forAccum n (rv v) resultLocal
  | .forBody n body => .forBody n (body.map rewritePlainLoopOp)
  | op => op

private def findForIn (env : Environment) (e : Expr) : Option (Nat × Ops.Val) :=
  let rec go (fuel : Nat) (e : Expr) : Option (Nat × Ops.Val) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := e.consumeMData
      if e.getAppFn.constName? == some ``Id.run || endsWith e ".run" then
        if e.getAppArgs.size ≥ 1 then go fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else none
      else if e.getAppFn.constName? == some ``ForIn.forIn || endsWith e ".forIn" then
        let args := e.getAppArgs
        let n? := args.findSome? (forRangeEnd env)
        let rec findAdd (fuel : Nat) (e : Expr) : Option Ops.Val :=
          match fuel with
          | 0 => none
          | fuel' + 1 =>
            let e := strip e
            if isConstNamed e ``HAdd.hAdd && e.getAppArgs.size ≥ 2 then
              (asVal env 8 e.getAppArgs[e.getAppArgs.size - 1]!).map rewritePlainLoopIx
            else
              match e with
              | .lam _ _ body _ => findAdd fuel' body
              | .letE _ _ value body _ => findAdd fuel' value <|> findAdd fuel' body
              | _ => e.getAppArgs.findSome? (findAdd fuel')
        let addend? := args.findSome? (findAdd 16)
        match n?, addend? with
        | some n, some v =>
          if n = 0 || n > 64 then none else some (n, v)
        | _, _ => none
      else if isConstNamed e ``ite || isConstNamed e ``dite then none
      else
        match e with
        | .letE _ _ value body _ => go fuel' value <|> go fuel' body
        | .lam _ _ body _ => go fuel' body
        | .app f a => go fuel' f <|> go fuel' a
        | _ => none
  go 16 e

/-- `for i in [:n]` 里 `ForInStep.done` 提前返回。累加仍走 `findForIn`。 -/
private def findForBodyExpr (env : Environment) (e : Expr) : Option (Nat × Expr) :=
  let rec go (fuel : Nat) (e : Expr) : Option (Nat × Expr) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := e.consumeMData
      if e.getAppFn.constName? == some ``Id.run || endsWith e ".run" then
        if e.getAppArgs.size ≥ 1 then go fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else none
      else if e.getAppFn.constName? == some ``ForIn.forIn || endsWith e ".forIn" then
        if (findForIn env e).isSome then none
        else
          let args := e.getAppArgs
          let n? := args.findSome? (forRangeEnd env)
          -- `forIn xs init (fun i r => body)`：最后一个 λ 是循环体。
          let rec lastLam (fuel : Nat) (e : Expr) : Option Expr :=
            match fuel with
            | 0 => none
            | fuel' + 1 =>
              match strip e with
              | .lam _ _ body _ =>
                match strip body with
                | .lam _ _ body2 _ => some (peelLets body2)
                | _ => some (peelLets body)
              | .letE _ _ _ body _ => lastLam fuel' body
              | e => e.getAppArgs.findSome? (lastLam fuel')
          let bodyE? :=
            if args.size > 0 then lastLam 8 args[args.size - 1]! else none
          match n?, bodyE? with
          | some n, some bodyE =>
            if n = 0 || n > 64 then none else some (n, bodyE)
          | _, _ => none
      else if isConstNamed e ``ite || isConstNamed e ``dite then none
      else
        match e with
        | .letE _ _ value body _ => go fuel' value <|> go fuel' body
        | .lam _ _ body _ => go fuel' body
        | .app f a => go fuel' f <|> go fuel' a
        | _ => none
  go 16 e

/-- Conservatively detect a structured State binding before zeta reduction erases its sharing. -/
def containsStructuredStateLet (env : Environment) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
      match strip e with
      | .letE _ type value body _ =>
          let userStructure :=
            (type.consumeMData.getAppFn.constName?.map (isUserType env)).getD false
          (userStructure && (isIteExpr value || (unfoldUserHelper env value).isSome)) ||
            containsStructuredStateLet env fuel value || containsStructuredStateLet env fuel body
      | .lam _ _ body _ => containsStructuredStateLet env fuel body
      | .app fn arg =>
          containsStructuredStateLet env fuel fn || containsStructuredStateLet env fuel arg
      | _ => false

/-- Detect a marked State transition below surrounding control/record syntax. -/
private def containsInlineStateTransition (env : Environment) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
      let e := strip e
      let here :=
        match unfoldUserHelper env e with
        | some (name, _) => inlineHelperPreservesUserType env name
        | none => false
      here || match e with
        | .letE _ _ value body _ =>
            containsInlineStateTransition env fuel value ||
              containsInlineStateTransition env fuel body
        | .lam _ _ body _ => containsInlineStateTransition env fuel body
        | .app fn arg =>
            containsInlineStateTransition env fuel fn ||
              containsInlineStateTransition env fuel arg
        | _ => false

/--
`do let mut st := s; for ... do st := ...; k st` 的 loop body 与 continuation。
真正是否为 state-carrying loop 由 body 解码出的显式 store 判定；普通 early-return
`forBody` 继续走旧路径。
-/
private def findForStateExpr (env : Environment) (e : Expr) :
    Option (Nat × Expr × Expr × Expr) :=
  let rec findForExpr (fuel : Nat) (e : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if e.getAppFn.constName? == some ``ForIn.forIn || endsWith e ".forIn" then some e
      else if isConstNamed e ``ite || isConstNamed e ``dite then none
      else
        match e with
        | .letE _ _ value body _ =>
          findForExpr fuel' value <|> findForExpr fuel' (body.instantiate1 value)
        | .lam _ _ body _ => findForExpr fuel' body
        | _ => e.getAppArgs.findSome? (findForExpr fuel')
  let loopParts? := do
    let forExpr ← findForExpr 32 e
    let n ← forExpr.getAppArgs.findSome? (forRangeEnd env)
    let rec lastLam (fuel : Nat) (e : Expr) : Option Expr :=
      match fuel with
      | 0 => none
      | fuel' + 1 =>
        match strip e with
        | .lam _ _ body _ =>
          match strip body with
          | .lam _ _ body2 _ => some (substLets 128 body2)
          | _ => some (substLets 128 body)
        | .letE _ _ _ body _ => lastLam fuel' body
        | e => e.getAppArgs.findSome? (lastLam fuel')
    let args := forExpr.getAppArgs
    if args.size < 2 then none else
    let initial := args[args.size - 2]!
    let body ← if h : args.size > 0 then lastLam 16 args[args.size - 1] else none
    if n = 0 || n > 64 then none else some (n, initial, body)
  let rec findContinuation (fuel : Nat) (e : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if e.getAppFn.constName? == some ``Id.run || endsWith e ".run" then
        if e.getAppArgs.size ≥ 1 then
          findContinuation fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else none
      else if isConstNamed e ``ite || isConstNamed e ``dite then none
      else
        match e with
        | .letE _ _ value body _ => findContinuation fuel' (body.instantiate1 value)
        | _ =>
          if e.getAppFn.constName? == some ``Bind.bind || endsWith e ".bind" then
            let args := e.getAppArgs
            if args.any fun a => (findForExpr 16 a).isSome then
              match args.findRev? fun a => match strip a with | .lam .. => true | _ => false with
              | some continuation =>
                match strip continuation with
                | .lam _ _ continuationBody _ =>
                  if containsStructuredStateLet env 2048 continuationBody ||
                      containsInlineStateTransition env 2048 continuationBody then
                    some (strip continuationBody)
                  else
                    some (peelControl 16
                      (substLets 128 continuationBody))
                | _ => none
              | none => none
            else args.findSome? (findContinuation fuel')
          else
            e.getAppArgs.findSome? (findContinuation fuel')
  match loopParts?, findContinuation 32 e with
  | some (n, initial, bodyE), some continuation => some (n, initial, bodyE, continuation)
  | _, _ => none

/-- Flatten the right-nested `MProd` generated by two or more `let mut UInt64` bindings. The
constructor's explicit type arguments keep this gate restricted to scalar `UInt64` leaves. -/
private def scalarFrameLeaves (e : Expr) : Option (Array Expr) :=
  let rec go (fuel : Nat) (value : Expr) : Option (Array Expr) := do
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let value := strip value
      if !isConstNamed value ``MProd.mk then none else
      let args := value.getAppArgs
      if h : args.size ≥ 4 then
        let decodeLeaf (type value : Expr) : Option (Array Expr) :=
          if type.consumeMData.getAppFn.constName? == some ``UInt64 then
            some #[value]
          else if type.consumeMData.getAppFn.constName? == some ``MProd then
            go fuel' value
          else
            none
        let left ← decodeLeaf args[args.size - 4] args[args.size - 2]
        let right ← decodeLeaf args[args.size - 3] args[args.size - 1]
        return left ++ right
      else
        none
  go 32 e

/-- Rebuild an `MProd` frame with extractor local markers while preserving its exact nested shape. -/
private def scalarFrameLocalShape (e : Expr) (base : Nat) : Option Expr := do
  let leaves ← scalarFrameLeaves e
  let rec go (fuel : Nat) (value : Expr) (index : Nat) : Expr × Nat :=
    match fuel with
    | 0 => (value, index)
    | fuel' + 1 =>
      let value := strip value
      if isConstNamed value ``MProd.mk && value.getAppArgs.size ≥ 4 then
        let args := value.getAppArgs
        let (left, index) := go fuel' args[args.size - 2]! index
        let (right, index) := go fuel' args[args.size - 1]! index
        let headArgs := args.extract 0 (args.size - 2)
        (mkAppN value.getAppFn (headArgs ++ #[left, right]), index)
      else
        (mkApp (mkConst ``localRef) (mkNatLit (base + index)), index + 1)
  let (shape, count) := go 32 e 0
  if count == leaves.size then some shape else none

/-- Elaboration flattens a final `MProd` pattern into one continuation lambda per scalar leaf.
Apply that branch directly after replacing the loop result with local markers. -/
private def reduceScalarFrameContinuation? (env : Environment) (e frame : Expr) : Option Expr := do
  let leaves ← scalarFrameLeaves frame
  let e := strip e
  let matcherName ← e.getAppFn.constName?
  let matcher ← Lean.Meta.getMatcherInfoCore? env matcherName
  if matcher.numDiscrs != 1 then none else pure ()
  let args := e.getAppArgs
  let discr ← args[matcher.getFirstDiscrPos]?
  if strip discr != strip frame then none else pure ()
  let branch ← args[matcher.getFirstAltPos]?
  if (peelLams branch).1 != leaves.size then none else
    some (branch.beta leaves)

/-- Mark every scalar-frame yield with its target-local base. The marker is private extraction
syntax, not a source SDK primitive or a target opcode. -/
private def markScalarFrameYields (base : Nat) (e : Expr) : Expr :=
  let rec go (fuel : Nat) (e : Expr) : Expr :=
    match fuel with
    | 0 => e
    | fuel' + 1 =>
      let raw := strip e
      if (isConstNamed raw ``ForInStep.yield || endsWith raw ".yield") &&
          raw.getAppArgs.size ≥ 2 then
        let args := raw.getAppArgs
        let type := args[args.size - 2]!
        let value := go fuel' args[args.size - 1]!
        let marked := mkApp3 (mkConst ``scalarFrameYield) type (mkNatLit base) value
        mkAppN raw.getAppFn (args.extract 0 (args.size - 1) |>.push marked)
      else
        match raw with
        | .app fn arg => .app (go fuel' fn) (go fuel' arg)
        | .lam name type body info => .lam name (go fuel' type) (go fuel' body) info
        | .forallE name type body info => .forallE name (go fuel' type) (go fuel' body) info
        | .letE name type value body nondep =>
            .letE name (go fuel' type) (go fuel' value) (go fuel' body) nondep
        | .mdata data body => .mdata data (go fuel' body)
        | .proj type index value => .proj type index (go fuel' value)
        | e => e
  go 128 e

/-- 收集 `xs.set … .set …` 整条链。先外层（旧向量），后内层（新写）。
一次 `set` 可以改多叶（`left` + `parent`）。 -/
private def collectIndexSets (env : Environment) (e : Expr)
    (deduplicate : Bool := false) (appliedBases : Array Expr := #[]) : Array Ops.Op :=
  let rec go (fuel : Nat) (e : Expr) (state : Array Expr × Array Ops.Op) :
      Array Expr × Array Ops.Op :=
    match fuel with
    | 0 => state
    | fuel' + 1 =>
      let e := strip e
      match e with
      | .letE _ _ value body _ => go fuel' (body.instantiate1 value) state
      | .lam _ _ body _ => go fuel' body state
      | _ =>
        if isExceptOkHead e && e.getAppArgs.size ≥ 1 then
          go fuel' e.getAppArgs[e.getAppArgs.size - 1]! state
        else if isConstNamed e ``Prod.mk && e.getAppArgs.size ≥ 2 then
          go fuel' e.getAppArgs[e.getAppArgs.size - 2]! state
        else if isVectorSet e then
          -- `Vector.set α n xs i v h`：只沿 xs 追溯旧写。payload/下标里的
          -- vector reads 不是写；共享 record projections 也会重复引用同一个 set node。
          if deduplicate && state.1.contains e then state else
            let args := e.getAppArgs
            let state :=
              if h : args.size ≥ 4 then go fuel' args[args.size - 4] state else state
            match asIndexSets env e with
            | some ops =>
                let seen := if deduplicate then state.1.push e else state.1
                (seen, state.2 ++ ops)
            | none => state
        else
          let inheritedFromAppliedBase :=
            match e.getAppFn.constName? with
            | some projection =>
              match env.getProjectionFnInfo? projection with
              | some _ =>
                let args := e.getAppArgs
                (args[args.size - 1]?.map appliedBases.contains).getD false
              | none => false
            | none => false
          if inheritedFromAppliedBase then state
          else e.getAppArgs.foldl (init := state) fun state arg => go fuel' arg state
  (go 16 e (#[], #[])).2

private def findIndexSet (env : Environment) (e : Expr) : Option Ops.Op :=
  (collectIndexSets env e)[0]?


/-- Flatten one logical bounded byte value into `length, byte₀ … byteₙ₋₁`. Constructors already
carry literal leaves; a parameter or local root is projected so the target input binder can later
rewrite it to canonical scalar locals. -/
private def normalizeBoundedParameterFrame (capacity : Nat) (values : Array Ops.Val) :
    Array Ops.Val := Id.run do
  unless values.size == capacity + 1 do return values
  let .field _ "length" := values[0]! | return values
  let mut normalized : Array Ops.Val := #[values[0]!]
  for position in [0:capacity] do
    match values[position + 1]! with
    | .indexGet base "values" (.local index) length elementOffset =>
        unless index == position && (length == 0 || length == capacity) &&
            elementOffset == 0 do
          return values
        normalized := normalized.push
          (.indexGet base "values" (.lit (UInt64.ofNat position)) capacity 0)
    | _ => return values
  return normalized

private def nearAccountIdFrame? (env : Environment) (e : Expr) : Option (Array Ops.Val) := do
  let length ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.length) e)
  let w0 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w0) e)
  let w1 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w1) e)
  let w2 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w2) e)
  let w3 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w3) e)
  let w4 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w4) e)
  let w5 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w5) e)
  let w6 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w6) e)
  let w7 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w7) e)
  return #[length, w0, w1, w2, w3, w4, w5, w6, w7]

private def nearBoundedMessage64Frame? (env : Environment) (e : Expr) : Option (Array Ops.Val) := do
  let length ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.BoundedMessage64.length) e)
  let w0 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.BoundedMessage64.w0) e)
  let w1 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.BoundedMessage64.w1) e)
  let w2 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.BoundedMessage64.w2) e)
  let w3 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.BoundedMessage64.w3) e)
  let w4 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.BoundedMessage64.w4) e)
  let w5 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.BoundedMessage64.w5) e)
  let w6 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.BoundedMessage64.w6) e)
  let w7 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.BoundedMessage64.w7) e)
  return #[length, w0, w1, w2, w3, w4, w5, w6, w7]

private def nearCryptoBytes32Frame? (env : Environment) (e : Expr) : Option (Array Ops.Val) := do
  let e := substLets 32 (strip (unfoldUserHelpers env 8 e))
  let w0 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.CryptoBytes32.w0) e)
  let w1 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.CryptoBytes32.w1) e)
  let w2 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.CryptoBytes32.w2) e)
  let w3 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.CryptoBytes32.w3) e)
  return #[w0, w1, w2, w3]

private def nearCryptoBytes64Frame? (env : Environment) (e : Expr) : Option (Array Ops.Val) := do
  let e := substLets 32 (strip (unfoldUserHelpers env 8 e))
  let w0 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.CryptoBytes64.w0) e)
  let w1 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.CryptoBytes64.w1) e)
  let w2 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.CryptoBytes64.w2) e)
  let w3 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.CryptoBytes64.w3) e)
  let w4 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.CryptoBytes64.w4) e)
  let w5 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.CryptoBytes64.w5) e)
  let w6 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.CryptoBytes64.w6) e)
  let w7 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.CryptoBytes64.w7) e)
  return #[w0, w1, w2, w3, w4, w5, w6, w7]

private partial def staticAccountTokenTag? (env : Environment) (fuel : Nat) (e : Expr) : Option Nat :=
  staticNatVal? env e <|>
    match fuel, strip e with
    | fuel' + 1, .const name _ =>
        match env.find? name with
        | some (.defnInfo info) => staticAccountTokenTag? env fuel' info.value
        | _ => none
    | _, _ => none

private def accountTokenStorageKeyFrame (tag : Ops.Val) (account : Array Ops.Val) : Array Ops.Val := Id.run do
  let length := account[0]!
  let byte (word : Ops.Val) (shift : Nat) : Ops.Val :=
    .bitAnd (.shiftR word (.lit (UInt64.ofNat shift))) (.lit 0xff)
  let mut values : Array Ops.Val := #[.addU64 length (.lit 8)]
  for index in [0:4] do
    values := values.push (byte tag (index * 8))
  for index in [0:4] do
    values := values.push (byte length (index * 8))
  for wordIndex in [0:8] do
    for byteIndex in [0:8] do
      values := values.push (byte account[wordIndex + 1]! (byteIndex * 8))
  values

private def accountTokenLengthAdmissible (account : Array Ops.Val) : Bool :=
  match staticUInt64? account[0]! with
  | some length => 2 ≤ length && length ≤ 64
  | none => true

private def nearTokenStorageValueFrame (lo hi : Ops.Val) : Array Ops.Val := Id.run do
  let byte (word : Ops.Val) (shift : Nat) : Ops.Val :=
    .bitAnd (.shiftR word (.lit (UInt64.ofNat shift))) (.lit 0xff)
  let mut values : Array Ops.Val := #[.lit 16]
  for word in #[lo, hi] do
    for byteIndex in [0:8] do
      values := values.push (byte word (byteIndex * 8))
  values

private def boundedStorageFrame? (env : Environment) (capacity : Nat) (e : Expr) :
    Option (Array Ops.Val) := do
  let e := substLets 32 (strip (unfoldUserHelpers env 8 e))
  if let some values := asBoundedCtorFields env e then
    if values.size == capacity + 1 then
      return normalizeBoundedParameterFrame capacity values
    else none
  let root ← val env e
  let mut values : Array Ops.Val := #[.field root "length"]
  for index in [0:capacity] do
    values := values.push (.indexGet root "values" (.lit (UInt64.ofNat index)) capacity 0)
  return values

/-- Preserve source lets that sequence NEAR effects before generic zeta reduction. Otherwise an
ignored UInt64 sequencing result would erase the host/log or guest-memory mutation before
`decodeExpr` can turn it into a typed effect. -/
partial def mentionsNearEffect (env : Environment) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
      e.getUsedConstantsAsSet.toList.any fun name =>
        name == ``ProofForge.Wasm.Near.Runtime.logUtf8 ||
        name == ``ProofForge.Wasm.Near.Runtime.logUtf8Bounded ||
        name == ``ProofForge.Wasm.Near.Runtime.storageUnregisteredLog ||
        name == ``ProofForge.Wasm.Near.Runtime.nep297StringData ||
        name == ``ProofForge.Wasm.Near.Runtime.nep141FtMint ||
        name == ``ProofForge.Wasm.Near.Runtime.nep141FtTransfer ||
        name == ``ProofForge.Wasm.Near.Runtime.nep141FtBurn ||
        name == ``ProofForge.Wasm.Near.Runtime.nep141FtMintMemo ||
        name == ``ProofForge.Wasm.Near.Runtime.nep141FtTransferMemo ||
        name == ``ProofForge.Wasm.Near.Runtime.nep141FtBurnMemo ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallDetached ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFtOnTransferReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFtOnTransferThenResolveReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallThenReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAndThenReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAnd3ThenReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAnd4ThenReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAnd5ThenReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAnd6ThenReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAnd7ThenReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAnd8ThenReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseTransferDetached ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseTransferReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseResultRead ||
        name == ``ProofForge.Wasm.Near.Runtime.transientBuffer64Begin ||
        name == ``ProofForge.Wasm.Near.Runtime.transientBuffer64Set ||
        name == ``ProofForge.Wasm.Near.Runtime.transientBuffer64Finish ||
        name == ``ProofForge.Wasm.Near.Runtime.storageRead ||
        name == ``ProofForge.Wasm.Near.Runtime.storageWrite ||
        name == ``ProofForge.Wasm.Near.Runtime.storageRemove ||
        name == ``ProofForge.Wasm.Near.Runtime.storageHasKey ||
        name == ``ProofForge.Wasm.Near.Runtime.sha256Hash ||
        name == ``ProofForge.Wasm.Near.Runtime.keccak256Hash ||
        name == ``ProofForge.Wasm.Near.Runtime.keccak512Hash ||
        name == ``ProofForge.Wasm.Near.Runtime.ripemd160Hash ||
        name == ``ProofForge.Wasm.Near.Runtime.ecrecover ||
        name == ``ProofForge.Wasm.Near.Runtime.ed25519Verify ||
        name == ``ProofForge.Wasm.Near.Runtime.accountNearTokenRead ||
        name == ``ProofForge.Wasm.Near.Runtime.accountNearTokenWrite ||
        name == ``ProofForge.Wasm.Near.Runtime.accountNearTokenRemove ||
        name == ``ProofForge.Wasm.Near.Runtime.accountNearTokenHasKey ||
        name == ``ProofForge.Wasm.Near.Runtime.accountNearTokenFixtureWriteMalformed ||
        name == ``ProofForge.Wasm.Near.Sdk.Store.DirectAccountNearTokenMap.read ||
        name == ``ProofForge.Wasm.Near.Sdk.Store.DirectAccountNearTokenMap.has ||
        name == ``ProofForge.Wasm.Near.Sdk.Store.DirectAccountNearTokenMap.put ||
        name == ``ProofForge.Wasm.Near.Sdk.Store.DirectAccountNearTokenMap.remove ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.callDetached ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.callReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.ftOnTransferReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.ftOnTransferThenResolveReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.callThenReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.callAndThenReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.callAnd3ThenReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.callAnd4ThenReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.callAnd5ThenReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.callAnd6ThenReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.callAnd7ThenReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.callAnd8ThenReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.thenReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and3Returned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and4Returned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and5Returned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and6Returned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and7Returned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and8Returned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.transferDetached ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.transferReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.transferAccountDetached ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.transferAccountReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseTransferAccountDetached ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseTransferAccountReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.ResultBuffer.read ||
        name == ``ProofForge.Wasm.Near.Sdk.Transient.Buffer64.begin ||
        name == ``ProofForge.Wasm.Near.Sdk.Transient.Buffer64.set ||
        name == ``ProofForge.Wasm.Near.Sdk.Transient.Buffer64.finish ||
        name == ``ProofForge.Wasm.Near.Sdk.Storage.ResultBuffer.read ||
        name == ``ProofForge.Wasm.Near.Sdk.Storage.ResultBuffer.write ||
        name == ``ProofForge.Wasm.Near.Sdk.Storage.ResultBuffer.remove ||
        name == ``ProofForge.Wasm.Near.Sdk.Storage.ResultBuffer.hasKey ||
        (Attr.isInline env name &&
          match env.find? name with
          | some (.defnInfo info) => mentionsNearEffect env fuel info.value
          | _ => false)

/-- Read a compile-time Nat, unfolding plain `def` aliases such as `defaultMaxFanIn`. -/
private partial def staticNatOrDefn? (env : Environment) (fuel : Nat) (e : Expr) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      let e := strip e
      staticNatVal? env e <|>
        match e.getAppFn.constName? with
        | some name =>
            match env.find? name with
            | some (.defnInfo info) => staticNatOrDefn? env fuel' info.value
            | _ => none
        | none => none

/-- True when `e` is a PromiseHandle lifecycle API that carries compile-time `maxFanIn`. -/
private def isPromiseHandleLifecycleApi (e : Expr) : Bool :=
  isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.thenReturned ||
    isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and3Returned ||
    isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and4Returned ||
    isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and5Returned ||
    isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and6Returned ||
    isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and7Returned ||
    isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and8Returned

/-- Fail-closed message when a PromiseHandle API's `maxFanIn` literal exceeds the opcode ladder
(`maxFanInCompileCeiling = 8`). N>8 requires new fixed `andN` ops; Extract must not silently
accept an over-ceiling handle capacity. Bare / partial apps (empty args) are ignored so the
AST walk can reach the fully applied call. -/
private def promiseHandleMaxFanInCeilingError? (env : Environment) (e : Expr) : Option String :=
  let e := strip e
  if !isPromiseHandleLifecycleApi e || e.getAppArgs.isEmpty then none
  else
    match staticNatOrDefn? env 16 e.getAppArgs[0]! with
    | some n =>
        if ProofForge.Wasm.Near.Sdk.Promises.maxFanInWithinCeiling n then none
        else
          some s!"extract/unsupported: PromiseHandle maxFanIn {n} exceeds compile ceiling {ProofForge.Wasm.Near.Sdk.Promises.maxFanInCompileCeiling}"
    | none =>
        some "extract/unsupported: PromiseHandle maxFanIn must be a static Nat within the compile ceiling"

/-- Walk a body for over-ceiling PromiseHandle APIs before effect decode can accept them. -/
private partial def findPromiseHandleMaxFanInCeilingError (env : Environment) :
    Nat → Expr → Option String
  | 0, _ => none
  | fuel + 1, e =>
      let e := strip e
      promiseHandleMaxFanInCeilingError? env e <|>
        match e with
        | .letE _ _ value body _ =>
            findPromiseHandleMaxFanInCeilingError env fuel value <|>
              findPromiseHandleMaxFanInCeilingError env fuel (body.instantiate1 value)
        | .lam _ _ body _ => findPromiseHandleMaxFanInCeilingError env fuel body
        | .app fn arg =>
            findPromiseHandleMaxFanInCeilingError env fuel fn <|>
              findPromiseHandleMaxFanInCeilingError env fuel arg
        | .mdata _ inner => findPromiseHandleMaxFanInCeilingError env fuel inner
        | _ => none

/-- Whether the PromiseHandle API head at `e` has a static `maxFanIn` within the compile ceiling.
Returns `none` when the head is not a PromiseHandle lifecycle API or is not yet applied.
Returns `some false` when the API is applied but `maxFanIn` is non-static or over the ceiling. -/
private def promiseHandleMaxFanInWithinCeiling? (env : Environment) (e : Expr) : Option Bool :=
  let e := strip e
  if !isPromiseHandleLifecycleApi e || e.getAppArgs.isEmpty then none
  else
    match staticNatOrDefn? env 16 e.getAppArgs[0]! with
    | some n => some (ProofForge.Wasm.Near.Sdk.Promises.maxFanInWithinCeiling n)
    | none => some false

/-- NEAR logging and invocation-memory mutations stay effects so CFG rewrites cannot duplicate,
discard, or reorder them as pure scalar expressions. Buffer capacities remain compile-time. -/
private def decodeNearEffect (env : Environment) (e : Expr) : Option (Array Ops.Op) :=
  let rec find (fuel : Nat) (e : Expr) : Option Ops.Op :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      -- Defense in depth: never decode PromiseHandle APIs above the compile ceiling.
      if let some false := promiseHandleMaxFanInWithinCeiling? env e then none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.logUtf8 then
        (e.getAppArgs.back? >>= staticString? env 64).map Ops.Op.nearLogUtf8
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.logUtf8Bounded &&
          e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 2]! with
        | some capacity =>
            if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
              (boundedStorageFrame? env capacity args[args.size - 1]!).map fun message =>
                .nearLogUtf8Bounded capacity message
            else none
        | none => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageUnregisteredLog &&
          e.getAppArgs.size ≥ 1 then
        (nearAccountIdFrame? env e.getAppArgs.back!).map Ops.Op.nearStorageUnregisteredLog
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nep297StringData &&
          e.getAppArgs.size ≥ 5 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 5]!,
            staticString? env 64 args[args.size - 4]!,
            staticString? env 64 args[args.size - 3]!,
            staticString? env 64 args[args.size - 2]! with
        | some capacity, some standard, some version, some event =>
            if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
              (boundedStorageFrame? env capacity args[args.size - 1]!).map fun data =>
                .nearNep297StringData standard version event capacity data
            else none
        | _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nep141FtMint &&
          e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        let owner := args[args.size - 2]!
        let amount := args[args.size - 1]!
        match nearAccountIdFrame? env owner,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) amount),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) amount) with
        | some owner, some amountLo, some amountHi =>
            some (.nearNep141FtMint owner amountLo amountHi)
        | _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nep141FtTransfer &&
          e.getAppArgs.size ≥ 3 then
        let args := e.getAppArgs
        let oldOwner := args[args.size - 3]!
        let newOwner := args[args.size - 2]!
        let amount := args[args.size - 1]!
        match nearAccountIdFrame? env oldOwner, nearAccountIdFrame? env newOwner,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) amount),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) amount) with
        | some oldOwner, some newOwner, some amountLo, some amountHi =>
            some (.nearNep141FtTransfer oldOwner newOwner amountLo amountHi)
        | _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nep141FtBurn &&
          e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        let owner := args[args.size - 2]!
        let amount := args[args.size - 1]!
        match nearAccountIdFrame? env owner,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) amount),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) amount) with
        | some owner, some amountLo, some amountHi =>
            some (.nearNep141FtBurn owner amountLo amountHi)
        | _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nep141FtMintMemo &&
          e.getAppArgs.size ≥ 4 then
        let args := e.getAppArgs
        let amount := args[args.size - 2]!
        match staticNatVal? env args[args.size - 4]!,
            nearAccountIdFrame? env args[args.size - 3]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) amount),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) amount) with
        | some memoCapacity, some owner, some amountLo, some amountHi =>
            if ProofForge.Wasm.Near.Codec.nep141MemoCapacityValid memoCapacity then
              (boundedStorageFrame? env memoCapacity args[args.size - 1]!).map fun memo =>
                .nearNep141FtMintMemo memoCapacity owner amountLo amountHi memo
            else none
        | _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nep141FtTransferMemo &&
          e.getAppArgs.size ≥ 5 then
        let args := e.getAppArgs
        let amount := args[args.size - 2]!
        match staticNatVal? env args[args.size - 5]!,
            nearAccountIdFrame? env args[args.size - 4]!,
            nearAccountIdFrame? env args[args.size - 3]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) amount),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) amount) with
        | some memoCapacity, some oldOwner, some newOwner, some amountLo, some amountHi =>
            if ProofForge.Wasm.Near.Codec.nep141MemoCapacityValid memoCapacity then
              (boundedStorageFrame? env memoCapacity args[args.size - 1]!).map fun memo =>
                .nearNep141FtTransferMemo memoCapacity oldOwner newOwner amountLo amountHi memo
            else none
        | _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nep141FtBurnMemo &&
          e.getAppArgs.size ≥ 4 then
        let args := e.getAppArgs
        let amount := args[args.size - 2]!
        match staticNatVal? env args[args.size - 4]!,
            nearAccountIdFrame? env args[args.size - 3]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) amount),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) amount) with
        | some memoCapacity, some owner, some amountLo, some amountHi =>
            if ProofForge.Wasm.Near.Codec.nep141MemoCapacityValid memoCapacity then
              (boundedStorageFrame? env memoCapacity args[args.size - 1]!).map fun memo =>
                .nearNep141FtBurnMemo memoCapacity owner amountLo amountHi memo
            else none
        | _, _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.transferDetached ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.transferReturned) &&
          e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        let amount := args[args.size - 1]!
        let returned := isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.transferReturned
        match staticString? env 64 args[args.size - 2]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) amount),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) amount) with
        | some receiver, some amountLo, some amountHi =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid receiver then
              some (if returned then
                .nearPromiseTransferReturned receiver amountLo amountHi
              else
                .nearPromiseTransferDetached receiver amountLo amountHi)
            else none
        | _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseTransferDetached ||
          isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseTransferReturned) &&
          e.getAppArgs.size ≥ 3 then
        let args := e.getAppArgs
        let returned := isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseTransferReturned
        match staticString? env 64 args[args.size - 3]!,
            val env args[args.size - 2]!, val env args[args.size - 1]! with
        | some receiver, some amountLo, some amountHi =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid receiver then
              some (if returned then
                .nearPromiseTransferReturned receiver amountLo amountHi
              else
                .nearPromiseTransferDetached receiver amountLo amountHi)
            else none
        | _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.transferAccountDetached ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.transferAccountReturned) &&
          e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        let amount := args[args.size - 1]!
        let returned := isConstNamed e
          ``ProofForge.Wasm.Near.Sdk.Promises.transferAccountReturned
        match nearAccountIdFrame? env args[args.size - 2]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) amount),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) amount) with
        | some receiver, some amountLo, some amountHi =>
            if accountTokenLengthAdmissible receiver then
              some (if returned then
                .nearPromiseTransferAccountReturned receiver amountLo amountHi
              else
                .nearPromiseTransferAccountDetached receiver amountLo amountHi)
            else none
        | _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseTransferAccountDetached ||
          isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseTransferAccountReturned) &&
          e.getAppArgs.size ≥ 3 then
        let args := e.getAppArgs
        let returned := isConstNamed e
          ``ProofForge.Wasm.Near.Runtime.promiseTransferAccountReturned
        match nearAccountIdFrame? env args[args.size - 3]!,
            val env args[args.size - 2]!, val env args[args.size - 1]! with
        | some receiver, some amountLo, some amountHi =>
            if accountTokenLengthAdmissible receiver then
              some (if returned then
                .nearPromiseTransferAccountReturned receiver amountLo amountHi
              else
                .nearPromiseTransferAccountDetached receiver amountLo amountHi)
            else none
        | _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.ftOnTransferReturned &&
          e.getAppArgs.size ≥ 4 then
        let args := e.getAppArgs
        let amount := args[args.size - 2]!
        match nearAccountIdFrame? env args[args.size - 4]!,
            nearAccountIdFrame? env args[args.size - 3]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) amount),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) amount),
            nearBoundedMessage64Frame? env args[args.size - 1]! with
        | some receiver, some sender, some amountLo, some amountHi, some message =>
            if accountTokenLengthAdmissible receiver && accountTokenLengthAdmissible sender then
              some (.nearPromiseFtOnTransferReturned receiver sender amountLo amountHi
                message)
            else none
        | _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFtOnTransferReturned &&
          e.getAppArgs.size ≥ 4 then
        let args := e.getAppArgs
        let amount := args[args.size - 2]!
        match nearAccountIdFrame? env args[args.size - 4]!,
            nearAccountIdFrame? env args[args.size - 3]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) amount),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) amount),
            nearBoundedMessage64Frame? env args[args.size - 1]! with
        | some receiver, some sender, some amountLo, some amountHi, some message =>
            if accountTokenLengthAdmissible receiver && accountTokenLengthAdmissible sender then
              some (.nearPromiseFtOnTransferReturned receiver sender amountLo amountHi
                message)
            else none
        | _, _, _, _, _ => none
      else if (isConstNamed e
          ``ProofForge.Wasm.Near.Sdk.Promises.ftOnTransferThenResolveReturned ||
          isConstNamed e
            ``ProofForge.Wasm.Near.Runtime.promiseFtOnTransferThenResolveReturned) &&
          e.getAppArgs.size ≥ 4 then
        let args := e.getAppArgs
        let amount := args[args.size - 2]!
        match nearAccountIdFrame? env args[args.size - 4]!,
            nearAccountIdFrame? env args[args.size - 3]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) amount),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) amount),
            nearBoundedMessage64Frame? env args[args.size - 1]! with
        | some receiver, some sender, some amountLo, some amountHi, some message =>
            if accountTokenLengthAdmissible receiver && accountTokenLengthAdmissible sender then
              some (.nearPromiseFtOnTransferThenResolveReturned receiver sender amountLo amountHi
                message)
            else none
        | _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callThenReturned &&
          e.getAppArgs.size ≥ 11 then
        let args := e.getAppArgs
        let childDeposit := args[args.size - 6]!
        let callbackDeposit := args[args.size - 2]!
        match staticNatVal? env args[args.size - 11]!,
            staticNatVal? env args[args.size - 10]!,
            staticString? env 64 args[args.size - 9]!,
            staticString? env 64 args[args.size - 8]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) childDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) childDeposit),
            val env args[args.size - 5]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) callbackDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) callbackDeposit),
            val env args[args.size - 1]! with
        | some childArgsCapacity, some callbackArgsCapacity,
            some receiver, some childMethod, some callbackMethod,
            some childDepositLo, some childDepositHi, some childGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid receiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid childMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid childArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env childArgsCapacity args[args.size - 7]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 3]! with
              | some childArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallThenReturned receiver childMethod callbackMethod
                    childArgsCapacity callbackArgsCapacity childArguments callbackArguments
                    childDepositLo childDepositHi childGas
                    callbackDepositLo callbackDepositHi callbackGas)
              | _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callAndThenReturned &&
          e.getAppArgs.size ≥ 17 then
        let args := e.getAppArgs
        let leftDeposit := args[args.size - 11]!
        let rightDeposit := args[args.size - 6]!
        let callbackDeposit := args[args.size - 2]!
        match staticNatVal? env args[args.size - 17]!,
            staticNatVal? env args[args.size - 16]!,
            staticNatVal? env args[args.size - 15]!,
            staticString? env 64 args[args.size - 14]!,
            staticString? env 64 args[args.size - 13]!,
            staticString? env 64 args[args.size - 9]!,
            staticString? env 64 args[args.size - 8]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) leftDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) leftDeposit),
            val env args[args.size - 10]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) rightDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) rightDeposit),
            val env args[args.size - 5]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) callbackDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) callbackDeposit),
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some rightArgsCapacity, some callbackArgsCapacity,
            some leftReceiver, some leftMethod, some rightReceiver, some rightMethod,
            some callbackMethod, some leftDepositLo, some leftDepositHi, some leftGas,
            some rightDepositLo, some rightDepositHi, some rightGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 12]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 7]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 3]! with
              | some leftArguments, some rightArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallAndThenReturned
                    leftReceiver leftMethod rightReceiver rightMethod callbackMethod
                    leftArgsCapacity rightArgsCapacity callbackArgsCapacity
                    leftArguments rightArguments callbackArguments
                    leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
                    callbackDepositLo callbackDepositHi callbackGas)
              | _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callAnd3ThenReturned &&
          e.getAppArgs.size ≥ 23 then
        let args := e.getAppArgs
        let leftDeposit := args[args.size - 16]!
        let midDeposit := args[args.size - 11]!
        let rightDeposit := args[args.size - 6]!
        let callbackDeposit := args[args.size - 2]!
        match staticNatVal? env args[args.size - 23]!,
            staticNatVal? env args[args.size - 22]!,
            staticNatVal? env args[args.size - 21]!,
            staticNatVal? env args[args.size - 20]!,
            staticString? env 64 args[args.size - 19]!,
            staticString? env 64 args[args.size - 18]!,
            staticString? env 64 args[args.size - 14]!,
            staticString? env 64 args[args.size - 13]!,
            staticString? env 64 args[args.size - 9]!,
            staticString? env 64 args[args.size - 8]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) leftDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) leftDeposit),
            val env args[args.size - 15]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) midDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) midDeposit),
            val env args[args.size - 10]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) rightDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) rightDeposit),
            val env args[args.size - 5]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) callbackDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) callbackDeposit),
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some callbackArgsCapacity, some leftReceiver, some leftMethod, some midReceiver,
            some midMethod, some rightReceiver, some rightMethod, some callbackMethod,
            some leftDepositLo, some leftDepositHi, some leftGas, some midDepositLo,
            some midDepositHi, some midGas, some rightDepositLo, some rightDepositHi,
            some rightGas, some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 17]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 12]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 7]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 3]! with
              | some leftArguments, some midArguments, some rightArguments,
                  some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd3ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                      callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity
                      callbackArgsCapacity leftArguments midArguments rightArguments
                      callbackArguments leftDepositLo leftDepositHi leftGas midDepositLo
                      midDepositHi midGas rightDepositLo rightDepositHi rightGas
                      callbackDepositLo callbackDepositHi callbackGas)
              | _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.thenReturned &&
          e.getAppArgs.size ≥ 13 then
        let args := e.getAppArgs
        let childDeposit := args[args.size - 6]!
        let callbackDeposit := args[args.size - 2]!
        match staticNatVal? env args[args.size - 12]!,
            staticNatVal? env args[args.size - 11]!,
            staticString? env 64 args[args.size - 9]!,
            staticString? env 64 args[args.size - 8]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) childDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) childDeposit),
            val env args[args.size - 5]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) callbackDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) callbackDeposit),
            val env args[args.size - 1]! with
        | some childArgsCapacity, some callbackArgsCapacity,
            some receiver, some childMethod, some callbackMethod,
            some childDepositLo, some childDepositHi, some childGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid receiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid childMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid childArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env childArgsCapacity args[args.size - 7]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 3]! with
              | some childArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallThenReturned receiver childMethod callbackMethod
                    childArgsCapacity callbackArgsCapacity childArguments callbackArguments
                    childDepositLo childDepositHi childGas
                    callbackDepositLo callbackDepositHi callbackGas)
              | _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and3Returned &&
          e.getAppArgs.size ≥ 25 then
        let args := e.getAppArgs
        let leftDeposit := args[args.size - 16]!
        let midDeposit := args[args.size - 11]!
        let rightDeposit := args[args.size - 6]!
        let callbackDeposit := args[args.size - 2]!
        match staticNatVal? env args[args.size - 24]!,
            staticNatVal? env args[args.size - 23]!,
            staticNatVal? env args[args.size - 22]!,
            staticNatVal? env args[args.size - 21]!,
            staticString? env 64 args[args.size - 19]!,
            staticString? env 64 args[args.size - 18]!,
            staticString? env 64 args[args.size - 14]!,
            staticString? env 64 args[args.size - 13]!,
            staticString? env 64 args[args.size - 9]!,
            staticString? env 64 args[args.size - 8]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) leftDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) leftDeposit),
            val env args[args.size - 15]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) midDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) midDeposit),
            val env args[args.size - 10]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) rightDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) rightDeposit),
            val env args[args.size - 5]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) callbackDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) callbackDeposit),
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some callbackArgsCapacity, some leftReceiver, some leftMethod, some midReceiver,
            some midMethod, some rightReceiver, some rightMethod, some callbackMethod,
            some leftDepositLo, some leftDepositHi, some leftGas, some midDepositLo,
            some midDepositHi, some midGas, some rightDepositLo, some rightDepositHi,
            some rightGas, some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 17]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 12]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 7]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 3]! with
              | some leftArguments, some midArguments, some rightArguments,
                  some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd3ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                      callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity
                      callbackArgsCapacity leftArguments midArguments rightArguments
                      callbackArguments leftDepositLo leftDepositHi leftGas midDepositLo
                      midDepositHi midGas rightDepositLo rightDepositHi rightGas
                      callbackDepositLo callbackDepositHi callbackGas)
              | _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and4Returned &&
          e.getAppArgs.size ≥ 31 then
        let args := e.getAppArgs
        let leftDeposit := args[args.size - 21]!
        let midDeposit := args[args.size - 16]!
        let rightDeposit := args[args.size - 11]!
        let fourthDeposit := args[args.size - 6]!
        let callbackDeposit := args[args.size - 2]!
        match staticNatVal? env args[args.size - 30]!,
            staticNatVal? env args[args.size - 29]!,
            staticNatVal? env args[args.size - 28]!,
            staticNatVal? env args[args.size - 27]!,
            staticNatVal? env args[args.size - 26]!,
            staticString? env 64 args[args.size - 24]!,
            staticString? env 64 args[args.size - 23]!,
            staticString? env 64 args[args.size - 19]!,
            staticString? env 64 args[args.size - 18]!,
            staticString? env 64 args[args.size - 14]!,
            staticString? env 64 args[args.size - 13]!,
            staticString? env 64 args[args.size - 9]!,
            staticString? env 64 args[args.size - 8]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) leftDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) leftDeposit),
            val env args[args.size - 20]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) midDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) midDeposit),
            val env args[args.size - 15]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) rightDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) rightDeposit),
            val env args[args.size - 10]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) fourthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) fourthDeposit),
            val env args[args.size - 5]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) callbackDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) callbackDeposit),
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some fourthArgsCapacity, some callbackArgsCapacity, some leftReceiver, some leftMethod,
            some midReceiver, some midMethod, some rightReceiver, some rightMethod,
            some fourthReceiver, some fourthMethod, some callbackMethod,
            some leftDepositLo, some leftDepositHi, some leftGas, some midDepositLo,
            some midDepositHi, some midGas, some rightDepositLo, some rightDepositHi,
            some rightGas, some fourthDepositLo, some fourthDepositHi, some fourthGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fourthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fourthMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fourthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 22]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 17]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 12]!,
                  boundedStorageFrame? env fourthArgsCapacity args[args.size - 7]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 3]! with
              | some leftArguments, some midArguments, some rightArguments, some fourthArguments,
                  some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd4ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                      fourthReceiver fourthMethod callbackMethod leftArgsCapacity midArgsCapacity
                      rightArgsCapacity fourthArgsCapacity callbackArgsCapacity leftArguments
                      midArguments rightArguments fourthArguments callbackArguments leftDepositLo
                      leftDepositHi leftGas midDepositLo midDepositHi midGas rightDepositLo
                      rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
                      callbackDepositLo callbackDepositHi callbackGas)
              | _, _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and5Returned &&
          e.getAppArgs.size ≥ 37 then
        let args := e.getAppArgs
        let leftDeposit := args[args.size - 26]!
        let midDeposit := args[args.size - 21]!
        let rightDeposit := args[args.size - 16]!
        let fourthDeposit := args[args.size - 11]!
        let fifthDeposit := args[args.size - 6]!
        let callbackDeposit := args[args.size - 2]!
        match staticNatVal? env args[args.size - 36]!,
            staticNatVal? env args[args.size - 35]!,
            staticNatVal? env args[args.size - 34]!,
            staticNatVal? env args[args.size - 33]!,
            staticNatVal? env args[args.size - 32]!,
            staticNatVal? env args[args.size - 31]!,
            staticString? env 64 args[args.size - 29]!,
            staticString? env 64 args[args.size - 28]!,
            staticString? env 64 args[args.size - 24]!,
            staticString? env 64 args[args.size - 23]!,
            staticString? env 64 args[args.size - 19]!,
            staticString? env 64 args[args.size - 18]!,
            staticString? env 64 args[args.size - 14]!,
            staticString? env 64 args[args.size - 13]!,
            staticString? env 64 args[args.size - 9]!,
            staticString? env 64 args[args.size - 8]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) leftDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) leftDeposit),
            val env args[args.size - 25]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) midDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) midDeposit),
            val env args[args.size - 20]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) rightDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) rightDeposit),
            val env args[args.size - 15]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) fourthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) fourthDeposit),
            val env args[args.size - 10]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) fifthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) fifthDeposit),
            val env args[args.size - 5]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) callbackDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) callbackDeposit),
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some fourthArgsCapacity, some fifthArgsCapacity, some callbackArgsCapacity,
            some leftReceiver, some leftMethod, some midReceiver, some midMethod,
            some rightReceiver, some rightMethod, some fourthReceiver, some fourthMethod,
            some fifthReceiver, some fifthMethod, some callbackMethod,
            some leftDepositLo, some leftDepositHi, some leftGas, some midDepositLo,
            some midDepositHi, some midGas, some rightDepositLo, some rightDepositHi,
            some rightGas, some fourthDepositLo, some fourthDepositHi, some fourthGas,
            some fifthDepositLo, some fifthDepositHi, some fifthGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fourthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fourthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fifthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fifthMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fourthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fifthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 27]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 22]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 17]!,
                  boundedStorageFrame? env fourthArgsCapacity args[args.size - 12]!,
                  boundedStorageFrame? env fifthArgsCapacity args[args.size - 7]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 3]! with
              | some leftArguments, some midArguments, some rightArguments, some fourthArguments,
                  some fifthArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd5ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                      fourthReceiver fourthMethod fifthReceiver fifthMethod callbackMethod
                      leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
                      fifthArgsCapacity callbackArgsCapacity leftArguments midArguments
                      rightArguments fourthArguments fifthArguments callbackArguments leftDepositLo
                      leftDepositHi leftGas midDepositLo midDepositHi midGas rightDepositLo
                      rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
                      fifthDepositLo fifthDepositHi fifthGas callbackDepositLo callbackDepositHi
                      callbackGas)
              | _, _, _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and6Returned &&
          e.getAppArgs.size ≥ 43 then
        let args := e.getAppArgs
        let leftDeposit := args[args.size - 31]!
        let midDeposit := args[args.size - 26]!
        let rightDeposit := args[args.size - 21]!
        let fourthDeposit := args[args.size - 16]!
        let fifthDeposit := args[args.size - 11]!
        let sixthDeposit := args[args.size - 6]!
        let callbackDeposit := args[args.size - 2]!
        match staticNatVal? env args[args.size - 36]!,
            staticNatVal? env args[args.size - 36]!,
            staticNatVal? env args[args.size - 36]!,
            staticNatVal? env args[args.size - 36]!,
            staticNatVal? env args[args.size - 36]!,
            staticNatVal? env args[args.size - 36]!,
            staticNatVal? env args[args.size - 36]!,
            staticString? env 64 args[args.size - 33]!,
            staticString? env 64 args[args.size - 33]!,
            staticString? env 64 args[args.size - 28]!,
            staticString? env 64 args[args.size - 28]!,
            staticString? env 64 args[args.size - 23]!,
            staticString? env 64 args[args.size - 23]!,
            staticString? env 64 args[args.size - 18]!,
            staticString? env 64 args[args.size - 18]!,
            staticString? env 64 args[args.size - 13]!,
            staticString? env 64 args[args.size - 13]!,
            staticString? env 64 args[args.size - 8]!,
            staticString? env 64 args[args.size - 8]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) leftDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) leftDeposit),
            val env args[args.size - 30]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) midDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) midDeposit),
            val env args[args.size - 25]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) rightDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) rightDeposit),
            val env args[args.size - 20]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) fourthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) fourthDeposit),
            val env args[args.size - 15]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) fifthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) fifthDeposit),
            val env args[args.size - 10]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) sixthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) sixthDeposit),
            val env args[args.size - 5]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) callbackDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) callbackDeposit),
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some fourthArgsCapacity, some fifthArgsCapacity, some sixthArgsCapacity,
            some callbackArgsCapacity, some leftReceiver, some leftMethod, some midReceiver,
            some midMethod, some rightReceiver, some rightMethod, some fourthReceiver,
            some fourthMethod, some fifthReceiver, some fifthMethod, some sixthReceiver,
            some sixthMethod, some callbackMethod, some leftDepositLo, some leftDepositHi,
            some leftGas, some midDepositLo, some midDepositHi, some midGas, some rightDepositLo,
            some rightDepositHi, some rightGas, some fourthDepositLo, some fourthDepositHi,
            some fourthGas, some fifthDepositLo, some fifthDepositHi, some fifthGas,
            some sixthDepositLo, some sixthDepositHi, some sixthGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fourthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fourthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fifthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fifthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid sixthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid sixthMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fourthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fifthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid sixthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 32]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 27]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 22]!,
                  boundedStorageFrame? env fourthArgsCapacity args[args.size - 17]!,
                  boundedStorageFrame? env fifthArgsCapacity args[args.size - 12]!,
                  boundedStorageFrame? env sixthArgsCapacity args[args.size - 7]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 3]! with
              | some leftArguments, some midArguments, some rightArguments, some fourthArguments,
                  some fifthArguments, some sixthArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd6ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                      fourthReceiver fourthMethod fifthReceiver fifthMethod sixthReceiver sixthMethod
                      callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
                      fifthArgsCapacity sixthArgsCapacity callbackArgsCapacity leftArguments midArguments
                      rightArguments fourthArguments fifthArguments sixthArguments callbackArguments
                      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas rightDepositLo
                      rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas fifthDepositLo
                      fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas callbackDepositLo
                      callbackDepositHi callbackGas)
              | _, _, _, _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none

      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and7Returned &&
          e.getAppArgs.size ≥ 48 then
        let args := e.getAppArgs
        find fuel'
          (mkAppN (mkConst ``ProofForge.Wasm.Near.Sdk.Promises.callAnd7ThenReturned)
            (args.extract 1 9 ++ args.extract 10 args.size))
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle.and8Returned &&
          e.getAppArgs.size ≥ 55 then
        let args := e.getAppArgs
        -- Layout: maxFanIn, 9 capacity Nats, handle, then callAnd8 business args.
        -- Force `@[pf_inline]` unfold to Runtime: a 53-arg `callAnd8ThenReturned` hits the
        -- SDK decoder (size ≥ 53) which returns `none` on match failure and never falls
        -- through. and7 accidentally avoids this because its delegated size is 47 < 48.
        let delegated :=
          mkAppN (mkConst ``ProofForge.Wasm.Near.Sdk.Promises.callAnd8ThenReturned)
            (args.extract 1 10 ++ args.extract 11 args.size)
        match unfoldUserHelper env delegated with
        | some (_, unfolded) => find fuel' unfolded
        | none => find fuel' delegated
      else if (isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callDetached ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callReturned) &&
          e.getAppArgs.size ≥ 6 then
        let args := e.getAppArgs
        let deposit := args[args.size - 2]!
        let returned := isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callReturned
        match staticNatVal? env args[args.size - 6]!,
            staticString? env 64 args[args.size - 5]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) deposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) deposit),
            val env args[args.size - 1]! with
        | some argsCapacity, some receiver, some method, some depositLo, some depositHi, some gas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid receiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid method &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid argsCapacity then
              (boundedStorageFrame? env argsCapacity args[args.size - 3]!).map fun arguments =>
                if returned then
                  .nearPromiseFunctionCallReturned receiver method argsCapacity arguments
                    depositLo depositHi gas
                else
                  .nearPromiseFunctionCallDetached receiver method argsCapacity arguments
                    depositLo depositHi gas
            else none
        | _, _, _, _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallDetached ||
          isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallReturned) &&
          e.getAppArgs.size ≥ 7 then
        let args := e.getAppArgs
        let returned := isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallReturned
        match staticNatVal? env args[args.size - 7]!,
            staticString? env 64 args[args.size - 6]!,
            staticString? env 64 args[args.size - 5]!,
            val env args[args.size - 3]!, val env args[args.size - 2]!,
            val env args[args.size - 1]! with
        | some argsCapacity, some receiver, some method, some depositLo, some depositHi, some gas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid receiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid method &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid argsCapacity then
              (boundedStorageFrame? env argsCapacity args[args.size - 4]!).map fun arguments =>
                if returned then
                  .nearPromiseFunctionCallReturned receiver method argsCapacity arguments
                    depositLo depositHi gas
                else
                  .nearPromiseFunctionCallDetached receiver method argsCapacity arguments
                    depositLo depositHi gas
            else none
        | _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callAnd4ThenReturned &&
          e.getAppArgs.size ≥ 29 then
        let args := e.getAppArgs
        let leftDeposit := args[args.size - 21]!
        let midDeposit := args[args.size - 16]!
        let rightDeposit := args[args.size - 11]!
        let fourthDeposit := args[args.size - 6]!
        let callbackDeposit := args[args.size - 2]!
        match staticNatVal? env args[args.size - 29]!,
            staticNatVal? env args[args.size - 28]!,
            staticNatVal? env args[args.size - 27]!,
            staticNatVal? env args[args.size - 26]!,
            staticNatVal? env args[args.size - 25]!,
            staticString? env 64 args[args.size - 24]!,
            staticString? env 64 args[args.size - 23]!,
            staticString? env 64 args[args.size - 19]!,
            staticString? env 64 args[args.size - 18]!,
            staticString? env 64 args[args.size - 14]!,
            staticString? env 64 args[args.size - 13]!,
            staticString? env 64 args[args.size - 9]!,
            staticString? env 64 args[args.size - 8]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) leftDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) leftDeposit),
            val env args[args.size - 20]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) midDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) midDeposit),
            val env args[args.size - 15]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) rightDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) rightDeposit),
            val env args[args.size - 10]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) fourthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) fourthDeposit),
            val env args[args.size - 5]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) callbackDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) callbackDeposit),
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some fourthArgsCapacity, some callbackArgsCapacity, some leftReceiver, some leftMethod,
            some midReceiver, some midMethod, some rightReceiver, some rightMethod,
            some fourthReceiver, some fourthMethod, some callbackMethod,
            some leftDepositLo, some leftDepositHi, some leftGas, some midDepositLo,
            some midDepositHi, some midGas, some rightDepositLo, some rightDepositHi,
            some rightGas, some fourthDepositLo, some fourthDepositHi, some fourthGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fourthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fourthMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fourthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 22]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 17]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 12]!,
                  boundedStorageFrame? env fourthArgsCapacity args[args.size - 7]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 3]! with
              | some leftArguments, some midArguments, some rightArguments, some fourthArguments,
                  some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd4ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                      fourthReceiver fourthMethod callbackMethod leftArgsCapacity midArgsCapacity
                      rightArgsCapacity fourthArgsCapacity callbackArgsCapacity leftArguments
                      midArguments rightArguments fourthArguments callbackArguments leftDepositLo
                      leftDepositHi leftGas midDepositLo midDepositHi midGas rightDepositLo
                      rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
                      callbackDepositLo callbackDepositHi callbackGas)
              | _, _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callAnd5ThenReturned &&
          e.getAppArgs.size ≥ 35 then
        let args := e.getAppArgs
        let leftDeposit := args[args.size - 26]!
        let midDeposit := args[args.size - 21]!
        let rightDeposit := args[args.size - 16]!
        let fourthDeposit := args[args.size - 11]!
        let fifthDeposit := args[args.size - 6]!
        let callbackDeposit := args[args.size - 2]!
        match staticNatVal? env args[args.size - 35]!,
            staticNatVal? env args[args.size - 34]!,
            staticNatVal? env args[args.size - 33]!,
            staticNatVal? env args[args.size - 32]!,
            staticNatVal? env args[args.size - 31]!,
            staticNatVal? env args[args.size - 30]!,
            staticString? env 64 args[args.size - 29]!,
            staticString? env 64 args[args.size - 28]!,
            staticString? env 64 args[args.size - 24]!,
            staticString? env 64 args[args.size - 23]!,
            staticString? env 64 args[args.size - 19]!,
            staticString? env 64 args[args.size - 18]!,
            staticString? env 64 args[args.size - 14]!,
            staticString? env 64 args[args.size - 13]!,
            staticString? env 64 args[args.size - 9]!,
            staticString? env 64 args[args.size - 8]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) leftDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) leftDeposit),
            val env args[args.size - 25]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) midDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) midDeposit),
            val env args[args.size - 20]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) rightDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) rightDeposit),
            val env args[args.size - 15]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) fourthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) fourthDeposit),
            val env args[args.size - 10]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) fifthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) fifthDeposit),
            val env args[args.size - 5]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) callbackDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) callbackDeposit),
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some fourthArgsCapacity, some fifthArgsCapacity, some callbackArgsCapacity,
            some leftReceiver, some leftMethod, some midReceiver, some midMethod,
            some rightReceiver, some rightMethod, some fourthReceiver, some fourthMethod,
            some fifthReceiver, some fifthMethod, some callbackMethod,
            some leftDepositLo, some leftDepositHi, some leftGas, some midDepositLo,
            some midDepositHi, some midGas, some rightDepositLo, some rightDepositHi,
            some rightGas, some fourthDepositLo, some fourthDepositHi, some fourthGas,
            some fifthDepositLo, some fifthDepositHi, some fifthGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fourthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fourthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fifthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fifthMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fourthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fifthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 27]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 22]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 17]!,
                  boundedStorageFrame? env fourthArgsCapacity args[args.size - 12]!,
                  boundedStorageFrame? env fifthArgsCapacity args[args.size - 7]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 3]! with
              | some leftArguments, some midArguments, some rightArguments, some fourthArguments,
                  some fifthArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd5ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                      fourthReceiver fourthMethod fifthReceiver fifthMethod callbackMethod
                      leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
                      fifthArgsCapacity callbackArgsCapacity leftArguments midArguments
                      rightArguments fourthArguments fifthArguments callbackArguments leftDepositLo
                      leftDepositHi leftGas midDepositLo midDepositHi midGas rightDepositLo
                      rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
                      fifthDepositLo fifthDepositHi fifthGas callbackDepositLo callbackDepositHi
                      callbackGas)
              | _, _, _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callAnd6ThenReturned &&
          e.getAppArgs.size ≥ 42 then
        let args := e.getAppArgs
        let leftDeposit := args[args.size - 32]!
        let midDeposit := args[args.size - 27]!
        let rightDeposit := args[args.size - 22]!
        let fourthDeposit := args[args.size - 17]!
        let fifthDeposit := args[args.size - 12]!
        let sixthDeposit := args[args.size - 7]!
        let callbackDeposit := args[args.size - 2]!
        match staticNatVal? env args[args.size - 42]!,
            staticNatVal? env args[args.size - 41]!,
            staticNatVal? env args[args.size - 40]!,
            staticNatVal? env args[args.size - 39]!,
            staticNatVal? env args[args.size - 38]!,
            staticNatVal? env args[args.size - 37]!,
            staticNatVal? env args[args.size - 36]!,
            staticString? env 64 args[args.size - 35]!,
            staticString? env 64 args[args.size - 34]!,
            staticString? env 64 args[args.size - 30]!,
            staticString? env 64 args[args.size - 29]!,
            staticString? env 64 args[args.size - 25]!,
            staticString? env 64 args[args.size - 24]!,
            staticString? env 64 args[args.size - 20]!,
            staticString? env 64 args[args.size - 19]!,
            staticString? env 64 args[args.size - 15]!,
            staticString? env 64 args[args.size - 14]!,
            staticString? env 64 args[args.size - 10]!,
            staticString? env 64 args[args.size - 9]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) leftDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) leftDeposit),
            val env args[args.size - 31]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) midDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) midDeposit),
            val env args[args.size - 26]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) rightDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) rightDeposit),
            val env args[args.size - 21]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) fourthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) fourthDeposit),
            val env args[args.size - 16]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) fifthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) fifthDeposit),
            val env args[args.size - 11]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) sixthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) sixthDeposit),
            val env args[args.size - 6]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) callbackDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) callbackDeposit),
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some fourthArgsCapacity, some fifthArgsCapacity, some sixthArgsCapacity,
            some callbackArgsCapacity, some leftReceiver, some leftMethod, some midReceiver,
            some midMethod, some rightReceiver, some rightMethod, some fourthReceiver,
            some fourthMethod, some fifthReceiver, some fifthMethod, some sixthReceiver,
            some sixthMethod, some callbackMethod, some leftDepositLo, some leftDepositHi,
            some leftGas, some midDepositLo, some midDepositHi, some midGas, some rightDepositLo,
            some rightDepositHi, some rightGas, some fourthDepositLo, some fourthDepositHi,
            some fourthGas, some fifthDepositLo, some fifthDepositHi, some fifthGas,
            some sixthDepositLo, some sixthDepositHi, some sixthGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fourthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fourthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fifthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fifthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid sixthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid sixthMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fourthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fifthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid sixthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 33]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 28]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 23]!,
                  boundedStorageFrame? env fourthArgsCapacity args[args.size - 18]!,
                  boundedStorageFrame? env fifthArgsCapacity args[args.size - 13]!,
                  boundedStorageFrame? env sixthArgsCapacity args[args.size - 8]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 3]! with
              | some leftArguments, some midArguments, some rightArguments, some fourthArguments,
                  some fifthArguments, some sixthArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd6ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                      fourthReceiver fourthMethod fifthReceiver fifthMethod sixthReceiver sixthMethod
                      callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
                      fifthArgsCapacity sixthArgsCapacity callbackArgsCapacity leftArguments midArguments
                      rightArguments fourthArguments fifthArguments sixthArguments callbackArguments
                      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas rightDepositLo
                      rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas fifthDepositLo
                      fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas callbackDepositLo
                      callbackDepositHi callbackGas)
              | _, _, _, _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callAnd7ThenReturned &&
          e.getAppArgs.size ≥ 48 then
        let args := e.getAppArgs
        let leftDeposit := args[args.size - 37]!
        let midDeposit := args[args.size - 32]!
        let rightDeposit := args[args.size - 27]!
        let fourthDeposit := args[args.size - 22]!
        let fifthDeposit := args[args.size - 17]!
        let sixthDeposit := args[args.size - 13]!
        let seventhDeposit := args[args.size - 6]!
        let callbackDeposit := args[args.size - 2]!
        match staticNatVal? env args[args.size - 48]!,
            staticNatVal? env args[args.size - 47]!,
            staticNatVal? env args[args.size - 46]!,
            staticNatVal? env args[args.size - 45]!,
            staticNatVal? env args[args.size - 44]!,
            staticNatVal? env args[args.size - 43]!,
            staticNatVal? env args[args.size - 42]!,
            staticNatVal? env args[args.size - 41]!,
            staticString? env 64 args[args.size - 40]!,
            staticString? env 64 args[args.size - 39]!,
            staticString? env 64 args[args.size - 35]!,
            staticString? env 64 args[args.size - 34]!,
            staticString? env 64 args[args.size - 30]!,
            staticString? env 64 args[args.size - 29]!,
            staticString? env 64 args[args.size - 25]!,
            staticString? env 64 args[args.size - 24]!,
            staticString? env 64 args[args.size - 20]!,
            staticString? env 64 args[args.size - 19]!,
            staticString? env 64 args[args.size - 15]!,
            staticString? env 64 args[args.size - 14]!,
            staticString? env 64 args[args.size - 9]!,
            staticString? env 64 args[args.size - 8]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) leftDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) leftDeposit),
            val env args[args.size - 36]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) midDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) midDeposit),
            val env args[args.size - 31]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) rightDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) rightDeposit),
            val env args[args.size - 26]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) fourthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) fourthDeposit),
            val env args[args.size - 21]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) fifthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) fifthDeposit),
            val env args[args.size - 16]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) sixthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) sixthDeposit),
            val env args[args.size - 12]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) seventhDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) seventhDeposit),
            val env args[args.size - 5]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) callbackDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) callbackDeposit),
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some fourthArgsCapacity, some fifthArgsCapacity, some sixthArgsCapacity,
            some seventhArgsCapacity, some callbackArgsCapacity, some leftReceiver, some leftMethod,
            some midReceiver, some midMethod, some rightReceiver, some rightMethod, some fourthReceiver,
            some fourthMethod, some fifthReceiver, some fifthMethod, some sixthReceiver,
            some sixthMethod, some seventhReceiver, some seventhMethod, some callbackMethod,
            some leftDepositLo, some leftDepositHi, some leftGas, some midDepositLo, some midDepositHi,
            some midGas, some rightDepositLo, some rightDepositHi, some rightGas, some fourthDepositLo,
            some fourthDepositHi, some fourthGas, some fifthDepositLo, some fifthDepositHi, some fifthGas,
            some sixthDepositLo, some sixthDepositHi, some sixthGas, some seventhDepositLo,
            some seventhDepositHi, some seventhGas, some callbackDepositLo, some callbackDepositHi,
            some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fourthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fourthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fifthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fifthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid sixthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid sixthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid seventhReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid seventhMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fourthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fifthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid sixthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid seventhArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 39]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 34]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 29]!,
                  boundedStorageFrame? env fourthArgsCapacity args[args.size - 24]!,
                  boundedStorageFrame? env fifthArgsCapacity args[args.size - 19]!,
                  boundedStorageFrame? env sixthArgsCapacity args[args.size - 14]!,
                  boundedStorageFrame? env seventhArgsCapacity args[args.size - 7]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 3]! with
              | some leftArguments, some midArguments, some rightArguments, some fourthArguments,
                  some fifthArguments, some sixthArguments, some seventhArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd7ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                      fourthReceiver fourthMethod fifthReceiver fifthMethod sixthReceiver sixthMethod
                      seventhReceiver seventhMethod callbackMethod leftArgsCapacity midArgsCapacity
                      rightArgsCapacity fourthArgsCapacity fifthArgsCapacity sixthArgsCapacity
                      seventhArgsCapacity callbackArgsCapacity leftArguments midArguments rightArguments
                      fourthArguments fifthArguments sixthArguments seventhArguments callbackArguments
                      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas rightDepositLo
                      rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas fifthDepositLo
                      fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas seventhDepositLo
                      seventhDepositHi seventhGas callbackDepositLo callbackDepositHi callbackGas)
              | _, _, _, _, _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callAnd8ThenReturned &&
          e.getAppArgs.size ≥ 53 then
        let args := e.getAppArgs
        let leftDeposit := args[args.size - 41]!
        let midDeposit := args[args.size - 36]!
        let rightDeposit := args[args.size - 31]!
        let fourthDeposit := args[args.size - 26]!
        let fifthDeposit := args[args.size - 21]!
        let sixthDeposit := args[args.size - 16]!
        let seventhDeposit := args[args.size - 11]!
        let eighthDeposit := args[args.size - 6]!
        let callbackDeposit := args[args.size - 2]!
        match staticNatVal? env args[args.size - 53]!,
            staticNatVal? env args[args.size - 52]!,
            staticNatVal? env args[args.size - 51]!,
            staticNatVal? env args[args.size - 50]!,
            staticNatVal? env args[args.size - 49]!,
            staticNatVal? env args[args.size - 48]!,
            staticNatVal? env args[args.size - 47]!,
            staticNatVal? env args[args.size - 46]!,
            staticNatVal? env args[args.size - 45]!,
            staticString? env 64 args[args.size - 44]!,
            staticString? env 64 args[args.size - 43]!,
            staticString? env 64 args[args.size - 39]!,
            staticString? env 64 args[args.size - 38]!,
            staticString? env 64 args[args.size - 34]!,
            staticString? env 64 args[args.size - 33]!,
            staticString? env 64 args[args.size - 29]!,
            staticString? env 64 args[args.size - 28]!,
            staticString? env 64 args[args.size - 24]!,
            staticString? env 64 args[args.size - 23]!,
            staticString? env 64 args[args.size - 19]!,
            staticString? env 64 args[args.size - 18]!,
            staticString? env 64 args[args.size - 14]!,
            staticString? env 64 args[args.size - 13]!,
            staticString? env 64 args[args.size - 9]!,
            staticString? env 64 args[args.size - 8]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) leftDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) leftDeposit),
            val env args[args.size - 40]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) midDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) midDeposit),
            val env args[args.size - 35]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) rightDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) rightDeposit),
            val env args[args.size - 30]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) fourthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) fourthDeposit),
            val env args[args.size - 25]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) fifthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) fifthDeposit),
            val env args[args.size - 20]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) sixthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) sixthDeposit),
            val env args[args.size - 15]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) seventhDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) seventhDeposit),
            val env args[args.size - 10]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) eighthDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) eighthDeposit),
            val env args[args.size - 5]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) callbackDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) callbackDeposit),
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some fourthArgsCapacity, some fifthArgsCapacity, some sixthArgsCapacity,
            some seventhArgsCapacity, some eighthArgsCapacity, some callbackArgsCapacity,
            some leftReceiver, some leftMethod, some midReceiver, some midMethod, some rightReceiver,
            some rightMethod, some fourthReceiver, some fourthMethod, some fifthReceiver,
            some fifthMethod, some sixthReceiver, some sixthMethod, some seventhReceiver,
            some seventhMethod, some eighthReceiver, some eighthMethod, some callbackMethod,
            some leftDepositLo, some leftDepositHi, some leftGas, some midDepositLo, some midDepositHi,
            some midGas, some rightDepositLo, some rightDepositHi, some rightGas, some fourthDepositLo,
            some fourthDepositHi, some fourthGas, some fifthDepositLo, some fifthDepositHi, some fifthGas,
            some sixthDepositLo, some sixthDepositHi, some sixthGas, some seventhDepositLo,
            some seventhDepositHi, some seventhGas, some eighthDepositLo, some eighthDepositHi,
            some eighthGas, some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fourthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fourthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fifthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fifthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid sixthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid sixthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid seventhReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid seventhMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid eighthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid eighthMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fourthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fifthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid sixthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid seventhArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid eighthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 43]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 38]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 33]!,
                  boundedStorageFrame? env fourthArgsCapacity args[args.size - 28]!,
                  boundedStorageFrame? env fifthArgsCapacity args[args.size - 23]!,
                  boundedStorageFrame? env sixthArgsCapacity args[args.size - 18]!,
                  boundedStorageFrame? env seventhArgsCapacity args[args.size - 12]!,
                  boundedStorageFrame? env eighthArgsCapacity args[args.size - 7]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 3]! with
              | some leftArguments, some midArguments, some rightArguments, some fourthArguments,
                  some fifthArguments, some sixthArguments, some seventhArguments, some eighthArguments,
                  some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd8ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                      fourthReceiver fourthMethod fifthReceiver fifthMethod sixthReceiver sixthMethod
                      seventhReceiver seventhMethod eighthReceiver eighthMethod callbackMethod
                      leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
                      fifthArgsCapacity sixthArgsCapacity seventhArgsCapacity eighthArgsCapacity
                      callbackArgsCapacity leftArguments midArguments rightArguments fourthArguments
                      fifthArguments sixthArguments seventhArguments eighthArguments callbackArguments
                      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas rightDepositLo
                      rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas fifthDepositLo
                      fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas seventhDepositLo
                      seventhDepositHi seventhGas eighthDepositLo eighthDepositHi eighthGas callbackDepositLo
                      callbackDepositHi callbackGas)
              | _, _, _, _, _, _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callDetached ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callReturned) &&
          e.getAppArgs.size ≥ 6 then
        let args := e.getAppArgs
        let deposit := args[args.size - 2]!
        let returned := isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callReturned
        match staticNatVal? env args[args.size - 6]!,
            staticString? env 64 args[args.size - 5]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) deposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) deposit),
            val env args[args.size - 1]! with
        | some argsCapacity, some receiver, some method, some depositLo, some depositHi, some gas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid receiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid method &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid argsCapacity then
              (boundedStorageFrame? env argsCapacity args[args.size - 3]!).map fun arguments =>
                if returned then
                  .nearPromiseFunctionCallReturned receiver method argsCapacity arguments
                    depositLo depositHi gas
                else
                  .nearPromiseFunctionCallDetached receiver method argsCapacity arguments
                    depositLo depositHi gas
            else none
        | _, _, _, _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallDetached ||
          isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallReturned) &&
          e.getAppArgs.size ≥ 7 then
        let args := e.getAppArgs
        let returned := isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallReturned
        match staticNatVal? env args[args.size - 7]!,
            staticString? env 64 args[args.size - 6]!,
            staticString? env 64 args[args.size - 5]!,
            val env args[args.size - 3]!, val env args[args.size - 2]!,
            val env args[args.size - 1]! with
        | some argsCapacity, some receiver, some method, some depositLo, some depositHi, some gas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid receiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid method &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid argsCapacity then
              (boundedStorageFrame? env argsCapacity args[args.size - 4]!).map fun arguments =>
                if returned then
                  .nearPromiseFunctionCallReturned receiver method argsCapacity arguments
                    depositLo depositHi gas
                else
                  .nearPromiseFunctionCallDetached receiver method argsCapacity arguments
                    depositLo depositHi gas
            else none
        | _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallThenReturned &&
          e.getAppArgs.size ≥ 13 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 13]!,
            staticNatVal? env args[args.size - 12]!,
            staticString? env 64 args[args.size - 11]!,
            staticString? env 64 args[args.size - 10]!,
            staticString? env 64 args[args.size - 9]!,
            val env args[args.size - 6]!, val env args[args.size - 5]!,
            val env args[args.size - 4]!, val env args[args.size - 3]!,
            val env args[args.size - 2]!, val env args[args.size - 1]! with
        | some childArgsCapacity, some callbackArgsCapacity,
            some receiver, some childMethod, some callbackMethod,
            some childDepositLo, some childDepositHi, some childGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid receiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid childMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid childArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env childArgsCapacity args[args.size - 8]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 7]! with
              | some childArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallThenReturned receiver childMethod callbackMethod
                    childArgsCapacity callbackArgsCapacity childArguments callbackArguments
                    childDepositLo childDepositHi childGas
                    callbackDepositLo callbackDepositHi callbackGas)
              | _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAndThenReturned &&
          e.getAppArgs.size ≥ 20 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 20]!,
            staticNatVal? env args[args.size - 19]!,
            staticNatVal? env args[args.size - 18]!,
            staticString? env 64 args[args.size - 17]!,
            staticString? env 64 args[args.size - 16]!,
            staticString? env 64 args[args.size - 15]!,
            staticString? env 64 args[args.size - 14]!,
            staticString? env 64 args[args.size - 13]!,
            val env args[args.size - 9]!, val env args[args.size - 8]!,
            val env args[args.size - 7]!, val env args[args.size - 6]!,
            val env args[args.size - 5]!, val env args[args.size - 4]!,
            val env args[args.size - 3]!, val env args[args.size - 2]!,
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some rightArgsCapacity, some callbackArgsCapacity,
            some leftReceiver, some leftMethod, some rightReceiver, some rightMethod,
            some callbackMethod, some leftDepositLo, some leftDepositHi, some leftGas,
            some rightDepositLo, some rightDepositHi, some rightGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 12]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 11]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 10]! with
              | some leftArguments, some rightArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallAndThenReturned
                    leftReceiver leftMethod rightReceiver rightMethod callbackMethod
                    leftArgsCapacity rightArgsCapacity callbackArgsCapacity
                    leftArguments rightArguments callbackArguments
                    leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
                    callbackDepositLo callbackDepositHi callbackGas)
              | _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAnd3ThenReturned &&
          e.getAppArgs.size ≥ 27 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 27]!,
            staticNatVal? env args[args.size - 26]!,
            staticNatVal? env args[args.size - 25]!,
            staticNatVal? env args[args.size - 24]!,
            staticString? env 64 args[args.size - 23]!,
            staticString? env 64 args[args.size - 22]!,
            staticString? env 64 args[args.size - 21]!,
            staticString? env 64 args[args.size - 20]!,
            staticString? env 64 args[args.size - 19]!,
            staticString? env 64 args[args.size - 18]!,
            staticString? env 64 args[args.size - 17]!,
            val env args[args.size - 12]!, val env args[args.size - 11]!,
            val env args[args.size - 10]!, val env args[args.size - 9]!,
            val env args[args.size - 8]!, val env args[args.size - 7]!,
            val env args[args.size - 6]!, val env args[args.size - 5]!,
            val env args[args.size - 4]!, val env args[args.size - 3]!,
            val env args[args.size - 2]!, val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some callbackArgsCapacity, some leftReceiver, some leftMethod, some midReceiver,
            some midMethod, some rightReceiver, some rightMethod, some callbackMethod,
            some leftDepositLo, some leftDepositHi, some leftGas, some midDepositLo,
            some midDepositHi, some midGas, some rightDepositLo, some rightDepositHi,
            some rightGas, some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 16]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 15]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 14]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 13]! with
              | some leftArguments, some midArguments, some rightArguments,
                  some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd3ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                    callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity
                    callbackArgsCapacity leftArguments midArguments rightArguments
                    callbackArguments leftDepositLo leftDepositHi leftGas midDepositLo
                    midDepositHi midGas rightDepositLo rightDepositHi rightGas
                    callbackDepositLo callbackDepositHi callbackGas)
              | _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAnd4ThenReturned &&
          e.getAppArgs.size ≥ 34 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 34]!,
            staticNatVal? env args[args.size - 33]!,
            staticNatVal? env args[args.size - 32]!,
            staticNatVal? env args[args.size - 31]!,
            staticNatVal? env args[args.size - 30]!,
            staticString? env 64 args[args.size - 29]!,
            staticString? env 64 args[args.size - 28]!,
            staticString? env 64 args[args.size - 27]!,
            staticString? env 64 args[args.size - 26]!,
            staticString? env 64 args[args.size - 25]!,
            staticString? env 64 args[args.size - 24]!,
            staticString? env 64 args[args.size - 23]!,
            staticString? env 64 args[args.size - 22]!,
            staticString? env 64 args[args.size - 21]!,
            val env args[args.size - 15]!, val env args[args.size - 14]!,
            val env args[args.size - 13]!, val env args[args.size - 12]!,
            val env args[args.size - 11]!, val env args[args.size - 10]!,
            val env args[args.size - 9]!, val env args[args.size - 8]!,
            val env args[args.size - 7]!, val env args[args.size - 6]!,
            val env args[args.size - 5]!, val env args[args.size - 4]!,
            val env args[args.size - 3]!, val env args[args.size - 2]!,
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some fourthArgsCapacity, some callbackArgsCapacity, some leftReceiver, some leftMethod,
            some midReceiver, some midMethod, some rightReceiver, some rightMethod,
            some fourthReceiver, some fourthMethod, some callbackMethod,
            some leftDepositLo, some leftDepositHi, some leftGas, some midDepositLo,
            some midDepositHi, some midGas, some rightDepositLo, some rightDepositHi,
            some rightGas, some fourthDepositLo, some fourthDepositHi, some fourthGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fourthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fourthMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fourthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 20]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 19]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 18]!,
                  boundedStorageFrame? env fourthArgsCapacity args[args.size - 17]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 16]! with
              | some leftArguments, some midArguments, some rightArguments, some fourthArguments,
                  some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd4ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                      fourthReceiver fourthMethod callbackMethod leftArgsCapacity midArgsCapacity
                      rightArgsCapacity fourthArgsCapacity callbackArgsCapacity leftArguments
                      midArguments rightArguments fourthArguments callbackArguments leftDepositLo
                      leftDepositHi leftGas midDepositLo midDepositHi midGas rightDepositLo
                      rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
                      callbackDepositLo callbackDepositHi callbackGas)
              | _, _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAnd5ThenReturned &&
          e.getAppArgs.size ≥ 41 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 41]!,
            staticNatVal? env args[args.size - 40]!,
            staticNatVal? env args[args.size - 39]!,
            staticNatVal? env args[args.size - 38]!,
            staticNatVal? env args[args.size - 37]!,
            staticNatVal? env args[args.size - 36]!,
            staticString? env 64 args[args.size - 35]!,
            staticString? env 64 args[args.size - 34]!,
            staticString? env 64 args[args.size - 33]!,
            staticString? env 64 args[args.size - 32]!,
            staticString? env 64 args[args.size - 31]!,
            staticString? env 64 args[args.size - 30]!,
            staticString? env 64 args[args.size - 29]!,
            staticString? env 64 args[args.size - 28]!,
            staticString? env 64 args[args.size - 27]!,
            staticString? env 64 args[args.size - 26]!,
            staticString? env 64 args[args.size - 25]!,
            val env args[args.size - 18]!, val env args[args.size - 17]!,
            val env args[args.size - 16]!, val env args[args.size - 15]!,
            val env args[args.size - 14]!, val env args[args.size - 13]!,
            val env args[args.size - 12]!, val env args[args.size - 11]!,
            val env args[args.size - 10]!, val env args[args.size - 9]!,
            val env args[args.size - 8]!, val env args[args.size - 7]!,
            val env args[args.size - 6]!, val env args[args.size - 5]!,
            val env args[args.size - 4]!, val env args[args.size - 3]!,
            val env args[args.size - 2]!, val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some fourthArgsCapacity, some fifthArgsCapacity, some callbackArgsCapacity,
            some leftReceiver, some leftMethod, some midReceiver, some midMethod,
            some rightReceiver, some rightMethod, some fourthReceiver, some fourthMethod,
            some fifthReceiver, some fifthMethod, some callbackMethod,
            some leftDepositLo, some leftDepositHi, some leftGas, some midDepositLo,
            some midDepositHi, some midGas, some rightDepositLo, some rightDepositHi,
            some rightGas, some fourthDepositLo, some fourthDepositHi, some fourthGas,
            some fifthDepositLo, some fifthDepositHi, some fifthGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fourthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fourthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fifthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fifthMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fourthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fifthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 24]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 23]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 22]!,
                  boundedStorageFrame? env fourthArgsCapacity args[args.size - 21]!,
                  boundedStorageFrame? env fifthArgsCapacity args[args.size - 20]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 19]! with
              | some leftArguments, some midArguments, some rightArguments, some fourthArguments,
                  some fifthArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd5ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                      fourthReceiver fourthMethod fifthReceiver fifthMethod callbackMethod
                      leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
                      fifthArgsCapacity callbackArgsCapacity leftArguments midArguments
                      rightArguments fourthArguments fifthArguments callbackArguments leftDepositLo
                      leftDepositHi leftGas midDepositLo midDepositHi midGas rightDepositLo
                      rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
                      fifthDepositLo fifthDepositHi fifthGas callbackDepositLo callbackDepositHi
                      callbackGas)
              | _, _, _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAnd6ThenReturned &&
          e.getAppArgs.size ≥ 48 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 48]!,
            staticNatVal? env args[args.size - 47]!,
            staticNatVal? env args[args.size - 46]!,
            staticNatVal? env args[args.size - 45]!,
            staticNatVal? env args[args.size - 44]!,
            staticNatVal? env args[args.size - 43]!,
            staticNatVal? env args[args.size - 42]!,
            staticString? env 64 args[args.size - 41]!,
            staticString? env 64 args[args.size - 40]!,
            staticString? env 64 args[args.size - 39]!,
            staticString? env 64 args[args.size - 38]!,
            staticString? env 64 args[args.size - 37]!,
            staticString? env 64 args[args.size - 36]!,
            staticString? env 64 args[args.size - 35]!,
            staticString? env 64 args[args.size - 34]!,
            staticString? env 64 args[args.size - 33]!,
            staticString? env 64 args[args.size - 32]!,
            staticString? env 64 args[args.size - 31]!,
            staticString? env 64 args[args.size - 30]!,
            staticString? env 64 args[args.size - 29]!,
            val env args[args.size - 21]!, val env args[args.size - 20]!,
            val env args[args.size - 19]!, val env args[args.size - 18]!,
            val env args[args.size - 17]!, val env args[args.size - 16]!,
            val env args[args.size - 15]!, val env args[args.size - 14]!,
            val env args[args.size - 13]!, val env args[args.size - 12]!,
            val env args[args.size - 11]!, val env args[args.size - 10]!,
            val env args[args.size - 9]!, val env args[args.size - 8]!,
            val env args[args.size - 7]!, val env args[args.size - 6]!,
            val env args[args.size - 5]!, val env args[args.size - 4]!,
            val env args[args.size - 3]!, val env args[args.size - 2]!,
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some fourthArgsCapacity, some fifthArgsCapacity, some sixthArgsCapacity,
            some callbackArgsCapacity, some leftReceiver, some leftMethod, some midReceiver,
            some midMethod, some rightReceiver, some rightMethod, some fourthReceiver,
            some fourthMethod, some fifthReceiver, some fifthMethod, some sixthReceiver,
            some sixthMethod, some callbackMethod, some leftDepositLo, some leftDepositHi,
            some leftGas, some midDepositLo, some midDepositHi, some midGas, some rightDepositLo,
            some rightDepositHi, some rightGas, some fourthDepositLo, some fourthDepositHi,
            some fourthGas, some fifthDepositLo, some fifthDepositHi, some fifthGas,
            some sixthDepositLo, some sixthDepositHi, some sixthGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fourthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fourthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fifthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fifthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid sixthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid sixthMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fourthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fifthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid sixthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 28]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 27]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 26]!,
                  boundedStorageFrame? env fourthArgsCapacity args[args.size - 25]!,
                  boundedStorageFrame? env fifthArgsCapacity args[args.size - 24]!,
                  boundedStorageFrame? env sixthArgsCapacity args[args.size - 23]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 22]! with
              | some leftArguments, some midArguments, some rightArguments, some fourthArguments,
                  some fifthArguments, some sixthArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd6ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                      fourthReceiver fourthMethod fifthReceiver fifthMethod sixthReceiver sixthMethod
                      callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
                      fifthArgsCapacity sixthArgsCapacity callbackArgsCapacity leftArguments midArguments
                      rightArguments fourthArguments fifthArguments sixthArguments callbackArguments
                      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas rightDepositLo
                      rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas fifthDepositLo
                      fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas callbackDepositLo
                      callbackDepositHi callbackGas)
              | _, _, _, _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAnd7ThenReturned &&
          e.getAppArgs.size ≥ 55 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 55]!,
            staticNatVal? env args[args.size - 54]!,
            staticNatVal? env args[args.size - 53]!,
            staticNatVal? env args[args.size - 52]!,
            staticNatVal? env args[args.size - 51]!,
            staticNatVal? env args[args.size - 50]!,
            staticNatVal? env args[args.size - 49]!,
            staticNatVal? env args[args.size - 48]!,
            staticString? env 64 args[args.size - 47]!,
            staticString? env 64 args[args.size - 46]!,
            staticString? env 64 args[args.size - 45]!,
            staticString? env 64 args[args.size - 44]!,
            staticString? env 64 args[args.size - 43]!,
            staticString? env 64 args[args.size - 42]!,
            staticString? env 64 args[args.size - 41]!,
            staticString? env 64 args[args.size - 40]!,
            staticString? env 64 args[args.size - 39]!,
            staticString? env 64 args[args.size - 38]!,
            staticString? env 64 args[args.size - 37]!,
            staticString? env 64 args[args.size - 36]!,
            staticString? env 64 args[args.size - 35]!,
            staticString? env 64 args[args.size - 34]!,
            staticString? env 64 args[args.size - 33]!,
            val env args[args.size - 24]!, val env args[args.size - 23]!,
            val env args[args.size - 22]!, val env args[args.size - 21]!,
            val env args[args.size - 20]!, val env args[args.size - 19]!,
            val env args[args.size - 18]!, val env args[args.size - 17]!,
            val env args[args.size - 16]!, val env args[args.size - 15]!,
            val env args[args.size - 14]!, val env args[args.size - 13]!,
            val env args[args.size - 12]!, val env args[args.size - 11]!,
            val env args[args.size - 10]!, val env args[args.size - 9]!,
            val env args[args.size - 8]!, val env args[args.size - 7]!,
            val env args[args.size - 6]!, val env args[args.size - 5]!,
            val env args[args.size - 4]!, val env args[args.size - 3]!,
            val env args[args.size - 2]!, val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some fourthArgsCapacity, some fifthArgsCapacity, some sixthArgsCapacity,
            some seventhArgsCapacity, some callbackArgsCapacity, some leftReceiver, some leftMethod,
            some midReceiver, some midMethod, some rightReceiver, some rightMethod, some fourthReceiver,
            some fourthMethod, some fifthReceiver, some fifthMethod, some sixthReceiver,
            some sixthMethod, some seventhReceiver, some seventhMethod, some callbackMethod,
            some leftDepositLo, some leftDepositHi, some leftGas, some midDepositLo, some midDepositHi,
            some midGas, some rightDepositLo, some rightDepositHi, some rightGas, some fourthDepositLo,
            some fourthDepositHi, some fourthGas, some fifthDepositLo, some fifthDepositHi, some fifthGas,
            some sixthDepositLo, some sixthDepositHi, some sixthGas, some seventhDepositLo,
            some seventhDepositHi, some seventhGas, some callbackDepositLo, some callbackDepositHi,
            some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fourthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fourthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fifthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fifthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid sixthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid sixthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid seventhReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid seventhMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fourthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fifthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid sixthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid seventhArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 32]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 31]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 30]!,
                  boundedStorageFrame? env fourthArgsCapacity args[args.size - 29]!,
                  boundedStorageFrame? env fifthArgsCapacity args[args.size - 28]!,
                  boundedStorageFrame? env sixthArgsCapacity args[args.size - 27]!,
                  boundedStorageFrame? env seventhArgsCapacity args[args.size - 26]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 25]! with
              | some leftArguments, some midArguments, some rightArguments, some fourthArguments,
                  some fifthArguments, some sixthArguments, some seventhArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd7ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                      fourthReceiver fourthMethod fifthReceiver fifthMethod sixthReceiver sixthMethod
                      seventhReceiver seventhMethod callbackMethod leftArgsCapacity midArgsCapacity
                      rightArgsCapacity fourthArgsCapacity fifthArgsCapacity sixthArgsCapacity
                      seventhArgsCapacity callbackArgsCapacity leftArguments midArguments rightArguments
                      fourthArguments fifthArguments sixthArguments seventhArguments callbackArguments
                      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas rightDepositLo
                      rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas fifthDepositLo
                      fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas seventhDepositLo
                      seventhDepositHi seventhGas callbackDepositLo callbackDepositHi callbackGas)
              | _, _, _, _, _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAnd8ThenReturned &&
          e.getAppArgs.size ≥ 62 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 62]!,
            staticNatVal? env args[args.size - 61]!,
            staticNatVal? env args[args.size - 60]!,
            staticNatVal? env args[args.size - 59]!,
            staticNatVal? env args[args.size - 58]!,
            staticNatVal? env args[args.size - 57]!,
            staticNatVal? env args[args.size - 56]!,
            staticNatVal? env args[args.size - 55]!,
            staticNatVal? env args[args.size - 54]!,
            staticString? env 64 args[args.size - 53]!,
            staticString? env 64 args[args.size - 52]!,
            staticString? env 64 args[args.size - 51]!,
            staticString? env 64 args[args.size - 50]!,
            staticString? env 64 args[args.size - 49]!,
            staticString? env 64 args[args.size - 48]!,
            staticString? env 64 args[args.size - 47]!,
            staticString? env 64 args[args.size - 46]!,
            staticString? env 64 args[args.size - 45]!,
            staticString? env 64 args[args.size - 44]!,
            staticString? env 64 args[args.size - 43]!,
            staticString? env 64 args[args.size - 42]!,
            staticString? env 64 args[args.size - 41]!,
            staticString? env 64 args[args.size - 40]!,
            staticString? env 64 args[args.size - 39]!,
            staticString? env 64 args[args.size - 38]!,
            staticString? env 64 args[args.size - 37]!,
            val env args[args.size - 27]!, val env args[args.size - 26]!,
            val env args[args.size - 25]!, val env args[args.size - 24]!,
            val env args[args.size - 23]!, val env args[args.size - 22]!,
            val env args[args.size - 21]!, val env args[args.size - 20]!,
            val env args[args.size - 19]!, val env args[args.size - 18]!,
            val env args[args.size - 17]!, val env args[args.size - 16]!,
            val env args[args.size - 15]!, val env args[args.size - 14]!,
            val env args[args.size - 13]!, val env args[args.size - 12]!,
            val env args[args.size - 11]!, val env args[args.size - 10]!,
            val env args[args.size - 9]!, val env args[args.size - 8]!,
            val env args[args.size - 7]!, val env args[args.size - 6]!,
            val env args[args.size - 5]!, val env args[args.size - 4]!,
            val env args[args.size - 3]!, val env args[args.size - 2]!,
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some midArgsCapacity, some rightArgsCapacity,
            some fourthArgsCapacity, some fifthArgsCapacity, some sixthArgsCapacity,
            some seventhArgsCapacity, some eighthArgsCapacity, some callbackArgsCapacity,
            some leftReceiver, some leftMethod, some midReceiver, some midMethod, some rightReceiver,
            some rightMethod, some fourthReceiver, some fourthMethod, some fifthReceiver,
            some fifthMethod, some sixthReceiver, some sixthMethod, some seventhReceiver,
            some seventhMethod, some eighthReceiver, some eighthMethod, some callbackMethod,
            some leftDepositLo, some leftDepositHi, some leftGas, some midDepositLo, some midDepositHi,
            some midGas, some rightDepositLo, some rightDepositHi, some rightGas, some fourthDepositLo,
            some fourthDepositHi, some fourthGas, some fifthDepositLo, some fifthDepositHi, some fifthGas,
            some sixthDepositLo, some sixthDepositHi, some sixthGas, some seventhDepositLo,
            some seventhDepositHi, some seventhGas, some eighthDepositLo, some eighthDepositHi,
            some eighthGas, some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid midReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid midMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fourthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fourthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid fifthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid fifthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid sixthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid sixthMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid seventhReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid seventhMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid eighthReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid eighthMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid midArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fourthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid fifthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid sixthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid seventhArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid eighthArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 36]!,
                  boundedStorageFrame? env midArgsCapacity args[args.size - 35]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 34]!,
                  boundedStorageFrame? env fourthArgsCapacity args[args.size - 33]!,
                  boundedStorageFrame? env fifthArgsCapacity args[args.size - 32]!,
                  boundedStorageFrame? env sixthArgsCapacity args[args.size - 31]!,
                  boundedStorageFrame? env seventhArgsCapacity args[args.size - 30]!,
                  boundedStorageFrame? env eighthArgsCapacity args[args.size - 29]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 28]! with
              | some leftArguments, some midArguments, some rightArguments, some fourthArguments,
                  some fifthArguments, some sixthArguments, some seventhArguments, some eighthArguments,
                  some callbackArguments =>
                  some (.nearPromiseFunctionCallAnd8ThenReturned
                    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
                      fourthReceiver fourthMethod fifthReceiver fifthMethod sixthReceiver sixthMethod
                      seventhReceiver seventhMethod eighthReceiver eighthMethod callbackMethod
                      leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
                      fifthArgsCapacity sixthArgsCapacity seventhArgsCapacity eighthArgsCapacity
                      callbackArgsCapacity leftArguments midArguments rightArguments fourthArguments
                      fifthArguments sixthArguments seventhArguments eighthArguments callbackArguments
                      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas rightDepositLo
                      rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas fifthDepositLo
                      fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas seventhDepositLo
                      seventhDepositHi seventhGas eighthDepositLo eighthDepositHi eighthGas callbackDepositLo
                      callbackDepositHi callbackGas)
              | _, _, _, _, _, _, _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultRead ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.ResultBuffer.read) &&
          e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 2]!, val env args[args.size - 1]! with
        | some capacity, some index =>
            if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
              some (.nearPromiseResultRead capacity index)
            else none
        | _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.transientBuffer64Begin ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Transient.Buffer64.begin) &&
          e.getAppArgs.size ≥ 1 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 1]! with
        | some capacity =>
            if ProofForge.Wasm.Near.Memory.buffer64CapacityValid capacity then
              some (.nearTransientBuffer64Begin capacity)
            else none
        | none => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.transientBuffer64Set ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Transient.Buffer64.set) &&
          e.getAppArgs.size ≥ 3 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 3]!, val env args[args.size - 2]!,
            val env args[args.size - 1]! with
        | some capacity, some index, some value =>
            if ProofForge.Wasm.Near.Memory.buffer64CapacityValid capacity then
              some (.nearTransientBuffer64Set capacity index value)
            else none
        | _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.transientBuffer64Finish ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Transient.Buffer64.finish) &&
          e.getAppArgs.size ≥ 1 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 1]! with
        | some capacity =>
            if ProofForge.Wasm.Near.Memory.buffer64CapacityValid capacity then
              some (.nearTransientBuffer64Finish capacity)
            else none
        | none => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Sdk.Store.DirectAccountNearTokenMap.read ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Store.DirectAccountNearTokenMap.has ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Store.DirectAccountNearTokenMap.remove) &&
          e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        match staticAccountTokenTag? env 8 args[args.size - 2]!,
            nearAccountIdFrame? env args[args.size - 1]! with
        | some tag, some account =>
            if tag ≤ 0xffffffff && accountTokenLengthAdmissible account then
              let key := accountTokenStorageKeyFrame (.lit (UInt64.ofNat tag)) account
              some (if isConstNamed e
                  ``ProofForge.Wasm.Near.Sdk.Store.DirectAccountNearTokenMap.read then
                .nearStorageRead 16 72 key
              else if isConstNamed e
                  ``ProofForge.Wasm.Near.Sdk.Store.DirectAccountNearTokenMap.has then
                .nearStorageHasKey 16 72 key
              else
                .nearStorageRemove 16 72 key)
            else none
        | _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Store.DirectAccountNearTokenMap.put &&
          e.getAppArgs.size ≥ 3 then
        let args := e.getAppArgs
        let value := args[args.size - 1]!
        let tag? := staticAccountTokenTag? env 8 args[args.size - 3]!
        let account? := nearAccountIdFrame? env args[args.size - 2]!
        let lo? := val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) value)
        let hi? := val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) value)
        match tag?, account?, lo?, hi? with
        | some tag, some account, some lo, some hi =>
            if tag ≤ 0xffffffff && accountTokenLengthAdmissible account then
              some (.nearStorageWrite 16 72 16
                (accountTokenStorageKeyFrame (.lit (UInt64.ofNat tag)) account)
                (nearTokenStorageValueFrame lo hi))
            else none
        | _, _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.sha256Hash ||
          isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak256Hash ||
          isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512Hash ||
          isConstNamed e ``ProofForge.Wasm.Near.Runtime.ripemd160Hash) &&
          e.getAppArgs.size ≥ 3 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 3]!,
            staticNatVal? env args[args.size - 2]! with
        | some resultCapacity, some inputCapacity =>
            if ProofForge.Wasm.Near.Codec.storageCapacityValid resultCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid inputCapacity then
              (boundedStorageFrame? env inputCapacity args[args.size - 1]!).map fun input =>
                if isConstNamed e ``ProofForge.Wasm.Near.Runtime.sha256Hash then
                  .nearSha256Hash resultCapacity inputCapacity input
                else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak256Hash then
                  .nearKeccak256Hash resultCapacity inputCapacity input
                else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.keccak512Hash then
                  .nearKeccak512Hash resultCapacity inputCapacity input
                else
                  .nearRipemd160Hash resultCapacity inputCapacity input
            else none
        | _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.ecrecover &&
          e.getAppArgs.size ≥ 5 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 5]!,
            nearCryptoBytes32Frame? env args[args.size - 4]!,
            nearCryptoBytes64Frame? env args[args.size - 3]!,
            val env args[args.size - 2]!,
            val env args[args.size - 1]! with
        | some resultCapacity, some hash, some sig, some v, some malleability =>
            if resultCapacity == 64 && hash.size == 4 && sig.size == 8 then
              some (.nearEcrecover resultCapacity hash sig v malleability)
            else none
        | _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.ed25519Verify &&
          e.getAppArgs.size ≥ 5 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 5]!,
            staticNatVal? env args[args.size - 4]!,
            nearCryptoBytes64Frame? env args[args.size - 3]!,
            nearCryptoBytes32Frame? env args[args.size - 1]! with
        | some resultCapacity, some msgCapacity, some sig, some pk =>
            if resultCapacity == 8 &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid msgCapacity then
              (boundedStorageFrame? env msgCapacity args[args.size - 2]!).map fun msg =>
                .nearEd25519Verify resultCapacity sig msg pk
            else none
        | _, _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.accountNearTokenRead ||
          isConstNamed e ``ProofForge.Wasm.Near.Runtime.accountNearTokenHasKey ||
          isConstNamed e ``ProofForge.Wasm.Near.Runtime.accountNearTokenRemove) &&
          e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        match val env args[args.size - 2]!,
            nearAccountIdFrame? env args[args.size - 1]! with
        | some tag, some account =>
            if accountTokenLengthAdmissible account then
              let key := accountTokenStorageKeyFrame tag account
              some (if isConstNamed e ``ProofForge.Wasm.Near.Runtime.accountNearTokenRead then
                .nearStorageRead 16 72 key
              else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.accountNearTokenHasKey then
                .nearStorageHasKey 16 72 key
              else
                .nearStorageRemove 16 72 key)
            else none
        | _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.accountNearTokenWrite &&
          e.getAppArgs.size ≥ 3 then
        let args := e.getAppArgs
        let value := args[args.size - 1]!
        match val env args[args.size - 3]!,
            nearAccountIdFrame? env args[args.size - 2]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) value),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) value) with
        | some tag, some account, some lo, some hi =>
            if accountTokenLengthAdmissible account then
              some (.nearStorageWrite 16 72 16
                (accountTokenStorageKeyFrame tag account)
                (nearTokenStorageValueFrame lo hi))
            else none
        | _, _, _, _ => none
      else if isConstNamed e
          ``ProofForge.Wasm.Near.Runtime.accountNearTokenFixtureWriteMalformed &&
          e.getAppArgs.size ≥ 3 then
        let args := e.getAppArgs
        match staticAccountTokenTag? env 8 args[args.size - 3]!,
            nearAccountIdFrame? env args[args.size - 2]!,
            staticNatVal? env args[args.size - 1]! with
        | some tag, some account, some length =>
            if tag ≤ 0xffffffff && accountTokenLengthAdmissible account && length ≤ 20 then
              let value := (#[.lit (UInt64.ofNat length)] ++
                (Array.range 20).map fun index => .lit (UInt64.ofNat (0xa0 + index)))
              some (.nearStorageWrite 16 72 20
                (accountTokenStorageKeyFrame (.lit (UInt64.ofNat tag)) account) value)
            else none
        | _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageRead &&
          e.getAppArgs.size ≥ 3 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 3]!,
            staticNatVal? env args[args.size - 2]! with
        | some resultCapacity, some keyCapacity =>
            if ProofForge.Wasm.Near.Codec.storageCapacityValid resultCapacity &&
                ProofForge.Wasm.Near.Codec.rawStorageKeyCapacityValid keyCapacity then
              (boundedStorageFrame? env keyCapacity args[args.size - 1]!).map fun key =>
                .nearStorageRead resultCapacity keyCapacity key
            else none
        | _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageWrite &&
          e.getAppArgs.size ≥ 5 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 5]!,
            staticNatVal? env args[args.size - 4]!,
            staticNatVal? env args[args.size - 3]! with
        | some resultCapacity, some keyCapacity, some valueCapacity =>
            if ProofForge.Wasm.Near.Codec.storageCapacityValid resultCapacity &&
                ProofForge.Wasm.Near.Codec.rawStorageKeyCapacityValid keyCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid valueCapacity then
              match boundedStorageFrame? env keyCapacity args[args.size - 2]!,
                  boundedStorageFrame? env valueCapacity args[args.size - 1]! with
              | some key, some value =>
                  some (.nearStorageWrite resultCapacity keyCapacity valueCapacity key value)
              | _, _ => none
            else none
        | _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageRemove ||
          isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageHasKey) &&
          e.getAppArgs.size ≥ 3 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 3]!,
            staticNatVal? env args[args.size - 2]! with
        | some resultCapacity, some keyCapacity =>
            if ProofForge.Wasm.Near.Codec.storageCapacityValid resultCapacity &&
                ProofForge.Wasm.Near.Codec.rawStorageKeyCapacityValid keyCapacity then
              (boundedStorageFrame? env keyCapacity args[args.size - 1]!).map fun key =>
                if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageRemove then
                  .nearStorageRemove resultCapacity keyCapacity key
                else
                  .nearStorageHasKey resultCapacity keyCapacity key
            else none
        | _, _ => none
      else if let some fields := userCtorFields env e then
        match e.getAppFn.constName? with
        | some ctorName =>
          match env.find? ctorName with
          | some (.ctorInfo c) =>
            if c.induct == ``ProofForge.Wasm.Near.Sdk.Promises.PromiseHandle && fields.size ≥ 1 then
              find fuel' fields[0]!
            else none
          | _ => none
        | none => none
      else
        match unfoldUserHelper env e with
        | some (_, unfolded) => find fuel' unfolded
        | none => none
  match find 8 e with
  | some effect =>
      let e := strip e
      let result : Ops.Val :=
        if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Store.DirectAccountNearTokenMap.read ||
            isConstNamed e ``ProofForge.Wasm.Near.Sdk.Store.DirectAccountNearTokenMap.has ||
            isConstNamed e ``ProofForge.Wasm.Near.Sdk.Store.DirectAccountNearTokenMap.put ||
            isConstNamed e ``ProofForge.Wasm.Near.Sdk.Store.DirectAccountNearTokenMap.remove then
          Ops.Val.nearStorageResultStatus 16
        else
          .lit 0
      some #[effect, .returnU64 result]
  | none => none

/-- A vector root is not a scalar slot. Mixed static/dynamic writeback can see an inline
helper's vector parameter as a changed structure field; discard that synthetic root store. -/
private def dropVectorRootStores (dynamic stores : Array Ops.Op) : Array Ops.Op :=
  let vectorNames := dynamic.filterMap fun
    | .indexSetLeaf name _ _ _ _ | .indexSet name _ _ _ _ => some name
    | _ => none
  stores.filter fun
    | .storeField name _ => !vectorNames.contains name
    | _ => true

private def qualifyStatePrefix (statePrefix name : String) : String :=
  if statePrefix.isEmpty || name == statePrefix || name.startsWith (statePrefix ++ "_") then name
  else s!"{statePrefix}_{name}"

private def qualifyDynamicStateOp (statePrefix : String) : Ops.Op → Ops.Op
  | .indexSetLeaf name index value len leaf =>
      .indexSetLeaf (qualifyStatePrefix statePrefix name) index value len leaf
  | .indexSet name index value len elemOff =>
      .indexSet (qualifyStatePrefix statePrefix name) index value len elemOff
  | op => op

private def qualifyNestedStateName (statePrefix : String) (fieldNames : Array String)
    (name : String) : String :=
  if statePrefix.isEmpty || name == statePrefix || name.startsWith (statePrefix ++ "_") then name
  else if fieldNames.any fun field => name == field || name.startsWith (field ++ "_") then
    s!"{statePrefix}_{name}"
  else name

private partial def qualifyNestedStateVal (statePrefix : String) (fieldNames : Array String) :
    Ops.Val → Ops.Val
  | .arg i => .arg i
  | .local i => .local i
  | .field base name =>
      .field (qualifyNestedStateVal statePrefix fieldNames base)
        (qualifyNestedStateName statePrefix fieldNames name)
  | .lit value => .lit value
  | .bitAnd lhs rhs => .bitAnd (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .bitOr lhs rhs => .bitOr (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .bitXor lhs rhs => .bitXor (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .bitNot value => .bitNot (qualifyNestedStateVal statePrefix fieldNames value)
  | .shiftL lhs rhs => .shiftL (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .shiftR lhs rhs => .shiftR (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .indexGet base name index len elemOff =>
      .indexGet (qualifyNestedStateVal statePrefix fieldNames base)
        (qualifyNestedStateName statePrefix fieldNames name)
        (qualifyNestedStateVal statePrefix fieldNames index) len elemOff
  | .loopIx => .loopIx
  | .select cmp lhs rhs thn els =>
      .select cmp (qualifyNestedStateVal statePrefix fieldNames lhs)
        (qualifyNestedStateVal statePrefix fieldNames rhs)
        (qualifyNestedStateVal statePrefix fieldNames thn)
        (qualifyNestedStateVal statePrefix fieldNames els)
  | .addU64 lhs rhs => .addU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .subU64 lhs rhs => .subU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .mulU64 lhs rhs => .mulU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .divU64 lhs rhs => .divU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .modU64 lhs rhs => .modU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .ext kind operands =>
      .ext kind (operands.map (qualifyNestedStateVal statePrefix fieldNames))

private partial def qualifyNestedStateOp (statePrefix : String) (fieldNames : Array String) :
    Ops.Op → Ops.Op
  | .letLocal i value => .letLocal i (qualifyNestedStateVal statePrefix fieldNames value)
  | .joinLocal i => .joinLocal i
  | .setLocal i value => .setLocal i (qualifyNestedStateVal statePrefix fieldNames value)
  | .checkedAddU64 lhs rhs =>
      .checkedAddU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
        (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .checkedSubU64 lhs rhs =>
      .checkedSubU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
        (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .checkedMulU64 lhs rhs =>
      .checkedMulU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
        (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .checkedDivU64 lhs rhs =>
      .checkedDivU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
        (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .checkedModU64 lhs rhs =>
      .checkedModU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
        (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .ite cmp lhs rhs thn els =>
      .ite cmp (qualifyNestedStateVal statePrefix fieldNames lhs)
        (qualifyNestedStateVal statePrefix fieldNames rhs)
        (thn.map (qualifyNestedStateOp statePrefix fieldNames))
        (els.map (qualifyNestedStateOp statePrefix fieldNames))
  | .forAccum n value resultLocal =>
      .forAccum n (qualifyNestedStateVal statePrefix fieldNames value) resultLocal
  | .forBody n body => .forBody n (body.map (qualifyNestedStateOp statePrefix fieldNames))
  | .indexSetLeaf name index value len leaf =>
      .indexSetLeaf (qualifyNestedStateName statePrefix fieldNames name)
        (qualifyNestedStateVal statePrefix fieldNames index)
        (qualifyNestedStateVal statePrefix fieldNames value) len leaf
  | .indexSet name index value len elemOff =>
      .indexSet (qualifyNestedStateName statePrefix fieldNames name)
        (qualifyNestedStateVal statePrefix fieldNames index)
        (qualifyNestedStateVal statePrefix fieldNames value) len elemOff
  | .storeField name value =>
      .storeField (qualifyNestedStateName statePrefix fieldNames name)
        (qualifyNestedStateVal statePrefix fieldNames value)
  | .okState value => .okState (qualifyNestedStateVal statePrefix fieldNames value)
  | .returnU64 value => .returnU64 (qualifyNestedStateVal statePrefix fieldNames value)
  | .returnState value => .returnState (qualifyNestedStateVal statePrefix fieldNames value)
  | op => op

/-- A nested state helper's success value is consumed by the enclosing record update. Its writes
remain observable, but its state terminal must not be interpreted as a root-schema commit. -/
private partial def dropNestedStateTerminals (ops : Array Ops.Op) : Array Ops.Op :=
  ops.filterMap fun op =>
    match op with
    | .okState _ | .returnState _ => none
    | .ite cmp lhs rhs thn els =>
        some (.ite cmp lhs rhs (dropNestedStateTerminals thn) (dropNestedStateTerminals els))
    | .forBody n body => some (.forBody n (dropNestedStateTerminals body))
    | op => some op

/-- Once a nested transition has been lowered, the enclosing record's projection of that
structure is inheritance, not a scalar write. Keep later scalar/vector continuation effects while
removing only the impossible whole-structure store. -/
private partial def dropNestedRootStores (statePrefix : String)
    (ops : Array Ops.Op) : Array Ops.Op :=
  ops.filterMap fun op =>
    match op with
    | .storeField name _ => if name == statePrefix then none else some op
    | .ite cmp lhs rhs thn els =>
        some (.ite cmp lhs rhs (dropNestedRootStores statePrefix thn)
          (dropNestedRootStores statePrefix els))
    | .forBody n body => some (.forBody n (dropNestedRootStores statePrefix body))
    | op => some op

/-- Zeta-reduce syntax-only aliases at the head of an expression.
Compiler intrinsics and loops stay explicit so later effect/control decoding still sees them. -/
def zetaPureHeadLets (env : Environment) (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    match strip e with
    | .letE _ _ value body _ =>
        let effectful :=
          (decodeNearEffect env value).isSome ||
            (findForIn env value).isSome || (findForBodyExpr env value).isSome
        -- A scalar captured before an effect must remain a local: substituting its state-field read
        -- through the call can move that read after a later state write.
        let directAlias := match strip body with | .bvar 0 => true | _ => false
        if effectful || (!directAlias && !isIteExpr body) then e
        else zetaPureHeadLets env fuel' (body.instantiate1 value)
    | e => e

private def findYieldPayload (e : Expr) : Option Expr :=
  let rec go (fuel : Nat) (e : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if isConstNamed e ``ForInStep.yield || endsWith e ".yield" then
        if e.getAppArgs.size ≥ 1 then
          -- The payload remains under the yielded state/control binder. Keep accumulator 0,
          -- and lower the loop index plus outer method arguments back to callback scope.
          some (e.getAppArgs[e.getAppArgs.size - 1]!.lowerLooseBVars 1 1)
        else none
      else
        match e with
        | .letE _ _ value body _ => go fuel' body <|> go fuel' value
        -- Yield can sit under a dependent branch proof lambda. Dropping that binder without
        -- lowering would turn the loop index and outer arguments into unrelated `.arg`s.
        | .lam _ _ body _ => go fuel' (body.lowerLooseBVars 1 1)
        | _ => e.getAppArgs.findSome? (go fuel')
  go 32 e

/--
Lean composes consecutive mutable-state assignments as a record update whose unchanged
fields project from the previous expression. When that base is a `pf_inline` State helper,
preserve the helper transition before lowering the outer update. This is target-neutral
structured-state normalization; backends only see the resulting stores.
-/
private def findProjectedInlineBase (env : Environment) (fuel : Nat) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    let args := e.getAppArgs
    let projectedBase? :=
      match e.getAppFn.constName? with
      | some name =>
        match env.getProjectionFnInfo? name with
        | some _ =>
          if h : args.size > 0 then
            let base := args[args.size - 1]
            match unfoldUserHelper env base with
            | some (helper, _) =>
              if inlineHelperPreservesUserType env helper then some base else none
            | none => none
          else none
        | none => none
      | none => none
    projectedBase? <|> args.findSome? (findProjectedInlineBase env fuel')

/-- Collect the inline State expressions inherited through record projections. Once such an
expression has been lowered, later wrappers may still contain several projections of the same
result; retaining every applied ancestor prevents those transitions from being emitted again. -/
private def projectedInlineBases (env : Environment) (fuel : Nat) (e : Expr) : Array Expr :=
  let rec go (fuel : Nat) (e : Expr) (acc : Array Expr) : Array Expr :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      let e := strip e
      let args := e.getAppArgs
      let acc :=
        match e.getAppFn.constName? with
        | some name =>
          match env.getProjectionFnInfo? name with
          | some _ =>
            match args[args.size - 1]? with
            | some base =>
              match unfoldUserHelper env base with
              | some (helper, _) =>
                if inlineHelperPreservesUserType env helper && !acc.contains base then acc.push base
                else acc
              | none => acc
            | none => acc
          | none => acc
        | none => acc
      args.foldl (init := acc) fun acc arg => go fuel' arg acc
  go fuel e #[]

private def addAppliedBases (current extra : Array Expr) : Array Expr :=
  extra.foldl (init := current) fun result base =>
    if result.contains base then result else result.push base

/-- Find the mutable source underneath a composed State expression. -/
private def inlineStateSource (env : Environment) (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    let e := strip e
    if let .letE _ _ value body _ := e then
      inlineStateSource env fuel' (body.instantiate1 value)
    else if (isConstNamed e ``ite || isConstNamed e ``dite) && e.getAppArgs.size ≥ 2 then
      let args := e.getAppArgs
      let branch := args[args.size - 2]!
      let branch :=
        match strip branch with
        | .lam _ _ body _ => body.lowerLooseBVars 1 1
        | branch => branch
      inlineStateSource env fuel' branch
    else if (unfoldUserHelper env e).isSome then
      let args := e.getAppArgs
      if h : args.size > 0 then inlineStateSource env fuel' args[0] else e
    else
      let structureSource? :=
        match e.getAppFn.constName?, userCtorFields env e with
        | some ctor, some fields => Id.run do
          for h : i in [:fields.size] do
            let field := fields[i]
            if let some projection := (strip field).getAppFn.constName? then
              if let some info := env.getProjectionFnInfo? projection then
                let args := (strip field).getAppArgs
                if info.ctorName == ctor && info.i == i then
                  if h : args.size > 0 then return some args[args.size - 1]
          return none
        | _, _ => none
      let directProjectionBase? :=
        match e.getAppFn.constName? with
        | some name =>
          if !isUserName env name then none else match env.getProjectionFnInfo? name with
          | some _ =>
            let args := e.getAppArgs
            if h : args.size > 0 then some args[args.size - 1] else none
          | none => none
        | none => none
      match structureSource? <|> directProjectionBase? with
      | some base => inlineStateSource env fuel' base
      | none => e

private def isStateTransitionValue (env : Environment) : Nat → Bool → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, underControl, e =>
      let e := strip e
      match e with
      | .letE _ _ value body _ =>
          isStateTransitionValue env fuel underControl (body.instantiate1 value)
      | _ =>
        if (isConstNamed e ``ite || isConstNamed e ``dite) && e.getAppArgs.size ≥ 2 then
          let args := e.getAppArgs
          let peelProofLam (branch : Expr) : Expr :=
            match strip branch with
            | .lam _ _ body _ => body.lowerLooseBVars 1 1
            | branch => branch
          isStateTransitionValue env fuel true (peelProofLam args[args.size - 2]!) ||
            isStateTransitionValue env fuel true (peelProofLam args[args.size - 1]!)
        else
          match unfoldUserHelper env e with
          | some (name, _) => inlineHelperPreservesUserType env name
          | none =>
            match e.getAppFn.constName? with
            | some name =>
              match env.find? name with
              | some (.ctorInfo ctor) =>
                  underControl && isUserType env ctor.induct && isStructure env ctor.induct
              | _ => false
            | none => false

/-- Sequential decoding is needed when substitution would duplicate dynamic structure writes or
erase a conditional State constructor behind later projections. Straight-line scalar-only helpers
retain the established zeta-normalized Core shape. Follow marked helpers recursively so wrappers
around `Vector.set` remain generic. -/
private def stateTransitionNeedsSequencing (env : Environment) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
      let e := strip e
      if isIteExpr e || !(collectIndexSets env e).isEmpty then true
      else
        match e with
        | .letE _ _ value body _ =>
            stateTransitionNeedsSequencing env fuel value ||
              stateTransitionNeedsSequencing env fuel body
        | .lam _ _ body _ => stateTransitionNeedsSequencing env fuel body
        | _ =>
          match unfoldUserHelper env e with
          | some (_, unfolded) => stateTransitionNeedsSequencing env fuel unfolded
          | none => e.getAppArgs.any (stateTransitionNeedsSequencing env fuel)

/-- Follow structure-preserving helpers to their source value without erasing a nested projection.
For a helper over `s.askBook`, the root-state source is `s` but the type-correct substitution source
is `s.askBook`; sequential nested lowering needs both facts. -/
private def inlineTypedStateSource (env : Environment) (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    let e := strip e
    if let .letE _ _ value body _ := e then
      inlineTypedStateSource env fuel' (body.instantiate1 value)
    else if (isConstNamed e ``ite || isConstNamed e ``dite) && e.getAppArgs.size ≥ 2 then
      let args := e.getAppArgs
      let branch := args[args.size - 2]!
      let branch :=
        match strip branch with
        | .lam _ _ body _ => body.lowerLooseBVars 1 1
        | branch => branch
      inlineTypedStateSource env fuel' branch
    else if (unfoldUserHelper env e).isSome then
      let args := e.getAppArgs
      if h : args.size > 0 then inlineTypedStateSource env fuel' args[0] else e
    else
      let structureSource? :=
        match e.getAppFn.constName?, userCtorFields env e with
        | some ctor, some fields => Id.run do
          for h : i in [:fields.size] do
            let field := fields[i]
            if let some projection := (strip field).getAppFn.constName? then
              if let some info := env.getProjectionFnInfo? projection then
                let args := (strip field).getAppArgs
                if info.ctorName == ctor && info.i == i then
                  if h : args.size > 0 then return some args[args.size - 1]
          return none
        | _, _ => none
      match structureSource? with
      | some source => inlineTypedStateSource env fuel' source
      | none => e

/--
A let-bound user structure rooted at a method state argument is a sequential State transition,
not a pure value alias. Decoding it before the continuation avoids substituting an ever-growing
record expression through every later projection. Nested structures have a separate typed-source
path below; this boundary owns only transitions of the declared root state type.
-/
private def sequentialStateSource? (env : Environment) (type value : Expr)
    (stateType? : Option Name := none) : Option Expr := do
  let typeName ← type.consumeMData.getAppFn.constName?
  if !isUserType env typeName then none else
  if stateType?.any (· != typeName) then none else
  let value := strip value
  let source := inlineStateSource env 64 value
  if source == value then none else
  let directRecordUpdate :=
    match value.getAppFn.constName?, userCtorFields env value with
    | some ctor, some _ =>
        match env.find? ctor with
        | some (.ctorInfo info) => info.induct == typeName
        | _ => false
    | _, _ => false
  if !directRecordUpdate && !isStateTransitionValue env 64 false value then none else
  if !stateTransitionNeedsSequencing env 64 value then none else
  match strip source with
  | .bvar _ => some source
  | source =>
      if isConstNamed source ``methodArgRef || isConstNamed source ``localRef then
        some source
      else none

private structure NestedStateTransition where
  transition : Expr
  typedSource : Expr
  nestedType : Name
  fieldPrefix : String
  /-- Composed outer state, its mutable source, and the outer state type. -/
  outerOwner? : Option (Expr × Expr × Name) := none

private structure NestedStateNormalization where
  prior : Array Ops.Op
  transition : Expr
  typedSource : Expr
  outerState : Expr

/-- Find a structure-valued field transition embedded directly in an outer record update. Lean's
zeta reduction commonly turns `let book := update s.book; { s with book }` into exactly this shape.
Lowering the nested transition first prevents every leaf projection from independently expanding
the same helper, while retaining a target-neutral flattened field prefix. -/
private def nestedSequentialTransition? (env : Environment) (state : Expr)
    (statePrefix : String) : Option NestedStateTransition := Id.run do
  let state := strip state
  let some fields := userCtorFields env state | return none
  let some ctor := state.getAppFn.constName? | return none
  let some (.ctorInfo info) := env.find? ctor | return none
  let names := getStructureFields env info.induct
  for h : i in [:fields.size] do
    if i < names.size then
      let some fieldType := fieldTypeExpr env info.induct names[i]! | continue
      let some fieldTypeName := fieldType.consumeMData.getAppFn.constName? | continue
      if fieldTypeName != info.induct && isUserType env fieldTypeName &&
          isStructure env fieldTypeName then
        let transition := strip fields[i]
        if isStateTransitionValue env 64 false transition &&
            stateTransitionNeedsSequencing env 64 transition then
          let typedSource := inlineTypedStateSource env 64 transition
          if typedSource != transition then
            let fieldName := names[i]!.toString
            let pathPrefix :=
              if statePrefix.isEmpty then fieldName else s!"{statePrefix}_{fieldName}"
            let outerOwner? :=
              match typedSource.getAppFn.constName? with
              | some projection =>
                match env.getProjectionFnInfo? projection with
                | some projectionInfo =>
                  let args := typedSource.getAppArgs
                  if h : args.size > 0 then
                    let owner := args[args.size - 1]
                    let root := inlineStateSource env 64 owner
                    if owner == root then none else
                    match env.find? projectionInfo.ctorName with
                    | some (.ctorInfo ownerCtor) => some (owner, root, ownerCtor.induct)
                    | _ => none
                  else none
                | none => none
              | none => none
            return some {
              transition := transition
              typedSource := typedSource
              nestedType := fieldTypeName
              fieldPrefix := pathPrefix
              outerOwner? := outerOwner?
            }
  return none

private def stateNamesAlias (left right : String) : Bool :=
  left == right || left.startsWith (right ++ "_") || right.startsWith (left ++ "_")

private partial def valReadsWritten (written : Array String) : Ops.Val → Bool
  | .arg _ | .local _ | .lit _ | .loopIx => false
  | .field base name => written.any (stateNamesAlias name) || valReadsWritten written base
  | .indexGet base name index _ _ =>
      written.any (stateNamesAlias name) ||
        valReadsWritten written base || valReadsWritten written index
  | .bitNot value => valReadsWritten written value
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valReadsWritten written lhs || valReadsWritten written rhs
  | .select _ lhs rhs thn els =>
      valReadsWritten written lhs || valReadsWritten written rhs ||
        valReadsWritten written thn || valReadsWritten written els
  | .ext _ operands => operands.any (valReadsWritten written)
private structure SnapshotState where
  written : Array String := #[]
  bindings : Array (Ops.Val × Nat) := #[]
  prelude : Array Ops.Op := #[]

private def SnapshotState.snapshot (base : Nat) (state : SnapshotState)
    (value : Ops.Val) : SnapshotState × Ops.Val :=
  match state.bindings.find? (·.1 == value) with
  | some (_, localIx) => (state, .local localIx)
  | none =>
    let localIx := base + state.bindings.size
    ({ state with
        bindings := state.bindings.push (value, localIx)
        prelude := state.prelude.push (.letLocal localIx value) },
      .local localIx)

/-- Lower one simultaneous State update while collecting every required pre-write snapshot. -/
private def snapshotStateOps (base : Nat) (ops : Array Ops.Op) :
    SnapshotState × Array Ops.Op := Id.run do
  let mut state : SnapshotState := {}
  let mut body : Array Ops.Op := #[]
  let needsSnapshot (state : SnapshotState) (value : Ops.Val) : Bool :=
    valReadsWritten state.written value
  for op in ops do
    match op with
    | .indexSetLeaf name index value len leaf =>
      let (next, index) :=
        if needsSnapshot state index then state.snapshot base index else (state, index)
      state := next
      let (next, value) :=
        if needsSnapshot state value then state.snapshot base value else (state, value)
      state := { next with written := next.written.push name }
      body := body.push (.indexSetLeaf name index value len leaf)
    | .indexSet name index value len offset =>
      let (next, index) :=
        if needsSnapshot state index then state.snapshot base index else (state, index)
      state := next
      let (next, value) :=
        if needsSnapshot state value then state.snapshot base value else (state, value)
      state := { next with written := next.written.push name }
      body := body.push (.indexSet name index value len offset)
    | .storeField name value =>
      let (next, value) :=
        if needsSnapshot state value then state.snapshot base value else (state, value)
      state := { next with written := next.written.push name }
      body := body.push (.storeField name value)
    | .okState value =>
      let (next, value) :=
        if needsSnapshot state value then state.snapshot base value else (state, value)
      state := next
      body := body.push (.okState value)
    | op => body := body.push op
  return (state, body)

/--
Lean record-update RHS expressions all observe the pre-update value. Keep flat write Ops, but
snapshot only expressions that a preceding write in this same source update would invalidate.
-/
private def snapshotStateUpdate (base : Nat) (ops : Array Ops.Op) : Array Ops.Op :=
  let (state, body) := snapshotStateOps base ops
  state.prelude ++ body

private def decodeYieldState (env : Environment) (fuel localDepth : Nat) (state : Expr)
    (appliedBases : Array Expr := #[]) (stateType? : Option Name := none)
    (statePrefix : String := "") (deepScalars : Bool := false) :
    Except String (Array Ops.Op) :=
  match fuel with
  | 0 => .error "extract/unsupported: inline state depth"
  | fuel' + 1 =>
    let raw := strip state
    let sequential? : Option (Expr × Expr × Expr) :=
      match raw with
      | .letE _ type value body _ =>
          (sequentialStateSource? env type value stateType?).map fun source =>
            (value, source, body)
      | _ => none
    let ordinaryLet? : Option (Expr × Expr × Expr) :=
      match raw with
      | .letE _ type value body _ => some (type, value, body)
      | _ => none
    match sequential?, ordinaryLet? with
    | some (value, source, body), _ =>
      match decodeYieldState env fuel' localDepth value appliedBases stateType? statePrefix deepScalars,
          decodeYieldState env fuel' localDepth (body.instantiate1 source) appliedBases
            stateType? statePrefix deepScalars with
      | .ok prior, .ok continuation => .ok (prior ++ continuation)
      | .error reason, _ =>
          .error s!"extract/unsupported: sequential inline state binding: {reason}"
      | _, .error reason => .error reason
    | none, some (type, value, body) =>
      let scalarType := type.consumeMData.getAppFn.constName?
      if scalarType == some ``UInt64 then
        match localScalarValue? env (if deepScalars then 128 else 32) value with
        | some localValue =>
          if shouldMaterializeLocal type localValue then
            let marker := mkApp (mkConst ``localRef) (mkNatLit localDepth)
            match decodeYieldState env fuel' (localDepth + 1)
                (body.instantiate1 marker) appliedBases stateType? statePrefix deepScalars with
            | .ok continuation => .ok (#[.letLocal localDepth localValue] ++ continuation)
            | .error reason => .error reason
          else
            decodeYieldState env fuel' localDepth (body.instantiate1 value) appliedBases stateType?
              statePrefix deepScalars
        | none =>
            decodeYieldState env fuel' localDepth (body.instantiate1 value) appliedBases stateType?
              statePrefix deepScalars
      else
        decodeYieldState env fuel' localDepth (body.instantiate1 value) appliedBases stateType?
          statePrefix deepScalars
    | none, none =>
      let state0 := raw
      let appliedBases := addAppliedBases #[] <|
        appliedBases.map fun base => strip (substLets 256 base)
      if appliedBases.contains state0 then
        .ok #[]
      else if let some (name, unfolded) := unfoldUserHelper env state0 then do
        let args := state0.getAppArgs
        let (prior, normalized, bodyAppliedBases) ←
          if h : args.size > 0 then
            let base := args[0]
            let source :=
              if statePrefix.isEmpty then inlineStateSource env 64 base
              else inlineTypedStateSource env 64 base
            if source == base then
              .ok (#[], unfolded, appliedBases)
            else do
              let prior ← decodeYieldState env fuel' localDepth base appliedBases stateType?
                statePrefix deepScalars
              let normalized := unfolded.replace fun e => if e == base then some source else none
              let bodyAppliedBases := addAppliedBases appliedBases #[base]
              let bodyAppliedBases :=
                addAppliedBases bodyAppliedBases (projectedInlineBases env 64 base)
              .ok (prior, normalized, bodyAppliedBases)
          else
            .ok (#[], unfolded, appliedBases)
        match decodeYieldState env fuel' localDepth normalized bodyAppliedBases stateType?
            statePrefix deepScalars with
        | .ok ops => .ok (prior ++ ops)
        | .error reason => .error s!"extract/unsupported: inline state {name}: {reason}"
      else if (isConstNamed state0 ``ite || isConstNamed state0 ``dite) &&
          state0.getAppArgs.size ≥ 2 then
        let args := state0.getAppArgs
        let peelProofLam (e : Expr) : Expr :=
          match strip e with
          | .lam _ _ body _ => body.lowerLooseBVars 1 1
          | e => e
        let thn := peelProofLam args[args.size - 2]!
        let els := peelProofLam args[args.size - 1]!
        match args.findSome? (asCondition env),
            decodeYieldState env fuel' localDepth thn appliedBases stateType? statePrefix deepScalars,
            decodeYieldState env fuel' localDepth els appliedBases stateType? statePrefix deepScalars with
        | some (cmp, lhs, rhs), .ok thnOps, .ok elsOps =>
          .ok #[.ite cmp lhs rhs thnOps elsOps]
        | none, _, _ =>
          .error s!"extract/unsupported: inline state condition: {args[args.size - 4]!}"
        | _, .error reason, _ => .error s!"extract/unsupported: inline state then: {reason}"
        | _, _, .error reason => .error s!"extract/unsupported: inline state else: {reason}"
      else if let some nested := nestedSequentialTransition? env state0 statePrefix then do
        let normalized : NestedStateNormalization ←
          match nested.outerOwner? with
          | none => .ok (NestedStateNormalization.mk #[] nested.transition
              nested.typedSource state0)
          | some (owner, root, ownerType) => do
            let prior ← decodeYieldState env fuel' localDepth owner appliedBases
              (some ownerType) "" deepScalars
            -- The composed owner may itself contain the nested transition whose result is also
            -- referenced by a scalar argument of the later helper (for example an allocated
            -- address read from a just-pruned tree). That transition has already run as part of
            -- `prior`; rewrite the exact same-typed value to its normalized projection as well.
            let appliedNested? := nestedSequentialTransition? env owner ""
            let rewriteApplied (e : Expr) : Expr :=
              let e := e.replace fun candidate => if candidate == owner then some root else none
              match appliedNested? with
              | none => e
              | some applied =>
                let source := applied.typedSource.replace fun candidate =>
                  if candidate == owner then some root else none
                let appliedSourceVal := val env applied.typedSource
                e.replace fun candidate =>
                  let candidateSource := inlineTypedStateSource env 64 candidate
                  let sameTypedSource := candidateSource == applied.typedSource ||
                    (appliedSourceVal.isSome && val env candidateSource == appliedSourceVal)
                  if candidate == applied.transition || (sameTypedSource &&
                      isStateTransitionValue env 64 false candidate) then
                    some source
                  else none
            let transition :=
              rewriteApplied nested.transition
            let typedSource :=
              rewriteApplied nested.typedSource
            let outerState := state0.replace fun e => if e == owner then some root else none
            .ok (NestedStateNormalization.mk prior transition typedSource outerState)
        let nestedOps ←
          match decodeYieldState env fuel' localDepth normalized.transition appliedBases
              (some nested.nestedType) nested.fieldPrefix deepScalars with
          | .ok ops =>
              let fieldNames := (getStructureFields env nested.nestedType).map (·.toString)
              .ok (dropNestedStateTerminals
                (ops.map (qualifyNestedStateOp nested.fieldPrefix fieldNames)))
          | .error reason =>
              .error s!"extract/unsupported: nested sequential state field: {reason}"
        let continuationState :=
          normalized.outerState.replace fun e =>
            if e == normalized.transition then some normalized.typedSource else none
        match decodeYieldState env fuel' localDepth continuationState appliedBases stateType?
            statePrefix deepScalars with
        | .ok continuation =>
            .ok (dropNestedRootStores nested.fieldPrefix
              (normalized.prior ++ nestedOps ++ continuation))
        | .error reason => .error reason
      else do
        let priorBase? := findProjectedInlineBase env 64 state0
        let prior ←
          match priorBase? with
          | none => .ok #[]
          | some base =>
            if appliedBases.contains base then .ok #[] else match unfoldUserHelper env base with
            | some (name, _) =>
              -- Keep the helper application intact here. Its normal decode path sequences the
              -- state argument before β-expanded scalar lets; decoding the body directly would
              -- read the pre-transition state and duplicate those lets through every projection.
              match decodeYieldState env fuel' localDepth base appliedBases stateType?
                  statePrefix deepScalars with
              | .ok ops => .ok ops
              | .error reason =>
                .error s!"extract/unsupported: projected inline state {name}: {reason}"
            | none => .error "extract/unsupported: projected inline state"
        -- The prior transition has now run. Rewrite outer projections of its result back to
        -- the helper's source state expression; state-loop normalization interprets those
        -- projections against the current mutable state, preserving the sequential semantics.
        let outerState :=
          match priorBase? with
          | none => state0
          | some base =>
            let args := base.getAppArgs
            if h : args.size > 0 then
              let sourceState := args[0]
              state0.replace fun e => if e == base then some sourceState else none
            else state0
        let outerAppliedBases :=
          match priorBase? with
          | some base =>
            let bases := addAppliedBases appliedBases #[base]
            addAppliedBases bases (projectedInlineBases env 64 base)
          | none => appliedBases
        let dynamic := (collectIndexSets env outerState (deduplicate := true)
          (appliedBases := outerAppliedBases)).map (qualifyDynamicStateOp statePrefix)
        let static := (flattenLeaves env statePrefix outerState outerAppliedBases).map fun p =>
          (.storeField p.1 p.2 : Ops.Op)
        let update := snapshotStateUpdate localDepth
          (dynamic ++ dropVectorRootStores dynamic static)
        .ok (prior ++ update)

/-- Lower one marked `MProd` yield as a simultaneous scalar-frame update. Every right-hand side is
snapshotted before any frame slot changes, so later assignments cannot observe an earlier write. -/
private def scalarFrameYieldOps (env : Environment) (state : Expr) :
    Option (Except String (Array Ops.Op)) :=
  let state := strip state
  if !isConstNamed state ``scalarFrameYield then none else
  some do
    let args := state.getAppArgs
    if args.size < 2 then
      throw "extract/unsupported: scalar frame yield marker"
    let base ←
      match asLit 8 args[args.size - 2]! with
      | some (.lit base) => .ok base.toNat
      | _ => .error "extract/unsupported: scalar frame local base"
    let leaves ←
      match scalarFrameLeaves args[args.size - 1]! with
      | some leaves => .ok leaves
      | none => .error "extract/unsupported: scalar frame yield shape"
    if leaves.size < 2 then
      throw "extract/unsupported: scalar frame requires multiple UInt64 values"
    let values ← leaves.mapM fun leaf =>
      match val env leaf with
      | some value => .ok value
      | none => .error "extract/unsupported: scalar frame yield value"
    let mut ops : Array Ops.Op := #[]
    for index in [:values.size] do
      ops := ops.push (.letLocal (base + values.size + index) values[index]!)
    for index in [:values.size] do
      ops := ops.push (.setLocal (base + index) (.local (base + values.size + index)))
    return ops

/-- State loop 的 `yield newState` 只写账户并继续，不生成 commit/exit。 -/
private def asYieldStores (env : Environment) (e : Expr) (localDepth : Nat)
    (stateType? : Option Name := none) (deepScalars : Bool := false) :
    Option (Except String (Array Ops.Op)) :=
  match findYieldPayload e with
  | none => none
  | some state =>
      scalarFrameYieldOps env state <|>
        some (decodeYieldState env 128 localDepth state (stateType? := stateType?)
          (deepScalars := deepScalars))

/-- An inline State helper used as the state component of `.ok (state, ret)` still owns a real
transition. Decode that transition before returning the pair's explicit scalar result. -/
private def asInlineStateSuccess (env : Environment) (e : Expr) (localDepth : Nat)
    (stateType? : Option Name := none) (deepScalars : Bool := false) :
    Option (Except String (Array Ops.Op)) :=
  let e := peelControl 8 (dropUnusedHeadLets 32 e)
  if !isExceptOkHead e || e.getAppArgs.size < 1 then none else
  let pair := strip e.getAppArgs[e.getAppArgs.size - 1]!
  if !isConstNamed pair ``Prod.mk || pair.getAppArgs.size < 2 then none else
  let args := pair.getAppArgs
  let state := args[args.size - 2]!
  let result := args[args.size - 1]!
  if (unfoldUserHelper env state).isNone then none else
  some do
    let returns ←
      match effectfulResultOps env result with
      | some returns => .ok returns
      | none => .error "extract/unsupported: inline state success result"
    let stores ← decodeYieldState env 128 localDepth state (stateType? := stateType?)
      (deepScalars := deepScalars)
    return stores ++ returns
private def decodePlain (env : Environment) (e : Expr) (stateful : Bool)
    (localDepth : Nat) (stateType? : Option Name := none) (deepScalars : Bool := false) :
    Except String (Array Ops.Op) :=
  -- A direct update of one field in a multi-field State is still a complete state transition.
  -- Historically only branch/loop callers requested single-leaf stores, forcing source programs
  -- to wrap ordinary updates in an artificial always-true comparison. Keep the one-field-state
  -- shorthand below, but decode one changed leaf explicitly when the declared State has siblings.
  let includeSingleStore := stateful || stateType?.any fun stateType =>
    (getStructureFields env stateType).size > 1
  -- 必须在 peelLets 之前找效应：剥掉 `have sent := …` 后调用就没了。
  if let some ops := decodeNearEffect env e then
    .ok ops
  else if let some (n, addend) := findForIn env e then
    .ok #[.forAccum n addend localDepth, .returnU64 (.local localDepth)]
  else if let some result := asYieldStores env e localDepth stateType? deepScalars then
    result
  else if let some result := asInlineStateSuccess env e localDepth stateType? deepScalars then
    result
  else
  -- Record updates repeat one shared constructor through every unchanged projection. Emit each
  -- exact Vector.set node once; separate branch/set expressions remain distinct.
  let isets := collectIndexSets env e (deduplicate := true)
  if isets.size ≥ 1 then
    match asStoreFields env e true with
    | some stores =>
      .ok (snapshotStateUpdate localDepth (isets ++ dropVectorRootStores isets stores))
    | none =>
      match isets[isets.size - 1]! with
      | .indexSetLeaf _ _ v _ _ | .indexSet _ _ v _ _ =>
        -- `.ok ({ state with xs := xs.set i value }, ret)` returns its explicit second
        -- component, which need not be `value`. Loop yields have no public return and keep
        -- the written value as their internal fallback.
        let ret := if isForInStep e then v else (findOkRet env e).getD v
        .ok (snapshotStateUpdate localDepth (isets.push (.okState ret)))
      | _ => .ok isets
  else if let some op := findIndexSet env e then
    match op with
    | .indexSetLeaf _ _ v _ _ | .indexSet _ _ v _ _ =>
      let ret := if isForInStep e then v else (findOkRet env e).getD v
      .ok (snapshotStateUpdate localDepth #[op, .okState ret])
    | _ => .ok #[op]
  else
  let optionResult? := asConstructedOptionResult env 8 e
  let decodedError := decodeErrorCtor env e
  let e := peelControl 8 e
  if let .overflow := decodedError then
    .ok #[.errorOverflow]
  else if let .named name := decodedError then
    .ok #[.errorNamed name]
  else if let .typed frame := decodedError then
    .ok #[.errorTyped frame]
  else if let .unsupported reason := decodedError then
    .error s!"extract/unsupported: {reason}"
  else if let some (tag, payload) := optionResult? then
    -- A constructed Option is already a fixed logical frame. Target codecs retain ownership of
    -- the tag width and wire layout; extraction only preserves both source leaves through joins.
    .ok #[.returnU64 tag, .returnU64 payload]
  else if let some values := asOkNoop env e then
    if stateful && values.isEmpty then
      .ok #[.okState (.lit 0)]
    else if stateful && values.size == 1 then
      .ok #[.okState values[0]!]
    else
      .ok (values.map fun value => .returnU64 value)
  else if let some ops := asStoreFields env e includeSingleStore then
    .ok (snapshotStateUpdate localDepth ops)
  else if let some ops := asExceptOkBoundaryReturns env e then
    .ok ops
  else if let some v := asOkState env e then
    .ok #[.okState v]
  else if let some v := asOkScalar env e then
    .ok #[.okState v]
  else if let some vs := asBoundedCtorFields env e then
    .ok (returnStatesOf vs)
  else if let some vs := asWideCtorFields env e then
    .ok (vs.map fun value => .returnU64 value)
  else if let some vs := asRegisteredBoundaryCtorFields env e then
    .ok (vs.map fun value => .returnU64 value)
  else if let some vs := asStateFields env e then
    .ok (returnStatesOf vs)
  else if let some v := asStateMk env e then
    .ok #[.returnState v]
  else if isConstNamed e ``Prod.mk && e.getAppArgs.size ≥ 2 then
    -- Flat pairs remain the common path; nested products (Feature A depth ≤ 2) flatten to the
    -- same ordered scalar return frame that codecs already pack as nested ABI tuples.
    match scalarResultValues env 16 e with
    | some values =>
        if values.isEmpty then
          .error "extract/unsupported: empty pair return"
        else
          .ok (values.map fun value => .returnU64 value)
    | none => .error "extract/unsupported: pair return"
  else if let some leaf := nearRuntimeLeaf? e then
    .ok #[.returnU64 leaf]
  else if let some v := val env e then
    match v with
    | .field _ _ => .ok #[.returnU64 v]
    | .arg _ => .ok #[.returnU64 v]
    | .local _ => .ok #[.returnU64 v]
    | .lit _ => .ok #[.returnU64 v]
    | .ext (.near _) _ =>
        .ok #[.returnU64 v]
    | .indexGet .. => .ok #[.returnU64 v]
    | .addU64 .. | .subU64 .. | .mulU64 .. | .divU64 .. | .modU64 .. =>
        .ok #[.returnU64 v]
    | .bitAnd .. | .bitOr .. | .bitXor .. | .bitNot .. | .shiftL .. | .shiftR .. =>
        .ok #[.returnU64 v]
    | v =>
      if Ops.isLangLeaf v then .ok #[.returnU64 v]
      else .error "extract/unsupported: body"
  else
    .error "extract/unsupported: body"

private def findBy (args : Array Expr) (p : Expr → Bool) : Option Expr :=
  args.find? p

private def lastNamedBin (env : Environment) (want : Name) (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let rec go (fuel : Nat) (e : Expr) : Option (Ops.Val × Ops.Val) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if isConstNamed e want then
        match binArgs e with
        | some (l, r) =>
          match val env l, val env r with
          | some lv, some rv => some (lv, rv)
          | _, _ => none
        | none => none
      else
        match e with
        | .letE _ _ value body _ => go fuel' value <|> go fuel' body
        | .lam _ _ body _ => go fuel' body
        | _ => e.getAppArgs.findSome? (go fuel')
  go 16 e

/--
Turn the terminal successes of a scalar `Except` producer into assignments to one join slot.
Checked arithmetic already branches to the enclosing error exit, so operations after a terminal
success are unreachable and must not be copied into the joined path.
-/
private partial def lowerBindProducer (slot : Nat) (ops : Array Ops.Op) :
    Option (Array Ops.Op × Bool × Bool) := Id.run do
  let mut lowered := #[]
  let mut hadSuccess := false
  for op in ops do
    match op with
    | .okState value | .returnU64 value =>
        return some (lowered.push (.setLocal slot value), true, true)
    | .errorOverflow | .errorNamed _ =>
        return some (lowered.push op, hadSuccess, true)
    | .ite cmp lhs rhs thn els =>
        let some (thn', thnSuccess, thnTerminates) := lowerBindProducer slot thn
          | return none
        let some (els', elsSuccess, elsTerminates) := lowerBindProducer slot els
          | return none
        lowered := lowered.push (.ite cmp lhs rhs thn' els')
        hadSuccess := hadSuccess || thnSuccess || elsSuccess
        if thnTerminates && elsTerminates then
          return some (lowered, hadSuccess, true)
    | .letLocal .. | .joinLocal .. | .setLocal ..
    | .checkedAddU64 .. | .checkedSubU64 .. | .checkedMulU64 ..
    | .checkedDivU64 .. | .checkedModU64 .. | .forAccum .. =>
        lowered := lowered.push op
    | .forBody bound body =>
        let some (body', bodySuccess, bodyTerminates) := lowerBindProducer slot body
          | return none
        if bodySuccess || bodyTerminates then return none
        lowered := lowered.push (.forBody bound body')
    | .ext _ =>
        -- Target effects can precede a scalar success just like checked arithmetic. Preserve
        -- them in order; their own backend contracts fail closed before the join continuation.
        lowered := lowered.push op
    | _ => return none
  return some (lowered, hadSuccess, false)

/-- Like `lowerBindProducer`, but terminal success assigns `limbCount` consecutive `.returnU64`
values into `slot .. slot + limbCount - 1`. -/
private def terminalReturnLimbs? (limbCount : Nat) (ops : Array Ops.Op) : Option (Array Ops.Val) :=
  if ops.size < limbCount then none else
  let tail := ops.extract (ops.size - limbCount) ops.size
  tail.mapM fun op =>
    match op with
    | .returnU64 value => some value
    | _ => none

private partial def lowerBindProducerMulti (slot limbCount : Nat) (ops : Array Ops.Op) :
    Option (Array Ops.Op × Bool × Bool) :=
  if let some values := terminalReturnLimbs? limbCount ops then
    some (ops.extract 0 (ops.size - limbCount) ++ (Array.range limbCount).map fun i =>
      (.setLocal (slot + i) values[i]! : Ops.Op), true, true)
  else Id.run do
    let mut lowered := #[]
    let mut hadSuccess := false
    for op in ops do
      match op with
      | .errorOverflow | .errorNamed _ =>
          return some (lowered.push op, hadSuccess, true)
      | .ite cmp lhs rhs thn els =>
          let some (thn', thnSuccess, thnTerminates) := lowerBindProducerMulti slot limbCount thn
            | return none
          let some (els', elsSuccess, elsTerminates) := lowerBindProducerMulti slot limbCount els
            | return none
          lowered := lowered.push (.ite cmp lhs rhs thn' els')
          hadSuccess := hadSuccess || thnSuccess || elsSuccess
          if thnTerminates && elsTerminates then
            return some (lowered, hadSuccess, true)
      | .okState value =>
          if limbCount == 1 then
            return some (lowered.push (.setLocal slot value), true, true)
          else
            return none
      | .letLocal .. | .joinLocal .. | .setLocal ..
      | .checkedAddU64 .. | .checkedSubU64 .. | .checkedMulU64 ..
      | .checkedDivU64 .. | .checkedModU64 .. | .forAccum .. =>
          lowered := lowered.push op
      | .forBody bound body =>
          let some (body', bodySuccess, bodyTerminates) := lowerBindProducerMulti slot limbCount body
            | return none
          if bodySuccess || bodyTerminates then return none
          lowered := lowered.push (.forBody bound body')
      | .ext _ =>
          lowered := lowered.push op
      | _ => return none
    return some (lowered, hadSuccess, false)

private def boundaryBindArg (localDepth : Nat) (ty : Expr) : Expr :=
  let ty := ty.consumeMData
  let localRefLit (offset : Nat) : Expr :=
    mkApp (mkConst ``localRef) (mkNatLit (localDepth + offset))
  if isUInt128Type ty then
    mkApp (mkApp (mkConst ``ProofForge.Core.Value.UInt128.mk) (localRefLit 0))
      (localRefLit 1)
  else if isUInt256Type ty then
    mkApp (mkApp (mkApp (mkApp (mkConst ``ProofForge.Core.Value.UInt256.mk)
          (localRefLit 0)) (localRefLit 1)) (localRefLit 2)) (localRefLit 3)
  else
    localRefLit 0

private def joinLocals (localDepth limbCount : Nat) : Array Ops.Op :=
  (Array.range limbCount).map fun i => (.joinLocal (localDepth + i) : Ops.Op)

/-- After a fixed-limb bind producer stores into locals, the continuation must run on the success
path before the branch ends. Appending it after a top-level `ite` leaves `setLocal` sequences
without a terminal and drops JSON u128 returns on the floor. -/
private partial def appendBindContinuation (continuation : Array Ops.Op) (ops : Array Ops.Op) :
    Array Ops.Op :=
  match ops.toList with
  | [.ite cmp lhs rhs thn els] =>
      #[.ite cmp lhs rhs (appendBindContinuation continuation thn ++ continuation) els]
  | _ => ops ++ continuation

/-- The return of an ignored scalar helper is not a method return. Keep its branch structure and
effects, but splice the caller's continuation after every successful helper path. -/
private partial def dropIgnoredScalarTerminals (ops : Array Ops.Op) : Array Ops.Op :=
  ops.filterMap fun op =>
    match op with
    | .returnU64 _ | .okState _ => none
    | .ite cmp lhs rhs thn els =>
        some (.ite cmp lhs rhs (dropIgnoredScalarTerminals thn) (dropIgnoredScalarTerminals els))
    | .forBody n body => some (.forBody n (dropIgnoredScalarTerminals body))
    | op => some op

/-- Monadic join heads that sequence a fallible scalar producer into a continuation. -/
private def isExceptSequencerHead (e : Expr) : Bool :=
  isConstNamed e ``Bind.bind || endsWith e ".bind" ||
    isConstNamed e ``ProofForge.Core.Except.andThen || endsWith e ".andThen"

/-- A bind enclosing a loop belongs to the surrounding monadic control flow and must be decoded
before loop discovery. Binds inside the callback body are part of that iteration and do not hide
the state loop itself. -/
private def loopUnderBind (fuel : Nat) (e : Expr) (underBind : Bool := false) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    let e := strip e
    if e.getAppFn.constName? == some ``ForIn.forIn || endsWith e ".forIn" then underBind
    else if isExceptSequencerHead e then
      let args := e.getAppArgs
      if h : args.size ≥ 2 then
        let producer := args[args.size - 2]
        let continuation := args[args.size - 1]
        -- `forIn ... >>= continuation` is the loop's own sequencing bind. A loop in the
        -- producer is therefore not hidden by this bind. Decode that producer first even when
        -- its continuation contains another sequential loop; the recursive continuation decode
        -- will then own the later loop. If the producer has no loop, a continuation loop remains
        -- hidden under this bind and must wait for normal bind lowering.
        let producerOwnsLoop := producer.getUsedConstantsAsSet.toList.any fun name =>
          name == ``ForIn.forIn || name.toString.endsWith ".forIn"
        if producerOwnsLoop then loopUnderBind fuel' producer underBind
        else loopUnderBind fuel' producer underBind || loopUnderBind fuel' continuation true
      else
        args.any (loopUnderBind fuel' · true)
    else
      e.getAppArgs.any (loopUnderBind fuel' · underBind)

/-- A scalar let whose producer owns bounded control/effects needs one join local before its caller
can compare or transform the result. Ordinary scalar lets remain eligible for direct substitution. -/
private def isSequencedScalarProducer (env : Environment) (type value : Expr) : Bool :=
  type.consumeMData.getAppFn.constName? == some ``UInt64 &&
    (mentionsNearEffect env 16 value ||
      (findForIn env value).isSome ||
      (findForBodyExpr env value).isSome)

/-- Find one effect-free UInt64 helper below a pure expression wrapper whose bounded control must
be evaluated before the enclosing comparison/arithmetic expression. Never cross a control
boundary: branch arms and bind continuations retain their original evaluation order. Effectful
producers require an explicit source `let`, so replacing a repeated pure subtree cannot coalesce
effects. -/
private def nestedSequencedScalarHelper? (env : Environment) (e : Expr) : Option Expr :=
  let rec visit (fuel : Nat) (candidate : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let candidate := candidate.consumeMData
      let head := strip candidate
      if isConstNamed head ``ite || isConstNamed head ``dite || isExceptSequencerHead head then
        none
      else
        match unfoldUserHelper env candidate with
        | some (name, unfolded) =>
            match env.find? name with
            | some (.defnInfo info) =>
                if (resultType 16 info.type).consumeMData.getAppFn.constName? == some ``UInt64 &&
                    ((findForIn env unfolded).isSome || (findForBodyExpr env unfolded).isSome) then
                  some candidate
                else
                  candidate.getAppArgs.findSome? (visit fuel')
            | _ => candidate.getAppArgs.findSome? (visit fuel')
        | none => candidate.getAppArgs.findSome? (visit fuel')
  e.getAppArgs.findSome? (visit 16)

def decodeExpr (env : Environment) (fuel : Nat) (e : Expr)
    (stateful : Bool := false) (preserveLocals : Bool := false)
    (localDepth : Nat := 0) (stateType? : Option Name := none)
    (deepScalars : Bool := false) :
    Except String (Array Ops.Op) :=
  match fuel with
  | 0 => .error "extract/unsupported: ite depth"
  | fuel' + 1 => Id.run do
    -- Do-notation over a branch-selected inline helper can leave a head beta redex after the bind
    -- result is replaced by a lexical marker. Normalize that language-level composition before
    -- looking for effects or control flow; this keeps helper composition out of target Ops/Emit.
    let e := e.headBeta
    let e := (reducePureInlineMatch? env e).getD e
    -- NEAR N13: reject PromiseHandle APIs whose maxFanIn exceeds the fixed and3..and8 ladder.
    if let some reason := findPromiseHandleMaxFanInCeilingError env 64 e then
      return .error reason
    let stripped := strip e
    if isConstNamed stripped ``Id.run then
      if let some guarded := guardedRunBody? 64 stripped then
        return decodeExpr env fuel' guarded (stateful := stateful)
          (preserveLocals := preserveLocals) (localDepth := localDepth)
          (stateType? := stateType?) (deepScalars := deepScalars)
    match strip e with
    | .letE _ ty value body _ =>
      let ignoredInlineEffect :=
        if body.hasLooseBVar 0 then false
        else
          (decodeNearEffect env value).isSome ||
            match unfoldUserHelper env value with
            | some (_, unfolded) =>
                mentionsNearEffect env 64 unfolded
            | none => false
      if ignoredInlineEffect then
        match decodeExpr env fuel' value (preserveLocals := preserveLocals)
              (localDepth := localDepth) (stateType? := stateType?)
              (deepScalars := deepScalars),
            decodeExpr env fuel' (body.instantiate1 value) (stateful := stateful)
              (preserveLocals := preserveLocals) (localDepth := localDepth)
              (stateType? := stateType?) (deepScalars := deepScalars) with
        | .ok helperOps, .ok continuationOps =>
            return .ok (dropIgnoredScalarTerminals helperOps ++ continuationOps)
        | .error reason, _ =>
            return .error s!"extract/unsupported: inline effect helper: {reason}"
        | _, .error reason => return .error reason
      let effectful :=
        mentionsNearEffect env 16 value || (decodeNearEffect env value).isSome ||
          (findForIn env value).isSome || (findForBodyExpr env value).isSome
      let scalarControlProducer := isSequencedScalarProducer env ty value
      if scalarControlProducer then
        match decodeExpr env fuel' value (preserveLocals := preserveLocals)
            (localDepth := localDepth + 1) (stateType? := stateType?)
            (deepScalars := deepScalars) with
        | .error reason =>
            return .error s!"extract/unsupported: scalar control producer: {reason}"
        | .ok producerOps =>
          match lowerBindProducer localDepth producerOps with
          | some (joinedProducer, true, true) =>
            let marker := mkApp (mkConst ``localRef) (mkNatLit localDepth)
            match decodeExpr env fuel' (body.instantiate1 marker) (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth + 1)
                (stateType? := stateType?) (deepScalars := deepScalars) with
            | .ok continuationOps =>
                return .ok (#[.joinLocal localDepth] ++ joinedProducer ++ continuationOps)
            | .error reason =>
                return .error s!"extract/unsupported: scalar control continuation: {reason}"
          | _ =>
              return .error "extract/unsupported: scalar control producer has no value"
      else if !effectful then
        if let some source := sequentialStateSource? env ty value stateType? then
          match decodeYieldState env 128 localDepth value (stateType? := stateType?)
              (statePrefix := "") (deepScalars := deepScalars),
              decodeExpr env fuel' (body.instantiate1 source) (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth)
                (stateType? := stateType?) (deepScalars := deepScalars) with
          | .ok prior, .ok continuation => return .ok (prior ++ continuation)
          | .error reason, _ =>
            return .error s!"extract/unsupported: sequential state binding: {reason}"
          | _, .error reason => return .error reason
        else if ty.consumeMData.getAppFn.constName? == some ``UInt64 then
          match localScalarValue? env (if deepScalars then 128 else 32) value with
          | some localValue =>
            if preserveLocals && shouldMaterializeLocal ty localValue then
              let marker := mkApp (mkConst ``localRef) (mkNatLit localDepth)
              match decodeExpr env fuel' (body.instantiate1 marker)
                  (stateful := stateful) (preserveLocals := preserveLocals)
                  (localDepth := localDepth + 1) (stateType? := stateType?)
                  (deepScalars := deepScalars) with
              | .ok ops => return .ok (#[.letLocal localDepth localValue] ++ ops)
              | .error reason => return .error reason
            else
              return decodeExpr env fuel' (body.instantiate1 value)
                (stateful := stateful) (preserveLocals := preserveLocals)
                (localDepth := localDepth) (stateType? := stateType?)
                (deepScalars := deepScalars)
          | _ =>
            return decodeExpr env fuel' (body.instantiate1 value)
              (stateful := stateful) (preserveLocals := preserveLocals)
              (localDepth := localDepth) (stateType? := stateType?)
              (deepScalars := deepScalars)
        else
          return decodeExpr env fuel' (body.instantiate1 value)
            (stateful := stateful) (preserveLocals := preserveLocals)
            (localDepth := localDepth) (stateType? := stateType?)
            (deepScalars := deepScalars)
    | _ => pure ()
    if let some producer := nestedSequencedScalarHelper? env e then
      match decodeExpr env fuel' producer (preserveLocals := preserveLocals)
          (localDepth := localDepth + 1) (stateType? := stateType?)
          (deepScalars := deepScalars) with
      | .error reason =>
          return .error s!"extract/unsupported: nested scalar control producer: {reason}"
      | .ok producerOps =>
        match lowerBindProducer localDepth producerOps with
        | some (joinedProducer, true, true) =>
            let marker := mkApp (mkConst ``localRef) (mkNatLit localDepth)
            let continuation := e.replace fun candidate =>
              if candidate == producer then some marker else none
            match decodeExpr env fuel' continuation (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth + 1)
                (stateType? := stateType?) (deepScalars := deepScalars) with
            | .ok continuationOps =>
                return .ok (#[.joinLocal localDepth] ++ joinedProducer ++ continuationOps)
            | .error reason =>
                return .error s!"extract/unsupported: nested scalar control continuation: {reason}"
        | _ =>
            return .error "extract/unsupported: nested scalar control producer has no value"
    -- Branch decoders normalize their arms independently. Zeta-reducing the entire branch here
    -- duplicates let-bound State transitions into every projection before the sequential-state
    -- boundary can consume them, making composed record updates exponential.
    let structured := strip e
    let fullySubstituted :=
      if isConstNamed structured ``ite || isConstNamed structured ``dite then e
      else substLets 256 e
    let controlled := peelControl 16 fullySubstituted
    let e :=
      if (unfoldUserHelper env fullySubstituted).isSome then fullySubstituted
      else if (unfoldUserHelper env controlled).isSome then controlled
      else e
    let e0 := strip e
    if isExceptSequencerHead e0 && e0.getAppArgs.size ≥ 2 then
      let args := e0.getAppArgs
      let producer := args[args.size - 2]!
      let continuation := args[args.size - 1]!
      match strip continuation with
      | .lam _ ty body _ =>
        if isScalarResult env ty then
          match decodeExpr env fuel' producer (preserveLocals := preserveLocals)
              (localDepth := localDepth + 1) (stateType? := stateType?)
              (deepScalars := deepScalars) with
          | .error reason =>
              return .error s!"extract/unsupported: bind producer: {reason}"
          | .ok producerOps =>
            match lowerBindProducer localDepth producerOps with
            | some (joinedProducer, true, true) =>
              let marker := mkApp (mkConst ``localRef) (mkNatLit localDepth)
              match decodeExpr env fuel' (body.instantiate1 marker) (stateful := stateful)
                  (preserveLocals := preserveLocals) (localDepth := localDepth + 1)
                  (stateType? := stateType?) (deepScalars := deepScalars) with
              | .ok continuationOps =>
                  return .ok (#[.joinLocal localDepth] ++ joinedProducer ++ continuationOps)
              | .error reason =>
                  return .error s!"extract/unsupported: bind continuation: {reason}"
            | _ =>
                return .error "extract/unsupported: bind producer is not a scalar control value"
        else if let some limbCount := fixedLimbBindCount? env ty then
          let producer := unfoldUserHelpers env 16 producer
          match decodeExpr env fuel' producer (preserveLocals := preserveLocals)
              (localDepth := localDepth + limbCount) (stateType? := stateType?)
              (deepScalars := deepScalars) with
          | .error reason =>
              return .error s!"extract/unsupported: bind producer: {reason}"
          | .ok producerOps =>
            match lowerBindProducerMulti localDepth limbCount producerOps with
            | some (joinedProducer, true, true) =>
              let boundArg := boundaryBindArg localDepth ty
              match decodeExpr env fuel' (body.instantiate1 boundArg) (stateful := stateful)
                  (preserveLocals := preserveLocals) (localDepth := localDepth + limbCount)
                  (stateType? := stateType?) (deepScalars := deepScalars) with
              | .ok continuationOps =>
                  let joined := appendBindContinuation continuationOps joinedProducer
                  return .ok (joinLocals localDepth limbCount ++ joined)
              | .error reason =>
                  return .error s!"extract/unsupported: bind continuation: {reason}"
            | _ =>
                return .error "extract/unsupported: bind producer is not a fixed-limb boundary value"
        else
          pure ()
      | _ => pure ()
    let scalarLoop? : Option (Except String (Array Ops.Op)) :=
      match if loopUnderBind 64 e then none else findForStateExpr env e with
      | none => none
      | some (n, initial, bodyE, continuation) =>
        match scalarFrameLeaves initial with
        | none => none
        | some leaves =>
          if leaves.size < 2 || isForInDone bodyE then none else some do
            let frame ←
              match scalarFrameLocalShape initial localDepth with
              | some frame => .ok frame
              | none => .error "extract/unsupported: scalar frame local shape"
            let initialValues ← leaves.mapM fun leaf =>
              match val env leaf with
              | some value => .ok value
              | none => .error "extract/unsupported: scalar frame initial value"
            let body := markScalarFrameYields localDepth (bodyE.instantiate1 frame)
            let bodyOps ←
              match decodeExpr env fuel' body (stateful := true) (preserveLocals := true)
                  (localDepth := localDepth + 2 * leaves.size) (stateType? := stateType?)
                  (deepScalars := n > 4) with
              | .ok ops => .ok ops
              | .error reason =>
                  .error s!"extract/unsupported: scalar frame body: {reason}"
            let continuation := continuation.instantiate1 frame
            let continuation :=
              (reduceScalarFrameContinuation? env continuation frame).getD continuation
            let continuationOps ←
              match decodeExpr env fuel' continuation (stateful := true)
                  (preserveLocals := preserveLocals)
                  (localDepth := localDepth + 2 * leaves.size) (stateType? := stateType?)
                  (deepScalars := n > 4) with
              | .ok ops => .ok ops
              | .error reason =>
                  .error s!"extract/unsupported: scalar frame continuation: {reason}"
            let initialOps := initialValues.mapIdx fun index value =>
              (.letLocal (localDepth + index) value : Ops.Op)
            return initialOps ++ #[.forBody n (bodyOps.map rewriteLoopOp)] ++ continuationOps
    if let some result := scalarLoop? then
      return result
    let stateLoop? : Option (Except String (Array Ops.Op)) :=
      -- State-loop callbacks capture scalar outer lets by value, while their mutable state binder
      -- must remain visible so `findForStateExpr` can distinguish them from ordinary loops.
      match if loopUnderBind 64 e then none else findForStateExpr env e with
      | none => none
      | some (n, initial, bodyE, continuation) =>
        if isForInDone bodyE then none else
        match decodeYieldState env 128 localDepth initial (stateType? := stateType?),
            decodeExpr env fuel' bodyE (stateful := true)
              (preserveLocals := preserveLocals) (localDepth := localDepth)
              (stateType? := stateType?) (deepScalars := n > 4) with
        | .error reason, _ =>
            some (.error s!"extract/unsupported: state loop initial value: {reason}")
        | _, .error reason => some (.error s!"extract/unsupported: state loop body: {reason}")
        | .ok initialOps, .ok bodyOps =>
          if Ops.hasStoreField bodyOps || Ops.hasIndexSet bodyOps then
            match decodeExpr env fuel' continuation (stateful := true)
                (preserveLocals := preserveLocals)
                (localDepth := localDepth) (stateType? := stateType?)
                (deepScalars := n > 4) with
            | .error reason =>
              some (.error s!"extract/unsupported: state loop continuation: {reason}")
            | .ok continuationOps =>
              some (.ok (initialOps ++ #[.forBody n (bodyOps.map rewriteLoopOp)] ++
                continuationOps))
          else none
    if let some result := stateLoop? then
      return result
    else if (isConstNamed e0 ``ite || isConstNamed e0 ``dite) && e0.getAppArgs.size ≥ 5 then
      -- 已经是比较 / dite，不要再往下搜 forIn（循环体自己就是 ite）。
      pure ()
    else if let some (name, unfolded) := unfoldUserHelper env e then
      -- A marked helper owns its control flow. Expose that control flow before recursive
      -- effect discovery, which must never select a nested effect and erase an enclosing
      -- branch.
      match decodeExpr env fuel' (substIteLets 256 unfolded) (stateful := stateful)
          (preserveLocals := preserveLocals) (localDepth := localDepth)
          (stateType? := stateType?) (deepScalars := deepScalars) with
      | .ok ops => return .ok ops
      | .error reason => return .error s!"extract/unsupported: inline {name}: {reason}"
    else if let some ops := decodeNearEffect env e then
      return .ok ops
    else if let some (n, addend) := findForIn env e then
      return .ok #[.forAccum n addend localDepth, .returnU64 (.local localDepth)]
    else if let some (n, bodyE) := findForBodyExpr env e then
      match decodeExpr env fuel' bodyE (preserveLocals := preserveLocals)
          (localDepth := localDepth) (stateType? := stateType?)
          (deepScalars := deepScalars) with
      | .ok ops => return .ok #[.forBody n (ops.map rewritePlainLoopOp), .errorOverflow]
      | .error r => return .error r
    let e := strip e
    if (isConstNamed e ``ite || isConstNamed e ``dite) && e.getAppArgs.size ≥ 5 then
      let args := e.getAppArgs
      let rec peelProofLam (fuel : Nat) (lower : Bool) (e : Expr) : Expr :=
        match fuel with
        | 0 => e
        | fuel' + 1 =>
          match strip e with
          -- 先代入 `have __src`，再降 proof λ。反过来会把 `h` 叠到 `__src` 上。
          | .lam _ _ body _ =>
            let body := substIteLets 16 body
            let body := if lower then body.lowerLooseBVars 1 1 else body
            peelProofLam fuel' lower body
          | e => e
      -- 不在这里 peelLets：效应调用必须留给 decodeNearEffect。
      -- 只代 then / else：入口代整个 ite 会把 `have y` 塞进 `y ≠ 0`，asCmp 认不出。
      let tRaw := args[args.size - 2]!
      let fRaw := args[args.size - 1]!
      let lower :=
        stateful ||
          (!(collectIndexSets env tRaw).isEmpty &&
            !isForInStep tRaw && !isForInStep fRaw)
      let t := peelProofLam 4 lower tRaw
      let f := peelProofLam 4 stateful fRaw
      -- Preserve lexical scalar reads in an effectful arm so its recursive decoder can
      -- materialize them before a later write consumes them.
      -- Substituting here would embed the read into the effect operand and could re-read mutated
      -- storage. NEAR effects need the same treatment: zeta-reducing an ignored raw-storage
      -- result here would silently erase the host mutation before the arm is decoded.
      let t :=
        if containsStructuredStateLet env 64 t ||
            mentionsNearEffect env 64 t then t
        else substIteLets 64 t
      let f :=
        if containsStructuredStateLet env 64 f ||
            mentionsNearEffect env 64 f then f
        else substIteLets 64 f
      let checkedSubMatches (candidate : Expr) : Bool :=
        match asCheckedSubGuard env candidate with
        | none => false
        | some (guardLhs, guardRhs) =>
          let directResult :=
            match strip t with
            | .letE _ _ value _ _ => val env value
            | _ => asOkState env t
          let directMatch :=
            match directResult with
            | some (.subU64 bodyLhs bodyRhs) =>
                guardLhs == bodyLhs && guardRhs == bodyRhs
            | _ => false
          let nestedMatch :=
            match lastNamedBin env ``HSub.hSub t with
            | some (bodyLhs, bodyRhs) =>
                guardLhs == bodyLhs && guardRhs == bodyRhs
            | none => false
          directMatch || nestedMatch
      let rec hasNestedIte (fuel : Nat) (e : Expr) : Bool :=
        match fuel with
        | 0 => false
        | fuel' + 1 =>
          let e := strip e
          if isConstNamed e ``ite || isConstNamed e ``dite then true
          else
            match e with
            | .letE _ _ value body _ =>
                hasNestedIte fuel' value || hasNestedIte fuel' body
            | .lam _ _ body _ => hasNestedIte fuel' body
            | .app fn arg => hasNestedIte fuel' fn || hasNestedIte fuel' arg
            | _ => false
      if isErrorOverflow f && !isForInYield f then
        if let some condE := findBy args (fun a =>
            (asCmp env a).isSome &&
              (asCheckedAddGuard env a).isNone &&
              (asCheckedMulGuard env a).isNone &&
              !checkedSubMatches a &&
              -- 真支再套 ite 时，`y ≠ 0` 是比较，不是除法守卫。
              ((asNeZero env a).isNone ||
                isConstNamed (peelLets (strip t)) ``ite ||
                  isConstNamed (peelLets (strip t)) ``dite)) then
          let decodedThen := decodeExpr env fuel' t (stateful := stateful)
            (preserveLocals := preserveLocals) (localDepth := localDepth)
            (stateType? := stateType?) (deepScalars := deepScalars)
          let structuredThen := containsStructuredStateLet env 2048 t ||
            containsInlineStateTransition env 2048 t
          if let .ok thn := decodedThen then
            let rec hasNearEffect (fuel : Nat) (ops : Array Ops.Op) : Bool :=
              match fuel with
              | 0 => false
              | fuel' + 1 => ops.any fun op =>
                  match op with
                  | .ext (.near _) => true
                  | .ite _ _ _ nestedThen nestedElse =>
                      hasNearEffect fuel' nestedThen || hasNearEffect fuel' nestedElse
                  | .forBody _ body => hasNearEffect fuel' body
                  | _ => false
            -- A state-producing arm may also contain an ignored NEAR storage/log/memory result.
            -- Prefer the recursively decoded sequence over `asStoreFields`; the latter sees only
            -- the final state constructor and would silently discard the preceding host effect.
            if hasNearEffect 8 thn then
              match asCmp env condE with
              | some (cmp, lv, rv) =>
                  return .ok #[.ite cmp lv rv thn #[.errorOverflow]]
              | none => pure ()
            if thn.any fun | .letLocal .. => true | _ => false then
              match asCmp env condE with
              | some (cmp, lv, rv) =>
                return .ok #[.ite cmp lv rv thn #[.errorOverflow]]
              | none => pure ()
          match asCmp env condE, asIndexSet env t,
              asStoreFields env t true, asOkState env t, decodedThen with
          | some (cmp, lv, rv), some iset, _, _, _ =>
            if structuredThen || hasNestedIte 64 t then
              match decodeExpr env fuel' t (stateful := stateful)
                  (preserveLocals := preserveLocals) (localDepth := localDepth)
                  (stateType? := stateType?) (deepScalars := deepScalars) with
              | .ok thn => return .ok #[.ite cmp lv rv thn #[.errorOverflow]]
              | .error r => return .error r
            else
              let isets := collectIndexSets env t
              let ops := if isets.size ≥ 1 then isets else #[iset]
              match asStoreFields env t true with
              | some stores =>
                return .ok #[.ite cmp lv rv
                  (ops ++ dropVectorRootStores ops stores) #[.errorOverflow]]
              | none =>
                match ops[ops.size - 1]! with
                | .indexSetLeaf _ _ v _ _ | .indexSet _ _ v _ _ =>
                  -- 多叶 set 的返回值是 `.ok (_, y)`。循环体不要用 findOkRet。
                  let ret :=
                    if isForInStep t then v else (findOkRet env t).getD v
                  return .ok #[.ite cmp lv rv (ops.push (.okState ret)) #[.errorOverflow]]
                | _ => return .ok #[.ite cmp lv rv ops #[.errorOverflow]]
          | some (cmp, lv, rv), none, some stores, _, _ =>
            return .ok #[.ite cmp lv rv (snapshotStateUpdate localDepth stores) #[.errorOverflow]]
          | some (cmp, lv, rv), none, none, some v, _ =>
            return .ok #[.ite cmp lv rv #[.okState v] #[.errorOverflow]]
          | some (cmp, lv, rv), none, none, none, .ok thn =>
            match decodeExpr env fuel' f (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth)
                (stateType? := stateType?) (deepScalars := deepScalars) with
            | .ok els => return .ok #[.ite cmp lv rv thn els]
            | .error _ => return .ok #[.ite cmp lv rv thn #[.errorOverflow]]
          | some _, none, none, none, .error reason =>
            return .error s!"extract/unsupported: comparison continuation: {reason}"
          | _, _, _, _, _ => return .error "extract/unsupported: ite then/cmp"
        else if let some condE := findBy args (fun a => (asCheckedAddGuard env a).isSome) then
          match asCheckedAddGuard env condE,
              decodeExpr env fuel' t (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth)
                (stateType? := stateType?) (deepScalars := deepScalars), asStoreFields env t,
              asOkState env t with
          | some (lhs, rhs), .ok thn, _, _ =>
            -- then 支可以再套比较。先做 checked-add，再跑内层。
            -- 内层若只是 okState，仍压成旧的三连。
            match thn.toList with
            | [.okState v] =>
              let dest := match lhs with | .field .. => lhs | _ => v
              return .ok #[.checkedAddU64 lhs rhs, .okState dest, .errorOverflow]
            | _ =>
              return .ok (#[.checkedAddU64 lhs rhs] ++ thn)
          | some (lhs, rhs), .error _, some stores, _ =>
            return .ok (#[.checkedAddU64 lhs rhs] ++ stores)
          | some (lhs, rhs), .error _, none, some v =>
            let dest := match lhs with | .field .. => lhs | _ => v
            return .ok #[.checkedAddU64 lhs rhs, .okState dest, .errorOverflow]
          | some _, .error reason, none, none =>
            return .error s!"extract/unsupported: checked-add continuation: {reason}"
          | _, _, _, _ => return .error "extract/unsupported: ite then/add"
        else if let some condE := findBy args (fun a =>
            (asCheckedMulGuard env a).isSome && (collectIndexSets env t).isEmpty) then
          match asCheckedMulGuard env condE,
              decodeExpr env fuel' t (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth)
                (stateType? := stateType?) (deepScalars := deepScalars),
              asStoreFields env t, asOkState env t with
          | some (lhs, rhs), _, some stores, _ =>
            match stores.toList with
            | [.okState v] =>
              let dest := match lhs with | .field .. => lhs | _ => v
              return .ok #[.checkedMulU64 lhs rhs, .okState dest, .errorOverflow]
            | _ =>
              return .ok (#[.checkedMulU64 lhs rhs] ++ stores ++ #[.errorOverflow])
          | some (lhs, rhs), .ok thn, none, _ =>
            match thn.toList with
            | [.okState v] =>
              let dest := match lhs with | .field .. => lhs | _ => v
              return .ok #[.checkedMulU64 lhs rhs, .okState dest, .errorOverflow]
            | _ =>
              return .ok (#[.checkedMulU64 lhs rhs] ++ thn ++ #[.errorOverflow])
          | some (lhs, rhs), .error _, none, some v =>
            let dest := match lhs with | .field .. => lhs | _ => v
            return .ok #[.checkedMulU64 lhs rhs, .okState dest, .errorOverflow]
          | some _, .error reason, none, none =>
            return .error s!"extract/unsupported: checked-mul continuation: {reason}"
          | _, _, _, _ => return .error "extract/unsupported: ite then/mul"
        else if let some condE := findBy args (fun a =>
            checkedSubMatches a && (collectIndexSets env t).isEmpty) then
          match asCheckedSubGuard env condE,
              decodeExpr env fuel' t (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth)
                (stateType? := stateType?) (deepScalars := deepScalars),
              decodeExpr env fuel' f (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth)
                (stateType? := stateType?) (deepScalars := deepScalars), asStoreFields env t,
              asOkState env t with
          | some (lhs, rhs), _, .ok #[.errorOverflow], _, some v =>
            let dest := match lhs with | .field .. => lhs | _ => v
            return .ok #[.checkedSubU64 lhs rhs, .okState dest, .errorOverflow]
          | some _, .ok thn, .ok els, _, _ =>
            let some (cmp, lv, rv) := asCmp env condE
              | return .error "extract/unsupported: ite then"
            return .ok #[.ite cmp lv rv thn els]
          | some (lhs, rhs), _, _, some stores, _ =>
            return .ok (#[.checkedSubU64 lhs rhs] ++ stores)
          | some (lhs, rhs), _, _, none, some v =>
            let dest := match lhs with | .field .. => lhs | _ => v
            return .ok #[.checkedSubU64 lhs rhs, .okState dest, .errorOverflow]
          | _, _, _, _, _ => return .error "extract/unsupported: ite then/sub"
        else if let some condE := findBy args (fun a =>
            (asNeZero env a).isSome && (collectIndexSets env t).isEmpty) then
          match asNeZero env condE with
          | none => return .error "extract/unsupported: ite then"
          | some den =>
            let v := (asOkState env t).getD (.arg 0)
            let fallback := (.field (.arg 1) "value", den)
            if (lastNamedBin env ``HMod.hMod t).isSome then
              let (lhs, rhs) := (lastNamedBin env ``HMod.hMod t).getD fallback
              return .ok #[.checkedModU64 lhs (if rhs == den then rhs else den), .okState v, .errorOverflow]
            else if (lastNamedBin env ``UInt64.mod t).isSome then
              let (lhs, rhs) := (lastNamedBin env ``UInt64.mod t).getD fallback
              return .ok #[.checkedModU64 lhs (if rhs == den then rhs else den), .okState v, .errorOverflow]
            else
              let (lhs, rhs) := (lastNamedBin env ``HDiv.hDiv t).getD fallback
              return .ok #[.checkedDivU64 lhs (if rhs == den then rhs else den), .okState v, .errorOverflow]
        else
          let condE := args[args.size - 4]!
          match asCondition env condE,
              decodeExpr env fuel' t (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth)
                (stateType? := stateType?) (deepScalars := deepScalars) with
          | some (cmp, lv, rv), .ok thn =>
            return .ok #[.ite cmp lv rv thn #[.errorOverflow]]
          | _, _ => return .error "extract/unsupported: ite cond"
      else
        let isValueCmp (a : Expr) : Bool :=
          (asCmp env a).isSome &&
            (asCheckedAddGuard env a).isNone &&
            (asCheckedMulGuard env a).isNone &&
            !checkedSubMatches a
        if isForInYield f && !stateful then
          let some condE := findBy args isValueCmp <|> findBy args (fun a => (asCmp env a).isSome)
            | return .error s!"extract/unsupported: ite cond: {args[args.size - 4]!}"
          let some (cmp, lv, rv) := asCmp env condE
            | return .error s!"extract/unsupported: ite cond: {condE}"
          match decodeExpr env fuel' t (stateful := stateful)
              (preserveLocals := preserveLocals) (localDepth := localDepth)
              (stateType? := stateType?) (deepScalars := deepScalars) with
          | .ok thn => return .ok #[.ite cmp lv rv thn #[]]
          | .error r => return .error s!"extract/unsupported: forBody then {r}"
        let some condE := findBy args isValueCmp <|> findBy args (fun a => (asCmp env a).isSome)
          | match asCondition env args[args.size - 4]! with
            | some condition =>
              match decodeExpr env fuel' t (stateful := stateful)
                    (preserveLocals := preserveLocals) (localDepth := localDepth)
                    (stateType? := stateType?) (deepScalars := deepScalars),
                  decodeExpr env fuel' f (stateful := stateful)
                    (preserveLocals := preserveLocals) (localDepth := localDepth)
                    (stateType? := stateType?) (deepScalars := deepScalars) with
              | .ok thn, .ok els => return .ok #[.ite condition.1 condition.2.1 condition.2.2 thn els]
              | .error r, _ =>
                return .error (if stateful then s!"state loop then: {r}" else s!"ite then: {r}")
              | _, .error r =>
                return .error (if stateful then s!"state loop else: {r}" else s!"ite else: {r}")
            | none => return .error s!"extract/unsupported: ite cond: {args[args.size - 4]!}"
        let some (cmp, lv, rv) := asCmp env condE
          | return .error s!"extract/unsupported: ite cond: {condE}"
        match decodeExpr env fuel' t (stateful := stateful)
              (preserveLocals := preserveLocals) (localDepth := localDepth)
              (stateType? := stateType?) (deepScalars := deepScalars),
            decodeExpr env fuel' f (stateful := stateful)
              (preserveLocals := preserveLocals) (localDepth := localDepth)
              (stateType? := stateType?) (deepScalars := deepScalars) with
        | .ok thn, .ok els => return .ok #[.ite cmp lv rv thn els]
        | .error r, _ =>
          return .error (if stateful then s!"state loop then: {r}" else s!"ite then: {r}")
        | _, .error r =>
          return .error (if stateful then s!"state loop else: {r}" else s!"ite else: {r}")
    else if let some ops := decodeNearEffect env e then
      return .ok ops
    else if let some reduced := reduceUInt64NewtypeMatch? env e then
      return decodeExpr env fuel' reduced (stateful := stateful)
        (preserveLocals := preserveLocals) (localDepth := localDepth)
        (stateType? := stateType?) (deepScalars := deepScalars)
    else if isUInt64VariantMatcher env e then
      let args := e.getAppArgs
      let some matcherName := e.getAppFn.constName?
        | return .error "extract/unsupported: variant matcher name"
      let some info := Lean.Meta.getMatcherInfoCore? env matcherName
        | return .error "extract/unsupported: variant matcher metadata"
      let some variantName := matcherDiscrTypeName? env e
        | return .error "extract/unsupported: variant discriminant type"
      let some payloadWidth := uint64VariantPayloadWidth? env variantName
        | return .error "extract/unsupported: variant payload layout"
      let some disc := args[info.getFirstDiscrPos]?
        | return .error "extract/unsupported: variant discriminant"
      let tag :=
        match val env disc with
        | some (.field base name) =>
          if name.endsWith "_tag" then .field base name else .field base s!"{name}_tag"
        | some base => .field base "variant_tag"
        | none => .field (.arg 0) "variant_tag"
      let payloads : Array Ops.Val := Id.run do
        let mut payloads : Array Ops.Val := #[]
        for index in [:payloadWidth] do
          let payload :=
            match tag with
            | .field base name =>
              let root := if name.endsWith "_tag" then name.dropEnd 4 |>.copy else name
              .field base s!"{root}_p{index}"
            | _ => .field (.arg 0) s!"variant_p{index}"
          payloads := payloads.push payload
        return payloads
      let alternativesResult : Except String (Array (Array Ops.Op)) := Id.run do
        let mut alternatives : Array (Array Ops.Op) := #[]
        for index in [:info.numAlts] do
          let some altInfo := info.altInfos[index]?
            | return .error "extract/unsupported: variant alternative metadata"
          let some altExpr := args[info.getFirstAltPos + index]?
            | return .error "extract/unsupported: variant alternative"
          if altInfo.numFields > payloads.size then
            return .error "extract/unsupported: variant alternative exceeds payload layout"
          let altBody? : Option Expr := Id.run do
            let mut body := altExpr
            for fieldIndex in [:altInfo.numFields] do
              match strip body with
              | .lam _ _ lamBody _ =>
                let marker := mkApp (mkConst ``localRef) (mkNatLit (localDepth + fieldIndex))
                body := lamBody.instantiate1 marker
              | _ => return none
            return some body
          let some altBody := altBody?
            | return .error "extract/unsupported: variant alternative binders"
          -- Lean represents a nullary matcher branch as `Unit → result`; payload alternatives
          -- have already consumed their source-field binders above.
          let altBody := peelMatcherLams 8 altBody
          match decodeExpr env fuel' altBody (stateful := stateful)
              (preserveLocals := preserveLocals)
              (localDepth := localDepth + altInfo.numFields) (stateType? := stateType?)
              (deepScalars := deepScalars) with
          | .ok ops =>
            let mut withPayloads : Array Ops.Op := #[]
            for fieldIndex in [:altInfo.numFields] do
              withPayloads := withPayloads.push
                (.letLocal (localDepth + fieldIndex) payloads[fieldIndex]!)
            alternatives := alternatives.push (withPayloads ++ ops)
          | .error reason => return .error reason
        return .ok alternatives
      match alternativesResult with
      | .error reason => return .error reason
      | .ok alternatives =>
        let mut chain : Array Ops.Op := #[.errorNamed "invalidVariant"]
        for offset in [:alternatives.size] do
          let index := alternatives.size - 1 - offset
          chain := #[.ite .eq tag (.lit (UInt64.ofNat index)) alternatives[index]! chain]
        return .ok chain
    else if isOptionLikeMatcher env e && e.getAppArgs.size ≥ 3 then
      -- `match opt with | none => a | some n => b` → ite (eq tag 0) a b。
      let args := e.getAppArgs
      let disc := args[args.size - 3]!
      let noneE := peelLets args[args.size - 2]!
      let someE := peelLets args[args.size - 1]!
      let tag :=
        match val env disc with
        | some (.field b n) =>
          if n.endsWith "_tag" then .field b n else .field b s!"{n}_tag"
        | some b => .field b "slot_tag"
        | none => .field (.arg 0) "slot_tag"
      let payload :=
        match tag with
        | .field b n =>
          let base := if n.endsWith "_tag" then n.dropEnd 4 |>.copy else n
          .field b s!"{base}_p0"
        | _ => .field (.arg 0) "slot_p0"
      let noneBody := peelMatcherLams 8 noneE
      match decodeExpr env fuel' noneBody (stateful := stateful)
          (preserveLocals := preserveLocals) (localDepth := localDepth)
          (stateType? := stateType?) (deepScalars := deepScalars) with
      | .error r => return .error r
      | .ok noneOps =>
        match strip someE with
        | .lam _ _ body _ =>
          match strip body with
          | .bvar 0 =>
            return .ok #[.ite .eq tag (.lit 0) noneOps #[.returnU64 payload]]
          | _ =>
            let marker := mkApp (mkConst ``localRef) (mkNatLit localDepth)
            let someBody := peelMatcherLams 8 (body.instantiate1 marker)
            match decodeExpr env fuel' someBody (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth + 1)
                (stateType? := stateType?) (deepScalars := deepScalars) with
            | .ok someOps =>
              return .ok #[.ite .eq tag (.lit 0) noneOps
                (#[.letLocal localDepth payload] ++ someOps)]
            | .error r => return .error r
        | _ =>
          let someBody := peelMatcherLams 8 someE
          let someOps :=
            match strip someBody with
            | .bvar _ => #[.returnU64 payload]
            | _ =>
              match decodeExpr env fuel' someBody (stateful := stateful)
                  (preserveLocals := preserveLocals) (localDepth := localDepth)
                  (stateType? := stateType?) (deepScalars := deepScalars) with
              | .ok ops =>
                match ops with
                | #[.returnU64 (.arg _)] => #[.returnU64 payload]
                | #[.returnState (.arg _)] => #[.returnU64 payload]
                | _ => ops
              | .error _ => #[.returnU64 payload]
          return .ok #[.ite .eq tag (.lit 0) noneOps someOps]
    else
      return decodePlain env e stateful localDepth stateType? deepScalars


end ProofForge.Extract
