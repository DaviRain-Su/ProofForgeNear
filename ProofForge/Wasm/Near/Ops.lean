import ProofForge.Core.Ops
import ProofForge.Core.CFG
import ProofForge.Wasm.Near.Memory
import ProofForge.Wasm.Near.Codec

/-!
# NEAR target dialect

Value/effect extensions owned by the NEAR Protocol chain. v0 admits scalar
context reads, lossless u128 token values, lossless 64-byte account-id leaves,
invocation-memory operations, bounded raw storage, static Promise calls, one static self-callback
edge, native transfers, bounded callback-result observation, and view-safe hashing /
signature host calls (`sha256` / `keccak256` / `keccak512` / `ripemd160` / `ecrecover` /
`ed25519_verify`).
`reserved` is rejected by `wellFormed`.
-/

namespace ProofForge.Wasm.Near.Ops

/-- NEAR-owned value intrinsics. -/
inductive ValKind where
  | blockIndex
  | blockTimestamp
  | storageUsage
  /-- Legacy predecessor w0 plus the remaining lossless AccountId leaves. -/
  | predecessor
  | predecessorLen
  | predecessorW1 | predecessorW2 | predecessorW3 | predecessorW4
  | predecessorW5 | predecessorW6 | predecessorW7
  /-- Legacy checked UInt64 leaves plus lossless u128 low/high leaves. -/
  | attachedDeposit
  | attachedDepositW0 | attachedDepositW1
  | accountBalance
  | accountBalanceW0 | accountBalanceW1
  /-- Locked (staked) balance leaves; lossless u128 low/high. -/
  | accountLockedBalance
  | accountLockedBalanceW0 | accountLockedBalanceW1
  /-- Chain/gas context leaves. -/
  | epochHeight
  | prepaidGas
  | usedGas
  /-- Pure checked-u128 predicates and modular limbs; operands are left lo/hi, right lo/hi. -/
  | nearTokenAddOk | nearTokenAddW0 | nearTokenAddW1
  | nearTokenSubOk | nearTokenSubW0 | nearTokenSubW1
  | nearTokenMulU64Ok | nearTokenMulU64W0 | nearTokenMulU64W1
  /-- Legacy current-account w0 plus the remaining lossless AccountId leaves. -/
  | currentAccountId
  | currentAccountIdLen
  | currentAccountIdW1 | currentAccountIdW2 | currentAccountIdW3 | currentAccountIdW4
  | currentAccountIdW5 | currentAccountIdW6 | currentAccountIdW7
  /-- Legacy signer w0 plus the remaining lossless AccountId leaves. -/
  | signer
  | signerLen
  | signerW1 | signerW2 | signerW3 | signerW4
  | signerW5 | signerW6 | signerW7
  /-- `signer_account_pk` 33 bytes (curve tag + key) as five little-endian windows. -/
  | signerPk
  | signerPkW1 | signerPkW2 | signerPkW3 | signerPkW4
  /-- `random_seed` 32 bytes as four little-endian windows. -/
  | randomSeed
  | randomSeedW1 | randomSeedW2 | randomSeedW3
  /-- Crypto host result windows. Capacity is the declared result bound; bytes pack little-endian. -/
  | sha256ResultW0 (capacity : Nat) | sha256ResultW1 (capacity : Nat)
  | sha256ResultW2 (capacity : Nat) | sha256ResultW3 (capacity : Nat)
  | keccak256ResultW0 (capacity : Nat) | keccak256ResultW1 (capacity : Nat)
  | keccak256ResultW2 (capacity : Nat) | keccak256ResultW3 (capacity : Nat)
  | keccak512ResultW0 (capacity : Nat) | keccak512ResultW1 (capacity : Nat)
  | keccak512ResultW2 (capacity : Nat) | keccak512ResultW3 (capacity : Nat)
  | keccak512ResultW4 (capacity : Nat) | keccak512ResultW5 (capacity : Nat)
  | keccak512ResultW6 (capacity : Nat) | keccak512ResultW7 (capacity : Nat)
  /-- RIPEMD-160 is 20 bytes; W2 holds the last 4 bytes zero-padded. -/
  | ripemd160ResultW0 (capacity : Nat) | ripemd160ResultW1 (capacity : Nat)
  | ripemd160ResultW2 (capacity : Nat)
  | ecrecoverStatus (capacity : Nat)
  | ecrecoverResultW0 (capacity : Nat) | ecrecoverResultW1 (capacity : Nat)
  | ecrecoverResultW2 (capacity : Nat) | ecrecoverResultW3 (capacity : Nat)
  | ecrecoverResultW4 (capacity : Nat) | ecrecoverResultW5 (capacity : Nat)
  | ecrecoverResultW6 (capacity : Nat) | ecrecoverResultW7 (capacity : Nat)
  | ed25519VerifyOk (capacity : Nat)
  /-- Read from the one active invocation-local UInt64 buffer. -/
  | transientBuffer64Get (capacity : Nat)
  /-- Metadata and byte access for the latest raw-storage operation. -/
  | storageResultStatus (capacity : Nat)
  | storageResultLength (capacity : Nat)
  | storageResultFits (capacity : Nat)
  | storageResultByte (capacity : Nat)
  | storageResultNearTokenW0Strict
  | storageResultNearTokenW1Strict
  /-- Callback-result count plus metadata and byte access for the latest bounded read. -/
  | promiseResultsCount
  | promiseResultStatus (capacity : Nat)
  | promiseResultLength (capacity : Nat)
  | promiseResultFits (capacity : Nat)
  | promiseResultByte (capacity : Nat)
  | promiseResultBorshUInt64D (capacity : Nat)
  | promiseResultQuotedU128Valid (capacity : Nat)
  | promiseResultQuotedU128W0 (capacity : Nat)
  | promiseResultQuotedU128W1 (capacity : Nat)
  /-- Placeholder; never produced by the v0 lowering and rejected by `wellFormed`. -/
  | reserved
  deriving BEq, Repr, Inhabited

def ValKind.arity : ValKind → Nat
  | .nearTokenAddOk | .nearTokenAddW0 | .nearTokenAddW1
  | .nearTokenSubOk | .nearTokenSubW0 | .nearTokenSubW1 => 4
  | .nearTokenMulU64Ok | .nearTokenMulU64W0 | .nearTokenMulU64W1 => 3
  | .transientBuffer64Get _ | .storageResultByte _ | .promiseResultByte _
  | .promiseResultBorshUInt64D _ => 1
  | .reserved => 0
  | _ => 0

abbrev Val := ProofForge.Core.Ops.Val ValKind
abbrev Cmp := ProofForge.Core.Ops.Cmp

/-- NEAR-owned effects. Logging accepts deterministic static data or a fixed-capacity dynamic
UTF-8 frame; the emitter stages the latter through invocation-local linear memory. -/
inductive OpExt (V : Type) where
  | logUtf8 (message : String)
  | logUtf8Bounded (capacity : Nat) (message : Array V)
  | storageUnregisteredLog (account : Array V)
  | nep297StringData (standard version event : String) (capacity : Nat) (data : Array V)
  | nep141FtMint (owner : Array V) (amountLo amountHi : V)
  | nep141FtTransfer (oldOwner newOwner : Array V) (amountLo amountHi : V)
  | nep141FtBurn (owner : Array V) (amountLo amountHi : V)
  | nep141FtMintMemo (memoCapacity : Nat) (owner : Array V) (amountLo amountHi : V)
      (memo : Array V)
  | nep141FtTransferMemo (memoCapacity : Nat) (oldOwner newOwner : Array V)
      (amountLo amountHi : V) (memo : Array V)
  | nep141FtBurnMemo (memoCapacity : Nat) (owner : Array V) (amountLo amountHi : V)
      (memo : Array V)
  | promiseFunctionCallDetached (receiver method : String) (argsCapacity : Nat)
      (arguments : Array V) (depositLo depositHi gas : V)
  | promiseFunctionCallReturned (receiver method : String) (argsCapacity : Nat)
      (arguments : Array V) (depositLo depositHi gas : V)
  | promiseTransferDetached (receiver : String) (amountLo amountHi : V)
  | promiseTransferReturned (receiver : String) (amountLo amountHi : V)
  | promiseTransferAccountDetached (receiver : Array V) (amountLo amountHi : V)
  | promiseTransferAccountReturned (receiver : Array V) (amountLo amountHi : V)
  | promiseCreateAccountDetached (receiver : String)
  | promiseCreateAccountReturned (receiver : String)
  | promiseDeployContractDetached (codeCapacity : Nat) (receiver : String) (code : Array V)
  | promiseDeployContractReturned (codeCapacity : Nat) (receiver : String) (code : Array V)
  | promiseStakeDetached (receiver : String) (publicKey : Array V) (stakeLo stakeHi : V)
  | promiseStakeReturned (receiver : String) (publicKey : Array V) (stakeLo stakeHi : V)
  | promiseAddKeyDetached (receiver : String) (publicKey : Array V) (nonce : V)
  | promiseAddKeyReturned (receiver : String) (publicKey : Array V) (nonce : V)
  | promiseDeleteKeyDetached (receiver : String) (publicKey : Array V)
  | promiseDeleteKeyReturned (receiver : String) (publicKey : Array V)
  | promiseDeleteAccountDetached (receiver beneficiary : String)
  | promiseDeleteAccountReturned (receiver beneficiary : String)
  | promiseFtOnTransferReturned (receiver sender : Array V) (amountLo amountHi : V)
      (message : Array V)
  | promiseFtOnTransferThenResolveReturned (receiver sender : Array V) (amountLo amountHi : V)
      (message : Array V)
  | promiseFunctionCallThenReturned (receiver childMethod callbackMethod : String)
      (childArgsCapacity callbackArgsCapacity : Nat)
      (childArguments callbackArguments : Array V)
      (childDepositLo childDepositHi childGas : V)
      (callbackDepositLo callbackDepositHi callbackGas : V)
  | promiseFunctionCallAndThenReturned
      (leftReceiver leftMethod rightReceiver rightMethod callbackMethod : String)
      (leftArgsCapacity rightArgsCapacity callbackArgsCapacity : Nat)
      (leftArguments rightArguments callbackArguments : Array V)
      (leftDepositLo leftDepositHi leftGas : V)
      (rightDepositLo rightDepositHi rightGas : V)
      (callbackDepositLo callbackDepositHi callbackGas : V)
  | promiseFunctionCallAnd3ThenReturned
      (leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod callbackMethod : String)
      (leftArgsCapacity midArgsCapacity rightArgsCapacity callbackArgsCapacity : Nat)
      (leftArguments midArguments rightArguments callbackArguments : Array V)
      (leftDepositLo leftDepositHi leftGas : V)
      (midDepositLo midDepositHi midGas : V)
      (rightDepositLo rightDepositHi rightGas : V)
      (callbackDepositLo callbackDepositHi callbackGas : V)
  | promiseFunctionCallAnd4ThenReturned
      (leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
        fourthReceiver fourthMethod callbackMethod : String)
      (leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity callbackArgsCapacity : Nat)
      (leftArguments midArguments rightArguments fourthArguments callbackArguments : Array V)
      (leftDepositLo leftDepositHi leftGas : V)
      (midDepositLo midDepositHi midGas : V)
      (rightDepositLo rightDepositHi rightGas : V)
      (fourthDepositLo fourthDepositHi fourthGas : V)
      (callbackDepositLo callbackDepositHi callbackGas : V)
  | promiseFunctionCallAnd5ThenReturned
      (leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
        fourthReceiver fourthMethod fifthReceiver fifthMethod callbackMethod : String)
      (leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity fifthArgsCapacity
        callbackArgsCapacity : Nat)
      (leftArguments midArguments rightArguments fourthArguments fifthArguments callbackArguments : Array V)
      (leftDepositLo leftDepositHi leftGas : V)
      (midDepositLo midDepositHi midGas : V)
      (rightDepositLo rightDepositHi rightGas : V)
      (fourthDepositLo fourthDepositHi fourthGas : V)
      (fifthDepositLo fifthDepositHi fifthGas : V)
      (callbackDepositLo callbackDepositHi callbackGas : V)
  | promiseFunctionCallAnd6ThenReturned
      (leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
        fourthReceiver fourthMethod fifthReceiver fifthMethod sixthReceiver sixthMethod callbackMethod : String)
      (leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity fifthArgsCapacity
        sixthArgsCapacity callbackArgsCapacity : Nat)
      (leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
        callbackArguments : Array V)
      (leftDepositLo leftDepositHi leftGas : V)
      (midDepositLo midDepositHi midGas : V)
      (rightDepositLo rightDepositHi rightGas : V)
      (fourthDepositLo fourthDepositHi fourthGas : V)
      (fifthDepositLo fifthDepositHi fifthGas : V)
      (sixthDepositLo sixthDepositHi sixthGas : V)
      (callbackDepositLo callbackDepositHi callbackGas : V)
  | promiseFunctionCallAnd7ThenReturned
      (leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
        fourthReceiver fourthMethod fifthReceiver fifthMethod sixthReceiver sixthMethod
        seventhReceiver seventhMethod callbackMethod : String)
      (leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity fifthArgsCapacity
        sixthArgsCapacity seventhArgsCapacity callbackArgsCapacity : Nat)
      (leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
        seventhArguments callbackArguments : Array V)
      (leftDepositLo leftDepositHi leftGas : V)
      (midDepositLo midDepositHi midGas : V)
      (rightDepositLo rightDepositHi rightGas : V)
      (fourthDepositLo fourthDepositHi fourthGas : V)
      (fifthDepositLo fifthDepositHi fifthGas : V)
      (sixthDepositLo sixthDepositHi sixthGas : V)
      (seventhDepositLo seventhDepositHi seventhGas : V)
      (callbackDepositLo callbackDepositHi callbackGas : V)
  | promiseFunctionCallAnd8ThenReturned
      (leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod
        fourthReceiver fourthMethod fifthReceiver fifthMethod sixthReceiver sixthMethod
        seventhReceiver seventhMethod eighthReceiver eighthMethod callbackMethod : String)
      (leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity fifthArgsCapacity
        sixthArgsCapacity seventhArgsCapacity eighthArgsCapacity callbackArgsCapacity : Nat)
      (leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
        seventhArguments eighthArguments callbackArguments : Array V)
      (leftDepositLo leftDepositHi leftGas : V)
      (midDepositLo midDepositHi midGas : V)
      (rightDepositLo rightDepositHi rightGas : V)
      (fourthDepositLo fourthDepositHi fourthGas : V)
      (fifthDepositLo fifthDepositHi fifthGas : V)
      (sixthDepositLo sixthDepositHi sixthGas : V)
      (seventhDepositLo seventhDepositHi seventhGas : V)
      (eighthDepositLo eighthDepositHi eighthGas : V)
      (callbackDepositLo callbackDepositHi callbackGas : V)
  | promiseResultRead (capacity : Nat) (index : V)
  | transientBuffer64Begin (capacity : Nat)
  | transientBuffer64Set (capacity : Nat) (index value : V)
  | transientBuffer64Finish (capacity : Nat)
  | storageRead (resultCapacity keyCapacity : Nat) (key : Array V)
  | storageWrite (resultCapacity keyCapacity valueCapacity : Nat)
      (key value : Array V)
  | storageRemove (resultCapacity keyCapacity : Nat) (key : Array V)
  | storageHasKey (resultCapacity keyCapacity : Nat) (key : Array V)
  | sha256Hash (resultCapacity inputCapacity : Nat) (input : Array V)
  | keccak256Hash (resultCapacity inputCapacity : Nat) (input : Array V)
  | keccak512Hash (resultCapacity inputCapacity : Nat) (input : Array V)
  | ripemd160Hash (resultCapacity inputCapacity : Nat) (input : Array V)
  | ecrecover (resultCapacity : Nat) (hash sig : Array V) (v malleability : V)
  | ed25519Verify (resultCapacity : Nat) (sig msg pk : Array V)
  /-- Placeholder; never produced by the v0 lowering and rejected by `wellFormed`. -/
  | reserved
  deriving BEq, Repr, Inhabited

abbrev Op := ProofForge.Core.Ops.Op ValKind OpExt

private def storageFrameWellFormed (capacity : Nat) (values : Array Val) : Bool :=
  Codec.storageCapacityValid capacity && values.size == capacity + 1 &&
    values.all (·.wellFormed ValKind.arity)

private def storageKeyFrameWellFormed (capacity : Nat) (values : Array Val) : Bool :=
  Codec.rawStorageKeyCapacityValid capacity && values.size == capacity + 1 &&
    values.all (·.wellFormed ValKind.arity)

private def accountIdFrameWellFormed (values : Array Val) : Bool :=
  values.size == 9 && values.all (·.wellFormed ValKind.arity)

private def packedBytes64FrameWellFormed (values : Array Val) : Bool :=
  values.size == 9 && values.all (·.wellFormed ValKind.arity)

private def packedWords32WellFormed (values : Array Val) : Bool :=
  values.size == 4 && values.all (·.wellFormed ValKind.arity)

private def packedWords64WellFormed (values : Array Val) : Bool :=
  values.size == 8 && values.all (·.wellFormed ValKind.arity)

private def cryptoHashWellFormed (resultCapacity expected inputCapacity : Nat)
    (input : Array Val) : Bool :=
  resultCapacity == expected && storageFrameWellFormed inputCapacity input

def OpExt.wellFormed : OpExt Val → Bool
  | .logUtf8 message => message.toUTF8.size ≤ 1024
  | .logUtf8Bounded capacity message => storageFrameWellFormed capacity message
  | .storageUnregisteredLog account => accountIdFrameWellFormed account
  | .nep297StringData standard version event capacity data =>
      standard.toUTF8.size ≤ 64 && version.toUTF8.size ≤ 64 && event.toUTF8.size ≤ 64 &&
        storageFrameWellFormed capacity data
  | .nep141FtMint owner amountLo amountHi =>
      accountIdFrameWellFormed owner && amountLo.wellFormed ValKind.arity &&
        amountHi.wellFormed ValKind.arity
  | .nep141FtTransfer oldOwner newOwner amountLo amountHi =>
      accountIdFrameWellFormed oldOwner && accountIdFrameWellFormed newOwner &&
        amountLo.wellFormed ValKind.arity && amountHi.wellFormed ValKind.arity
  | .nep141FtBurn owner amountLo amountHi =>
      accountIdFrameWellFormed owner && amountLo.wellFormed ValKind.arity &&
        amountHi.wellFormed ValKind.arity
  | .nep141FtMintMemo memoCapacity owner amountLo amountHi memo =>
      Codec.nep141MemoCapacityValid memoCapacity && accountIdFrameWellFormed owner &&
        storageFrameWellFormed memoCapacity memo &&
        amountLo.wellFormed ValKind.arity && amountHi.wellFormed ValKind.arity
  | .nep141FtTransferMemo memoCapacity oldOwner newOwner amountLo amountHi memo =>
      Codec.nep141MemoCapacityValid memoCapacity && accountIdFrameWellFormed oldOwner &&
        accountIdFrameWellFormed newOwner &&
        storageFrameWellFormed memoCapacity memo && amountLo.wellFormed ValKind.arity &&
        amountHi.wellFormed ValKind.arity
  | .nep141FtBurnMemo memoCapacity owner amountLo amountHi memo =>
      Codec.nep141MemoCapacityValid memoCapacity && accountIdFrameWellFormed owner &&
        storageFrameWellFormed memoCapacity memo &&
        amountLo.wellFormed ValKind.arity && amountHi.wellFormed ValKind.arity
  | .promiseFunctionCallDetached receiver method argsCapacity arguments depositLo depositHi gas =>
      Codec.accountIdLiteralValid receiver && Codec.promiseMethodLiteralValid method &&
        storageFrameWellFormed argsCapacity arguments &&
        depositLo.wellFormed ValKind.arity && depositHi.wellFormed ValKind.arity &&
        gas.wellFormed ValKind.arity
  | .promiseFunctionCallReturned receiver method argsCapacity arguments depositLo depositHi gas =>
      Codec.accountIdLiteralValid receiver && Codec.promiseMethodLiteralValid method &&
        storageFrameWellFormed argsCapacity arguments &&
        depositLo.wellFormed ValKind.arity && depositHi.wellFormed ValKind.arity &&
        gas.wellFormed ValKind.arity
  | .promiseTransferDetached receiver amountLo amountHi
  | .promiseTransferReturned receiver amountLo amountHi =>
      Codec.accountIdLiteralValid receiver && amountLo.wellFormed ValKind.arity &&
        amountHi.wellFormed ValKind.arity
  | .promiseTransferAccountDetached receiver amountLo amountHi
  | .promiseTransferAccountReturned receiver amountLo amountHi =>
      accountIdFrameWellFormed receiver && amountLo.wellFormed ValKind.arity &&
        amountHi.wellFormed ValKind.arity
  | .promiseCreateAccountDetached receiver
  | .promiseCreateAccountReturned receiver =>
      Codec.accountIdLiteralValid receiver
  | .promiseDeployContractDetached codeCapacity receiver code
  | .promiseDeployContractReturned codeCapacity receiver code =>
      Codec.accountIdLiteralValid receiver && storageFrameWellFormed codeCapacity code
  | .promiseStakeDetached receiver publicKey stakeLo stakeHi
  | .promiseStakeReturned receiver publicKey stakeLo stakeHi =>
      Codec.accountIdLiteralValid receiver && packedWords32WellFormed publicKey &&
        stakeLo.wellFormed ValKind.arity && stakeHi.wellFormed ValKind.arity
  | .promiseAddKeyDetached receiver publicKey nonce
  | .promiseAddKeyReturned receiver publicKey nonce =>
      Codec.accountIdLiteralValid receiver && packedWords32WellFormed publicKey &&
        nonce.wellFormed ValKind.arity
  | .promiseDeleteKeyDetached receiver publicKey
  | .promiseDeleteKeyReturned receiver publicKey =>
      Codec.accountIdLiteralValid receiver && packedWords32WellFormed publicKey
  | .promiseDeleteAccountDetached receiver beneficiary
  | .promiseDeleteAccountReturned receiver beneficiary =>
      Codec.accountIdLiteralValid receiver && Codec.accountIdLiteralValid beneficiary
  | .promiseFtOnTransferReturned receiver sender amountLo amountHi message =>
      accountIdFrameWellFormed receiver && accountIdFrameWellFormed sender &&
        packedBytes64FrameWellFormed message && amountLo.wellFormed ValKind.arity &&
        amountHi.wellFormed ValKind.arity
  | .promiseFtOnTransferThenResolveReturned receiver sender amountLo amountHi message =>
      accountIdFrameWellFormed receiver && accountIdFrameWellFormed sender &&
        packedBytes64FrameWellFormed message && amountLo.wellFormed ValKind.arity &&
        amountHi.wellFormed ValKind.arity
  | .promiseFunctionCallThenReturned receiver childMethod callbackMethod
      childArgsCapacity callbackArgsCapacity childArguments callbackArguments
      childDepositLo childDepositHi childGas callbackDepositLo callbackDepositHi callbackGas =>
      Codec.accountIdLiteralValid receiver && Codec.promiseMethodLiteralValid childMethod &&
        Codec.promiseMethodLiteralValid callbackMethod &&
        storageFrameWellFormed childArgsCapacity childArguments &&
        storageFrameWellFormed callbackArgsCapacity callbackArguments &&
        childDepositLo.wellFormed ValKind.arity &&
        childDepositHi.wellFormed ValKind.arity && childGas.wellFormed ValKind.arity &&
        callbackDepositLo.wellFormed ValKind.arity &&
        callbackDepositHi.wellFormed ValKind.arity && callbackGas.wellFormed ValKind.arity
  | .promiseFunctionCallAndThenReturned
      leftReceiver leftMethod rightReceiver rightMethod callbackMethod
      leftArgsCapacity rightArgsCapacity callbackArgsCapacity
      leftArguments rightArguments callbackArguments
      leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
      callbackDepositLo callbackDepositHi callbackGas =>
      Codec.accountIdLiteralValid leftReceiver && Codec.promiseMethodLiteralValid leftMethod &&
        Codec.accountIdLiteralValid rightReceiver && Codec.promiseMethodLiteralValid rightMethod &&
        Codec.promiseMethodLiteralValid callbackMethod &&
        storageFrameWellFormed leftArgsCapacity leftArguments &&
        storageFrameWellFormed rightArgsCapacity rightArguments &&
        storageFrameWellFormed callbackArgsCapacity callbackArguments &&
        #[leftDepositLo, leftDepositHi, leftGas, rightDepositLo, rightDepositHi, rightGas,
          callbackDepositLo, callbackDepositHi, callbackGas].all
          (·.wellFormed ValKind.arity)
  | .promiseFunctionCallAnd3ThenReturned
      leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod callbackMethod
      leftArgsCapacity midArgsCapacity rightArgsCapacity callbackArgsCapacity
      leftArguments midArguments rightArguments callbackArguments
      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
      rightDepositLo rightDepositHi rightGas callbackDepositLo callbackDepositHi callbackGas =>
      Codec.accountIdLiteralValid leftReceiver && Codec.promiseMethodLiteralValid leftMethod &&
        Codec.accountIdLiteralValid midReceiver && Codec.promiseMethodLiteralValid midMethod &&
        Codec.accountIdLiteralValid rightReceiver && Codec.promiseMethodLiteralValid rightMethod &&
        Codec.promiseMethodLiteralValid callbackMethod &&
        storageFrameWellFormed leftArgsCapacity leftArguments &&
        storageFrameWellFormed midArgsCapacity midArguments &&
        storageFrameWellFormed rightArgsCapacity rightArguments &&
        storageFrameWellFormed callbackArgsCapacity callbackArguments &&
        #[leftDepositLo, leftDepositHi, leftGas, midDepositLo, midDepositHi, midGas,
          rightDepositLo, rightDepositHi, rightGas, callbackDepositLo, callbackDepositHi,
          callbackGas].all (·.wellFormed ValKind.arity)
  | .promiseFunctionCallAnd4ThenReturned
      leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
      callbackArgsCapacity leftArguments midArguments rightArguments fourthArguments callbackArguments
      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
      rightDepositLo rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
      callbackDepositLo callbackDepositHi callbackGas =>
      Codec.accountIdLiteralValid leftReceiver && Codec.promiseMethodLiteralValid leftMethod &&
        Codec.accountIdLiteralValid midReceiver && Codec.promiseMethodLiteralValid midMethod &&
        Codec.accountIdLiteralValid rightReceiver && Codec.promiseMethodLiteralValid rightMethod &&
        Codec.accountIdLiteralValid fourthReceiver && Codec.promiseMethodLiteralValid fourthMethod &&
        Codec.promiseMethodLiteralValid callbackMethod &&
        storageFrameWellFormed leftArgsCapacity leftArguments &&
        storageFrameWellFormed midArgsCapacity midArguments &&
        storageFrameWellFormed rightArgsCapacity rightArguments &&
        storageFrameWellFormed fourthArgsCapacity fourthArguments &&
        storageFrameWellFormed callbackArgsCapacity callbackArguments &&
        #[leftDepositLo, leftDepositHi, leftGas, midDepositLo, midDepositHi, midGas,
          rightDepositLo, rightDepositHi, rightGas, fourthDepositLo, fourthDepositHi, fourthGas,
          callbackDepositLo, callbackDepositHi, callbackGas].all (·.wellFormed ValKind.arity)
  | .promiseFunctionCallAnd5ThenReturned
      leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity
      fourthArgsCapacity fifthArgsCapacity callbackArgsCapacity leftArguments midArguments rightArguments
      fourthArguments fifthArguments callbackArguments leftDepositLo leftDepositHi leftGas
      midDepositLo midDepositHi midGas rightDepositLo rightDepositHi rightGas fourthDepositLo
      fourthDepositHi fourthGas fifthDepositLo fifthDepositHi fifthGas callbackDepositLo
      callbackDepositHi callbackGas =>
      Codec.accountIdLiteralValid leftReceiver && Codec.promiseMethodLiteralValid leftMethod &&
        Codec.accountIdLiteralValid midReceiver && Codec.promiseMethodLiteralValid midMethod &&
        Codec.accountIdLiteralValid rightReceiver && Codec.promiseMethodLiteralValid rightMethod &&
        Codec.accountIdLiteralValid fourthReceiver && Codec.promiseMethodLiteralValid fourthMethod &&
        Codec.accountIdLiteralValid fifthReceiver && Codec.promiseMethodLiteralValid fifthMethod &&
        Codec.promiseMethodLiteralValid callbackMethod &&
        storageFrameWellFormed leftArgsCapacity leftArguments &&
        storageFrameWellFormed midArgsCapacity midArguments &&
        storageFrameWellFormed rightArgsCapacity rightArguments &&
        storageFrameWellFormed fourthArgsCapacity fourthArguments &&
        storageFrameWellFormed fifthArgsCapacity fifthArguments &&
        storageFrameWellFormed callbackArgsCapacity callbackArguments &&
        #[leftDepositLo, leftDepositHi, leftGas, midDepositLo, midDepositHi, midGas,
          rightDepositLo, rightDepositHi, rightGas, fourthDepositLo, fourthDepositHi, fourthGas,
          fifthDepositLo, fifthDepositHi, fifthGas, callbackDepositLo, callbackDepositHi,
          callbackGas].all (·.wellFormed ValKind.arity)
  | .promiseFunctionCallAnd6ThenReturned
      leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod sixthReceiver sixthMethod callbackMethod leftArgsCapacity midArgsCapacity
      rightArgsCapacity fourthArgsCapacity fifthArgsCapacity sixthArgsCapacity callbackArgsCapacity
      leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
      callbackArguments leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
      rightDepositLo rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
      fifthDepositLo fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas
      callbackDepositLo callbackDepositHi callbackGas =>
      Codec.accountIdLiteralValid leftReceiver && Codec.promiseMethodLiteralValid leftMethod &&
        Codec.accountIdLiteralValid midReceiver && Codec.promiseMethodLiteralValid midMethod &&
        Codec.accountIdLiteralValid rightReceiver && Codec.promiseMethodLiteralValid rightMethod &&
        Codec.accountIdLiteralValid fourthReceiver && Codec.promiseMethodLiteralValid fourthMethod &&
        Codec.accountIdLiteralValid fifthReceiver && Codec.promiseMethodLiteralValid fifthMethod &&
        Codec.accountIdLiteralValid sixthReceiver && Codec.promiseMethodLiteralValid sixthMethod &&
        Codec.promiseMethodLiteralValid callbackMethod &&
        storageFrameWellFormed leftArgsCapacity leftArguments &&
        storageFrameWellFormed midArgsCapacity midArguments &&
        storageFrameWellFormed rightArgsCapacity rightArguments &&
        storageFrameWellFormed fourthArgsCapacity fourthArguments &&
        storageFrameWellFormed fifthArgsCapacity fifthArguments &&
        storageFrameWellFormed sixthArgsCapacity sixthArguments &&
        storageFrameWellFormed callbackArgsCapacity callbackArguments &&
        #[leftDepositLo, leftDepositHi, leftGas, midDepositLo, midDepositHi, midGas,
          rightDepositLo, rightDepositHi, rightGas, fourthDepositLo, fourthDepositHi, fourthGas,
          fifthDepositLo, fifthDepositHi, fifthGas, sixthDepositLo, sixthDepositHi, sixthGas,
          callbackDepositLo, callbackDepositHi, callbackGas].all (·.wellFormed ValKind.arity)
  | .promiseFunctionCallAnd7ThenReturned
      leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod sixthReceiver sixthMethod seventhReceiver seventhMethod callbackMethod
      leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity fifthArgsCapacity
      sixthArgsCapacity seventhArgsCapacity callbackArgsCapacity leftArguments midArguments
      rightArguments fourthArguments fifthArguments sixthArguments seventhArguments callbackArguments
      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas rightDepositLo
      rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas fifthDepositLo
      fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas seventhDepositLo seventhDepositHi
      seventhGas callbackDepositLo callbackDepositHi callbackGas =>
      Codec.accountIdLiteralValid leftReceiver && Codec.promiseMethodLiteralValid leftMethod &&
        Codec.accountIdLiteralValid midReceiver && Codec.promiseMethodLiteralValid midMethod &&
        Codec.accountIdLiteralValid rightReceiver && Codec.promiseMethodLiteralValid rightMethod &&
        Codec.accountIdLiteralValid fourthReceiver && Codec.promiseMethodLiteralValid fourthMethod &&
        Codec.accountIdLiteralValid fifthReceiver && Codec.promiseMethodLiteralValid fifthMethod &&
        Codec.accountIdLiteralValid sixthReceiver && Codec.promiseMethodLiteralValid sixthMethod &&
        Codec.accountIdLiteralValid seventhReceiver && Codec.promiseMethodLiteralValid seventhMethod &&
        Codec.promiseMethodLiteralValid callbackMethod &&
        storageFrameWellFormed leftArgsCapacity leftArguments &&
        storageFrameWellFormed midArgsCapacity midArguments &&
        storageFrameWellFormed rightArgsCapacity rightArguments &&
        storageFrameWellFormed fourthArgsCapacity fourthArguments &&
        storageFrameWellFormed fifthArgsCapacity fifthArguments &&
        storageFrameWellFormed sixthArgsCapacity sixthArguments &&
        storageFrameWellFormed seventhArgsCapacity seventhArguments &&
        storageFrameWellFormed callbackArgsCapacity callbackArguments &&
        #[leftDepositLo, leftDepositHi, leftGas, midDepositLo, midDepositHi, midGas,
          rightDepositLo, rightDepositHi, rightGas, fourthDepositLo, fourthDepositHi, fourthGas,
          fifthDepositLo, fifthDepositHi, fifthGas, sixthDepositLo, sixthDepositHi, sixthGas,
          seventhDepositLo, seventhDepositHi, seventhGas, callbackDepositLo, callbackDepositHi,
          callbackGas].all (·.wellFormed ValKind.arity)
  | .promiseFunctionCallAnd8ThenReturned
      leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod sixthReceiver sixthMethod seventhReceiver seventhMethod eighthReceiver
      eighthMethod callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
      fifthArgsCapacity sixthArgsCapacity seventhArgsCapacity eighthArgsCapacity callbackArgsCapacity
      leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
      seventhArguments eighthArguments callbackArguments leftDepositLo leftDepositHi leftGas
      midDepositLo midDepositHi midGas rightDepositLo rightDepositHi rightGas fourthDepositLo
      fourthDepositHi fourthGas fifthDepositLo fifthDepositHi fifthGas sixthDepositLo sixthDepositHi
      sixthGas seventhDepositLo seventhDepositHi seventhGas eighthDepositLo eighthDepositHi eighthGas
      callbackDepositLo callbackDepositHi callbackGas =>
      Codec.accountIdLiteralValid leftReceiver && Codec.promiseMethodLiteralValid leftMethod &&
        Codec.accountIdLiteralValid midReceiver && Codec.promiseMethodLiteralValid midMethod &&
        Codec.accountIdLiteralValid rightReceiver && Codec.promiseMethodLiteralValid rightMethod &&
        Codec.accountIdLiteralValid fourthReceiver && Codec.promiseMethodLiteralValid fourthMethod &&
        Codec.accountIdLiteralValid fifthReceiver && Codec.promiseMethodLiteralValid fifthMethod &&
        Codec.accountIdLiteralValid sixthReceiver && Codec.promiseMethodLiteralValid sixthMethod &&
        Codec.accountIdLiteralValid seventhReceiver && Codec.promiseMethodLiteralValid seventhMethod &&
        Codec.accountIdLiteralValid eighthReceiver && Codec.promiseMethodLiteralValid eighthMethod &&
        Codec.promiseMethodLiteralValid callbackMethod &&
        storageFrameWellFormed leftArgsCapacity leftArguments &&
        storageFrameWellFormed midArgsCapacity midArguments &&
        storageFrameWellFormed rightArgsCapacity rightArguments &&
        storageFrameWellFormed fourthArgsCapacity fourthArguments &&
        storageFrameWellFormed fifthArgsCapacity fifthArguments &&
        storageFrameWellFormed sixthArgsCapacity sixthArguments &&
        storageFrameWellFormed seventhArgsCapacity seventhArguments &&
        storageFrameWellFormed eighthArgsCapacity eighthArguments &&
        storageFrameWellFormed callbackArgsCapacity callbackArguments &&
        #[leftDepositLo, leftDepositHi, leftGas, midDepositLo, midDepositHi, midGas,
          rightDepositLo, rightDepositHi, rightGas, fourthDepositLo, fourthDepositHi, fourthGas,
          fifthDepositLo, fifthDepositHi, fifthGas, sixthDepositLo, sixthDepositHi, sixthGas,
          seventhDepositLo, seventhDepositHi, seventhGas, eighthDepositLo, eighthDepositHi, eighthGas,
          callbackDepositLo, callbackDepositHi, callbackGas].all (·.wellFormed ValKind.arity)
  | .promiseResultRead capacity index =>
      Codec.storageCapacityValid capacity && index.wellFormed ValKind.arity
  | .transientBuffer64Begin capacity | .transientBuffer64Finish capacity =>
      Memory.buffer64CapacityValid capacity
  | .transientBuffer64Set capacity index value =>
      Memory.buffer64CapacityValid capacity &&
        index.wellFormed ValKind.arity && value.wellFormed ValKind.arity
  | .storageRead resultCapacity keyCapacity key
  | .storageRemove resultCapacity keyCapacity key
  | .storageHasKey resultCapacity keyCapacity key =>
      Codec.storageCapacityValid resultCapacity && storageKeyFrameWellFormed keyCapacity key
  | .storageWrite resultCapacity keyCapacity valueCapacity key value =>
      Codec.storageCapacityValid resultCapacity && storageKeyFrameWellFormed keyCapacity key &&
        storageFrameWellFormed valueCapacity value
  | .sha256Hash resultCapacity inputCapacity input =>
      cryptoHashWellFormed resultCapacity 32 inputCapacity input
  | .keccak256Hash resultCapacity inputCapacity input =>
      cryptoHashWellFormed resultCapacity 32 inputCapacity input
  | .keccak512Hash resultCapacity inputCapacity input =>
      cryptoHashWellFormed resultCapacity 64 inputCapacity input
  | .ripemd160Hash resultCapacity inputCapacity input =>
      cryptoHashWellFormed resultCapacity 20 inputCapacity input
  | .ecrecover resultCapacity hash sig v malleability =>
      resultCapacity == 64 && packedWords32WellFormed hash && packedWords64WellFormed sig &&
        v.wellFormed ValKind.arity && malleability.wellFormed ValKind.arity
  | .ed25519Verify resultCapacity sig msg pk =>
      resultCapacity == 8 && packedWords64WellFormed sig && packedWords32WellFormed pk &&
        1 ≤ msg.size && storageFrameWellFormed (msg.size - 1) msg

  | .reserved => false

def Op.wellFormed (op : Op) : Bool :=
  ProofForge.Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

private def mapCfgPayload (mapValue : Val → Val) : OpExt Val → OpExt Val
  | .logUtf8 message => .logUtf8 message
  | .logUtf8Bounded capacity message => .logUtf8Bounded capacity (message.map mapValue)
  | .storageUnregisteredLog account => .storageUnregisteredLog (account.map mapValue)
  | .nep297StringData standard version event capacity data =>
      .nep297StringData standard version event capacity (data.map mapValue)
  | .nep141FtMint owner amountLo amountHi =>
      .nep141FtMint (owner.map mapValue) (mapValue amountLo) (mapValue amountHi)
  | .nep141FtTransfer oldOwner newOwner amountLo amountHi =>
      .nep141FtTransfer (oldOwner.map mapValue) (newOwner.map mapValue)
        (mapValue amountLo) (mapValue amountHi)
  | .nep141FtBurn owner amountLo amountHi =>
      .nep141FtBurn (owner.map mapValue) (mapValue amountLo) (mapValue amountHi)
  | .nep141FtMintMemo memoCapacity owner amountLo amountHi memo =>
      .nep141FtMintMemo memoCapacity (owner.map mapValue) (mapValue amountLo)
        (mapValue amountHi) (memo.map mapValue)
  | .nep141FtTransferMemo memoCapacity oldOwner newOwner amountLo amountHi memo =>
      .nep141FtTransferMemo memoCapacity (oldOwner.map mapValue) (newOwner.map mapValue)
        (mapValue amountLo) (mapValue amountHi) (memo.map mapValue)
  | .nep141FtBurnMemo memoCapacity owner amountLo amountHi memo =>
      .nep141FtBurnMemo memoCapacity (owner.map mapValue) (mapValue amountLo)
        (mapValue amountHi) (memo.map mapValue)
  | .promiseFunctionCallDetached receiver method argsCapacity arguments depositLo depositHi gas =>
      .promiseFunctionCallDetached receiver method argsCapacity (arguments.map mapValue)
        (mapValue depositLo) (mapValue depositHi) (mapValue gas)
  | .promiseFunctionCallReturned receiver method argsCapacity arguments depositLo depositHi gas =>
      .promiseFunctionCallReturned receiver method argsCapacity (arguments.map mapValue)
        (mapValue depositLo) (mapValue depositHi) (mapValue gas)
  | .promiseTransferDetached receiver amountLo amountHi =>
      .promiseTransferDetached receiver (mapValue amountLo) (mapValue amountHi)
  | .promiseTransferReturned receiver amountLo amountHi =>
      .promiseTransferReturned receiver (mapValue amountLo) (mapValue amountHi)
  | .promiseTransferAccountDetached receiver amountLo amountHi =>
      .promiseTransferAccountDetached (receiver.map mapValue)
        (mapValue amountLo) (mapValue amountHi)
  | .promiseTransferAccountReturned receiver amountLo amountHi =>
      .promiseTransferAccountReturned (receiver.map mapValue)
        (mapValue amountLo) (mapValue amountHi)
  | .promiseCreateAccountDetached receiver => .promiseCreateAccountDetached receiver
  | .promiseCreateAccountReturned receiver => .promiseCreateAccountReturned receiver
  | .promiseDeployContractDetached codeCapacity receiver code =>
      .promiseDeployContractDetached codeCapacity receiver (code.map mapValue)
  | .promiseDeployContractReturned codeCapacity receiver code =>
      .promiseDeployContractReturned codeCapacity receiver (code.map mapValue)
  | .promiseStakeDetached receiver publicKey stakeLo stakeHi =>
      .promiseStakeDetached receiver (publicKey.map mapValue)
        (mapValue stakeLo) (mapValue stakeHi)
  | .promiseStakeReturned receiver publicKey stakeLo stakeHi =>
      .promiseStakeReturned receiver (publicKey.map mapValue)
        (mapValue stakeLo) (mapValue stakeHi)
  | .promiseAddKeyDetached receiver publicKey nonce =>
      .promiseAddKeyDetached receiver (publicKey.map mapValue) (mapValue nonce)
  | .promiseAddKeyReturned receiver publicKey nonce =>
      .promiseAddKeyReturned receiver (publicKey.map mapValue) (mapValue nonce)
  | .promiseDeleteKeyDetached receiver publicKey =>
      .promiseDeleteKeyDetached receiver (publicKey.map mapValue)
  | .promiseDeleteKeyReturned receiver publicKey =>
      .promiseDeleteKeyReturned receiver (publicKey.map mapValue)
  | .promiseDeleteAccountDetached receiver beneficiary =>
      .promiseDeleteAccountDetached receiver beneficiary
  | .promiseDeleteAccountReturned receiver beneficiary =>
      .promiseDeleteAccountReturned receiver beneficiary
  | .promiseFtOnTransferReturned receiver sender amountLo amountHi message =>
      .promiseFtOnTransferReturned (receiver.map mapValue) (sender.map mapValue)
        (mapValue amountLo) (mapValue amountHi) (message.map mapValue)
  | .promiseFtOnTransferThenResolveReturned receiver sender amountLo amountHi message =>
      .promiseFtOnTransferThenResolveReturned (receiver.map mapValue) (sender.map mapValue)
        (mapValue amountLo) (mapValue amountHi) (message.map mapValue)
  | .promiseFunctionCallThenReturned receiver childMethod callbackMethod
      childArgsCapacity callbackArgsCapacity childArguments callbackArguments
      childDepositLo childDepositHi childGas callbackDepositLo callbackDepositHi callbackGas =>
      .promiseFunctionCallThenReturned receiver childMethod callbackMethod
        childArgsCapacity callbackArgsCapacity (childArguments.map mapValue)
        (callbackArguments.map mapValue) (mapValue childDepositLo) (mapValue childDepositHi)
        (mapValue childGas) (mapValue callbackDepositLo) (mapValue callbackDepositHi)
        (mapValue callbackGas)
  | .promiseFunctionCallAndThenReturned
      leftReceiver leftMethod rightReceiver rightMethod callbackMethod
      leftArgsCapacity rightArgsCapacity callbackArgsCapacity
      leftArguments rightArguments callbackArguments
      leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
      callbackDepositLo callbackDepositHi callbackGas =>
      .promiseFunctionCallAndThenReturned
        leftReceiver leftMethod rightReceiver rightMethod callbackMethod
        leftArgsCapacity rightArgsCapacity callbackArgsCapacity
        (leftArguments.map mapValue) (rightArguments.map mapValue)
        (callbackArguments.map mapValue)
        (mapValue leftDepositLo) (mapValue leftDepositHi) (mapValue leftGas)
        (mapValue rightDepositLo) (mapValue rightDepositHi) (mapValue rightGas)
        (mapValue callbackDepositLo) (mapValue callbackDepositHi) (mapValue callbackGas)
  | .promiseFunctionCallAnd3ThenReturned
      leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod callbackMethod
      leftArgsCapacity midArgsCapacity rightArgsCapacity callbackArgsCapacity
      leftArguments midArguments rightArguments callbackArguments
      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
      rightDepositLo rightDepositHi rightGas callbackDepositLo callbackDepositHi callbackGas =>
      .promiseFunctionCallAnd3ThenReturned
        leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod callbackMethod
        leftArgsCapacity midArgsCapacity rightArgsCapacity callbackArgsCapacity
        (leftArguments.map mapValue) (midArguments.map mapValue) (rightArguments.map mapValue)
        (callbackArguments.map mapValue)
        (mapValue leftDepositLo) (mapValue leftDepositHi) (mapValue leftGas)
        (mapValue midDepositLo) (mapValue midDepositHi) (mapValue midGas)
        (mapValue rightDepositLo) (mapValue rightDepositHi) (mapValue rightGas)
        (mapValue callbackDepositLo) (mapValue callbackDepositHi) (mapValue callbackGas)
  | .promiseFunctionCallAnd4ThenReturned
      leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
      callbackArgsCapacity leftArguments midArguments rightArguments fourthArguments callbackArguments
      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
      rightDepositLo rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
      callbackDepositLo callbackDepositHi callbackGas =>
      .promiseFunctionCallAnd4ThenReturned
        leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
        callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
        callbackArgsCapacity (leftArguments.map mapValue) (midArguments.map mapValue)
        (rightArguments.map mapValue) (fourthArguments.map mapValue) (callbackArguments.map mapValue)
        (mapValue leftDepositLo) (mapValue leftDepositHi) (mapValue leftGas)
        (mapValue midDepositLo) (mapValue midDepositHi) (mapValue midGas)
        (mapValue rightDepositLo) (mapValue rightDepositHi) (mapValue rightGas)
        (mapValue fourthDepositLo) (mapValue fourthDepositHi) (mapValue fourthGas)
        (mapValue callbackDepositLo) (mapValue callbackDepositHi) (mapValue callbackGas)
  | .promiseFunctionCallAnd5ThenReturned
      leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity
      fourthArgsCapacity fifthArgsCapacity callbackArgsCapacity leftArguments midArguments rightArguments
      fourthArguments fifthArguments callbackArguments leftDepositLo leftDepositHi leftGas
      midDepositLo midDepositHi midGas rightDepositLo rightDepositHi rightGas fourthDepositLo
      fourthDepositHi fourthGas fifthDepositLo fifthDepositHi fifthGas callbackDepositLo
      callbackDepositHi callbackGas =>
      .promiseFunctionCallAnd5ThenReturned
        leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
        fifthReceiver fifthMethod callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity
        fourthArgsCapacity fifthArgsCapacity callbackArgsCapacity
        (leftArguments.map mapValue) (midArguments.map mapValue) (rightArguments.map mapValue)
        (fourthArguments.map mapValue) (fifthArguments.map mapValue) (callbackArguments.map mapValue)
        (mapValue leftDepositLo) (mapValue leftDepositHi) (mapValue leftGas)
        (mapValue midDepositLo) (mapValue midDepositHi) (mapValue midGas)
        (mapValue rightDepositLo) (mapValue rightDepositHi) (mapValue rightGas)
        (mapValue fourthDepositLo) (mapValue fourthDepositHi) (mapValue fourthGas)
        (mapValue fifthDepositLo) (mapValue fifthDepositHi) (mapValue fifthGas)
        (mapValue callbackDepositLo) (mapValue callbackDepositHi) (mapValue callbackGas)
  | .promiseFunctionCallAnd6ThenReturned
      leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod sixthReceiver sixthMethod callbackMethod leftArgsCapacity midArgsCapacity
      rightArgsCapacity fourthArgsCapacity fifthArgsCapacity sixthArgsCapacity callbackArgsCapacity
      leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
      callbackArguments leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
      rightDepositLo rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
      fifthDepositLo fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas
      callbackDepositLo callbackDepositHi callbackGas =>
      .promiseFunctionCallAnd6ThenReturned
        leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
        fifthReceiver fifthMethod sixthReceiver sixthMethod callbackMethod leftArgsCapacity midArgsCapacity
        rightArgsCapacity fourthArgsCapacity fifthArgsCapacity sixthArgsCapacity callbackArgsCapacity
        (leftArguments.map mapValue) (midArguments.map mapValue) (rightArguments.map mapValue)
        (fourthArguments.map mapValue) (fifthArguments.map mapValue) (sixthArguments.map mapValue)
        (callbackArguments.map mapValue)
        (mapValue leftDepositLo) (mapValue leftDepositHi) (mapValue leftGas)
        (mapValue midDepositLo) (mapValue midDepositHi) (mapValue midGas)
        (mapValue rightDepositLo) (mapValue rightDepositHi) (mapValue rightGas)
        (mapValue fourthDepositLo) (mapValue fourthDepositHi) (mapValue fourthGas)
        (mapValue fifthDepositLo) (mapValue fifthDepositHi) (mapValue fifthGas)
        (mapValue sixthDepositLo) (mapValue sixthDepositHi) (mapValue sixthGas)
        (mapValue callbackDepositLo) (mapValue callbackDepositHi) (mapValue callbackGas)
  | .promiseFunctionCallAnd7ThenReturned
      leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod sixthReceiver sixthMethod seventhReceiver seventhMethod callbackMethod
      leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity fifthArgsCapacity
      sixthArgsCapacity seventhArgsCapacity callbackArgsCapacity leftArguments midArguments
      rightArguments fourthArguments fifthArguments sixthArguments seventhArguments callbackArguments
      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas rightDepositLo
      rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas fifthDepositLo
      fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas seventhDepositLo seventhDepositHi
      seventhGas callbackDepositLo callbackDepositHi callbackGas =>
      .promiseFunctionCallAnd7ThenReturned
        leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
        fifthReceiver fifthMethod sixthReceiver sixthMethod seventhReceiver seventhMethod callbackMethod
        leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity fifthArgsCapacity
        sixthArgsCapacity seventhArgsCapacity callbackArgsCapacity
        (leftArguments.map mapValue) (midArguments.map mapValue) (rightArguments.map mapValue)
        (fourthArguments.map mapValue) (fifthArguments.map mapValue) (sixthArguments.map mapValue)
        (seventhArguments.map mapValue) (callbackArguments.map mapValue)
        (mapValue leftDepositLo) (mapValue leftDepositHi) (mapValue leftGas)
        (mapValue midDepositLo) (mapValue midDepositHi) (mapValue midGas)
        (mapValue rightDepositLo) (mapValue rightDepositHi) (mapValue rightGas)
        (mapValue fourthDepositLo) (mapValue fourthDepositHi) (mapValue fourthGas)
        (mapValue fifthDepositLo) (mapValue fifthDepositHi) (mapValue fifthGas)
        (mapValue sixthDepositLo) (mapValue sixthDepositHi) (mapValue sixthGas)
        (mapValue seventhDepositLo) (mapValue seventhDepositHi) (mapValue seventhGas)
        (mapValue callbackDepositLo) (mapValue callbackDepositHi) (mapValue callbackGas)
  | .promiseFunctionCallAnd8ThenReturned
      leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod sixthReceiver sixthMethod seventhReceiver seventhMethod eighthReceiver
      eighthMethod callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
      fifthArgsCapacity sixthArgsCapacity seventhArgsCapacity eighthArgsCapacity callbackArgsCapacity
      leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
      seventhArguments eighthArguments callbackArguments leftDepositLo leftDepositHi leftGas
      midDepositLo midDepositHi midGas rightDepositLo rightDepositHi rightGas fourthDepositLo
      fourthDepositHi fourthGas fifthDepositLo fifthDepositHi fifthGas sixthDepositLo sixthDepositHi
      sixthGas seventhDepositLo seventhDepositHi seventhGas eighthDepositLo eighthDepositHi eighthGas
      callbackDepositLo callbackDepositHi callbackGas =>
      .promiseFunctionCallAnd8ThenReturned
        leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
        fifthReceiver fifthMethod sixthReceiver sixthMethod seventhReceiver seventhMethod eighthReceiver
        eighthMethod callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
        fifthArgsCapacity sixthArgsCapacity seventhArgsCapacity eighthArgsCapacity callbackArgsCapacity
        (leftArguments.map mapValue) (midArguments.map mapValue) (rightArguments.map mapValue)
        (fourthArguments.map mapValue) (fifthArguments.map mapValue) (sixthArguments.map mapValue)
        (seventhArguments.map mapValue) (eighthArguments.map mapValue) (callbackArguments.map mapValue)
        (mapValue leftDepositLo) (mapValue leftDepositHi) (mapValue leftGas)
        (mapValue midDepositLo) (mapValue midDepositHi) (mapValue midGas)
        (mapValue rightDepositLo) (mapValue rightDepositHi) (mapValue rightGas)
        (mapValue fourthDepositLo) (mapValue fourthDepositHi) (mapValue fourthGas)
        (mapValue fifthDepositLo) (mapValue fifthDepositHi) (mapValue fifthGas)
        (mapValue sixthDepositLo) (mapValue sixthDepositHi) (mapValue sixthGas)
        (mapValue seventhDepositLo) (mapValue seventhDepositHi) (mapValue seventhGas)
        (mapValue eighthDepositLo) (mapValue eighthDepositHi) (mapValue eighthGas)
        (mapValue callbackDepositLo) (mapValue callbackDepositHi) (mapValue callbackGas)
  | .promiseResultRead capacity index => .promiseResultRead capacity (mapValue index)
  | .transientBuffer64Begin capacity => .transientBuffer64Begin capacity
  | .transientBuffer64Set capacity index value =>
      .transientBuffer64Set capacity (mapValue index) (mapValue value)
  | .transientBuffer64Finish capacity => .transientBuffer64Finish capacity
  | .storageRead resultCapacity keyCapacity key =>
      .storageRead resultCapacity keyCapacity (key.map mapValue)
  | .storageWrite resultCapacity keyCapacity valueCapacity key value =>
      .storageWrite resultCapacity keyCapacity valueCapacity (key.map mapValue) (value.map mapValue)
  | .storageRemove resultCapacity keyCapacity key =>
      .storageRemove resultCapacity keyCapacity (key.map mapValue)
  | .storageHasKey resultCapacity keyCapacity key =>
      .storageHasKey resultCapacity keyCapacity (key.map mapValue)
  | .sha256Hash resultCapacity inputCapacity input =>
      .sha256Hash resultCapacity inputCapacity (input.map mapValue)
  | .keccak256Hash resultCapacity inputCapacity input =>
      .keccak256Hash resultCapacity inputCapacity (input.map mapValue)
  | .keccak512Hash resultCapacity inputCapacity input =>
      .keccak512Hash resultCapacity inputCapacity (input.map mapValue)
  | .ripemd160Hash resultCapacity inputCapacity input =>
      .ripemd160Hash resultCapacity inputCapacity (input.map mapValue)
  | .ecrecover resultCapacity hash sig v malleability =>
      .ecrecover resultCapacity (hash.map mapValue) (sig.map mapValue)
        (mapValue v) (mapValue malleability)
  | .ed25519Verify resultCapacity sig msg pk =>
      .ed25519Verify resultCapacity (sig.map mapValue) (msg.map mapValue) (pk.map mapValue)
  | .reserved => .reserved

private def cfgPayloadValues : OpExt Val → Array Val
  | .logUtf8 _ => #[]
  | .logUtf8Bounded _ message => message
  | .storageUnregisteredLog account => account
  | .nep297StringData _ _ _ _ data => data
  | .nep141FtMint owner amountLo amountHi => owner ++ #[amountLo, amountHi]
  | .nep141FtTransfer oldOwner newOwner amountLo amountHi =>
      oldOwner ++ newOwner ++ #[amountLo, amountHi]
  | .nep141FtBurn owner amountLo amountHi => owner ++ #[amountLo, amountHi]
  | .nep141FtMintMemo _ owner amountLo amountHi memo
  | .nep141FtBurnMemo _ owner amountLo amountHi memo => owner ++ #[amountLo, amountHi] ++ memo
  | .nep141FtTransferMemo _ oldOwner newOwner amountLo amountHi memo =>
      oldOwner ++ newOwner ++ #[amountLo, amountHi] ++ memo
  | .promiseFunctionCallDetached _ _ _ arguments depositLo depositHi gas =>
      arguments ++ #[depositLo, depositHi, gas]
  | .promiseFunctionCallReturned _ _ _ arguments depositLo depositHi gas =>
      arguments ++ #[depositLo, depositHi, gas]
  | .promiseTransferDetached _ amountLo amountHi
  | .promiseTransferReturned _ amountLo amountHi => #[amountLo, amountHi]
  | .promiseTransferAccountDetached receiver amountLo amountHi
  | .promiseTransferAccountReturned receiver amountLo amountHi =>
      receiver ++ #[amountLo, amountHi]
  | .promiseCreateAccountDetached _ | .promiseCreateAccountReturned _ => #[]
  | .promiseDeployContractDetached _ _ code
  | .promiseDeployContractReturned _ _ code => code
  | .promiseStakeDetached _ publicKey stakeLo stakeHi
  | .promiseStakeReturned _ publicKey stakeLo stakeHi =>
      publicKey ++ #[stakeLo, stakeHi]
  | .promiseAddKeyDetached _ publicKey nonce
  | .promiseAddKeyReturned _ publicKey nonce => publicKey ++ #[nonce]
  | .promiseDeleteKeyDetached _ publicKey
  | .promiseDeleteKeyReturned _ publicKey => publicKey
  | .promiseDeleteAccountDetached _ _ | .promiseDeleteAccountReturned _ _ => #[]
  | .promiseFtOnTransferReturned receiver sender amountLo amountHi message =>
      receiver ++ sender ++ #[amountLo, amountHi] ++ message
  | .promiseFtOnTransferThenResolveReturned receiver sender amountLo amountHi message =>
      receiver ++ sender ++ #[amountLo, amountHi] ++ message
  | .promiseFunctionCallThenReturned _ _ _ _ _ childArguments callbackArguments
      childDepositLo childDepositHi childGas callbackDepositLo callbackDepositHi callbackGas =>
      childArguments ++ callbackArguments ++
        #[childDepositLo, childDepositHi, childGas,
          callbackDepositLo, callbackDepositHi, callbackGas]
  | .promiseFunctionCallAndThenReturned _ _ _ _ _ _ _ _
      leftArguments rightArguments callbackArguments
      leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
      callbackDepositLo callbackDepositHi callbackGas =>
      leftArguments ++ rightArguments ++ callbackArguments ++
        #[leftDepositLo, leftDepositHi, leftGas, rightDepositLo, rightDepositHi, rightGas,
          callbackDepositLo, callbackDepositHi, callbackGas]
  | .promiseFunctionCallAnd3ThenReturned _ _ _ _ _ _ _ _ _ _ _
      leftArguments midArguments rightArguments callbackArguments
      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
      rightDepositLo rightDepositHi rightGas callbackDepositLo callbackDepositHi callbackGas =>
      leftArguments ++ midArguments ++ rightArguments ++ callbackArguments ++
        #[leftDepositLo, leftDepositHi, leftGas, midDepositLo, midDepositHi, midGas,
          rightDepositLo, rightDepositHi, rightGas, callbackDepositLo, callbackDepositHi,
          callbackGas]
  | .promiseFunctionCallAnd4ThenReturned _ _ _ _ _ _ _ _ _ _ _ _ _ _
      leftArguments midArguments rightArguments fourthArguments callbackArguments
      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
      rightDepositLo rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
      callbackDepositLo callbackDepositHi callbackGas =>
      leftArguments ++ midArguments ++ rightArguments ++ fourthArguments ++ callbackArguments ++
        #[leftDepositLo, leftDepositHi, leftGas, midDepositLo, midDepositHi, midGas,
          rightDepositLo, rightDepositHi, rightGas, fourthDepositLo, fourthDepositHi, fourthGas,
          callbackDepositLo, callbackDepositHi, callbackGas]
  | .promiseFunctionCallAnd5ThenReturned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      leftArguments midArguments rightArguments fourthArguments fifthArguments callbackArguments
      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
      rightDepositLo rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
      fifthDepositLo fifthDepositHi fifthGas callbackDepositLo callbackDepositHi callbackGas =>
      leftArguments ++ midArguments ++ rightArguments ++ fourthArguments ++ fifthArguments ++
        callbackArguments ++
        #[leftDepositLo, leftDepositHi, leftGas, midDepositLo, midDepositHi, midGas,
          rightDepositLo, rightDepositHi, rightGas, fourthDepositLo, fourthDepositHi, fourthGas,
          fifthDepositLo, fifthDepositHi, fifthGas, callbackDepositLo, callbackDepositHi,
          callbackGas]
  | .promiseFunctionCallAnd6ThenReturned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
      callbackArguments
      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
      rightDepositLo rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
      fifthDepositLo fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas
      callbackDepositLo callbackDepositHi callbackGas =>
      leftArguments ++ midArguments ++ rightArguments ++ fourthArguments ++ fifthArguments ++
        sixthArguments ++ callbackArguments ++
        #[leftDepositLo, leftDepositHi, leftGas, midDepositLo, midDepositHi, midGas,
          rightDepositLo, rightDepositHi, rightGas, fourthDepositLo, fourthDepositHi, fourthGas,
          fifthDepositLo, fifthDepositHi, fifthGas, sixthDepositLo, sixthDepositHi, sixthGas,
          callbackDepositLo, callbackDepositHi, callbackGas]
  | .promiseFunctionCallAnd7ThenReturned
      leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod sixthReceiver sixthMethod seventhReceiver seventhMethod callbackMethod
      leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity fifthArgsCapacity
      sixthArgsCapacity seventhArgsCapacity callbackArgsCapacity
      leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
      seventhArguments callbackArguments
      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
      rightDepositLo rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
      fifthDepositLo fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas
      seventhDepositLo seventhDepositHi seventhGas callbackDepositLo callbackDepositHi callbackGas =>
      leftArguments ++ midArguments ++ rightArguments ++ fourthArguments ++ fifthArguments ++
        sixthArguments ++ seventhArguments ++ callbackArguments ++
        #[leftDepositLo, leftDepositHi, leftGas, midDepositLo, midDepositHi, midGas,
          rightDepositLo, rightDepositHi, rightGas, fourthDepositLo, fourthDepositHi, fourthGas,
          fifthDepositLo, fifthDepositHi, fifthGas, sixthDepositLo, sixthDepositHi, sixthGas,
          seventhDepositLo, seventhDepositHi, seventhGas, callbackDepositLo, callbackDepositHi,
          callbackGas]
  | .promiseFunctionCallAnd8ThenReturned
      leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod fourthReceiver fourthMethod
      fifthReceiver fifthMethod sixthReceiver sixthMethod seventhReceiver seventhMethod eighthReceiver
      eighthMethod callbackMethod leftArgsCapacity midArgsCapacity rightArgsCapacity fourthArgsCapacity
      fifthArgsCapacity sixthArgsCapacity seventhArgsCapacity eighthArgsCapacity callbackArgsCapacity
      leftArguments midArguments rightArguments fourthArguments fifthArguments sixthArguments
      seventhArguments eighthArguments callbackArguments
      leftDepositLo leftDepositHi leftGas midDepositLo midDepositHi midGas
      rightDepositLo rightDepositHi rightGas fourthDepositLo fourthDepositHi fourthGas
      fifthDepositLo fifthDepositHi fifthGas sixthDepositLo sixthDepositHi sixthGas
      seventhDepositLo seventhDepositHi seventhGas eighthDepositLo eighthDepositHi eighthGas
      callbackDepositLo callbackDepositHi callbackGas =>
      leftArguments ++ midArguments ++ rightArguments ++ fourthArguments ++ fifthArguments ++
        sixthArguments ++ seventhArguments ++ eighthArguments ++ callbackArguments ++
        #[leftDepositLo, leftDepositHi, leftGas, midDepositLo, midDepositHi, midGas,
          rightDepositLo, rightDepositHi, rightGas, fourthDepositLo, fourthDepositHi, fourthGas,
          fifthDepositLo, fifthDepositHi, fifthGas, sixthDepositLo, sixthDepositHi, sixthGas,
          seventhDepositLo, seventhDepositHi, seventhGas, eighthDepositLo, eighthDepositHi, eighthGas,
          callbackDepositLo, callbackDepositHi, callbackGas]
  | .promiseResultRead _ index => #[index]
  | .transientBuffer64Begin _ | .transientBuffer64Finish _ => #[]
  | .transientBuffer64Set _ index value => #[index, value]
  | .storageRead _ _ key | .storageRemove _ _ key | .storageHasKey _ _ key => key
  | .storageWrite _ _ _ key value => key ++ value
  | .sha256Hash _ _ input | .keccak256Hash _ _ input
  | .keccak512Hash _ _ input | .ripemd160Hash _ _ input => input
  | .ecrecover _ hash sig v malleability => hash ++ sig ++ #[v, malleability]
  | .ed25519Verify _ sig msg pk => sig ++ msg ++ pk
  | .reserved => #[]

def cfgDialect : Core.CFG.Dialect ValKind OpExt where
  mapValues := mapCfgPayload
  values := cfgPayloadValues
  payloadEq := fun left right => left == right

end ProofForge.Wasm.Near.Ops
