import ProofForge.Attr
import ProofForge.Wasm.Near.Runtime
import ProofForge.Wasm.Near.Sdk.Transient
import ProofForge.Wasm.Near.Sdk.Storage
import ProofForge.Wasm.Near.Sdk.Promise
import ProofForge.Wasm.Near.Sdk.Fungible.Ledger
import ProofForge.Wasm.Near.Sdk.Fungible.Registration
import ProofForge.Wasm.Near.Sdk.Store.AccountTokenLookup
import ProofForge.Wasm.Near.Sdk.Store.Codec
import ProofForge.Wasm.Near.Sdk.Store.Iterable
import ProofForge.Wasm.Near.Sdk.Store.Lookup
import ProofForge.Wasm.Near.Sdk.Store.Queue
import ProofForge.Wasm.Near.Sdk.Store.Vector

namespace ProofForge.Wasm.Near.Sdk

/-!
Source-facing NEAR SDK. Names erase through `@[pf_inline]` to Runtime stubs;
they do not add Ops, IR nodes, or emitter cases unless explicitly documented as event effects.
Bounded Promise-result observation, strict Borsh UInt64 result decoding, full-AccountId
self-callback authentication, exact NEP-141 mint/transfer/burn event serialization with
optional bounded memos, and the integrated `NearFungibleLedger` public FT surface are available.
-/

notation "AccountId" => Runtime.AccountId
notation "NearToken" => Runtime.NearToken

namespace «NearToken»

@[pf_inline] def zero : NearToken := ⟨0, 0⟩

/-- True when both limbs are zero. -/
@[pf_inline] def isZero (value : NearToken) : Bool :=
  value.w0 = 0 && value.w1 = 0

/-- Unsigned 128-bit less-or-equal comparison. -/
@[pf_inline] def le (left right : NearToken) : Bool :=
  if left.w1 < right.w1 then true
  else if left.w1 > right.w1 then false
  else left.w0 ≤ right.w0

/-- Unsigned 128-bit less-than comparison. -/
@[pf_inline] def lt (left right : NearToken) : Bool :=
  le left right && !(left.w0 = right.w0 && left.w1 = right.w1)

/-- Construct a token from explicit low/high limbs. -/
@[pf_inline] def ofLimbs (w0 w1 : UInt64) : NearToken := ⟨w0, w1⟩

/-- True exactly when unsigned 128-bit addition is representable. -/
@[pf_inline] def canAdd (left right : NearToken) : Bool :=
  Runtime.nearTokenAddOk left.w0 left.w1 right.w0 right.w1 != 0

/-- Checked addition. Returns `none` on overflow instead of exposing limb helpers. -/
@[pf_inline] def add? (left right : NearToken) : Option NearToken :=
  if canAdd left right then
    some ⟨Runtime.nearTokenAddW0 left.w0 left.w1 right.w0 right.w1,
      Runtime.nearTokenAddW1 left.w0 left.w1 right.w0 right.w1⟩
  else
    none

/-- Low modular result limb. Precondition: `canAdd left right`. -/
@[pf_inline] def addW0 (left right : NearToken) : UInt64 :=
  Runtime.nearTokenAddW0 left.w0 left.w1 right.w0 right.w1

/-- High result limb including the low-limb carry. Precondition: `canAdd left right`. -/
@[pf_inline] def addW1 (left right : NearToken) : UInt64 :=
  Runtime.nearTokenAddW1 left.w0 left.w1 right.w0 right.w1

/-- Checked addition with an explicit typed error for `Except` chains. -/
@[pf_inline] def addChecked (left right : NearToken) (error : ε) : Except ε NearToken :=
  if canAdd left right then
    .ok (ofLimbs (addW0 left right) (addW1 left right))
  else
    .error error

/-- True exactly when `left ≥ right` as unsigned 128-bit values. -/
@[pf_inline] def canSub (left right : NearToken) : Bool :=
  Runtime.nearTokenSubOk left.w0 left.w1 right.w0 right.w1 != 0

/-- Checked subtraction. Returns `none` on underflow. -/
@[pf_inline] def sub? (left right : NearToken) : Option NearToken :=
  if canSub left right then
    some ⟨Runtime.nearTokenSubW0 left.w0 left.w1 right.w0 right.w1,
      Runtime.nearTokenSubW1 left.w0 left.w1 right.w0 right.w1⟩
  else
    none

/-- Low modular result limb. Precondition: `canSub left right`. -/
@[pf_inline] def subW0 (left right : NearToken) : UInt64 :=
  Runtime.nearTokenSubW0 left.w0 left.w1 right.w0 right.w1

/-- High result limb including the low-limb borrow. Precondition: `canSub left right`. -/
@[pf_inline] def subW1 (left right : NearToken) : UInt64 :=
  Runtime.nearTokenSubW1 left.w0 left.w1 right.w0 right.w1

/-- Checked subtraction with an explicit typed error for `Except` chains. -/
@[pf_inline] def subChecked (left right : NearToken) (error : ε) : Except ε NearToken :=
  if canSub left right then
    .ok (ofLimbs (subW0 left right) (subW1 left right))
  else
    .error error

/-- True exactly when `value * factor` is representable as an unsigned 128-bit value. -/
@[pf_inline] def canMulUInt64 (value : NearToken) (factor : UInt64) : Bool :=
  Runtime.nearTokenMulU64Ok value.w0 value.w1 factor != 0

/-- Checked full-width multiply by one `UInt64` factor. -/
@[pf_inline] def mulUInt64? (value : NearToken) (factor : UInt64) : Option NearToken :=
  if canMulUInt64 value factor then
    some ⟨Runtime.nearTokenMulU64W0 value.w0 value.w1 factor,
      Runtime.nearTokenMulU64W1 value.w0 value.w1 factor⟩
  else
    none

/-- Low exact product limb. Precondition: `canMulUInt64 value factor`. -/
@[pf_inline] def mulUInt64W0 (value : NearToken) (factor : UInt64) : UInt64 :=
  Runtime.nearTokenMulU64W0 value.w0 value.w1 factor

/-- High exact product limb. Precondition: `canMulUInt64 value factor`. -/
@[pf_inline] def mulUInt64W1 (value : NearToken) (factor : UInt64) : UInt64 :=
  Runtime.nearTokenMulU64W1 value.w0 value.w1 factor

/-- Checked multiply with an explicit typed error for `Except` chains. -/
@[pf_inline] def mulUInt64Checked (value : NearToken) (factor : UInt64) (error : ε) :
    Except ε NearToken :=
  if canMulUInt64 value factor then
    .ok (ofLimbs (mulUInt64W0 value factor) (mulUInt64W1 value factor))
  else
    .error error

end «NearToken»

namespace «AccountId»

/-- Lossless equality over the length and all 64 bytes. Nested `if` keeps the
comparison inside the current wasm scalar subset; this is not a host call. -/
@[pf_inline] def eq (left right : AccountId) : Bool :=
  if left.length = right.length then
    if left.w0 = right.w0 then
      if left.w1 = right.w1 then
        if left.w2 = right.w2 then
          if left.w3 = right.w3 then
            if left.w4 = right.w4 then
              if left.w5 = right.w5 then
                if left.w6 = right.w6 then
                  left.w7 = right.w7
                else false
              else false
            else false
          else false
        else false
      else false
    else false
  else false

end «AccountId»

namespace Context

@[pf_inline] def blockHeight : UInt64 :=
  Runtime.blockIndex

@[pf_inline] def unixTimeSeconds : UInt64 :=
  Runtime.blockTimestamp

/-- Current contract storage usage in bytes. It reflects earlier writes in the same invocation. -/
@[pf_inline] def storageUsage : UInt64 :=
  Runtime.storageUsage

/-- Complete immediate caller. Init/entry only; views fail closed at emit. -/
@[pf_inline] def caller : AccountId :=
  Runtime.predecessorAccountId

/-- Legacy low word. Not an identity; use `caller` for authorization. -/
@[pf_inline] def callerLo : UInt64 := Runtime.predecessor

/-- Complete attached yoctoNEAR amount. Init/entry only; views fail closed. -/
@[pf_inline] def attachedDeposit : NearToken :=
  Runtime.attachedDeposit128

/-- Legacy UInt64 projection. Traps if the attached amount exceeds UInt64. -/
@[pf_inline] def attachedDepositLo : UInt64 := Runtime.attachedDeposit

/-- Complete, view-safe current-account balance. -/
@[pf_inline] def balanceOfSelf : NearToken :=
  Runtime.accountBalance128

/-- Legacy UInt64 balance. Traps if the current balance exceeds UInt64. -/
@[pf_inline] def balanceOfSelfLo : UInt64 := Runtime.accountBalance

/-- Complete current contract account id. View-safe. -/
@[pf_inline] def self : AccountId :=
  Runtime.selfAccountId

/-- Legacy low word. Not an identity; use `self` for equality. -/
@[pf_inline] def selfLo : UInt64 := Runtime.currentAccountId

/-- Current epoch height. View-safe. -/
@[pf_inline] def epochHeight : UInt64 := Runtime.epochHeight

/-- Gas prepaid by the transaction. View-forbidden; init/entry only. -/
@[pf_inline] def prepaidGas : UInt64 := Runtime.prepaidGas

/-- Gas burnt so far in this invocation. View-forbidden; init/entry only. -/
@[pf_inline] def usedGas : UInt64 := Runtime.usedGas

/-- Complete, view-safe locked (staked) balance of the current account. -/
@[pf_inline] def lockedBalance : NearToken :=
  Runtime.accountLockedBalance128

/-- Legacy UInt64 locked balance. Traps if the locked amount exceeds UInt64. -/
@[pf_inline] def lockedBalanceLo : UInt64 := Runtime.accountLockedBalance

/-- Complete transaction-signer account id. View-forbidden; init/entry only. -/
@[pf_inline] def signer : AccountId :=
  Runtime.signerAccountId

/-- Legacy low word. Not an identity; use `signer` for authorization. -/
@[pf_inline] def signerLo : UInt64 := Runtime.signer

/-- Signer public-key little-endian windows over the 33 wire bytes
(1 curve tag byte + 32 key bytes); `signerPkW4` carries only byte 32.
View-forbidden; init/entry only. -/
@[pf_inline] def signerPkW0 : UInt64 := Runtime.signerPk
@[pf_inline] def signerPkW1 : UInt64 := Runtime.signerPkW1
@[pf_inline] def signerPkW2 : UInt64 := Runtime.signerPkW2
@[pf_inline] def signerPkW3 : UInt64 := Runtime.signerPkW3
@[pf_inline] def signerPkW4 : UInt64 := Runtime.signerPkW4

/-- `random_seed` little-endian windows (32 bytes). View-safe, but the value is the
block's public VRF output — never secret, never user-specific. -/
@[pf_inline] def randomSeedW0 : UInt64 := Runtime.randomSeed
@[pf_inline] def randomSeedW1 : UInt64 := Runtime.randomSeedW1
@[pf_inline] def randomSeedW2 : UInt64 := Runtime.randomSeedW2
@[pf_inline] def randomSeedW3 : UInt64 := Runtime.randomSeedW3

end Context

namespace Logs

/-- Log one compile-time UTF-8 string. The current static slice accepts at most 1024 UTF-8 bytes
and returns zero for source sequencing; receipt logging remains the observable effect. -/
@[pf_inline] def write (message : String) : UInt64 :=
  Runtime.logUtf8 message

/-- Log the active bytes of one bounded UTF-8 string. Canonical `BoundedString` input is validated
before source execution; internally constructed values must satisfy `BoundedString.wellFormed`. -/
@[pf_inline] def writeBounded (capacity : Nat)
    (message : ProofForge.Core.Value.BoundedString capacity) : UInt64 :=
  Runtime.logUtf8Bounded capacity message

/-- Emit near-contract-standards' exact missing-registration informational log for one complete
AccountId. This closed helper does not expose arbitrary prefix/suffix composition. -/
@[pf_inline] def storageUnregistered (account : AccountId) : UInt64 :=
  Runtime.storageUnregisteredLog account

end Logs

namespace Events

/-- Emit one compact NEP-297 `EVENT_JSON:` envelope with a bounded string `data` value. This is a
closed event serializer, not a generic JSON ABI. Metadata is compile-time and all strings receive
serde_json-compatible escaping in the target emitter. -/
@[pf_inline] def writeStringData (standard version event : String) (capacity : Nat)
    (data : ProofForge.Core.Value.BoundedString capacity) : UInt64 :=
  Runtime.nep297StringData capacity standard version event data

namespace FungibleToken

/-- Emit one exact NEP-141 v1.0.0 `ft_mint` event. Amount is a quoted full-u128 decimal and the
optional memo is deliberately omitted. Event support does not provide FT state or methods. -/
@[pf_inline] def mint (owner : AccountId) (amount : NearToken) : UInt64 :=
  Runtime.nep141FtMint owner amount

/-- Emit one exact NEP-141 v1.0.0 `ft_transfer` event. The record is ordered old owner, new owner,
then quoted full-u128 amount; optional memo is deliberately omitted. -/
@[pf_inline] def transfer
    (oldOwner newOwner : AccountId) (amount : NearToken) : UInt64 :=
  Runtime.nep141FtTransfer oldOwner newOwner amount

/-- Emit one exact NEP-141 v1.0.0 `ft_burn` event. Amount is quoted full-u128 decimal and the
optional memo is deliberately omitted. -/
@[pf_inline] def burn (owner : AccountId) (amount : NearToken) : UInt64 :=
  Runtime.nep141FtBurn owner amount

/-- Emit `ft_mint` with one bounded UTF-8 memo after the quoted amount field. -/
@[pf_inline] def mintWithMemo (owner : AccountId) (amount : NearToken) (memoCapacity : Nat)
    (memo : ProofForge.Core.Value.BoundedString memoCapacity) : UInt64 :=
  Runtime.nep141FtMintMemo memoCapacity owner amount memo

/-- Emit `ft_transfer` with one bounded UTF-8 memo after the quoted amount field. -/
@[pf_inline] def transferWithMemo (oldOwner newOwner : AccountId) (amount : NearToken)
    (memoCapacity : Nat) (memo : ProofForge.Core.Value.BoundedString memoCapacity) : UInt64 :=
  Runtime.nep141FtTransferMemo memoCapacity oldOwner newOwner amount memo

/-- Emit `ft_burn` with one bounded UTF-8 memo after the quoted amount field. -/
@[pf_inline] def burnWithMemo (owner : AccountId) (amount : NearToken) (memoCapacity : Nat)
    (memo : ProofForge.Core.Value.BoundedString memoCapacity) : UInt64 :=
  Runtime.nep141FtBurnMemo memoCapacity owner amount memo

end FungibleToken

end Events

namespace Access

/-- Callback/private-entry predicate. Promise callbacks should require the
immediate predecessor to equal the current contract account. -/
@[pf_inline] def isSelfCall : Bool :=
  AccountId.eq Context.caller Context.self

end Access

namespace Hash

/-- Compile-time SHA-256 result bound. Call `hash` then consume `w0..w3` before another crypto op. -/
abbrev Sha256 := Nat

@[pf_inline] def Sha256.hash {inputCapacity : Nat}
    (buffer : Sha256) (input : ProofForge.Core.Value.BoundedBytes inputCapacity) : UInt64 :=
  Runtime.sha256Hash buffer inputCapacity input

@[pf_inline] def Sha256.w0 (buffer : Sha256) : UInt64 := Runtime.sha256ResultW0 buffer
@[pf_inline] def Sha256.w1 (buffer : Sha256) : UInt64 := Runtime.sha256ResultW1 buffer
@[pf_inline] def Sha256.w2 (buffer : Sha256) : UInt64 := Runtime.sha256ResultW2 buffer
@[pf_inline] def Sha256.w3 (buffer : Sha256) : UInt64 := Runtime.sha256ResultW3 buffer

/-- Compile-time Keccak-256 result bound. -/
abbrev Keccak256 := Nat

@[pf_inline] def Keccak256.hash {inputCapacity : Nat}
    (buffer : Keccak256) (input : ProofForge.Core.Value.BoundedBytes inputCapacity) : UInt64 :=
  Runtime.keccak256Hash buffer inputCapacity input

@[pf_inline] def Keccak256.w0 (buffer : Keccak256) : UInt64 := Runtime.keccak256ResultW0 buffer
@[pf_inline] def Keccak256.w1 (buffer : Keccak256) : UInt64 := Runtime.keccak256ResultW1 buffer
@[pf_inline] def Keccak256.w2 (buffer : Keccak256) : UInt64 := Runtime.keccak256ResultW2 buffer
@[pf_inline] def Keccak256.w3 (buffer : Keccak256) : UInt64 := Runtime.keccak256ResultW3 buffer

/-- Compile-time Keccak-512 result bound. Not SHA3-512. -/
abbrev Keccak512 := Nat

@[pf_inline] def Keccak512.hash {inputCapacity : Nat}
    (buffer : Keccak512) (input : ProofForge.Core.Value.BoundedBytes inputCapacity) : UInt64 :=
  Runtime.keccak512Hash buffer inputCapacity input

@[pf_inline] def Keccak512.w0 (buffer : Keccak512) : UInt64 := Runtime.keccak512ResultW0 buffer
@[pf_inline] def Keccak512.w1 (buffer : Keccak512) : UInt64 := Runtime.keccak512ResultW1 buffer
@[pf_inline] def Keccak512.w2 (buffer : Keccak512) : UInt64 := Runtime.keccak512ResultW2 buffer
@[pf_inline] def Keccak512.w3 (buffer : Keccak512) : UInt64 := Runtime.keccak512ResultW3 buffer
@[pf_inline] def Keccak512.w4 (buffer : Keccak512) : UInt64 := Runtime.keccak512ResultW4 buffer
@[pf_inline] def Keccak512.w5 (buffer : Keccak512) : UInt64 := Runtime.keccak512ResultW5 buffer
@[pf_inline] def Keccak512.w6 (buffer : Keccak512) : UInt64 := Runtime.keccak512ResultW6 buffer
@[pf_inline] def Keccak512.w7 (buffer : Keccak512) : UInt64 := Runtime.keccak512ResultW7 buffer

/-- Compile-time RIPEMD-160 result bound (20 bytes; `w2` is 4-byte zero-padded). -/
abbrev Ripemd160 := Nat

@[pf_inline] def Ripemd160.hash {inputCapacity : Nat}
    (buffer : Ripemd160) (input : ProofForge.Core.Value.BoundedBytes inputCapacity) : UInt64 :=
  Runtime.ripemd160Hash buffer inputCapacity input

@[pf_inline] def Ripemd160.w0 (buffer : Ripemd160) : UInt64 := Runtime.ripemd160ResultW0 buffer
@[pf_inline] def Ripemd160.w1 (buffer : Ripemd160) : UInt64 := Runtime.ripemd160ResultW1 buffer
@[pf_inline] def Ripemd160.w2 (buffer : Ripemd160) : UInt64 := Runtime.ripemd160ResultW2 buffer

/-- Compile-time `ecrecover` result bound. `status = 0` means recovered; nonzero fails closed. -/
abbrev Ecrecover := Nat

notation "CryptoBytes32" => Runtime.CryptoBytes32
notation "CryptoBytes64" => Runtime.CryptoBytes64

@[pf_inline] def Ecrecover.recover (buffer : Ecrecover)
    (hash : CryptoBytes32) (sig : CryptoBytes64) (v malleability : UInt64) : UInt64 :=
  Runtime.ecrecover buffer hash sig v malleability

@[pf_inline] def Ecrecover.status (buffer : Ecrecover) : UInt64 :=
  Runtime.ecrecoverStatus buffer

@[pf_inline] def Ecrecover.ok (buffer : Ecrecover) : Bool :=
  buffer.status == 0

@[pf_inline] def Ecrecover.w0 (buffer : Ecrecover) : UInt64 := Runtime.ecrecoverResultW0 buffer
@[pf_inline] def Ecrecover.w1 (buffer : Ecrecover) : UInt64 := Runtime.ecrecoverResultW1 buffer
@[pf_inline] def Ecrecover.w2 (buffer : Ecrecover) : UInt64 := Runtime.ecrecoverResultW2 buffer
@[pf_inline] def Ecrecover.w3 (buffer : Ecrecover) : UInt64 := Runtime.ecrecoverResultW3 buffer
@[pf_inline] def Ecrecover.w4 (buffer : Ecrecover) : UInt64 := Runtime.ecrecoverResultW4 buffer
@[pf_inline] def Ecrecover.w5 (buffer : Ecrecover) : UInt64 := Runtime.ecrecoverResultW5 buffer
@[pf_inline] def Ecrecover.w6 (buffer : Ecrecover) : UInt64 := Runtime.ecrecoverResultW6 buffer
@[pf_inline] def Ecrecover.w7 (buffer : Ecrecover) : UInt64 := Runtime.ecrecoverResultW7 buffer

/-- Compile-time `ed25519_verify` result bound. Host `1` is valid; `0` is invalid. -/
abbrev Ed25519 := Nat

@[pf_inline] def Ed25519.verify {msgCapacity : Nat} (buffer : Ed25519)
    (sig : CryptoBytes64) (msg : ProofForge.Core.Value.BoundedBytes msgCapacity)
    (pk : CryptoBytes32) : UInt64 :=
  Runtime.ed25519Verify buffer msgCapacity sig msg pk

@[pf_inline] def Ed25519.ok (buffer : Ed25519) : Bool :=
  Runtime.ed25519VerifyOk buffer != 0

end Hash

end ProofForge.Wasm.Near.Sdk
