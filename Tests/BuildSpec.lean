import ProofForge
import ProofForge.Wasm.Near.Commands
import Tests.Fixtures
import Examples.Counter
import Examples.TokenShape
import Examples.NearPromiseHandle
import Examples.NearTokenErgonomics
import Examples.Near.NearBytes
import Examples.Near.NearCtx
import Examples.Near.NearFtReceiverDual
import Examples.Near.NearFtReceiverValue
import Examples.Near.NearFungibleLedger
import Examples.Near.NearFungibleTokenEvent
import Examples.Near.NearIterable
import Examples.Near.NearJsonAccountInput
import Examples.Near.NearJsonAmountInput
import Examples.Near.NearJsonBooleanMutation
import Examples.Near.NearJsonFtOnTransferInput
import Examples.Near.NearJsonFtResolveInput
import Examples.Near.NearJsonFtTransferCallInput
import Examples.Near.NearJsonFtTransferInput
import Examples.Near.NearJsonMemoInput
import Examples.Near.NearJsonMessageInput
import Examples.Near.NearJsonStorageDepositInput
import Examples.Near.NearJsonStorageUnregisterInput
import Examples.Near.NearJsonStorageWithdrawInput
import Examples.Near.NearJsonU128Mutation
import Examples.Near.NearJsonUnitOutput
import Examples.Near.NearLookup
import Examples.Near.NearMemory
import Examples.Near.NearMigration
import Examples.Near.NearOutput
import Examples.Near.NearPromise
import Examples.Near.NearPromiseOrValue
import Examples.Near.NearPromiseResult
import Examples.Near.NearQueue
import Examples.Near.NearStorage
import Examples.Near.NearStorageBalanceBoundsOutput
import Examples.Near.NearStorageBalanceOutput
import Examples.Near.NearStorageEconomics
import Examples.Near.NearStorageRegistration
import Examples.Near.NearTokenArithmetic
import Examples.Near.NearTokenStorage
import Examples.Near.NearVector

/-!
# NEAR build surface

`#pf_near_build` re-extracts each registered fixture and pins
the target IR digest against `ProofForge.Wasm.Near.Registry`.
-/

#pf_near_build Examples.Counter

#pf_near_build Examples.TokenShape

#pf_near_build Examples.NearPromiseHandle

#pf_near_build Examples.NearTokenErgonomics

#pf_near_build Examples.Near.NearBytes

#pf_near_build Examples.Near.NearCtx

#pf_near_build Examples.Near.NearFtReceiverDual

#pf_near_build Examples.Near.NearFtReceiverValue

#pf_near_build Examples.Near.NearFungibleLedger

#pf_near_build Examples.Near.NearFungibleTokenEvent

#pf_near_build Examples.Near.NearIterable

#pf_near_build Examples.Near.NearJsonAccountInput

#pf_near_build Examples.Near.NearJsonAmountInput

#pf_near_build Examples.Near.NearJsonBooleanMutation

#pf_near_build Examples.Near.NearJsonFtOnTransferInput

#pf_near_build Examples.Near.NearJsonFtResolveInput

#pf_near_build Examples.Near.NearJsonFtTransferCallInput

#pf_near_build Examples.Near.NearJsonFtTransferInput

#pf_near_build Examples.Near.NearJsonMemoInput

#pf_near_build Examples.Near.NearJsonMessageInput

#pf_near_build Examples.Near.NearJsonStorageDepositInput

#pf_near_build Examples.Near.NearJsonStorageUnregisterInput

#pf_near_build Examples.Near.NearJsonStorageWithdrawInput

#pf_near_build Examples.Near.NearJsonU128Mutation

#pf_near_build Examples.Near.NearJsonUnitOutput

#pf_near_build Examples.Near.NearLookup

#pf_near_build Examples.Near.NearMemory

#pf_near_build Examples.Near.NearMigration

#pf_near_build Examples.Near.NearOutput

#pf_near_build Examples.Near.NearPromise

#pf_near_build Examples.Near.NearPromiseOrValue

#pf_near_build Examples.Near.NearPromiseResult

#pf_near_build Examples.Near.NearQueue

#pf_near_build Examples.Near.NearStorage

#pf_near_build Examples.Near.NearStorageBalanceBoundsOutput

#pf_near_build Examples.Near.NearStorageBalanceOutput

#pf_near_build Examples.Near.NearStorageEconomics

#pf_near_build Examples.Near.NearStorageRegistration

#pf_near_build Examples.Near.NearTokenArithmetic

#pf_near_build Examples.Near.NearTokenStorage

#pf_near_build Examples.Near.NearVector

/--
error: extract/unsupported: no pf_entry
-/
#guard_msgs (error) in
#pf_near_build Tests.Fixtures
