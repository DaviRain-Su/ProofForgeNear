import ProofForge

/-!
Chain context fixture: epoch height, gas meters, locked balance, random seed.
View entries read only view-safe leaves; gas meters are view-forbidden and live
on mutating entries.
-/
namespace Examples.Near.NearChain
open ProofForge.Wasm.Near.Sdk

structure State where
  stamped : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { stamped := 0 }

/-- view：当前 epoch height。 -/
@[pf_entry]
def epoch (_s : State) : UInt64 :=
  Context.epochHeight

/-- view：当前账户 locked(staked)余额的低 64 位。 -/
@[pf_entry]
def lockedLo (_s : State) : UInt64 :=
  Context.lockedBalance.w0

/-- view：当前账户 locked(staked)余额的高 64 位。 -/
@[pf_entry]
def lockedHigh (_s : State) : UInt64 :=
  Context.lockedBalance.w1

/-- view：random_seed 的前 8 字节 LE。公开 VRF 输出,不是秘密。 -/
@[pf_entry]
def seedLo (_s : State) : UInt64 :=
  Context.randomSeedW0

/-- view：random_seed 的最高 8 字节(字节 24..31)。 -/
@[pf_entry]
def seedTop (_s : State) : UInt64 :=
  Context.randomSeedW3

/-- 入口：预付 gas。view 禁止。 -/
@[pf_entry]
def prepaid (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Context.prepaidGas }, Context.prepaidGas)
  else
    .error .overflow

/-- 入口：当前已燃烧 gas。view 禁止。 -/
@[pf_entry]
def burnt (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ stamped := Context.usedGas }, Context.usedGas)
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.stamped

end Examples.Near.NearChain
