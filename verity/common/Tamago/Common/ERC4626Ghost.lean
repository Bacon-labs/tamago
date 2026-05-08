import Tamago.Tokens.ERC4626

/-!
ERC4626 closed-world ghost definitions.

This module intentionally lives outside `verity/spec`: Tama treats public
top-level definitions in spec modules as candidate obligations, while the
definitions here model the closed-world ERC4626 trace alphabet used by public
trace-wide economic specs.
-/

namespace Tamago.Common.ERC4626Ghost

open Verity
open Verity.EVM.Uint256
open Tamago.Tokens.ERC4626

/-!
## Closed-World Trace Model

The closed-world model includes successful `approve`, share `transfer`, share
`transferFrom`, `deposit`, `mint`, `withdraw`, `redeem`, `donate`, and
`distributeYield` actions from the constructor state.

`donate` models a direct ERC20 asset transfer into the vault: external backing
increases, but this implementation's managed `totalAssets` accounting does not.

`distributeYield` models realized yield: external backing and managed
`totalAssets` both increase, while share supply is unchanged.

The model intentionally excludes failed calls, fees, slashing, and arbitrary
external ERC20 transfers to non-vault accounts. Those excluded phenomena are
covered by other public specs: failed calls by revert/no-change specs,
donation inflow by the closed-world `donate` action and the weaker
donation-permitted backing property, yield inflow by `distributeYield`, and
external ERC20 behavior by the traced asset-transfer specs plus mirror tests.

Within this closed world, "all possible execution traces" means every finite
sequence whose elements are in `ClosedWorldAction` and whose adjacent states
satisfy `ClosedWorldStep`. The coverage is structural:

* `ClosedWorldReachable.init` covers the empty trace from constructor state.
* `ClosedWorldReachable.step` extends any already-covered finite trace by one
  valid successful action.
* Induction on `ClosedWorldReachable` therefore covers every finite closed-world
  trace, because every nonempty finite trace can be decomposed into a shorter
  trace plus its last action.

The step relation encodes the effect of each allowed action family. Share-only
actions leave managed assets and backing unchanged; donation increases only
vault asset backing; yield distribution increases managed assets and backing
without minting shares; deposit/mint increase managed assets, share supply, and
vault asset balance together; withdraw/redeem decrease them together. The public
closed-world specs prove invariants for every reachable state, not just for
selected sample traces.
-/

inductive ClosedWorldAction where
  | approve (ownerAddr spender : Address) (amount : Nat)
  | transfer (fromAddr toAddr : Address) (amount : Nat)
  | transferFrom (spender fromAddr toAddr : Address) (amount : Nat)
  | donate (donor : Address) (amount : Nat)
  | distributeYield (source : Address) (amount : Nat)
  | deposit (sender receiver : Address) (assets : Nat)
  | mint (sender receiver : Address) (shares : Nat)
  | withdraw (sender receiver ownerAddr : Address) (assets : Nat)
  | redeem (sender receiver ownerAddr : Address) (shares : Nat)

structure ClosedWorldState where
  managedAssets : Nat
  tokenSupply : Nat
  vaultAssetBalance : Nat
  fixedShareValueFloor : Nat
  callerWealthBound : Nat
  unrecognizedSurplus : Nat

def ClosedWorldGood (w : ClosedWorldState) : Prop :=
  w.tokenSupply ≤ w.managedAssets ∧
  w.managedAssets ≤ w.vaultAssetBalance ∧
  1 ≤ w.fixedShareValueFloor ∧
  w.callerWealthBound = 0

def ClosedWorldStep
    (action : ClosedWorldAction) (before after : ClosedWorldState) : Prop :=
  match action with
  | ClosedWorldAction.approve _ _ _ =>
      after = before
  | ClosedWorldAction.transfer _ _ _ =>
      after = before
  | ClosedWorldAction.transferFrom _ _ _ _ =>
      after = before
  | ClosedWorldAction.donate _ amount =>
      after.managedAssets = before.managedAssets ∧
      after.tokenSupply = before.tokenSupply ∧
      after.vaultAssetBalance = before.vaultAssetBalance + amount ∧
      after.fixedShareValueFloor = before.fixedShareValueFloor ∧
      after.callerWealthBound = before.callerWealthBound ∧
      after.unrecognizedSurplus = before.unrecognizedSurplus + amount
  | ClosedWorldAction.distributeYield _ amount =>
      after.managedAssets = before.managedAssets + amount ∧
      after.tokenSupply = before.tokenSupply ∧
      after.vaultAssetBalance = before.vaultAssetBalance + amount ∧
      after.fixedShareValueFloor = before.fixedShareValueFloor + amount ∧
      after.callerWealthBound = before.callerWealthBound ∧
      after.unrecognizedSurplus = before.unrecognizedSurplus
  | ClosedWorldAction.deposit _ _ assets =>
      after.managedAssets = before.managedAssets + assets ∧
      after.tokenSupply = before.tokenSupply + assets ∧
      after.vaultAssetBalance = before.vaultAssetBalance + assets ∧
      after.fixedShareValueFloor = before.fixedShareValueFloor ∧
      after.callerWealthBound = before.callerWealthBound ∧
      after.unrecognizedSurplus = before.unrecognizedSurplus
  | ClosedWorldAction.mint _ _ shares =>
      after.managedAssets = before.managedAssets + shares ∧
      after.tokenSupply = before.tokenSupply + shares ∧
      after.vaultAssetBalance = before.vaultAssetBalance + shares ∧
      after.fixedShareValueFloor = before.fixedShareValueFloor ∧
      after.callerWealthBound = before.callerWealthBound ∧
      after.unrecognizedSurplus = before.unrecognizedSurplus
  | ClosedWorldAction.withdraw _ _ _ assets =>
      after.managedAssets = before.managedAssets - assets ∧
      after.tokenSupply = before.tokenSupply - assets ∧
      after.vaultAssetBalance = before.vaultAssetBalance - assets ∧
      after.fixedShareValueFloor = before.fixedShareValueFloor ∧
      after.callerWealthBound = before.callerWealthBound ∧
      after.unrecognizedSurplus = before.unrecognizedSurplus
  | ClosedWorldAction.redeem _ _ _ shares =>
      after.managedAssets = before.managedAssets - shares ∧
      after.tokenSupply = before.tokenSupply - shares ∧
      after.vaultAssetBalance = before.vaultAssetBalance - shares ∧
      after.fixedShareValueFloor = before.fixedShareValueFloor ∧
      after.callerWealthBound = before.callerWealthBound ∧
      after.unrecognizedSurplus = before.unrecognizedSurplus

inductive ClosedWorldReachable : ClosedWorldState → Prop where
  | init :
      ClosedWorldReachable
        { managedAssets := 0, tokenSupply := 0, vaultAssetBalance := 0,
          fixedShareValueFloor := 1, callerWealthBound := 0,
          unrecognizedSurplus := 0 }
  | step {before after : ClosedWorldState} (action : ClosedWorldAction) :
      ClosedWorldReachable before →
      ClosedWorldStep action before after →
      ClosedWorldReachable after

inductive ClosedWorldFollows : ClosedWorldState → ClosedWorldState → Prop where
  | refl (w : ClosedWorldState) :
      ClosedWorldFollows w w
  | step {start before after : ClosedWorldState} (action : ClosedWorldAction) :
      ClosedWorldFollows start before →
      ClosedWorldStep action before after →
      ClosedWorldFollows start after

end Tamago.Common.ERC4626Ghost
