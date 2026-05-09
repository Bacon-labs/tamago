import Tamago.Tokens.ERC4626

/-!
ERC4626 concrete-call helper definitions.

This module intentionally lives outside `verity/spec`: Tama treats public
top-level definitions in spec modules as candidate obligations, while the
definitions here are modeling support for the public ERC4626 specs.
-/

namespace Tamago.Common.ERC4626Concrete

open Verity
open Verity.EVM.Uint256
open Tamago.Tokens.ERC4626

/-!
## Ghost ERC20 Asset State and Transfer Traces

The Verity `ContractState` for an ERC4626 vault models only the vault's own
storage. The underlying ERC20 asset balances live in another contract, so the
asset world is modeled explicitly as `AssetBalances` instead of being read from
vault storage.

Asset movement is connected to concrete vault execution through ERC4626-local
ghost trace events. The source-level `safeTransferFrom` and `safeTransfer`
wrappers first run the standard ERC20 ECM helper and append an asset-transfer
trace event only after that helper returns successfully. Verity's `Contract.run`
rolls the state back on revert, so a reverted vault call cannot retain a trace
event from a transfer point it failed past.
-/

abbrev AssetBalances := Address → Uint256

def assetBalancesUnchanged (pre post : AssetBalances) : Prop :=
  ∀ account, post account = pre account

def assetTraceContains (event : Event) (events : List Event) : Prop :=
  event ∈ events

def hasSafeTransferFromTrace
    (asset fromAddr toAddr : Address) (amount : Uint256)
    (s : ContractState) : Prop :=
  assetTraceContains
    (Tamago.Tokens.erc4626AssetSafeTransferFromEvent asset fromAddr toAddr amount)
    s.events

def hasSafeTransferTrace
    (asset fromAddr toAddr : Address) (amount : Uint256)
    (s : ContractState) : Prop :=
  assetTraceContains
    (Tamago.Tokens.erc4626AssetSafeTransferEvent asset fromAddr toAddr amount)
    s.events

def assetWorldAfterTransfer
    (pre : AssetBalances) (fromAddr toAddr : Address) (amount : Uint256) :
    AssetBalances :=
  fun account =>
    if fromAddr = toAddr then
      pre account
    else if account = fromAddr then
      Verity.EVM.Uint256.sub (pre account) amount
    else if account = toAddr then
      pre account + amount
    else
      pre account

/-!
## Local Arithmetic Helpers

These definitions mirror the simple no-fee, no-yield ERC4626 share/asset
arithmetic used by the vault. Keeping the formulas here makes the public specs
readable while keeping helper definitions out of the public spec namespace.
-/

def depositShares (assets : Uint256) (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.div
    (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
    (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1)

def mintAssets (shares : Uint256) (s : ContractState) : Uint256 :=
  let denominator := Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1
  Verity.EVM.Uint256.div
    (Verity.EVM.Uint256.add
      (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.sub denominator 1))
    denominator

def withdrawShares (assets : Uint256) (s : ContractState) : Uint256 :=
  let denominator := Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1
  Verity.EVM.Uint256.div
    (Verity.EVM.Uint256.add
      (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
      (Verity.EVM.Uint256.sub denominator 1))
    denominator

def redeemAssets (shares : Uint256) (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.div
    (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
    (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)

def revertedWithOriginalState {α : Type} (s : ContractState) (result : ContractResult α) : Prop :=
  ∃ reason, result = ContractResult.revert reason s

def fixedShareAssets (shares : Uint256) (s : ContractState) : Uint256 :=
  Verity.EVM.Uint256.div
    (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
    (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)

def assetDenominatedWealth
    (liquidAssets shareBalance : Uint256) (s : ContractState) : Nat :=
  liquidAssets.val + (fixedShareAssets shareBalance s).val

end Tamago.Common.ERC4626Concrete
