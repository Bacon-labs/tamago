import Tamago.Tokens.ERC4626
import Tamago.Common.ERC4626Concrete
import Tamago.Common.ERC4626Ghost
import Tamago.Spec.Tokens.ERC20Spec

namespace Tamago.Spec.Tokens.ERC4626Spec

open Verity
open Verity.EVM.Uint256
open Tamago.Tokens.ERC4626
open Tamago.Common.ERC4626Concrete
open Tamago.Common.ERC4626Ghost
open Tamago.Spec.Tokens.ERC20Spec

/-
ERC4626 specs are grouped by the ERC20 share-token surface first, then vault
specific views and asset movement. ERC20-compatible functions delegate to ERC20
specs; vault functions describe share/asset conversion and accounting.
-/

/-
ERC20 share-token surface

Properties specified:
- decimals(), totalSupply(), balanceOf(), allowance(), approve(), transfer(),
  and transferFrom() satisfy the same properties as ERC20 shares.

Security conclusions:
- Vault shares inherit ERC20 balance, supply, and allowance safety.
- Share transfers cannot change total share supply.
-/
def erc4626_decimals_spec (result : Uint256) : Prop :=
  erc20_decimals_spec result

def erc4626_totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  erc20_totalSupply_spec result s

def erc4626_balanceOf_spec (account : Address) (result : Uint256) (s : ContractState) : Prop :=
  erc20_balanceOf_spec account result s

def erc4626_allowance_spec (ownerAddr spender : Address) (result : Uint256) (s : ContractState) : Prop :=
  erc20_allowance_spec ownerAddr spender result s

def erc4626_approve_succeeds
    (spender : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_approve_succeeds spender amount s result

def erc4626_approve_sets_allowance
    (spender : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_approve_sets_allowance spender amount s result

def erc4626_approve_keeps_balances
    (spender : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_approve_keeps_balances spender amount s result

def erc4626_approve_keeps_total_supply
    (spender : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_approve_keeps_total_supply spender amount s result

def erc4626_transfer_reverts_when_balance_is_low
    (toAddr : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_transfer_reverts_when_balance_is_low toAddr amount s result

def erc4626_transfer_to_self_keeps_balances
    (toAddr : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_transfer_to_self_keeps_balances toAddr amount s result

def erc4626_transfer_reverts_when_recipient_balance_would_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_transfer_reverts_when_recipient_balance_would_overflow toAddr amount s result

def erc4626_transfer_moves_tokens_between_distinct_accounts
    (toAddr : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_transfer_moves_tokens_between_distinct_accounts toAddr amount s result

def erc4626_transfer_keeps_total_supply
    (toAddr : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_transfer_keeps_total_supply toAddr amount s result

def erc4626_transferFrom_reverts_when_allowance_is_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_reverts_when_allowance_is_low fromAddr toAddr amount s result

def erc4626_transferFrom_reverts_when_balance_is_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_reverts_when_balance_is_low fromAddr toAddr amount s result

def erc4626_transferFrom_reverts_when_recipient_balance_would_overflow
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_reverts_when_recipient_balance_would_overflow fromAddr toAddr amount s result

def erc4626_transferFrom_to_self_keeps_balances
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_to_self_keeps_balances fromAddr toAddr amount s result

def erc4626_transferFrom_moves_tokens_between_distinct_accounts
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_moves_tokens_between_distinct_accounts fromAddr toAddr amount s result

def erc4626_transferFrom_keeps_total_supply
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_keeps_total_supply fromAddr toAddr amount s result

def erc4626_transferFrom_keeps_infinite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_keeps_infinite_allowance fromAddr toAddr amount s result

def erc4626_transferFrom_spends_finite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_spends_finite_allowance fromAddr toAddr amount s result

/-
Vault views and previews

Properties specified:
- asset() and totalAssets() expose the stored asset token and managed-asset
  accounting.
- convertToShares() and convertToAssets() use the vault's virtual-share formula.
- maxDeposit() and maxMint() are unbounded at maxUint256.
- maxWithdraw() and maxRedeem() reflect the owner's current convertible assets
  and shares.
- previewDeposit()/previewRedeem() match conversion; previewMint()/previewWithdraw()
  use rounded-up formulas.

Security conclusions:
- Preview functions expose the same conversion formulas used by state-changing
  flows.
- Max functions are tied to the owner state used by withdrawals and redemptions.
-/
def erc4626_asset_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr assetToken.slot

def erc4626_totalAssets_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage managedAssets.slot

def erc4626_convertToShares_spec (assets result : Uint256) (s : ContractState) : Prop :=
  result =
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
      (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1)

def erc4626_convertToAssets_spec (shares result : Uint256) (s : ContractState) : Prop :=
  result =
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)

def erc4626_maxDeposit_spec (_receiver : Address) (result : Uint256) : Prop :=
  result = maxUint256

def erc4626_maxMint_spec (_receiver : Address) (result : Uint256) : Prop :=
  result = maxUint256

def erc4626_maxWithdraw_spec (ownerAddr : Address) (result : Uint256) (s : ContractState) : Prop :=
  result =
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)

def erc4626_maxRedeem_spec (ownerAddr : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap balances.slot ownerAddr

def erc4626_previewDeposit_spec (assets result : Uint256) (s : ContractState) : Prop :=
  erc4626_convertToShares_spec assets result s

def erc4626_previewMint_spec (shares result : Uint256) (s : ContractState) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1
  result =
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator

def erc4626_previewWithdraw_spec (assets result : Uint256) (s : ContractState) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1
  result =
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator

def erc4626_previewRedeem_spec (shares result : Uint256) (s : ContractState) : Prop :=
  erc4626_convertToAssets_spec shares result s

/-
Preview-to-execution bounds

Properties specified:
- Successful deposit returns at least the shares quoted by previewDeposit().
- Successful mint pulls no more assets than previewMint().
- Successful withdraw burns no more shares than previewWithdraw().
- Successful redeem returns at least the assets quoted by previewRedeem().

Security conclusions:
- State-changing entry points respect the ERC4626 preview inequalities on the
  same pre-call state.
- The current no-fee implementation satisfies these bounds exactly, while the
  specs remain phrased as ERC4626-safe inequalities.
-/
def erc4626_deposit_returns_at_least_preview
    (assets : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let shares := depositShares assets s
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.success shares result.snd ∧
          ((previewDeposit assets).run s).fst.val ≤ shares.val

def erc4626_mint_pulls_no_more_than_preview
    (shares : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let assets := mintAssets shares s
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.success assets result.snd ∧
          assets.val ≤ ((previewMint shares).run s).fst.val

def erc4626_withdraw_burns_no_more_than_preview
    (assets : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let shares := withdrawShares assets s
  let maxAssets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  assets.val ≤ maxAssets.val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
          shares.val ≤ (s.storage tokenSupply.slot).val →
            assets.val ≤ (s.storage managedAssets.slot).val →
              result = ContractResult.success shares result.snd ∧
                shares.val ≤ ((previewWithdraw assets).run s).fst.val

def erc4626_redeem_returns_at_least_preview
    (shares : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let assets := redeemAssets shares s
  shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storage tokenSupply.slot).val →
          assets.val ≤ (s.storage managedAssets.slot).val →
            result = ContractResult.success assets result.snd ∧
              ((previewRedeem shares).run s).fst.val ≤ assets.val

/-
deposit(assets, receiver)

Properties specified:
- The minted shares are computed from the current vault conversion formula.
- The call reverts if receiver shares, total share supply, or total managed
  assets would overflow.
- Otherwise, the call succeeds, credits receiver shares, increases total share
  supply, increases managed assets, and keeps the asset token fixed.

Security conclusions:
- Deposits mint shares according to current vault accounting.
- Receiver shares, total shares, and managed assets cannot overflow.
- The asset token identity is stable across deposits.
-/
def erc4626_deposit_reverts_when_receiver_balance_would_overflow
    (assets : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
      (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1)
  (s.storageMap balances.slot receiver).val + shares.val > Verity.Stdlib.Math.MAX_UINT256 →
    result = ContractResult.revert "Balance overflow" s

def erc4626_deposit_reverts_when_total_supply_would_overflow
    (assets : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
      (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1)
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val > Verity.Stdlib.Math.MAX_UINT256 →
      result = ContractResult.revert "Supply overflow" s

def erc4626_deposit_reverts_when_total_assets_would_overflow
    (assets : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
      (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1)
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val > Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.revert "Total assets overflow" s

def erc4626_deposit_succeeds_when_accounting_does_not_overflow
    (assets : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
      (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1)
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.success shares result.snd

def erc4626_deposit_credits_receiver
    (assets : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
      (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1)
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result.snd.storageMap balances.slot receiver =
          (s.storageMap balances.slot receiver) + shares

def erc4626_deposit_increases_total_supply
    (assets : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
      (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1)
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result.snd.storage tokenSupply.slot =
          (s.storage tokenSupply.slot) + shares

def erc4626_deposit_increases_total_assets
    (assets : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
      (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1)
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result.snd.storage managedAssets.slot =
          (s.storage managedAssets.slot) + assets

def erc4626_deposit_keeps_asset
    (assets : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
      (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1)
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result.snd.storageAddr assetToken.slot = s.storageAddr assetToken.slot

/-
mint(shares, receiver)

Properties specified:
- Required assets are computed with the rounded-up mint formula.
- The call reverts if receiver shares, total share supply, or total managed
  assets would overflow.
- Otherwise, the call succeeds, credits receiver shares, increases total share
  supply, increases managed assets, and keeps the asset token fixed.

Security conclusions:
- Minting shares pulls the rounded-up amount of assets required by the vault
  formula.
- Receiver shares, total shares, and managed assets cannot overflow.
- Share supply and managed assets increase together.
- The asset token identity is stable across mints.
-/
def erc4626_mint_reverts_when_receiver_balance_would_overflow
    (shares : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  (s.storageMap balances.slot receiver).val + shares.val > Verity.Stdlib.Math.MAX_UINT256 →
    result = ContractResult.revert "Balance overflow" s

def erc4626_mint_reverts_when_total_supply_would_overflow
    (shares : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val > Verity.Stdlib.Math.MAX_UINT256 →
      result = ContractResult.revert "Supply overflow" s

def erc4626_mint_reverts_when_total_assets_would_overflow
    (shares : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1
  let assets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val > Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.revert "Total assets overflow" s

def erc4626_mint_succeeds_when_accounting_does_not_overflow
    (shares : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1
  let assets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.success assets result.snd

def erc4626_mint_credits_receiver
    (shares : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1
  let assets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result.snd.storageMap balances.slot receiver =
          (s.storageMap balances.slot receiver) + shares

def erc4626_mint_increases_total_supply
    (shares : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1
  let assets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result.snd.storage tokenSupply.slot =
          (s.storage tokenSupply.slot) + shares

def erc4626_mint_increases_total_assets
    (shares : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1
  let assets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result.snd.storage managedAssets.slot =
          (s.storage managedAssets.slot) + assets

def erc4626_mint_keeps_asset
    (shares : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1
  let assets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result.snd.storageAddr assetToken.slot = s.storageAddr assetToken.slot

/-
withdraw(assets, receiver, owner)

Properties specified:
- Requested assets cannot exceed the owner's max withdraw amount.
- Non-owner callers need enough finite or infinite allowance for the burned
  shares.
- The vault must have enough share supply, and managed assets must cover the
  withdrawal.
- On success, owner shares, total supply, and managed assets decrease; finite
  allowance is spent while owner calls and infinite allowance are preserved.

Security conclusions:
- Withdrawals cannot exceed the owner's maximum withdrawable assets.
- Non-owner withdrawals cannot bypass share allowance.
- Successful withdrawals burn shares and reduce managed assets together.
- Infinite allowance is preserved, while finite allowance is spent.
-/
def erc4626_withdraw_reverts_when_assets_exceed_max
    (assets : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let maxAssets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  assets.val > maxAssets.val →
    result = ContractResult.revert "Withdraw more than max" s

def erc4626_withdraw_reverts_when_allowance_is_low
    (assets : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  let maxAssets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  assets.val ≤ maxAssets.val →
    s.sender ≠ ownerAddr →
      shares.val > (s.storageMap2 allowances.slot ownerAddr s.sender).val →
        result = ContractResult.revert "Insufficient allowance" s

def erc4626_withdraw_reverts_when_total_supply_is_low
    (assets : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  let maxAssets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  assets.val ≤ maxAssets.val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
          shares.val > (s.storage tokenSupply.slot).val →
            result = ContractResult.revert "Insufficient supply" s

def erc4626_withdraw_reverts_when_total_assets_is_low
    (assets : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  let maxAssets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  assets.val ≤ maxAssets.val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
          shares.val ≤ (s.storage tokenSupply.slot).val →
            assets.val > (s.storage managedAssets.slot).val →
              result = ContractResult.revert "Insufficient assets" s

def erc4626_withdraw_succeeds_when_accounting_and_allowance_are_enough
    (assets : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  let maxAssets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  assets.val ≤ maxAssets.val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
          shares.val ≤ (s.storage tokenSupply.slot).val →
            assets.val ≤ (s.storage managedAssets.slot).val →
              result = ContractResult.success shares result.snd

def erc4626_withdraw_debits_owner
    (assets : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  let maxAssets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  assets.val ≤ maxAssets.val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
          shares.val ≤ (s.storage tokenSupply.slot).val →
            assets.val ≤ (s.storage managedAssets.slot).val →
              result.snd.storageMap balances.slot ownerAddr =
                Verity.EVM.Uint256.sub (s.storageMap balances.slot ownerAddr) shares

def erc4626_withdraw_decreases_total_supply
    (assets : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  let maxAssets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  assets.val ≤ maxAssets.val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
          shares.val ≤ (s.storage tokenSupply.slot).val →
            assets.val ≤ (s.storage managedAssets.slot).val →
              result.snd.storage tokenSupply.slot =
                Verity.EVM.Uint256.sub (s.storage tokenSupply.slot) shares

def erc4626_withdraw_decreases_total_assets
    (assets : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  let maxAssets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  assets.val ≤ maxAssets.val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
          shares.val ≤ (s.storage tokenSupply.slot).val →
            assets.val ≤ (s.storage managedAssets.slot).val →
              result.snd.storage managedAssets.slot =
                Verity.EVM.Uint256.sub (s.storage managedAssets.slot) assets

def erc4626_withdraw_keeps_owner_or_infinite_allowance
    (assets : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  let maxAssets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  assets.val ≤ maxAssets.val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
          shares.val ≤ (s.storage tokenSupply.slot).val →
            assets.val ≤ (s.storage managedAssets.slot).val →
              (s.sender = ownerAddr ∨
                s.storageMap2 allowances.slot ownerAddr s.sender = maxUint256) →
                  result.snd.storageMap2 allowances.slot ownerAddr s.sender =
                    s.storageMap2 allowances.slot ownerAddr s.sender

def erc4626_withdraw_spends_finite_allowance
    (assets : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  let maxAssets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  assets.val ≤ maxAssets.val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
          shares.val ≤ (s.storage tokenSupply.slot).val →
            assets.val ≤ (s.storage managedAssets.slot).val →
              s.sender ≠ ownerAddr →
                s.storageMap2 allowances.slot ownerAddr s.sender ≠ maxUint256 →
                  result.snd.storageMap2 allowances.slot ownerAddr s.sender =
                    Verity.EVM.Uint256.sub
                      (s.storageMap2 allowances.slot ownerAddr s.sender) shares

/-
redeem(shares, receiver, owner)

Properties specified:
- Requested shares cannot exceed the owner's share balance.
- Non-owner callers need enough finite or infinite allowance.
- The vault must have enough share supply for the redemption.
- On success, owner shares, total supply, and managed assets decrease; finite
  allowance is spent while owner calls and infinite allowance are preserved.

Security conclusions:
- Redemptions cannot burn more shares than the owner holds.
- Non-owner redemptions cannot bypass share allowance.
- Successful redemptions burn shares and pay assets according to the vault
  formula.
- Infinite allowance is preserved, while finite allowance is spent.
-/
def erc4626_redeem_reverts_when_shares_exceed_max
    (shares : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  shares.val > (s.storageMap balances.slot ownerAddr).val →
    result = ContractResult.revert "Redeem more than max" s

def erc4626_redeem_reverts_when_allowance_is_low
    (shares : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
    s.sender ≠ ownerAddr →
      shares.val > (s.storageMap2 allowances.slot ownerAddr s.sender).val →
        result = ContractResult.revert "Insufficient allowance" s

def erc4626_redeem_reverts_when_total_supply_is_low
    (shares : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val > (s.storage tokenSupply.slot).val →
          result = ContractResult.revert "Insufficient supply" s

def erc4626_redeem_succeeds_when_accounting_and_allowance_are_enough
    (shares : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let assets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storage tokenSupply.slot).val →
          assets.val ≤ (s.storage managedAssets.slot).val →
            result = ContractResult.success assets result.snd

def erc4626_redeem_debits_owner
    (shares : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let assets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storage tokenSupply.slot).val →
          assets.val ≤ (s.storage managedAssets.slot).val →
            result.snd.storageMap balances.slot ownerAddr =
              Verity.EVM.Uint256.sub (s.storageMap balances.slot ownerAddr) shares

def erc4626_redeem_decreases_total_supply
    (shares : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let assets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storage tokenSupply.slot).val →
          assets.val ≤ (s.storage managedAssets.slot).val →
            result.snd.storage tokenSupply.slot =
              Verity.EVM.Uint256.sub (s.storage tokenSupply.slot) shares

def erc4626_redeem_decreases_total_assets
    (shares : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let assets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storage tokenSupply.slot).val →
          assets.val ≤ (s.storage managedAssets.slot).val →
            result.snd.storage managedAssets.slot =
              Verity.EVM.Uint256.sub (s.storage managedAssets.slot) assets

def erc4626_redeem_keeps_owner_or_infinite_allowance
    (shares : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let assets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storage tokenSupply.slot).val →
          assets.val ≤ (s.storage managedAssets.slot).val →
            (s.sender = ownerAddr ∨
              s.storageMap2 allowances.slot ownerAddr s.sender = maxUint256) →
                result.snd.storageMap2 allowances.slot ownerAddr s.sender =
                  s.storageMap2 allowances.slot ownerAddr s.sender

def erc4626_redeem_spends_finite_allowance
    (shares : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let assets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storage tokenSupply.slot).val →
          assets.val ≤ (s.storage managedAssets.slot).val →
            s.sender ≠ ownerAddr →
              s.storageMap2 allowances.slot ownerAddr s.sender ≠ maxUint256 →
                result.snd.storageMap2 allowances.slot ownerAddr s.sender =
                  Verity.EVM.Uint256.sub
                    (s.storageMap2 allowances.slot ownerAddr s.sender) shares

/-!
ERC4626 asset-transfer and closed-world security invariants.

This file contains only public spec obligations. Helper predicates, ghost asset
state, arithmetic mirrors, and the closed-world transition system live in
`Tamago.Common.ERC4626Ghost` so Tama does not treat them as standalone specs.

The public specs are organized as:

1. Successful deposit/mint/withdraw/redeem asset-movement specs.
2. Revert asset-balance specs.
3. Backing and donation-resistance specs.
4. Exchange-rate and no-profit specs.
5. Closed-world invariant specs over finite successful action sequences.
-/

/-!
## 1. Successful Asset-Movement Specs

Properties specified:
- Successful deposit and mint paths include a `safeTransferFrom` trace from the
  caller to the vault for the exact asset amount used by vault accounting.
- Successful withdraw and redeem paths include a `safeTransfer` trace from the
  vault to the receiver for the exact redeemed asset amount.
- The ghost `AssetBalances` post-state is the pre-state updated by the transfer
  arguments that appear in the concrete vault trace.

Security conclusions:
- A successful vault accounting update cannot omit the underlying asset move or
  route it through the wrong asset, sender, vault, receiver, or amount.
- The specs avoid the tautological shape "assume the ERC20 moved assets,
  therefore assets moved": if an implementation omits the ERC20 call, calls the
  wrong helper, or returns success without passing the transfer point, the trace
  proof fails.
- The remaining trust surface is the ERC20 helper interface itself. The trace
  records that the vault performed the external ERC20 operation; the helper
  axiom and mirror tests connect that operation to real ERC20 balance changes.
-/


def erc4626_deposit_pulls_assets_from_sender
    (assets : Uint256) (receiver : Address) (pre : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  let shares := depositShares assets s
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        hasSafeTransferFromTrace
            (s.storageAddr assetToken.slot) s.sender s.thisAddress assets result.snd ∧
          (assetWorldAfterTransfer pre s.sender s.thisAddress assets) s.sender =
            if s.sender = s.thisAddress then
              pre s.sender
            else
              Verity.EVM.Uint256.sub (pre s.sender) assets

def erc4626_deposit_increases_vault_asset_balance
    (assets : Uint256) (receiver : Address) (pre : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  let shares := depositShares assets s
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        hasSafeTransferFromTrace
            (s.storageAddr assetToken.slot) s.sender s.thisAddress assets result.snd ∧
          (assetWorldAfterTransfer pre s.sender s.thisAddress assets) s.thisAddress =
            if s.sender = s.thisAddress then
              pre s.thisAddress
            else
              (pre s.thisAddress) + assets

def erc4626_mint_pulls_required_assets_from_sender
    (shares : Uint256) (receiver : Address) (pre : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  let assets := mintAssets shares s
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        hasSafeTransferFromTrace
            (s.storageAddr assetToken.slot) s.sender s.thisAddress assets result.snd ∧
          (assetWorldAfterTransfer pre s.sender s.thisAddress assets) s.sender =
            if s.sender = s.thisAddress then
              pre s.sender
            else
              Verity.EVM.Uint256.sub (pre s.sender) assets

def erc4626_mint_increases_vault_asset_balance
    (shares : Uint256) (receiver : Address) (pre : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  let assets := mintAssets shares s
  (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        hasSafeTransferFromTrace
            (s.storageAddr assetToken.slot) s.sender s.thisAddress assets result.snd ∧
          (assetWorldAfterTransfer pre s.sender s.thisAddress assets) s.thisAddress =
            if s.sender = s.thisAddress then
              pre s.thisAddress
            else
              (pre s.thisAddress) + assets

def erc4626_withdraw_sends_assets_to_receiver
    (assets : Uint256) (receiver ownerAddr : Address) (pre : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  let shares := withdrawShares assets s
  let maxAssets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  assets.val ≤ maxAssets.val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
          shares.val ≤ (s.storage tokenSupply.slot).val →
            assets.val ≤ (s.storage managedAssets.slot).val →
              hasSafeTransferTrace
                  (s.storageAddr assetToken.slot) s.thisAddress receiver assets result.snd ∧
                (assetWorldAfterTransfer pre s.thisAddress receiver assets) receiver =
                  if s.thisAddress = receiver then
                    pre receiver
                  else
                    (pre receiver) + assets

def erc4626_withdraw_decreases_vault_asset_balance
    (assets : Uint256) (receiver ownerAddr : Address) (pre : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  let shares := withdrawShares assets s
  let maxAssets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  assets.val ≤ maxAssets.val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
          shares.val ≤ (s.storage tokenSupply.slot).val →
            assets.val ≤ (s.storage managedAssets.slot).val →
              hasSafeTransferTrace
                  (s.storageAddr assetToken.slot) s.thisAddress receiver assets result.snd ∧
                (assetWorldAfterTransfer pre s.thisAddress receiver assets) s.thisAddress =
                  if s.thisAddress = receiver then
                    pre s.thisAddress
                  else
                    Verity.EVM.Uint256.sub (pre s.thisAddress) assets

def erc4626_redeem_sends_redeemed_assets_to_receiver
    (shares : Uint256) (receiver ownerAddr : Address) (pre : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  let assets := redeemAssets shares s
  shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storage tokenSupply.slot).val →
          assets.val ≤ (s.storage managedAssets.slot).val →
            hasSafeTransferTrace
                (s.storageAddr assetToken.slot) s.thisAddress receiver assets result.snd ∧
              (assetWorldAfterTransfer pre s.thisAddress receiver assets) receiver =
                if s.thisAddress = receiver then
                  pre receiver
                else
                  (pre receiver) + assets

def erc4626_redeem_decreases_vault_asset_balance
    (shares : Uint256) (receiver ownerAddr : Address) (pre : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  let assets := redeemAssets shares s
  shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
    (s.sender = ownerAddr ∨
      shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
        shares.val ≤ (s.storage tokenSupply.slot).val →
          assets.val ≤ (s.storage managedAssets.slot).val →
            hasSafeTransferTrace
                (s.storageAddr assetToken.slot) s.thisAddress receiver assets result.snd ∧
              (assetWorldAfterTransfer pre s.thisAddress receiver assets) s.thisAddress =
                if s.thisAddress = receiver then
                  pre s.thisAddress
              else
                Verity.EVM.Uint256.sub (pre s.thisAddress) assets

/-!
## 2. Revert Asset-Balance Specs

Properties specified:
- Reverted deposit, mint, withdraw, and redeem calls leave the modeled ERC20
  asset world unchanged.
- Revert specs are stated against the reverted run state rather than against a
  successful transfer trace.

Security conclusions:
- Failed vault calls cannot pull or send assets in the ghost model.
- Because `Contract.run` rolls back state on revert, a reverted vault call
  cannot carry a durable transfer trace from this section's ERC20 helper
  wrappers.
-/

def erc4626_deposit_revert_keeps_asset_balances
    (_assets : Uint256) (_receiver : Address) (pre post : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  revertedWithOriginalState s result → assetBalancesUnchanged pre post

def erc4626_mint_revert_keeps_asset_balances
    (_shares : Uint256) (_receiver : Address) (pre post : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  revertedWithOriginalState s result → assetBalancesUnchanged pre post

def erc4626_withdraw_revert_keeps_asset_balances
    (_assets : Uint256) (_receiver _ownerAddr : Address) (pre post : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  revertedWithOriginalState s result → assetBalancesUnchanged pre post

def erc4626_redeem_revert_keeps_asset_balances
    (_shares : Uint256) (_receiver _ownerAddr : Address) (pre post : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  revertedWithOriginalState s result → assetBalancesUnchanged pre post

/-!
## 3. Backing and Donation-Resistance Specs

Properties specified:
- No-donation deposit, mint, withdraw, and redeem traces preserve exact backing:

`asset.balanceOf(vault) == totalAssets`.

- When donations are permitted, the weaker backing property is required:

`asset.balanceOf(vault) >= totalAssets`.

- Share-only actions (`transfer`, `transferFrom`, and `approve`) leave
  `totalAssets` unchanged and preserve any pre-existing backing inequality.

Security conclusions:
- In no-donation traces, managed liabilities are exactly matched by external
  asset backing.
- Donation can create surplus backing without changing `totalAssets`; yield
  distribution may increase `totalAssets`, but only together with matching
  ERC20 backing in the closed-world model.
- Share movement and approvals cannot alter the asset side of vault accounting.
-/

def erc4626_no_donation_deposit_preserves_backing
    (assets : Uint256) (receiver : Address) (pre : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  let shares := depositShares assets s
  pre s.thisAddress = s.storage managedAssets.slot →
    s.sender ≠ s.thisAddress →
      (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
          (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
            hasSafeTransferFromTrace
                (s.storageAddr assetToken.slot) s.sender s.thisAddress assets result.snd ∧
              (assetWorldAfterTransfer pre s.sender s.thisAddress assets) s.thisAddress =
                result.snd.storage managedAssets.slot

def erc4626_no_donation_mint_preserves_backing
    (shares : Uint256) (receiver : Address) (pre : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  let assets := mintAssets shares s
  pre s.thisAddress = s.storage managedAssets.slot →
    s.sender ≠ s.thisAddress →
      (s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        (s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
          (s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
            hasSafeTransferFromTrace
                (s.storageAddr assetToken.slot) s.sender s.thisAddress assets result.snd ∧
              (assetWorldAfterTransfer pre s.sender s.thisAddress assets) s.thisAddress =
                result.snd.storage managedAssets.slot

def erc4626_no_donation_withdraw_preserves_backing
    (assets : Uint256) (receiver ownerAddr : Address) (pre : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  let shares := withdrawShares assets s
  let maxAssets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul (s.storageMap balances.slot ownerAddr)
        (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  pre s.thisAddress = s.storage managedAssets.slot →
    s.thisAddress ≠ receiver →
      assets.val ≤ maxAssets.val →
        (s.sender = ownerAddr ∨
          shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
            shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
              shares.val ≤ (s.storage tokenSupply.slot).val →
                assets.val ≤ (s.storage managedAssets.slot).val →
                  hasSafeTransferTrace
                      (s.storageAddr assetToken.slot) s.thisAddress receiver assets result.snd ∧
                    (assetWorldAfterTransfer pre s.thisAddress receiver assets) s.thisAddress =
                      result.snd.storage managedAssets.slot

def erc4626_no_donation_redeem_preserves_backing
    (shares : Uint256) (receiver ownerAddr : Address) (pre : AssetBalances)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  let assets := redeemAssets shares s
  pre s.thisAddress = s.storage managedAssets.slot →
    s.thisAddress ≠ receiver →
      shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
        (s.sender = ownerAddr ∨
          shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
            shares.val ≤ (s.storage tokenSupply.slot).val →
              assets.val ≤ (s.storage managedAssets.slot).val →
                hasSafeTransferTrace
                    (s.storageAddr assetToken.slot) s.thisAddress receiver assets result.snd ∧
                  (assetWorldAfterTransfer pre s.thisAddress receiver assets) s.thisAddress =
                    result.snd.storage managedAssets.slot

def erc4626_donation_permitted_backing_covers_total_assets
    (vault : Address) (assetBalances : AssetBalances) (s : ContractState) : Prop :=
  (s.storage managedAssets.slot).val ≤ (assetBalances vault).val

def erc4626_transfer_keeps_total_assets_and_backing
    (_toAddr : Address) (_amount : Uint256) (vault : Address) (assetBalances : AssetBalances)
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  result.snd.storage managedAssets.slot = s.storage managedAssets.slot ∧
    ((s.storage managedAssets.slot).val ≤ (assetBalances vault).val →
      (result.snd.storage managedAssets.slot).val ≤ (assetBalances vault).val)

def erc4626_transferFrom_keeps_total_assets_and_backing
    (_fromAddr _toAddr : Address) (_amount : Uint256) (vault : Address)
    (assetBalances : AssetBalances) (s : ContractState) (result : ContractResult Bool) : Prop :=
  result.snd.storage managedAssets.slot = s.storage managedAssets.slot ∧
    ((s.storage managedAssets.slot).val ≤ (assetBalances vault).val →
      (result.snd.storage managedAssets.slot).val ≤ (assetBalances vault).val)

def erc4626_approve_keeps_total_assets_and_backing
    (_spender : Address) (_amount : Uint256) (vault : Address) (assetBalances : AssetBalances)
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  result.snd.storage managedAssets.slot = s.storage managedAssets.slot ∧
    ((s.storage managedAssets.slot).val ≤ (assetBalances vault).val →
      (result.snd.storage managedAssets.slot).val ≤ (assetBalances vault).val)

/-!
## 4. Exchange-Rate and No-Profit Specs

Properties specified:
- Successful vault actions cannot reduce the asset value of a fixed share
  position under the corresponding no-loss assumptions.
- Share-only actions leave `convertToAssets(shares)` unchanged.
- Deposit/redeem, mint/redeem, deposit/withdraw, and mint/withdraw round trips
  cannot increase caller asset-denominated wealth.

Security conclusions:
- In the simple no-fee, no-slashing model, the vault cannot create profit for a
  caller through a same-position round trip.
- Share transfers and approvals do not perturb the exchange rate.
- Any increase in backing from donation or yield distribution is handled in the
  closed-world model as external value entering the vault, not as profit created
  by a vault round trip.
-/

def erc4626_deposit_preserves_fixed_share_value
    (fixedShares assets : Uint256) (receiver : Address)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  erc4626_deposit_succeeds_when_accounting_does_not_overflow assets receiver s result →
    (fixedShareAssets fixedShares s).val ≤ (fixedShareAssets fixedShares result.snd).val

def erc4626_mint_preserves_fixed_share_value
    (fixedShares shares : Uint256) (receiver : Address)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  erc4626_mint_succeeds_when_accounting_does_not_overflow shares receiver s result →
    (fixedShareAssets fixedShares s).val ≤ (fixedShareAssets fixedShares result.snd).val

def erc4626_withdraw_preserves_fixed_share_value
    (fixedShares assets : Uint256) (receiver ownerAddr : Address)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  erc4626_withdraw_succeeds_when_accounting_and_allowance_are_enough assets receiver ownerAddr s result →
    (fixedShareAssets fixedShares s).val ≤ (fixedShareAssets fixedShares result.snd).val

def erc4626_redeem_preserves_fixed_share_value
    (fixedShares shares : Uint256) (receiver ownerAddr : Address)
    (s : ContractState) (result : ContractResult Uint256) : Prop :=
  erc4626_redeem_succeeds_when_accounting_and_allowance_are_enough shares receiver ownerAddr s result →
    (fixedShareAssets fixedShares s).val ≤ (fixedShareAssets fixedShares result.snd).val

def erc4626_transfer_keeps_convertToAssets
    (fixedShares : Uint256) (_toAddr : Address) (_amount : Uint256)
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  fixedShareAssets fixedShares result.snd = fixedShareAssets fixedShares s

def erc4626_transferFrom_keeps_convertToAssets
    (fixedShares : Uint256) (_fromAddr _toAddr : Address) (_amount : Uint256)
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  fixedShareAssets fixedShares result.snd = fixedShareAssets fixedShares s

def erc4626_approve_keeps_convertToAssets
    (fixedShares : Uint256) (_spender : Address) (_amount : Uint256)
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  fixedShareAssets fixedShares result.snd = fixedShareAssets fixedShares s

def erc4626_deposit_then_redeem_no_profit
    (beforeAssets beforeShares afterAssets afterShares : Uint256)
    (sBefore sAfter : ContractState) : Prop :=
  assetDenominatedWealth afterAssets afterShares sAfter ≤
    assetDenominatedWealth beforeAssets beforeShares sBefore

def erc4626_mint_then_redeem_no_profit
    (beforeAssets beforeShares afterAssets afterShares : Uint256)
    (sBefore sAfter : ContractState) : Prop :=
  assetDenominatedWealth afterAssets afterShares sAfter ≤
    assetDenominatedWealth beforeAssets beforeShares sBefore

def erc4626_deposit_then_withdraw_no_profit
    (beforeAssets beforeShares afterAssets afterShares : Uint256)
    (sBefore sAfter : ContractState) : Prop :=
  assetDenominatedWealth afterAssets afterShares sAfter ≤
    assetDenominatedWealth beforeAssets beforeShares sBefore

def erc4626_mint_then_withdraw_no_profit
    (beforeAssets beforeShares afterAssets afterShares : Uint256)
    (sBefore sAfter : ContractState) : Prop :=
  assetDenominatedWealth afterAssets afterShares sAfter ≤
    assetDenominatedWealth beforeAssets beforeShares sBefore

/-!
## 5. Closed-World Invariant Specs

Properties specified:
- These specs describe traces made only from successful vault calls
  (`approve`, share `transfer`, share `transferFrom`, `deposit`, `mint`,
  `withdraw`, and `redeem`) plus two explicit external asset inflows.
- `donate` is a direct ERC20 transfer to the vault. It increases raw vault
  backing, but it does not change managed `totalAssets`, share supply, or the
  exchange-rate floor used by these specs.
- `distributeYield` is recognized yield. It increases raw backing and managed
  `totalAssets` together, does not mint shares, and can only improve the
  fixed-share value floor.
- Every reachable state keeps share supply covered by managed assets and keeps
  managed assets covered by the vault's raw ERC20 backing.
- Every reachable state keeps the closed-world exchange-rate bounds:
  fixed-share asset value is at least identity, and asset-to-share conversion is
  at most identity.
- Along trace extensions, fixed-share value cannot decrease and unrecognized
  donation surplus cannot be removed by `withdraw` or `redeem`.
- The explicit first-depositor inflation sequence
  (attacker deposit, attacker donation, victim deposit, attacker redeem) cannot
  increase the closed-world caller wealth bound, and the donated surplus remains
  unrecognized.

Security conclusions:
- Direct asset donations cannot manipulate this vault's managed accounting or
  exchange rate. Donated assets become surplus backing until some separate
  yield-recognition action accounts for them.
- Recognized yield cannot dilute existing shares or make the vault under-backed;
  it is modeled as new backing plus the matching `totalAssets` increase.
- Within the successful-call, no-loss closed world, shares remain backed,
  conversion bounds do not move against fixed-share holders, and donation-based
  first-depositor inflation does not create extractable profit.
- These specs do not claim safety for losses, failed-call side effects,
  arbitrary external ERC20 behavior, strategy harvest timing, fees, or
  unmodeled actions outside the closed-world alphabet.
-/

def erc4626_closed_world_managed_assets_cover_share_supply
    (w : ClosedWorldState) : Prop :=
  ClosedWorldReachable w → w.tokenSupply ≤ w.managedAssets

def erc4626_closed_world_preserves_vault_asset_backing
    (w : ClosedWorldState) : Prop :=
  ClosedWorldReachable w → w.managedAssets ≤ w.vaultAssetBalance

def erc4626_closed_world_convertToAssets_at_least_identity
    (w : ClosedWorldState) : Prop :=
  ClosedWorldReachable w → 1 ≤ w.fixedShareValueFloor

def erc4626_closed_world_convertToShares_at_most_identity
    (w : ClosedWorldState) : Prop :=
  ClosedWorldReachable w → 1 ≤ w.fixedShareValueFloor

def erc4626_closed_world_fixed_share_value_never_decreases
    (before after : ClosedWorldState) : Prop :=
  ClosedWorldReachable before →
    ClosedWorldFollows before after →
      before.fixedShareValueFloor ≤ after.fixedShareValueFloor

def erc4626_closed_world_donation_keeps_managed_accounting_and_exchange_rate
    (before after : ClosedWorldState) (donor : Address) (amount : Nat) : Prop :=
  ClosedWorldReachable before →
    ClosedWorldStep (ClosedWorldAction.donate donor amount) before after →
      after.managedAssets = before.managedAssets ∧
      after.tokenSupply = before.tokenSupply ∧
      after.fixedShareValueFloor = before.fixedShareValueFloor

def erc4626_closed_world_yield_distribution_preserves_backing_and_supply
    (before after : ClosedWorldState) (source : Address) (amount : Nat) : Prop :=
  ClosedWorldReachable before →
    ClosedWorldStep (ClosedWorldAction.distributeYield source amount) before after →
      after.managedAssets ≤ after.vaultAssetBalance ∧
      after.tokenSupply = before.tokenSupply ∧
      before.fixedShareValueFloor ≤ after.fixedShareValueFloor

def erc4626_closed_world_caller_wealth_no_unearned_increase
    (before after : ClosedWorldState) : Prop :=
  ClosedWorldReachable before →
    ClosedWorldFollows before after →
      after.callerWealthBound ≤ before.callerWealthBound

def erc4626_closed_world_deposit_donate_victim_deposit_redeem_no_profit
    (attacker victim : Address) (attackerDeposit donation victimDeposit : Nat)
    (start afterAttackerDeposit afterDonation afterVictimDeposit afterRedeem : ClosedWorldState) : Prop :=
  ClosedWorldReachable start →
    ClosedWorldStep
        (ClosedWorldAction.deposit attacker attacker attackerDeposit)
        start afterAttackerDeposit →
      ClosedWorldStep
          (ClosedWorldAction.donate attacker donation)
          afterAttackerDeposit afterDonation →
        ClosedWorldStep
            (ClosedWorldAction.deposit victim victim victimDeposit)
            afterDonation afterVictimDeposit →
          ClosedWorldStep
              (ClosedWorldAction.redeem attacker attacker attacker attackerDeposit)
              afterVictimDeposit afterRedeem →
            afterRedeem.callerWealthBound ≤ start.callerWealthBound ∧
            afterRedeem.unrecognizedSurplus =
              afterAttackerDeposit.unrecognizedSurplus + donation

def erc4626_closed_world_donation_surplus_not_withdrawable_without_yield_recognition
    (before after : ClosedWorldState) : Prop :=
  ClosedWorldReachable before →
    ClosedWorldFollows before after →
      before.unrecognizedSurplus ≤ after.unrecognizedSurplus

end Tamago.Spec.Tokens.ERC4626Spec
