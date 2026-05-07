import src.tokens.ERC4626
import spec.tokens.ERC20Spec

namespace spec.tokens.ERC4626Spec

open Verity
open Verity.EVM.Uint256
open src.ERC4626
open spec.tokens.ERC20Spec

def erc4626_decimals_spec (result : Uint256) : Prop :=
  erc20_decimals_spec result

def erc4626_totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  erc20_totalSupply_spec result s

def erc4626_balanceOf_spec (account : Address) (result : Uint256) (s : ContractState) : Prop :=
  erc20_balanceOf_spec account result s

def erc4626_allowance_spec (ownerAddr spender : Address) (result : Uint256) (s : ContractState) : Prop :=
  erc20_allowance_spec ownerAddr spender result s

def erc4626_approve_effect
    (spender : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_approve_effect spender amount s result

def erc4626_transfer_balances_effect
    (toAddr : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_transfer_balances_effect toAddr amount s result

def erc4626_transferFrom_effect
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_effect fromAddr toAddr amount s result

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

def erc4626_deposit_effect
    (assets : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let shares :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul assets (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1))
      (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1)
  ((s.storageMap balances.slot receiver).val + shares.val > Verity.Stdlib.Math.MAX_UINT256 →
    result = ContractResult.revert "Balance overflow" s) ∧
  ((s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    ((s.storage tokenSupply.slot).val + shares.val > Verity.Stdlib.Math.MAX_UINT256 →
      result = ContractResult.revert "Supply overflow" s) ∧
    ((s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      ((s.storage managedAssets.slot).val + assets.val > Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.revert "Total assets overflow" s) ∧
      ((s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.success shares result.snd ∧
        result.snd.storageMap balances.slot receiver =
          (s.storageMap balances.slot receiver) + shares ∧
        result.snd.storage tokenSupply.slot =
          (s.storage tokenSupply.slot) + shares ∧
        result.snd.storage managedAssets.slot =
          (s.storage managedAssets.slot) + assets ∧
        result.snd.storageAddr assetToken.slot = s.storageAddr assetToken.slot)))

def erc4626_mint_effect
    (shares : Uint256) (receiver : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let denominator := Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1
  let assets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.add
        (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
        (Verity.EVM.Uint256.sub denominator 1))
      denominator
  ((s.storageMap balances.slot receiver).val + shares.val > Verity.Stdlib.Math.MAX_UINT256 →
    result = ContractResult.revert "Balance overflow" s) ∧
  ((s.storageMap balances.slot receiver).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    ((s.storage tokenSupply.slot).val + shares.val > Verity.Stdlib.Math.MAX_UINT256 →
      result = ContractResult.revert "Supply overflow" s) ∧
    ((s.storage tokenSupply.slot).val + shares.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      ((s.storage managedAssets.slot).val + assets.val > Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.revert "Total assets overflow" s) ∧
      ((s.storage managedAssets.slot).val + assets.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.success assets result.snd ∧
        result.snd.storageMap balances.slot receiver =
          (s.storageMap balances.slot receiver) + shares ∧
        result.snd.storage tokenSupply.slot =
          (s.storage tokenSupply.slot) + shares ∧
        result.snd.storage managedAssets.slot =
          (s.storage managedAssets.slot) + assets ∧
        result.snd.storageAddr assetToken.slot = s.storageAddr assetToken.slot)))

def erc4626_withdraw_effect
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
  (assets.val > maxAssets.val →
    result = ContractResult.revert "Withdraw more than max" s) ∧
  (assets.val ≤ maxAssets.val →
    (s.sender ≠ ownerAddr →
      shares.val > (s.storageMap2 allowances.slot ownerAddr s.sender).val →
        result = ContractResult.revert "Insufficient allowance" s) ∧
    ((s.sender = ownerAddr ∨
        shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
      (shares.val > (s.storageMap balances.slot ownerAddr).val →
        result = ContractResult.revert "Insufficient balance" s) ∧
      (shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
        (shares.val > (s.storage tokenSupply.slot).val →
          result = ContractResult.revert "Insufficient supply" s) ∧
        (shares.val ≤ (s.storage tokenSupply.slot).val →
          (assets.val > (s.storage managedAssets.slot).val →
            result = ContractResult.revert "Insufficient assets" s) ∧
          (assets.val ≤ (s.storage managedAssets.slot).val →
            result = ContractResult.success shares result.snd ∧
            result.snd.storageMap balances.slot ownerAddr =
              Verity.EVM.Uint256.sub (s.storageMap balances.slot ownerAddr) shares ∧
            result.snd.storage tokenSupply.slot =
              Verity.EVM.Uint256.sub (s.storage tokenSupply.slot) shares ∧
            result.snd.storage managedAssets.slot =
              Verity.EVM.Uint256.sub (s.storage managedAssets.slot) assets ∧
            ((s.sender = ownerAddr ∨
                s.storageMap2 allowances.slot ownerAddr s.sender = maxUint256) →
              result.snd.storageMap2 allowances.slot ownerAddr s.sender =
                s.storageMap2 allowances.slot ownerAddr s.sender) ∧
            (s.sender ≠ ownerAddr →
              s.storageMap2 allowances.slot ownerAddr s.sender ≠ maxUint256 →
                result.snd.storageMap2 allowances.slot ownerAddr s.sender =
                  Verity.EVM.Uint256.sub
                    (s.storageMap2 allowances.slot ownerAddr s.sender) shares))))))

def erc4626_redeem_effect
    (shares : Uint256) (_receiver ownerAddr : Address) (s : ContractState)
    (result : ContractResult Uint256) : Prop :=
  let assets :=
    Verity.EVM.Uint256.div
      (Verity.EVM.Uint256.mul shares (Verity.EVM.Uint256.add (s.storage managedAssets.slot) 1))
      (Verity.EVM.Uint256.add (s.storage tokenSupply.slot) 1)
  (shares.val > (s.storageMap balances.slot ownerAddr).val →
    result = ContractResult.revert "Redeem more than max" s) ∧
  (shares.val ≤ (s.storageMap balances.slot ownerAddr).val →
    (s.sender ≠ ownerAddr →
      shares.val > (s.storageMap2 allowances.slot ownerAddr s.sender).val →
        result = ContractResult.revert "Insufficient allowance" s) ∧
    ((s.sender = ownerAddr ∨
        shares.val ≤ (s.storageMap2 allowances.slot ownerAddr s.sender).val) →
      (shares.val > (s.storage tokenSupply.slot).val →
        result = ContractResult.revert "Insufficient supply" s) ∧
      (shares.val ≤ (s.storage tokenSupply.slot).val →
        (assets.val > (s.storage managedAssets.slot).val →
          result = ContractResult.revert "Insufficient assets" s) ∧
        (assets.val ≤ (s.storage managedAssets.slot).val →
          result = ContractResult.success assets result.snd ∧
          result.snd.storageMap balances.slot ownerAddr =
            Verity.EVM.Uint256.sub (s.storageMap balances.slot ownerAddr) shares ∧
          result.snd.storage tokenSupply.slot =
            Verity.EVM.Uint256.sub (s.storage tokenSupply.slot) shares ∧
          result.snd.storage managedAssets.slot =
            Verity.EVM.Uint256.sub (s.storage managedAssets.slot) assets ∧
          ((s.sender = ownerAddr ∨
              s.storageMap2 allowances.slot ownerAddr s.sender = maxUint256) →
            result.snd.storageMap2 allowances.slot ownerAddr s.sender =
              s.storageMap2 allowances.slot ownerAddr s.sender) ∧
          (s.sender ≠ ownerAddr →
            s.storageMap2 allowances.slot ownerAddr s.sender ≠ maxUint256 →
              result.snd.storageMap2 allowances.slot ownerAddr s.sender =
                Verity.EVM.Uint256.sub
                  (s.storageMap2 allowances.slot ownerAddr s.sender) shares)))))

end spec.tokens.ERC4626Spec
