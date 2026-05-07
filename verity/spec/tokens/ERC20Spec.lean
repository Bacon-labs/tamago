import src.tokens.ERC20
import spec.auth.OwnableSpec

namespace spec.tokens.ERC20Spec

open Verity
open Verity.EVM.Uint256
open src.tokens.ERC20
open spec.auth.OwnableSpec

def erc20_decimals_spec (result : Uint256) : Prop :=
  result = 18

def erc20_totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage tokenSupply.slot

def erc20_balanceOf_spec (account : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap balances.slot account

def erc20_allowance_spec (ownerAddr spender : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap2 allowances.slot ownerAddr spender

def erc20_owner_spec (result : Address) (s : ContractState) : Prop :=
  ownable_owner_spec result s

def erc20_transferOwnership_effect
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_effect newOwner s result

def erc20_renounceOwnership_effect
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_effect s result

def erc20_approve_effect
    (spender : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  result = ContractResult.success true result.snd ∧
  result.snd.storageMap2 allowances.slot s.sender spender = amount ∧
  result.snd.storageMap = s.storageMap ∧
  result.snd.storage tokenSupply.slot = s.storage tokenSupply.slot

def erc20_transfer_balances_effect
    (toAddr : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  (amount.val > (s.storageMap balances.slot s.sender).val →
    result = ContractResult.revert "Insufficient balance" s) ∧
  (amount.val ≤ (s.storageMap balances.slot s.sender).val →
    (s.sender = toAddr →
      result = ContractResult.success true result.snd ∧
      result.snd.storageMap = s.storageMap ∧
      result.snd.storage tokenSupply.slot = s.storage tokenSupply.slot) ∧
    (s.sender ≠ toAddr →
      ((s.storageMap balances.slot toAddr).val + amount.val > Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.revert "Recipient balance overflow" s) ∧
      ((s.storageMap balances.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.success true result.snd ∧
        result.snd.storageMap balances.slot s.sender =
          (s.storageMap balances.slot s.sender) - amount ∧
        result.snd.storageMap balances.slot toAddr =
          (s.storageMap balances.slot toAddr) + amount ∧
        result.snd.storage tokenSupply.slot = s.storage tokenSupply.slot)))

def erc20_transferFrom_effect
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  (amount.val > (s.storageMap2 allowances.slot fromAddr s.sender).val →
    result = ContractResult.revert "Insufficient allowance" s) ∧
  (amount.val ≤ (s.storageMap2 allowances.slot fromAddr s.sender).val →
    (amount.val > (s.storageMap balances.slot fromAddr).val →
      result = ContractResult.revert "Insufficient balance" s) ∧
    (amount.val ≤ (s.storageMap balances.slot fromAddr).val →
      (fromAddr ≠ toAddr →
        ((s.storageMap balances.slot toAddr).val + amount.val > Verity.Stdlib.Math.MAX_UINT256 →
          result = ContractResult.revert "Recipient balance overflow" s) ∧
        ((s.storageMap balances.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
          result = ContractResult.success true result.snd ∧
          result.snd.storageMap balances.slot fromAddr =
            (s.storageMap balances.slot fromAddr) - amount ∧
          result.snd.storageMap balances.slot toAddr =
            (s.storageMap balances.slot toAddr) + amount ∧
          result.snd.storage tokenSupply.slot = s.storage tokenSupply.slot)) ∧
      (fromAddr = toAddr →
        result = ContractResult.success true result.snd ∧
        result.snd.storageMap = s.storageMap ∧
        result.snd.storage tokenSupply.slot = s.storage tokenSupply.slot) ∧
      ((fromAddr = toAddr ∨
          (s.storageMap balances.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256) →
        (s.storageMap2 allowances.slot fromAddr s.sender =
            maxUint256) →
          result.snd.storageMap2 allowances.slot fromAddr s.sender =
            s.storageMap2 allowances.slot fromAddr s.sender) ∧
      ((fromAddr = toAddr ∨
          (s.storageMap balances.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256) →
        (s.storageMap2 allowances.slot fromAddr s.sender ≠
            maxUint256) →
          result.snd.storageMap2 allowances.slot fromAddr s.sender =
            Verity.EVM.Uint256.sub (s.storageMap2 allowances.slot fromAddr s.sender) amount)))

def erc20_mint_effect
    (toAddr : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  (s.sender ≠ s.storageAddr contractOwner.slot →
    result = ContractResult.revert "Caller is not the owner" s) ∧
  (s.sender = s.storageAddr contractOwner.slot →
    ((s.storageMap balances.slot toAddr).val + amount.val > Verity.Stdlib.Math.MAX_UINT256 →
      result = ContractResult.revert "Balance overflow" s) ∧
    ((s.storageMap balances.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      ((s.storage tokenSupply.slot).val + amount.val > Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.revert "Supply overflow" s) ∧
      ((s.storage tokenSupply.slot).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.success true result.snd ∧
        result.snd.storageMap balances.slot toAddr =
          (s.storageMap balances.slot toAddr) + amount ∧
        result.snd.storage tokenSupply.slot =
          (s.storage tokenSupply.slot) + amount ∧
        result.snd.storageAddr contractOwner.slot = s.storageAddr contractOwner.slot)))

def erc20_burn_effect
    (fromAddr : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  (s.sender ≠ s.storageAddr contractOwner.slot →
    result = ContractResult.revert "Caller is not the owner" s) ∧
  (s.sender = s.storageAddr contractOwner.slot →
    (amount.val > (s.storageMap balances.slot fromAddr).val →
      result = ContractResult.revert "Insufficient balance" s) ∧
    (amount.val ≤ (s.storageMap balances.slot fromAddr).val →
      (amount.val > (s.storage tokenSupply.slot).val →
        result = ContractResult.revert "Insufficient supply" s) ∧
      (amount.val ≤ (s.storage tokenSupply.slot).val →
        result = ContractResult.success true result.snd ∧
        result.snd.storageMap balances.slot fromAddr =
          Verity.EVM.Uint256.sub (s.storageMap balances.slot fromAddr) amount ∧
        result.snd.storage tokenSupply.slot =
          Verity.EVM.Uint256.sub (s.storage tokenSupply.slot) amount)))

end spec.tokens.ERC20Spec
