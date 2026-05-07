import src.tokens.WETH
import spec.tokens.ERC20Spec

namespace spec.tokens.WETHSpec

open Verity
open Verity.EVM.Uint256
open Contracts
open src.WETH
open spec.tokens.ERC20Spec

def weth_decimals_spec (result : Uint256) : Prop :=
  erc20_decimals_spec result

def weth_totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  erc20_totalSupply_spec result s

def weth_balanceOf_spec (account : Address) (result : Uint256) (s : ContractState) : Prop :=
  erc20_balanceOf_spec account result s

def weth_allowance_spec (ownerAddr spender : Address) (result : Uint256) (s : ContractState) : Prop :=
  erc20_allowance_spec ownerAddr spender result s

def weth_approve_effect
    (spender : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_approve_effect spender amount s result

def weth_deposit_effect (s : ContractState) (result : ContractResult Bool) : Prop :=
  ((s.storageMap balances.slot s.sender).val + s.msgValue.val > Verity.Stdlib.Math.MAX_UINT256 →
    result = ContractResult.revert "Balance overflow" s) ∧
  ((s.storageMap balances.slot s.sender).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    ((s.storage tokenSupply.slot).val + s.msgValue.val > Verity.Stdlib.Math.MAX_UINT256 →
      result = ContractResult.revert "Supply overflow" s) ∧
    ((s.storage tokenSupply.slot).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      result = ContractResult.success true result.snd ∧
      result.snd.storageMap balances.slot s.sender =
        (s.storageMap balances.slot s.sender) + s.msgValue ∧
      result.snd.storage tokenSupply.slot =
        (s.storage tokenSupply.slot) + s.msgValue))

def weth_transfer_balances_effect
    (toAddr : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_transfer_balances_effect toAddr amount s result

def weth_transferFrom_effect
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_effect fromAddr toAddr amount s result

def weth_withdraw_effect
    (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  (amount.val > (s.storageMap balances.slot s.sender).val →
    result = ContractResult.revert "Insufficient balance" s) ∧
  (amount.val ≤ (s.storageMap balances.slot s.sender).val →
    (amount.val > (s.storage tokenSupply.slot).val →
      result = ContractResult.revert "Insufficient supply" s) ∧
    (amount.val ≤ (s.storage tokenSupply.slot).val →
      result = ContractResult.success true result.snd ∧
      result.snd.storageMap balances.slot s.sender =
        Verity.EVM.Uint256.sub (s.storageMap balances.slot s.sender) amount ∧
      result.snd.storage tokenSupply.slot =
        Verity.EVM.Uint256.sub (s.storage tokenSupply.slot) amount))

end spec.tokens.WETHSpec
