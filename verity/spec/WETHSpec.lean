import src.WETH

namespace spec.WETHSpec

open Verity
open Verity.EVM.Uint256

def weth_totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 0

def weth_balanceOf_spec (account : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap 1 account

def weth_allowance_spec (ownerAddr spender : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap2 2 ownerAddr spender

def weth_approve_effect (spender : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap2 2 s.sender spender = amount ∧
  s'.storageMap = s.storageMap ∧
  s'.storage 0 = s.storage 0

def weth_deposit_effect (s s' : ContractState) : Prop :=
  (s.storageMap 1 s.sender).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
  (s.storage 0).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    s'.storageMap 1 s.sender = (s.storageMap 1 s.sender) + s.msgValue ∧
    s'.storage 0 = (s.storage 0) + s.msgValue

def weth_transfer_total_supply_preserved (s s' : ContractState) : Prop :=
  s'.storage 0 = s.storage 0

def weth_withdraw_effect (amount : Uint256) (s s' : ContractState) : Prop :=
  amount.val ≤ (s.storageMap 1 s.sender).val →
  amount.val ≤ (s.storage 0).val →
    s'.storageMap 1 s.sender = Verity.EVM.Uint256.sub (s.storageMap 1 s.sender) amount ∧
    s'.storage 0 = Verity.EVM.Uint256.sub (s.storage 0) amount

def weth_withdraw_insufficient_no_change (amount : Uint256) (s s' : ContractState) : Prop :=
  amount.val > (s.storageMap 1 s.sender).val →
    s'.storageMap 1 s.sender = s.storageMap 1 s.sender ∧
    s'.storage 0 = s.storage 0

end spec.WETHSpec
