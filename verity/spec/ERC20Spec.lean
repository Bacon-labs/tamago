import src.ERC20

namespace spec.ERC20Spec

open Verity
open Verity.EVM.Uint256

def erc20_decimals_spec (result : Uint256) : Prop :=
  result = 18

def erc20_totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 1

def erc20_balanceOf_spec (account : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap 2 account

def erc20_allowance_spec (ownerAddr spender : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap2 3 ownerAddr spender

def erc20_owner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr 0

def erc20_approve_effect (spender : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  s'.storageMap2 3 s.sender spender = amount ∧
  s'.storageMap = s.storageMap ∧
  s'.storage 1 = s.storage 1

def erc20_transfer_total_supply_preserved (s s' : ContractState) : Prop :=
  s'.storage 1 = s.storage 1

def erc20_transfer_balances_effect
    (toAddr : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  amount.val ≤ (s.storageMap 2 s.sender).val →
    (s.sender = toAddr →
      s'.storageMap = s.storageMap) ∧
    (s.sender ≠ toAddr →
      (s.storageMap 2 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        s'.storageMap 2 s.sender = (s.storageMap 2 s.sender) - amount ∧
        s'.storageMap 2 toAddr = (s.storageMap 2 toAddr) + amount)

def erc20_transferFrom_total_supply_preserved (s s' : ContractState) : Prop :=
  s'.storage 1 = s.storage 1

def erc20_transferFrom_allowance_effect
    (fromAddr toAddr : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  amount.val ≤ (s.storageMap2 3 fromAddr s.sender).val →
    amount.val ≤ (s.storageMap 2 fromAddr).val →
    (fromAddr ≠ toAddr →
      (s.storageMap 2 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256) →
    ((s.storageMap2 3 fromAddr s.sender =
        115792089237316195423570985008687907853269984665640564039457584007913129639935) →
      s'.storageMap2 3 fromAddr s.sender = s.storageMap2 3 fromAddr s.sender) ∧
    ((s.storageMap2 3 fromAddr s.sender ≠
        115792089237316195423570985008687907853269984665640564039457584007913129639935) →
      s'.storageMap2 3 fromAddr s.sender =
        Verity.EVM.Uint256.sub (s.storageMap2 3 fromAddr s.sender) amount)

def erc20_mint_effect (toAddr : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  s.sender = s.storageAddr 0 →
    (s.storageMap 2 toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage 1).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      s'.storageMap 2 toAddr = (s.storageMap 2 toAddr) + amount ∧
      s'.storage 1 = (s.storage 1) + amount ∧
      s'.storageAddr 0 = s.storageAddr 0

def erc20_mint_unauthorized_no_change
    (toAddr : Address) (_amount : Uint256) (s s' : ContractState) : Prop :=
  s.sender ≠ s.storageAddr 0 →
    s'.storage 1 = s.storage 1 ∧
    s'.storageMap 2 toAddr = s.storageMap 2 toAddr

def erc20_burn_effect (fromAddr : Address) (amount : Uint256) (s s' : ContractState) : Prop :=
  s.sender = s.storageAddr 0 →
    amount.val ≤ (s.storageMap 2 fromAddr).val →
    amount.val ≤ (s.storage 1).val →
      s'.storageMap 2 fromAddr = Verity.EVM.Uint256.sub (s.storageMap 2 fromAddr) amount ∧
      s'.storage 1 = Verity.EVM.Uint256.sub (s.storage 1) amount

def erc20_burn_unauthorized_no_change
    (fromAddr : Address) (_amount : Uint256) (s s' : ContractState) : Prop :=
  s.sender ≠ s.storageAddr 0 →
    s'.storage 1 = s.storage 1 ∧
    s'.storageMap 2 fromAddr = s.storageMap 2 fromAddr

end spec.ERC20Spec
