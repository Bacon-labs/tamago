import Tamago.Tokens.ERC20
import Tamago.Spec.Auth.OwnableSpec

namespace Tamago.Spec.Tokens.ERC20Spec

open Verity
open Verity.EVM.Uint256
open Tamago.Tokens.ERC20
open Tamago.Spec.Auth.OwnableSpec

/-
ERC20 specs are grouped by public function. Each mutating function is expressed
as a set of small first-principles properties.
-/

/-
Basic ERC20 views

Properties specified:
- decimals() returns the value recorded in the contract's immutable storage at
  construction, exposing the deployer-chosen precision.
- totalSupply(), balanceOf(account), and allowance(owner, spender) return the
  values from their storage locations.
- owner() delegates to the shared Ownable owner spec.

Security conclusions:
- Balance, allowance, supply, owner, and decimals getters expose the state used
  by mutating functions and by integrators that need to interpret the unit
  scale.
- Later safety properties are about the same state users can inspect publicly.
-/
def erc20_decimals_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage tokenDecimals.slot

def erc20_totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage tokenSupply.slot

def erc20_balanceOf_spec (account : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap balances.slot account

def erc20_allowance_spec (ownerAddr spender : Address) (result : Uint256) (s : ContractState) : Prop :=
  result = s.storageMap2 allowances.slot ownerAddr spender

def erc20_owner_spec (result : Address) (s : ContractState) : Prop :=
  ownable_owner_spec result s

/-
Ownable entry points

Properties specified:
- transferOwnership(newOwner) and renounceOwnership() reuse the Ownable specs.

Security conclusions:
- Mint and burn authority follows the shared Ownable authorization model.
- Ownership changes cannot bypass the standalone Ownable invariants.
-/
def erc20_transferOwnership_reverts_for_non_owner
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_reverts_for_non_owner newOwner s result

def erc20_transferOwnership_reverts_for_zero_owner
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_reverts_for_zero_owner newOwner s result

def erc20_transferOwnership_succeeds_for_owner_to_nonzero
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_succeeds_for_owner_to_nonzero newOwner s result

def erc20_transferOwnership_sets_new_owner
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_sets_new_owner newOwner s result

def erc20_transferOwnership_keeps_other_owner_slots
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_keeps_other_owner_slots newOwner s result

def erc20_transferOwnership_keeps_uint_storage
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_keeps_uint_storage newOwner s result

def erc20_transferOwnership_keeps_balances_and_allowances
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_keeps_balances_and_allowances newOwner s result

def erc20_transferOwnership_keeps_array_storage
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_keeps_array_storage newOwner s result

def erc20_renounceOwnership_reverts_for_non_owner
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_reverts_for_non_owner s result

def erc20_renounceOwnership_succeeds_for_owner
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_succeeds_for_owner s result

def erc20_renounceOwnership_clears_owner
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_clears_owner s result

def erc20_renounceOwnership_keeps_other_owner_slots
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_keeps_other_owner_slots s result

def erc20_renounceOwnership_keeps_uint_storage
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_keeps_uint_storage s result

def erc20_renounceOwnership_keeps_balances_and_allowances
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_keeps_balances_and_allowances s result

def erc20_renounceOwnership_keeps_array_storage
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_keeps_array_storage s result

/-
approve(spender, amount)

Properties specified:
- Approval always succeeds.
- The caller's allowance for the spender is set to exactly `amount`.
- Balances and total supply are unchanged.

Security conclusions:
- Approval changes spending permission only.
- Approving cannot mint, burn, or move tokens.
- Approving cannot change total supply.
-/
def erc20_approve_succeeds
    (_spender : Address) (_amount : Uint256) (_s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result = ContractResult.success true result.snd

def erc20_approve_sets_allowance
    (spender : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storageMap2 allowances.slot s.sender spender = amount

def erc20_approve_keeps_balances
    (_spender : Address) (_amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storageMap = s.storageMap

def erc20_approve_keeps_total_supply
    (_spender : Address) (_amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storage tokenSupply.slot = s.storage tokenSupply.slot

/-
transfer(to, amount)

Properties specified:
- The call reverts if the sender lacks `amount`.
- A self-transfer succeeds without changing balances.
- A transfer to another account reverts if the recipient balance would overflow.
- Otherwise, `amount` is debited from the sender and credited to the recipient.
- Total supply is unchanged for every path.

Security conclusions:
- Tokens can move only from spendable sender balance to recipient balance.
- Recipient balance overflow is rejected instead of wrapping.
- transfer() cannot create or destroy supply.
-/
def erc20_transfer_reverts_when_balance_is_low
    (_toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val > (s.storageMap balances.slot s.sender).val →
    result = ContractResult.revert "Insufficient balance" s

def erc20_transfer_to_self_keeps_balances
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap balances.slot s.sender).val →
    s.sender = toAddr →
      result = ContractResult.success true result.snd ∧
      result.snd.storageMap = s.storageMap

def erc20_transfer_reverts_when_recipient_balance_would_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap balances.slot s.sender).val →
    s.sender ≠ toAddr →
      (s.storageMap balances.slot toAddr).val + amount.val > Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.revert "Recipient balance overflow" s

def erc20_transfer_moves_tokens_between_distinct_accounts
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap balances.slot s.sender).val →
    s.sender ≠ toAddr →
      (s.storageMap balances.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.success true result.snd ∧
        result.snd.storageMap balances.slot s.sender =
          (s.storageMap balances.slot s.sender) - amount ∧
        result.snd.storageMap balances.slot toAddr =
          (s.storageMap balances.slot toAddr) + amount

def erc20_transfer_keeps_total_supply
    (_toAddr : Address) (_amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storage tokenSupply.slot = s.storage tokenSupply.slot

/-
transferFrom(from, to, amount)

Properties specified:
- The call reverts when allowance or source balance is too low.
- Self-transfers preserve balances.
- Distinct-account transfers move exactly `amount` without overflowing the
  recipient.
- Total supply is unchanged.
- Infinite allowance is preserved; finite allowance is reduced by `amount`.

Security conclusions:
- Delegated transfers cannot exceed allowance or source balance.
- Recipient balance overflow is rejected instead of wrapping.
- Infinite and finite allowances follow distinct, explicit spending rules.
- transferFrom() cannot create or destroy supply.
-/
def erc20_transferFrom_reverts_when_allowance_is_low
    (fromAddr : Address) (_toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val > (s.storageMap2 allowances.slot fromAddr s.sender).val →
    result = ContractResult.revert "Insufficient allowance" s

def erc20_transferFrom_reverts_when_balance_is_low
    (fromAddr : Address) (_toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap2 allowances.slot fromAddr s.sender).val →
    amount.val > (s.storageMap balances.slot fromAddr).val →
      result = ContractResult.revert "Insufficient balance" s

def erc20_transferFrom_reverts_when_recipient_balance_would_overflow
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap2 allowances.slot fromAddr s.sender).val →
    amount.val ≤ (s.storageMap balances.slot fromAddr).val →
      fromAddr ≠ toAddr →
        (s.storageMap balances.slot toAddr).val + amount.val > Verity.Stdlib.Math.MAX_UINT256 →
          result = ContractResult.revert "Recipient balance overflow" s

def erc20_transferFrom_to_self_keeps_balances
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap2 allowances.slot fromAddr s.sender).val →
    amount.val ≤ (s.storageMap balances.slot fromAddr).val →
      fromAddr = toAddr →
        result = ContractResult.success true result.snd ∧
        result.snd.storageMap = s.storageMap

def erc20_transferFrom_moves_tokens_between_distinct_accounts
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap2 allowances.slot fromAddr s.sender).val →
    amount.val ≤ (s.storageMap balances.slot fromAddr).val →
      fromAddr ≠ toAddr →
        (s.storageMap balances.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
          result = ContractResult.success true result.snd ∧
          result.snd.storageMap balances.slot fromAddr =
            (s.storageMap balances.slot fromAddr) - amount ∧
          result.snd.storageMap balances.slot toAddr =
            (s.storageMap balances.slot toAddr) + amount

def erc20_transferFrom_keeps_total_supply
    (_fromAddr _toAddr : Address) (_amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storage tokenSupply.slot = s.storage tokenSupply.slot

def erc20_transferFrom_keeps_infinite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap2 allowances.slot fromAddr s.sender).val →
    amount.val ≤ (s.storageMap balances.slot fromAddr).val →
      (fromAddr = toAddr ∨
        (fromAddr ≠ toAddr ∧
          (s.storageMap balances.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256)) →
        s.storageMap2 allowances.slot fromAddr s.sender = maxUint256 →
          result.snd.storageMap2 allowances.slot fromAddr s.sender =
            s.storageMap2 allowances.slot fromAddr s.sender

def erc20_transferFrom_spends_finite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap2 allowances.slot fromAddr s.sender).val →
    amount.val ≤ (s.storageMap balances.slot fromAddr).val →
      (fromAddr = toAddr ∨
        (fromAddr ≠ toAddr ∧
          (s.storageMap balances.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256)) →
        s.storageMap2 allowances.slot fromAddr s.sender ≠ maxUint256 →
          result.snd.storageMap2 allowances.slot fromAddr s.sender =
            Verity.EVM.Uint256.sub (s.storageMap2 allowances.slot fromAddr s.sender) amount

/-
mint(to, amount)

Properties specified:
- A non-owner cannot mint.
- Minting reverts if the recipient balance or total supply would overflow.
- A valid owner mint succeeds.
- The recipient balance and total supply each increase by `amount`.
- The owner slot is unchanged.

Security conclusions:
- New supply can be created only by the owner.
- Minting cannot overflow recipient balance or total supply accounting.
- Minting does not change ownership authority.
-/
def erc20_mint_reverts_for_non_owner
    (_toAddr : Address) (_amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  s.sender ≠ s.storageAddr contractOwner.slot →
    result = ContractResult.revert "Caller is not the owner" s

def erc20_mint_reverts_when_recipient_balance_would_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    (s.storageMap balances.slot toAddr).val + amount.val > Verity.Stdlib.Math.MAX_UINT256 →
      result = ContractResult.revert "Balance overflow" s

def erc20_mint_reverts_when_total_supply_would_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    (s.storageMap balances.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage tokenSupply.slot).val + amount.val > Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.revert "Supply overflow" s

def erc20_mint_succeeds_when_owner_and_no_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    (s.storageMap balances.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage tokenSupply.slot).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result = ContractResult.success true result.snd

def erc20_mint_credits_recipient
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    (s.storageMap balances.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage tokenSupply.slot).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result.snd.storageMap balances.slot toAddr =
          (s.storageMap balances.slot toAddr) + amount

def erc20_mint_increases_total_supply
    (toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    (s.storageMap balances.slot toAddr).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      (s.storage tokenSupply.slot).val + amount.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
        result.snd.storage tokenSupply.slot =
          (s.storage tokenSupply.slot) + amount

def erc20_mint_keeps_owner
    (_toAddr : Address) (_amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storageAddr contractOwner.slot = s.storageAddr contractOwner.slot

/-
burn(from, amount)

Properties specified:
- A non-owner cannot burn.
- Burning reverts if the account balance or total supply is too low.
- A valid owner burn succeeds.
- The account balance and total supply each decrease by `amount`.

Security conclusions:
- Supply can be destroyed only by the owner.
- Burning cannot underflow account balance or total supply accounting.
- Successful burns keep account balance and total supply synchronized.
-/
def erc20_burn_reverts_for_non_owner
    (_fromAddr : Address) (_amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  s.sender ≠ s.storageAddr contractOwner.slot →
    result = ContractResult.revert "Caller is not the owner" s

def erc20_burn_reverts_when_balance_is_low
    (fromAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    amount.val > (s.storageMap balances.slot fromAddr).val →
      result = ContractResult.revert "Insufficient balance" s

def erc20_burn_reverts_when_total_supply_is_low
    (fromAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    amount.val ≤ (s.storageMap balances.slot fromAddr).val →
      amount.val > (s.storage tokenSupply.slot).val →
        result = ContractResult.revert "Insufficient supply" s

def erc20_burn_succeeds_when_owner_has_balance_and_supply
    (fromAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    amount.val ≤ (s.storageMap balances.slot fromAddr).val →
      amount.val ≤ (s.storage tokenSupply.slot).val →
        result = ContractResult.success true result.snd

def erc20_burn_debits_account
    (fromAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    amount.val ≤ (s.storageMap balances.slot fromAddr).val →
      amount.val ≤ (s.storage tokenSupply.slot).val →
        result.snd.storageMap balances.slot fromAddr =
          Verity.EVM.Uint256.sub (s.storageMap balances.slot fromAddr) amount

def erc20_burn_decreases_total_supply
    (fromAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    amount.val ≤ (s.storageMap balances.slot fromAddr).val →
      amount.val ≤ (s.storage tokenSupply.slot).val →
        result.snd.storage tokenSupply.slot =
          Verity.EVM.Uint256.sub (s.storage tokenSupply.slot) amount

end Tamago.Spec.Tokens.ERC20Spec
