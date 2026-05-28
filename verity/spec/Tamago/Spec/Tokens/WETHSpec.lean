import Tamago.Tokens.WETH
import Tamago.Spec.Tokens.ERC20Spec

namespace Tamago.Spec.Tokens.WETHSpec

open Verity
open Verity.EVM.Uint256
open Contracts
open Tamago.Tokens.WETH
open Tamago.Spec.Tokens.ERC20Spec

/-
WETH specs reuse ERC20 accounting where the wrapped token behaves exactly like
an ERC20, then add first-principles properties for wrapping and unwrapping ETH.
-/

/-
ERC20-compatible behavior

Properties specified:
- decimals(), totalSupply(), balanceOf(), allowance(), and approve() satisfy the
  same properties as ERC20.
- transfer() and transferFrom() reuse the ERC20 movement and allowance specs.

Security conclusions:
- Wrapped ETH exposes ERC20-compatible balance, allowance, and supply state.
- Approval behavior cannot alter wrapped token balances or supply.
- Wrapped ETH movement inherits ERC20 balance and allowance safety.
- Transfers cannot create or destroy wrapped supply.
-/
def weth_decimals_spec (result : Uint256) : Prop :=
  result = 18

def weth_totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  erc20_totalSupply_spec result s

def weth_balanceOf_spec (account : Address) (result : Uint256) (s : ContractState) : Prop :=
  erc20_balanceOf_spec account result s

def weth_allowance_spec (ownerAddr spender : Address) (result : Uint256) (s : ContractState) : Prop :=
  erc20_allowance_spec ownerAddr spender result s

def weth_approve_succeeds
    (spender : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_approve_succeeds spender amount s result

def weth_approve_sets_allowance
    (spender : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_approve_sets_allowance spender amount s result

def weth_approve_keeps_balances
    (spender : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_approve_keeps_balances spender amount s result

def weth_approve_keeps_total_supply
    (spender : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_approve_keeps_total_supply spender amount s result

def weth_transfer_reverts_when_balance_is_low
    (toAddr : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_transfer_reverts_when_balance_is_low toAddr amount s result

def weth_transfer_to_self_keeps_balances
    (toAddr : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_transfer_to_self_keeps_balances toAddr amount s result

def weth_transfer_reverts_when_recipient_balance_would_overflow
    (toAddr : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_transfer_reverts_when_recipient_balance_would_overflow toAddr amount s result

def weth_transfer_moves_tokens_between_distinct_accounts
    (toAddr : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_transfer_moves_tokens_between_distinct_accounts toAddr amount s result

def weth_transfer_keeps_total_supply
    (toAddr : Address) (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  erc20_transfer_keeps_total_supply toAddr amount s result

def weth_transferFrom_reverts_when_allowance_is_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_reverts_when_allowance_is_low fromAddr toAddr amount s result

def weth_transferFrom_reverts_when_balance_is_low
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_reverts_when_balance_is_low fromAddr toAddr amount s result

def weth_transferFrom_reverts_when_recipient_balance_would_overflow
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_reverts_when_recipient_balance_would_overflow fromAddr toAddr amount s result

def weth_transferFrom_to_self_keeps_balances
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_to_self_keeps_balances fromAddr toAddr amount s result

def weth_transferFrom_moves_tokens_between_distinct_accounts
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_moves_tokens_between_distinct_accounts fromAddr toAddr amount s result

def weth_transferFrom_keeps_total_supply
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_keeps_total_supply fromAddr toAddr amount s result

def weth_transferFrom_keeps_infinite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_keeps_infinite_allowance fromAddr toAddr amount s result

def weth_transferFrom_spends_finite_allowance
    (fromAddr toAddr : Address) (amount : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  erc20_transferFrom_spends_finite_allowance fromAddr toAddr amount s result

/-
deposit()

Properties specified:
- The call reverts if crediting the sender or total supply would overflow.
- Otherwise, the deposit succeeds.
- The sender balance and total supply each increase by msg.value.
- If the contract's native ETH balance covered existing WETH supply before the
  call, then after the EVM credits msg.value at call entry, the native ETH
  balance covers the new WETH supply.

Security conclusions:
- Accepted deposits mint exactly msg.value WETH to the sender.
- Deposits cannot overflow sender balance or total supply accounting.
- Deposits preserve the native ETH backing needed to redeem all WETH.
-/
def weth_deposit_reverts_when_sender_balance_would_overflow
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  (s.storageMap balances.slot s.sender).val + s.msgValue.val > Verity.Stdlib.Math.MAX_UINT256 →
    result = ContractResult.revert "BalanceOverflow()" s

def weth_deposit_reverts_when_total_supply_would_overflow
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  (s.storageMap balances.slot s.sender).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + s.msgValue.val > Verity.Stdlib.Math.MAX_UINT256 →
      result = ContractResult.revert "TotalSupplyOverflow()" s

def weth_deposit_succeeds_when_accounting_does_not_overflow
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  (s.storageMap balances.slot s.sender).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      result = ContractResult.success true result.snd

def weth_deposit_credits_sender
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  (s.storageMap balances.slot s.sender).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      result.snd.storageMap balances.slot s.sender =
        (s.storageMap balances.slot s.sender) + s.msgValue

def weth_deposit_increases_total_supply
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  (s.storageMap balances.slot s.sender).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      result.snd.storage tokenSupply.slot =
        (s.storage tokenSupply.slot) + s.msgValue

def weth_deposit_preserves_native_backing
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  (s.storageMap balances.slot s.sender).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage tokenSupply.slot).val + s.msgValue.val ≤ Verity.Stdlib.Math.MAX_UINT256 →
      s.selfBalance.val ≥ (s.storage tokenSupply.slot).val + s.msgValue.val →
        result.snd.selfBalance.val ≥ (result.snd.storage tokenSupply.slot).val

/-
withdraw(amount)

Properties specified:
- The call reverts if the sender balance or total supply is too low.
- The call reverts if the contract does not have enough native ETH to pay the
  requested withdrawal.
- If the balance, supply, native ETH backing, and native transfer all succeed,
  the withdrawal succeeds.
- The sender balance and total supply each decrease by `amount`.
- The contract's native ETH balance decreases by exactly `amount`.
- Native ETH backing still covers WETH supply after a successful withdrawal.
- Current `ContractState` tracks the contract's native ETH balance but not
  arbitrary recipient ETH balances, so recipient ETH delivery is covered by the
  successful native-transfer check and concrete mirror tests.

Security conclusions:
- Withdrawals cannot burn more than the sender balance or total supply can
  cover.
- Withdrawals cannot burn WETH unless the contract has enough native ETH backing
  and the native ETH send reports success.
- Successful withdrawals burn exactly the requested amount and release exactly
  that much native ETH from the contract.
- WETH supply decreases in sync with sender balance while native backing remains
  sufficient for the remaining WETH.
-/
def weth_withdraw_reverts_when_balance_is_low
    (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  amount.val > (s.storageMap balances.slot s.sender).val →
    result = ContractResult.revert "InsufficientBalance()" s

def weth_withdraw_reverts_when_total_supply_is_low
    (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap balances.slot s.sender).val →
    amount.val > (s.storage tokenSupply.slot).val →
      result = ContractResult.revert "InsufficientSupply()" s

def weth_withdraw_reverts_when_eth_backing_is_low
    (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap balances.slot s.sender).val →
    amount.val ≤ (s.storage tokenSupply.slot).val →
      amount.val > s.selfBalance.val →
        result = ContractResult.revert "InsufficientEthBacking()" s

def weth_withdraw_reverts_when_native_transfer_fails
    (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap balances.slot s.sender).val →
    amount.val ≤ (s.storage tokenSupply.slot).val →
      amount.val ≤ s.selfBalance.val →
        Contracts.call 50000 (addressToWord s.sender) amount 0 0 0 0 = 0 →
          result = ContractResult.revert "EthTransferFailed()" s

def weth_withdraw_succeeds_when_balance_supply_eth_and_transfer_are_enough
    (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap balances.slot s.sender).val →
    amount.val ≤ (s.storage tokenSupply.slot).val →
      amount.val ≤ s.selfBalance.val →
        Contracts.call 50000 (addressToWord s.sender) amount 0 0 0 0 ≠ 0 →
      result = ContractResult.success true result.snd

def weth_withdraw_debits_sender
    (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap balances.slot s.sender).val →
    amount.val ≤ (s.storage tokenSupply.slot).val →
      amount.val ≤ s.selfBalance.val →
        Contracts.call 50000 (addressToWord s.sender) amount 0 0 0 0 ≠ 0 →
      result.snd.storageMap balances.slot s.sender =
        Verity.EVM.Uint256.sub (s.storageMap balances.slot s.sender) amount

def weth_withdraw_decreases_total_supply
    (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap balances.slot s.sender).val →
    amount.val ≤ (s.storage tokenSupply.slot).val →
      amount.val ≤ s.selfBalance.val →
        Contracts.call 50000 (addressToWord s.sender) amount 0 0 0 0 ≠ 0 →
      result.snd.storage tokenSupply.slot =
        Verity.EVM.Uint256.sub (s.storage tokenSupply.slot) amount

def weth_withdraw_decreases_native_balance
    (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  amount.val ≤ (s.storageMap balances.slot s.sender).val →
    amount.val ≤ (s.storage tokenSupply.slot).val →
      amount.val ≤ s.selfBalance.val →
        Contracts.call 50000 (addressToWord s.sender) amount 0 0 0 0 ≠ 0 →
      result.snd.selfBalance.val + amount.val = s.selfBalance.val

def weth_withdraw_preserves_native_backing
    (amount : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  s.selfBalance.val ≥ (s.storage tokenSupply.slot).val →
    amount.val ≤ (s.storageMap balances.slot s.sender).val →
      amount.val ≤ (s.storage tokenSupply.slot).val →
        amount.val ≤ s.selfBalance.val →
          Contracts.call 50000 (addressToWord s.sender) amount 0 0 0 0 ≠ 0 →
            result.snd.selfBalance.val ≥ (result.snd.storage tokenSupply.slot).val

end Tamago.Spec.Tokens.WETHSpec
