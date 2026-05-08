import Tamago.Tokens.ERC721
import Tamago.Spec.Auth.OwnableSpec

namespace Tamago.Spec.Tokens.ERC721Spec

open Verity
open Verity.EVM.Uint256
open Tamago.Tokens.ERC721
open Tamago.Spec.Auth.OwnableSpec

/-
ERC721 specs are grouped by public function. View specs state what public
readers expose. Mutating functions are decomposed into simple properties for
authorization, revert cases, successful updates, and frame conditions.
-/

/-
Supply and ownership views

Properties specified:
- totalSupply() returns stored supply.
- owner(), transferOwnership(), and renounceOwnership() reuse the Ownable specs.

Security conclusions:
- Mint authority follows the shared Ownable authorization model.
- Ownership transition functions inherit the standalone Ownable invariants.
-/
def erc721_totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage tokenSupply.slot

def erc721_owner_spec (result : Address) (s : ContractState) : Prop :=
  ownable_owner_spec result s

def erc721_transferOwnership_reverts_for_non_owner
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_reverts_for_non_owner newOwner s result

def erc721_transferOwnership_reverts_for_zero_owner
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_reverts_for_zero_owner newOwner s result

def erc721_transferOwnership_succeeds_for_owner_to_nonzero
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_succeeds_for_owner_to_nonzero newOwner s result

def erc721_transferOwnership_sets_new_owner
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_sets_new_owner newOwner s result

def erc721_transferOwnership_keeps_other_owner_slots
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_keeps_other_owner_slots newOwner s result

def erc721_transferOwnership_keeps_uint_storage
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_keeps_uint_storage newOwner s result

def erc721_transferOwnership_keeps_balances_and_allowances
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_keeps_balances_and_allowances newOwner s result

def erc721_transferOwnership_keeps_array_storage
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_keeps_array_storage newOwner s result

def erc721_renounceOwnership_reverts_for_non_owner
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_reverts_for_non_owner s result

def erc721_renounceOwnership_succeeds_for_owner
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_succeeds_for_owner s result

def erc721_renounceOwnership_clears_owner
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_clears_owner s result

def erc721_renounceOwnership_keeps_other_owner_slots
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_keeps_other_owner_slots s result

def erc721_renounceOwnership_keeps_uint_storage
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_keeps_uint_storage s result

def erc721_renounceOwnership_keeps_balances_and_allowances
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_keeps_balances_and_allowances s result

def erc721_renounceOwnership_keeps_array_storage
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_keeps_array_storage s result

/-
Token and approval views

Properties specified:
- balanceOf(account) rejects the zero address and otherwise returns its stored
  token count.
- ownerOf(tokenId) and getApproved(tokenId) reject missing tokens.
- Existing tokens expose the stored owner and token approval.
- isApprovedForAll(owner, operator) reflects the operator approval flag.

Security conclusions:
- Public NFT reads expose existing ownership and approval state.
- Missing tokens and invalid owners are rejected instead of returning fabricated
  state.
-/
def erc721_balanceOf_spec (account : Address) (result : ContractResult Uint256) (s : ContractState) : Prop :=
  (account = zeroAddress →
    result = ContractResult.revert "Invalid owner" s) ∧
  (account ≠ zeroAddress →
    result = ContractResult.success (s.storageMap balances.slot account) s)

def erc721_ownerOf_spec (tokenId : Uint256) (result : ContractResult Address) (s : ContractState) : Prop :=
  let ownerWord := s.storageMapUint tokenOwners.slot tokenId
  if ownerWord != 0 then
    result = ContractResult.success (wordToAddress ownerWord) s
  else
    result = ContractResult.revert "Token does not exist" s

def erc721_getApproved_spec (tokenId : Uint256) (result : ContractResult Address) (s : ContractState) : Prop :=
  let ownerWord := s.storageMapUint tokenOwners.slot tokenId
  if ownerWord != 0 then
    result = ContractResult.success (wordToAddress (s.storageMapUint tokenApprovals.slot tokenId)) s
  else
    result = ContractResult.revert "Token does not exist" s

def erc721_isApprovedForAll_spec (ownerAddr operator : Address) (result : Bool) (s : ContractState) : Prop :=
  result = (s.storageMap2 operatorApprovals.slot ownerAddr operator != 0)

/-
setApprovalForAll(operator, approved)

Properties specified:
- The call always succeeds.
- The caller's operator flag is set to the requested boolean value.
- Total supply, balances, and token owners are unchanged.

Security conclusions:
- Operator approval changes permission only.
- Setting operator approval cannot mint, burn, transfer, or alter ownership
  accounting.
-/
def erc721_setApprovalForAll_succeeds
    (_operator : Address) (_approved : Bool) (_s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result = ContractResult.success true result.snd

def erc721_setApprovalForAll_sets_operator_flag
    (operator : Address) (approved : Bool) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storageMap2 operatorApprovals.slot s.sender operator = Tamago.Tokens.boolToWord approved

def erc721_setApprovalForAll_keeps_supply
    (_operator : Address) (_approved : Bool) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storage tokenSupply.slot = s.storage tokenSupply.slot

def erc721_setApprovalForAll_keeps_balances_and_owners
    (_operator : Address) (_approved : Bool) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  result.snd.storageMap = s.storageMap ∧
  result.snd.storageMapUint = s.storageMapUint

/-
approve(approved, tokenId)

Properties specified:
- Missing tokens revert.
- Existing tokens reject callers that are neither the owner nor an approved
  operator for the owner.
- Authorized callers succeed and set the token approval.

Security conclusions:
- Per-token approval can be set only for an existing token.
- Only the token owner or an authorized operator can set approval.
- Approval updates do not transfer ownership.
-/
def erc721_approve_reverts_when_token_is_missing
    (_approved : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  s.storageMapUint tokenOwners.slot tokenId = 0 →
    result = ContractResult.revert "Token does not exist" s

def erc721_approve_reverts_when_sender_is_not_authorized
    (_approved : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  (s.storageMapUint tokenOwners.slot tokenId != 0) = true →
    ((s.sender == wordToAddress (s.storageMapUint tokenOwners.slot tokenId)) ||
      (s.storageMap2 operatorApprovals.slot
        (wordToAddress (s.storageMapUint tokenOwners.slot tokenId)) s.sender != 0)) = false →
        result = ContractResult.revert "Not authorized" s

def erc721_approve_succeeds_when_sender_is_authorized
    (_approved : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  (s.storageMapUint tokenOwners.slot tokenId != 0) = true →
    ((s.sender == wordToAddress (s.storageMapUint tokenOwners.slot tokenId)) ||
      (s.storageMap2 operatorApprovals.slot
        (wordToAddress (s.storageMapUint tokenOwners.slot tokenId)) s.sender != 0)) = true →
        result = ContractResult.success true result.snd

def erc721_approve_sets_token_approval
    (approved : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  (s.storageMapUint tokenOwners.slot tokenId != 0) = true →
    ((s.sender == wordToAddress (s.storageMapUint tokenOwners.slot tokenId)) ||
      (s.storageMap2 operatorApprovals.slot
        (wordToAddress (s.storageMapUint tokenOwners.slot tokenId)) s.sender != 0)) = true →
        result.snd.storageMapUint tokenApprovals.slot tokenId = addressToWord approved

/-
mint(to)

Properties specified:
- A non-owner cannot mint.
- The recipient cannot be the zero address.
- The next token id must be unowned.
- Minting reverts if recipient balance or total supply would overflow.
- A valid mint returns the next token id, assigns it to the recipient, credits
  the recipient balance, increases total supply, and advances nextTokenId.

Security conclusions:
- New NFTs can be created only by the owner.
- Minting cannot target the zero address or reuse an existing token id.
- Minting cannot overflow balance or supply accounting.
- Successful minting keeps owner, balance, supply, and token-id state
  synchronized.
-/
def erc721_mint_reverts_for_non_owner
    (_toAddr : Address) (s : ContractState) (result : ContractResult Uint256) : Prop :=
  s.sender ≠ s.storageAddr contractOwner.slot →
    result = ContractResult.revert "Caller is not the owner" s

def erc721_mint_reverts_for_zero_recipient
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    toAddr = zeroAddress →
      result = ContractResult.revert "Invalid recipient" s

def erc721_mint_reverts_when_next_token_is_already_minted
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    toAddr ≠ zeroAddress →
      s.storageMapUint tokenOwners.slot (s.storage nextTokenId.slot) ≠ 0 →
        result = ContractResult.revert "Token already minted" s

def erc721_mint_reverts_when_recipient_balance_would_overflow
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    toAddr ≠ zeroAddress →
      s.storageMapUint tokenOwners.slot (s.storage nextTokenId.slot) = 0 →
        (s.storageMap balances.slot toAddr).val + 1 > Verity.Stdlib.Math.MAX_UINT256 →
          result = ContractResult.revert "Balance overflow" s

def erc721_mint_reverts_when_total_supply_would_overflow
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    toAddr ≠ zeroAddress →
      s.storageMapUint tokenOwners.slot (s.storage nextTokenId.slot) = 0 →
        (s.storageMap balances.slot toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
          (s.storage tokenSupply.slot).val + 1 > Verity.Stdlib.Math.MAX_UINT256 →
            result = ContractResult.revert "Supply overflow" s

def erc721_mint_succeeds_with_next_token_id
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    toAddr ≠ zeroAddress →
      s.storageMapUint tokenOwners.slot (s.storage nextTokenId.slot) = 0 →
        (s.storageMap balances.slot toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
          (s.storage tokenSupply.slot).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
            result = ContractResult.success (s.storage nextTokenId.slot) result.snd

def erc721_mint_assigns_next_token_to_recipient
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    toAddr ≠ zeroAddress →
      s.storageMapUint tokenOwners.slot (s.storage nextTokenId.slot) = 0 →
        (s.storageMap balances.slot toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
          (s.storage tokenSupply.slot).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
            result.snd.storageMapUint tokenOwners.slot (s.storage nextTokenId.slot) =
              addressToWord toAddr

def erc721_mint_credits_recipient_balance
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    toAddr ≠ zeroAddress →
      s.storageMapUint tokenOwners.slot (s.storage nextTokenId.slot) = 0 →
        (s.storageMap balances.slot toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
          (s.storage tokenSupply.slot).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
            result.snd.storageMap balances.slot toAddr =
              (s.storageMap balances.slot toAddr) + 1

def erc721_mint_increases_total_supply
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    toAddr ≠ zeroAddress →
      s.storageMapUint tokenOwners.slot (s.storage nextTokenId.slot) = 0 →
        (s.storageMap balances.slot toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
          (s.storage tokenSupply.slot).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
            result.snd.storage tokenSupply.slot = (s.storage tokenSupply.slot) + 1

def erc721_mint_advances_next_token_id
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) : Prop :=
  s.sender = s.storageAddr contractOwner.slot →
    toAddr ≠ zeroAddress →
      s.storageMapUint tokenOwners.slot (s.storage nextTokenId.slot) = 0 →
        (s.storageMap balances.slot toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
          (s.storage tokenSupply.slot).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
            result.snd.storage nextTokenId.slot =
              Verity.EVM.Uint256.add (s.storage nextTokenId.slot) 1

/-
transferFrom(from, to, tokenId)

Properties specified:
- Transfers reject the zero recipient, missing tokens, wrong `from` owner, and
  unauthorized callers.
- Self-transfers succeed, keep balances unchanged, keep the owner, and clear
  token approval.
- Distinct-account transfers require enough sender balance and recipient
  balance headroom.
- Successful distinct transfers set the new owner, clear approval, debit the
  old owner, and credit the new owner.

Security conclusions:
- Tokens can move only from their actual owner to a nonzero recipient.
- Only the owner, approved address, or approved operator can move a token.
- Transfers clear token approval and keep balances aligned with ownership.
- Overflow and inconsistent-balance paths revert instead of corrupting
  accounting.
-/
def erc721_transferFrom_reverts_for_zero_recipient
    (_fromAddr toAddr : Address) (_tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  toAddr = zeroAddress →
    result = ContractResult.revert "Invalid recipient" s

def erc721_transferFrom_reverts_when_token_is_missing
    (_fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  toAddr ≠ zeroAddress →
    s.storageMapUint tokenOwners.slot tokenId = 0 →
      result = ContractResult.revert "Token does not exist" s

def erc721_transferFrom_reverts_when_from_is_not_owner
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  toAddr ≠ zeroAddress →
    s.storageMapUint tokenOwners.slot tokenId ≠ 0 →
      s.storageMapUint tokenOwners.slot tokenId ≠ addressToWord fromAddr →
        result = ContractResult.revert "From is not owner" s

def erc721_transferFrom_reverts_when_sender_is_not_authorized
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  toAddr ≠ zeroAddress →
      s.storageMapUint tokenOwners.slot tokenId ≠ 0 →
        s.storageMapUint tokenOwners.slot tokenId = addressToWord fromAddr →
        (((s.sender == fromAddr) ||
          (s.storageMapUint tokenApprovals.slot tokenId == addressToWord s.sender)) ||
          (s.storageMap2 operatorApprovals.slot fromAddr s.sender != 0)) = false →
          result = ContractResult.revert "Not authorized" s

def erc721_transferFrom_to_self_succeeds
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  toAddr ≠ zeroAddress →
    s.storageMapUint tokenOwners.slot tokenId ≠ 0 →
      s.storageMapUint tokenOwners.slot tokenId = addressToWord fromAddr →
        (((s.sender == fromAddr) ||
          (s.storageMapUint tokenApprovals.slot tokenId == addressToWord s.sender)) ||
          (s.storageMap2 operatorApprovals.slot fromAddr s.sender != 0)) = true →
          fromAddr = toAddr →
            result = ContractResult.success true result.snd

def erc721_transferFrom_to_self_keeps_balances
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  toAddr ≠ zeroAddress →
    s.storageMapUint tokenOwners.slot tokenId ≠ 0 →
      s.storageMapUint tokenOwners.slot tokenId = addressToWord fromAddr →
        (((s.sender == fromAddr) ||
          (s.storageMapUint tokenApprovals.slot tokenId == addressToWord s.sender)) ||
          (s.storageMap2 operatorApprovals.slot fromAddr s.sender != 0)) = true →
          fromAddr = toAddr →
            result.snd.storageMap = s.storageMap

def erc721_transferFrom_sets_owner_on_self_transfer
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  toAddr ≠ zeroAddress →
    s.storageMapUint tokenOwners.slot tokenId ≠ 0 →
      s.storageMapUint tokenOwners.slot tokenId = addressToWord fromAddr →
        (((s.sender == fromAddr) ||
          (s.storageMapUint tokenApprovals.slot tokenId == addressToWord s.sender)) ||
          (s.storageMap2 operatorApprovals.slot fromAddr s.sender != 0)) = true →
          fromAddr = toAddr →
            result.snd.storageMapUint tokenOwners.slot tokenId = addressToWord toAddr

def erc721_transferFrom_clears_approval_on_self_transfer
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  toAddr ≠ zeroAddress →
    s.storageMapUint tokenOwners.slot tokenId ≠ 0 →
      s.storageMapUint tokenOwners.slot tokenId = addressToWord fromAddr →
        (((s.sender == fromAddr) ||
          (s.storageMapUint tokenApprovals.slot tokenId == addressToWord s.sender)) ||
          (s.storageMap2 operatorApprovals.slot fromAddr s.sender != 0)) = true →
          fromAddr = toAddr →
            result.snd.storageMapUint tokenApprovals.slot tokenId = addressToWord zeroAddress

def erc721_transferFrom_reverts_when_from_balance_is_low
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  toAddr ≠ zeroAddress →
    s.storageMapUint tokenOwners.slot tokenId ≠ 0 →
      s.storageMapUint tokenOwners.slot tokenId = addressToWord fromAddr →
        (((s.sender == fromAddr) ||
          (s.storageMapUint tokenApprovals.slot tokenId == addressToWord s.sender)) ||
          (s.storageMap2 operatorApprovals.slot fromAddr s.sender != 0)) = true →
          fromAddr ≠ toAddr →
            (s.storageMap balances.slot fromAddr).val < 1 →
              result = ContractResult.revert "Insufficient balance" s

def erc721_transferFrom_reverts_when_to_balance_would_overflow
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  toAddr ≠ zeroAddress →
    s.storageMapUint tokenOwners.slot tokenId ≠ 0 →
      s.storageMapUint tokenOwners.slot tokenId = addressToWord fromAddr →
        (((s.sender == fromAddr) ||
          (s.storageMapUint tokenApprovals.slot tokenId == addressToWord s.sender)) ||
          (s.storageMap2 operatorApprovals.slot fromAddr s.sender != 0)) = true →
          fromAddr ≠ toAddr →
            (s.storageMap balances.slot fromAddr).val ≥ 1 →
              (s.storageMap balances.slot toAddr).val + 1 > Verity.Stdlib.Math.MAX_UINT256 →
                result = ContractResult.revert "Balance overflow" s

def erc721_transferFrom_between_distinct_accounts_succeeds
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  toAddr ≠ zeroAddress →
    s.storageMapUint tokenOwners.slot tokenId ≠ 0 →
      s.storageMapUint tokenOwners.slot tokenId = addressToWord fromAddr →
        (((s.sender == fromAddr) ||
          (s.storageMapUint tokenApprovals.slot tokenId == addressToWord s.sender)) ||
          (s.storageMap2 operatorApprovals.slot fromAddr s.sender != 0)) = true →
          fromAddr ≠ toAddr →
            (s.storageMap balances.slot fromAddr).val ≥ 1 →
              (s.storageMap balances.slot toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
                result = ContractResult.success true result.snd

def erc721_transferFrom_sets_new_owner
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  toAddr ≠ zeroAddress →
    s.storageMapUint tokenOwners.slot tokenId ≠ 0 →
      s.storageMapUint tokenOwners.slot tokenId = addressToWord fromAddr →
        (((s.sender == fromAddr) ||
          (s.storageMapUint tokenApprovals.slot tokenId == addressToWord s.sender)) ||
          (s.storageMap2 operatorApprovals.slot fromAddr s.sender != 0)) = true →
          fromAddr ≠ toAddr →
            (s.storageMap balances.slot fromAddr).val ≥ 1 →
              (s.storageMap balances.slot toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
                result.snd.storageMapUint tokenOwners.slot tokenId = addressToWord toAddr

def erc721_transferFrom_clears_token_approval
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  toAddr ≠ zeroAddress →
    s.storageMapUint tokenOwners.slot tokenId ≠ 0 →
      s.storageMapUint tokenOwners.slot tokenId = addressToWord fromAddr →
        (((s.sender == fromAddr) ||
          (s.storageMapUint tokenApprovals.slot tokenId == addressToWord s.sender)) ||
          (s.storageMap2 operatorApprovals.slot fromAddr s.sender != 0)) = true →
          fromAddr ≠ toAddr →
            (s.storageMap balances.slot fromAddr).val ≥ 1 →
              (s.storageMap balances.slot toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
                result.snd.storageMapUint tokenApprovals.slot tokenId = addressToWord zeroAddress

def erc721_transferFrom_debits_from_balance
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  toAddr ≠ zeroAddress →
    s.storageMapUint tokenOwners.slot tokenId ≠ 0 →
      s.storageMapUint tokenOwners.slot tokenId = addressToWord fromAddr →
        (((s.sender == fromAddr) ||
          (s.storageMapUint tokenApprovals.slot tokenId == addressToWord s.sender)) ||
          (s.storageMap2 operatorApprovals.slot fromAddr s.sender != 0)) = true →
          fromAddr ≠ toAddr →
            (s.storageMap balances.slot fromAddr).val ≥ 1 →
              (s.storageMap balances.slot toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
                result.snd.storageMap balances.slot fromAddr =
                  Verity.EVM.Uint256.sub (s.storageMap balances.slot fromAddr) 1

def erc721_transferFrom_credits_to_balance
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  toAddr ≠ zeroAddress →
    s.storageMapUint tokenOwners.slot tokenId ≠ 0 →
      s.storageMapUint tokenOwners.slot tokenId = addressToWord fromAddr →
        (((s.sender == fromAddr) ||
          (s.storageMapUint tokenApprovals.slot tokenId == addressToWord s.sender)) ||
          (s.storageMap2 operatorApprovals.slot fromAddr s.sender != 0)) = true →
          fromAddr ≠ toAddr →
            (s.storageMap balances.slot fromAddr).val ≥ 1 →
              (s.storageMap balances.slot toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
                result.snd.storageMap balances.slot toAddr =
                  (s.storageMap balances.slot toAddr) + 1

end Tamago.Spec.Tokens.ERC721Spec
