import src.tokens.ERC721
import spec.auth.OwnableSpec

namespace spec.tokens.ERC721Spec

open Verity
open Verity.EVM.Uint256
open src.ERC721
open spec.auth.OwnableSpec

def erc721_totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage tokenSupply.slot

def erc721_owner_spec (result : Address) (s : ContractState) : Prop :=
  ownable_owner_spec result s

def erc721_transferOwnership_effect
    (newOwner : Address) (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_transferOwnership_effect newOwner s result

def erc721_renounceOwnership_effect
    (s : ContractState) (result : ContractResult Bool) : Prop :=
  ownable_renounceOwnership_effect s result

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

def erc721_setApprovalForAll_effect
    (operator : Address) (approved : Bool) (s : ContractState) (result : ContractResult Bool) : Prop :=
  result = ContractResult.success true result.snd ∧
  result.snd.storageMap2 operatorApprovals.slot s.sender operator = src.boolToWord approved ∧
  result.snd.storage tokenSupply.slot = s.storage tokenSupply.slot ∧
  result.snd.storageMap = s.storageMap ∧
  result.snd.storageMapUint = s.storageMapUint

def erc721_approve_effect
    (approved : Address) (tokenId : Uint256) (s : ContractState) (result : ContractResult Bool) : Prop :=
  (s.storageMapUint tokenOwners.slot tokenId = 0 →
    result = ContractResult.revert "Token does not exist" s) ∧
  ((s.storageMapUint tokenOwners.slot tokenId != 0) = true →
    (((s.sender == wordToAddress (s.storageMapUint tokenOwners.slot tokenId)) ||
      (s.storageMap2 operatorApprovals.slot (wordToAddress (s.storageMapUint tokenOwners.slot tokenId)) s.sender != 0)) = false →
        result = ContractResult.revert "Not authorized" s) ∧
    (((s.sender == wordToAddress (s.storageMapUint tokenOwners.slot tokenId)) ||
      (s.storageMap2 operatorApprovals.slot (wordToAddress (s.storageMapUint tokenOwners.slot tokenId)) s.sender != 0)) = true →
        result = ContractResult.success true result.snd ∧
        result.snd.storageMapUint tokenApprovals.slot tokenId = addressToWord approved))

def erc721_mint_effect
    (toAddr : Address) (s : ContractState) (result : ContractResult Uint256) : Prop :=
  (s.sender ≠ s.storageAddr contractOwner.slot →
    result = ContractResult.revert "Caller is not the owner" s) ∧
  (s.sender = s.storageAddr contractOwner.slot →
    (toAddr = zeroAddress →
      result = ContractResult.revert "Invalid recipient" s) ∧
    (toAddr ≠ zeroAddress →
      (s.storageMapUint tokenOwners.slot (s.storage nextTokenId.slot) ≠ 0 →
        result = ContractResult.revert "Token already minted" s) ∧
      (s.storageMapUint tokenOwners.slot (s.storage nextTokenId.slot) = 0 →
        ((s.storageMap balances.slot toAddr).val + 1 > Verity.Stdlib.Math.MAX_UINT256 →
          result = ContractResult.revert "Balance overflow" s) ∧
        ((s.storageMap balances.slot toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
          ((s.storage tokenSupply.slot).val + 1 > Verity.Stdlib.Math.MAX_UINT256 →
            result = ContractResult.revert "Supply overflow" s) ∧
          ((s.storage tokenSupply.slot).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
            result = ContractResult.success (s.storage nextTokenId.slot) result.snd ∧
            result.snd.storageMapUint tokenOwners.slot (s.storage nextTokenId.slot) = addressToWord toAddr ∧
            result.snd.storageMap balances.slot toAddr = (s.storageMap balances.slot toAddr) + 1 ∧
            result.snd.storage tokenSupply.slot = (s.storage tokenSupply.slot) + 1 ∧
            result.snd.storage nextTokenId.slot =
              Verity.EVM.Uint256.add (s.storage nextTokenId.slot) 1)))))

def erc721_transferFrom_effect
    (fromAddr toAddr : Address) (tokenId : Uint256) (s : ContractState)
    (result : ContractResult Bool) : Prop :=
  (toAddr = zeroAddress →
    result = ContractResult.revert "Invalid recipient" s) ∧
  (toAddr ≠ zeroAddress →
    (s.storageMapUint tokenOwners.slot tokenId = 0 →
      result = ContractResult.revert "Token does not exist" s) ∧
    (s.storageMapUint tokenOwners.slot tokenId ≠ 0 →
      (s.storageMapUint tokenOwners.slot tokenId ≠ addressToWord fromAddr →
        result = ContractResult.revert "From is not owner" s) ∧
      (s.storageMapUint tokenOwners.slot tokenId = addressToWord fromAddr →
        ((((s.sender == fromAddr) ||
            (s.storageMapUint tokenApprovals.slot tokenId == addressToWord s.sender)) ||
            (s.storageMap2 operatorApprovals.slot fromAddr s.sender != 0)) = false →
          result = ContractResult.revert "Not authorized" s) ∧
        ((((s.sender == fromAddr) ||
            (s.storageMapUint tokenApprovals.slot tokenId == addressToWord s.sender)) ||
            (s.storageMap2 operatorApprovals.slot fromAddr s.sender != 0)) = true →
          (fromAddr = toAddr →
            result = ContractResult.success true result.snd ∧
            result.snd.storageMap = s.storageMap ∧
            result.snd.storageMapUint tokenOwners.slot tokenId = addressToWord toAddr ∧
            result.snd.storageMapUint tokenApprovals.slot tokenId = addressToWord zeroAddress) ∧
          (fromAddr ≠ toAddr →
            ((s.storageMap balances.slot fromAddr).val < 1 →
              result = ContractResult.revert "Insufficient balance" s) ∧
            ((s.storageMap balances.slot fromAddr).val ≥ 1 →
              ((s.storageMap balances.slot toAddr).val + 1 > Verity.Stdlib.Math.MAX_UINT256 →
                result = ContractResult.revert "Balance overflow" s) ∧
              ((s.storageMap balances.slot toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
                result = ContractResult.success true result.snd ∧
                result.snd.storageMapUint tokenOwners.slot tokenId = addressToWord toAddr ∧
                result.snd.storageMapUint tokenApprovals.slot tokenId = addressToWord zeroAddress ∧
                result.snd.storageMap balances.slot fromAddr =
                  Verity.EVM.Uint256.sub (s.storageMap balances.slot fromAddr) 1 ∧
                result.snd.storageMap balances.slot toAddr =
                  (s.storageMap balances.slot toAddr) + 1)))))))

end spec.tokens.ERC721Spec
