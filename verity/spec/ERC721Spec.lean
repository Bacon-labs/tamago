import src.ERC721

namespace spec.ERC721Spec

open Verity
open Verity.EVM.Uint256

def erc721_totalSupply_spec (result : Uint256) (s : ContractState) : Prop :=
  result = s.storage 1

def erc721_owner_spec (result : Address) (s : ContractState) : Prop :=
  result = s.storageAddr 0

def erc721_balanceOf_spec (account : Address) (result : Uint256) (s : ContractState) : Prop :=
  account ≠ zeroAddress → result = s.storageMap 3 account

def erc721_ownerOf_spec (tokenId : Uint256) (result : ContractResult Address) (s : ContractState) : Prop :=
  let ownerWord := s.storageMapUint 4 tokenId
  if ownerWord != 0 then
    result = ContractResult.success (wordToAddress ownerWord) s
  else
    result = ContractResult.revert "Token does not exist" s

def erc721_getApproved_spec (tokenId : Uint256) (result : ContractResult Address) (s : ContractState) : Prop :=
  let ownerWord := s.storageMapUint 4 tokenId
  if ownerWord != 0 then
    result = ContractResult.success (wordToAddress (s.storageMapUint 5 tokenId)) s
  else
    result = ContractResult.revert "Token does not exist" s

def erc721_isApprovedForAll_spec (ownerAddr operator : Address) (result : Bool) (s : ContractState) : Prop :=
  result = (s.storageMap2 6 ownerAddr operator != 0)

def erc721_setApprovalForAll_effect (operator : Address) (approved : Bool) (s s' : ContractState) : Prop :=
  s'.storageMap2 6 s.sender operator = src.boolToWord approved ∧
  s'.storage 1 = s.storage 1 ∧
  s'.storageMap = s.storageMap ∧
  s'.storageMapUint = s.storageMapUint

def erc721_approve_effect (approved : Address) (tokenId : Uint256) (s s' : ContractState) : Prop :=
  (s.storageMapUint 4 tokenId != 0) = true →
    ((s.sender == wordToAddress (s.storageMapUint 4 tokenId)) ||
      (s.storageMap2 6 (wordToAddress (s.storageMapUint 4 tokenId)) s.sender != 0)) = true →
      s'.storageMapUint 5 tokenId = addressToWord approved

def erc721_mint_effect (toAddr : Address) (s s' : ContractState) (result : Uint256) : Prop :=
  s.sender = s.storageAddr 0 →
    toAddr ≠ zeroAddress →
    s.storageMapUint 4 (s.storage 2) = 0 →
    (s.storageMap 3 toAddr).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
    (s.storage 1).val + 1 ≤ Verity.Stdlib.Math.MAX_UINT256 →
      result = s.storage 2 ∧
      s'.storageMapUint 4 (s.storage 2) = addressToWord toAddr ∧
      s'.storageMap 3 toAddr = (s.storageMap 3 toAddr) + 1 ∧
      s'.storage 1 = (s.storage 1) + 1 ∧
      s'.storage 2 = Verity.EVM.Uint256.add (s.storage 2) 1

def erc721_mint_unauthorized_no_change (toAddr : Address) (s s' : ContractState) : Prop :=
  s.sender ≠ s.storageAddr 0 →
    s'.storage 1 = s.storage 1 ∧
    s'.storage 2 = s.storage 2 ∧
    s'.storageMap 3 toAddr = s.storageMap 3 toAddr

def erc721_transferFrom_zero_recipient_no_change
    (_fromAddr : Address) (_tokenId : Uint256) (s s' : ContractState) : Prop :=
  s'.storage = s.storage ∧
  s'.storageMap = s.storageMap ∧
  s'.storageMapUint = s.storageMapUint

end spec.ERC721Spec
