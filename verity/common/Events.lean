import Compiler.CompilationModel

namespace common.Events

open Compiler.CompilationModel

def indexedAddress (name : String) : EventParam :=
  { name := name, ty := ParamType.address, kind := EventParamKind.indexed }

def indexedUint256 (name : String) : EventParam :=
  { name := name, ty := ParamType.uint256, kind := EventParamKind.indexed }

def uint256 (name : String) : EventParam :=
  { name := name, ty := ParamType.uint256, kind := EventParamKind.unindexed }

def bool (name : String) : EventParam :=
  { name := name, ty := ParamType.bool, kind := EventParamKind.unindexed }

def transfer : EventDef :=
  { name := "Transfer"
    params := [
      indexedAddress "from",
      indexedAddress "to",
      uint256 "value"
    ] }

def approval : EventDef :=
  { name := "Approval"
    params := [
      indexedAddress "owner",
      indexedAddress "spender",
      uint256 "value"
    ] }

def ownershipTransferred : EventDef :=
  { name := "OwnershipTransferred"
    params := [
      indexedAddress "previousOwner",
      indexedAddress "newOwner"
    ] }

def erc721Approval : EventDef :=
  { name := "Approval"
    params := [
      indexedAddress "owner",
      indexedAddress "approved",
      indexedUint256 "tokenId"
    ] }

def erc721Transfer : EventDef :=
  { name := "Transfer"
    params := [
      indexedAddress "from",
      indexedAddress "to",
      indexedUint256 "tokenId"
    ] }

def approvalForAll : EventDef :=
  { name := "ApprovalForAll"
    params := [
      indexedAddress "owner",
      indexedAddress "operator",
      bool "approved"
    ] }

def deposit : EventDef :=
  { name := "Deposit"
    params := [
      indexedAddress "sender",
      indexedAddress "owner",
      uint256 "assets",
      uint256 "shares"
    ] }

def withdraw : EventDef :=
  { name := "Withdraw"
    params := [
      indexedAddress "sender",
      indexedAddress "receiver",
      indexedAddress "owner",
      uint256 "assets",
      uint256 "shares"
    ] }

def wethDeposit : EventDef :=
  { name := "Deposit"
    params := [
      indexedAddress "dst",
      uint256 "wad"
    ] }

def wethWithdrawal : EventDef :=
  { name := "Withdrawal"
    params := [
      indexedAddress "src",
      uint256 "wad"
    ] }

end common.Events
