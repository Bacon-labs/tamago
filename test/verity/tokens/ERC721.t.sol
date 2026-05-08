// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {ERC721Deployer} from "../../../src/generated/verity/ERC721Deployer.sol";
import {ERC721Iface} from "../../../src/generated/verity/ERC721Iface.sol";
import {Test} from "forge-std/Test.sol";

contract ERC721Test is Test {
    event Transfer(address indexed from, address indexed to, uint256 indexed tokenId);
    event Approval(address indexed owner, address indexed approved, uint256 indexed tokenId);
    event ApprovalForAll(address indexed owner, address indexed operator, bool approved);
    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    function deployToken() internal returns (ERC721Iface token) {
        token = ERC721Deployer.deploy(address(this));
    }

    function nonzero(address account) internal pure returns (address) {
        return account == address(0) ? address(0xA11CE) : account;
    }

    function distinctNonzero(address account, address avoid) internal pure returns (address) {
        address candidate = nonzero(account);
        if (candidate == avoid) return avoid == address(0xBEEF) ? address(0xCAFE) : address(0xBEEF);
        return candidate;
    }

    function slot(uint256 index) internal pure returns (bytes32) {
        return bytes32(index);
    }

    function balanceSlot(address account) internal pure returns (bytes32) {
        return keccak256(abi.encode(account, uint256(3)));
    }

    function ownerSlot(uint256 tokenId) internal pure returns (bytes32) {
        return keccak256(abi.encode(tokenId, uint256(4)));
    }

    function approvalSlot(uint256 tokenId) internal pure returns (bytes32) {
        return keccak256(abi.encode(tokenId, uint256(5)));
    }

    // tama: mirrors=erc721_totalSupply_spec
    function testFuzzTotalSupplySpec() public {
        ERC721Iface token = deployToken();
        token.mint(address(this));
        assertEq(token.totalSupply(), 1);
    }

    // tama: mirrors=erc721_owner_spec
    function testFuzzOwnerSpec() public {
        ERC721Iface token = deployToken();
        assertEq(token.owner(), address(this));
    }

    // tama: mirrors=erc721_transferOwnership_reverts_for_non_owner
    function testFuzzTransferOwnershipRevertsForNonOwner(address rawAttacker, address rawNewOwner) public {
        address attacker = distinctNonzero(rawAttacker, address(this));
        address newOwner = nonzero(rawNewOwner);
        ERC721Iface token = deployToken();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.transferOwnership(newOwner);
    }

    // tama: mirrors=erc721_transferOwnership_reverts_for_zero_owner
    function testFuzzTransferOwnershipRevertsForZeroOwner() public {
        ERC721Iface token = deployToken();
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Invalid owner"));
        token.transferOwnership(address(0));
    }

    // tama: mirrors=erc721_transferOwnership_succeeds_for_owner_to_nonzero
    function testFuzzTransferOwnershipSucceedsForOwnerToNonzero(address rawNewOwner) public {
        address newOwner = nonzero(rawNewOwner);
        ERC721Iface token = deployToken();
        assertTrue(token.transferOwnership(newOwner));
    }

    // tama: mirrors=erc721_transferOwnership_sets_new_owner
    function testFuzzTransferOwnershipSetsNewOwner(address rawNewOwner) public {
        address newOwner = nonzero(rawNewOwner);
        ERC721Iface token = deployToken();
        token.transferOwnership(newOwner);
        assertEq(token.owner(), newOwner);
    }

    // tama: mirrors=erc721_transferOwnership_keeps_other_owner_slots
    function testFuzzTransferOwnershipKeepsOtherOwnerSlots(address rawNewOwner) public {
        address newOwner = nonzero(rawNewOwner);
        ERC721Iface token = deployToken();
        vm.store(address(token), slot(7), bytes32(uint256(uint160(address(0xCAFE)))));
        token.transferOwnership(newOwner);
        assertEq(vm.load(address(token), slot(7)), bytes32(uint256(uint160(address(0xCAFE)))));
    }

    // tama: mirrors=erc721_transferOwnership_keeps_uint_storage
    function testFuzzTransferOwnershipKeepsUintStorage(address rawNewOwner) public {
        address newOwner = nonzero(rawNewOwner);
        ERC721Iface token = deployToken();
        token.mint(address(this));
        token.transferOwnership(newOwner);
        assertEq(token.totalSupply(), 1);
    }

    // tama: mirrors=erc721_transferOwnership_keeps_balances_and_allowances
    function testFuzzTransferOwnershipKeepsBalancesAndAllowances(address rawNewOwner, address approved, address operator) public {
        address newOwner = nonzero(rawNewOwner);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(address(this));
        token.approve(approved, tokenId);
        token.setApprovalForAll(operator, true);
        token.transferOwnership(newOwner);
        assertEq(token.balanceOf(address(this)), 1);
        assertEq(token.ownerOf(tokenId), address(this));
        assertEq(token.getApproved(tokenId), approved);
        assertTrue(token.isApprovedForAll(address(this), operator));
    }

    // tama: mirrors=erc721_transferOwnership_keeps_array_storage
    function testFuzzTransferOwnershipKeepsArrayStorage(address rawNewOwner) public {
        address newOwner = nonzero(rawNewOwner);
        ERC721Iface token = deployToken();
        bytes32 arraySlot = keccak256(abi.encode(uint256(7)));
        vm.store(address(token), arraySlot, bytes32(uint256(0x1234)));
        token.transferOwnership(newOwner);
        assertEq(vm.load(address(token), arraySlot), bytes32(uint256(0x1234)));
    }

    function testFuzzTransferOwnershipEffect(address rawNewOwner) public {
        address newOwner = nonzero(rawNewOwner);
        ERC721Iface token = deployToken();
        vm.expectEmit(true, true, false, true, address(token));
        emit OwnershipTransferred(address(this), newOwner);
        assertTrue(token.transferOwnership(newOwner));
        assertEq(token.owner(), newOwner);
    }

    // tama: mirrors=erc721_renounceOwnership_reverts_for_non_owner
    function testFuzzRenounceOwnershipRevertsForNonOwner(address rawAttacker) public {
        address attacker = distinctNonzero(rawAttacker, address(this));
        ERC721Iface token = deployToken();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.renounceOwnership();
    }

    // tama: mirrors=erc721_renounceOwnership_succeeds_for_owner
    function testFuzzRenounceOwnershipSucceedsForOwner() public {
        ERC721Iface token = deployToken();
        assertTrue(token.renounceOwnership());
    }

    // tama: mirrors=erc721_renounceOwnership_clears_owner
    function testFuzzRenounceOwnershipClearsOwner() public {
        ERC721Iface token = deployToken();
        token.renounceOwnership();
        assertEq(token.owner(), address(0));
    }

    // tama: mirrors=erc721_renounceOwnership_keeps_other_owner_slots
    function testFuzzRenounceOwnershipKeepsOtherOwnerSlots() public {
        ERC721Iface token = deployToken();
        vm.store(address(token), slot(7), bytes32(uint256(uint160(address(0xCAFE)))));
        token.renounceOwnership();
        assertEq(vm.load(address(token), slot(7)), bytes32(uint256(uint160(address(0xCAFE)))));
    }

    // tama: mirrors=erc721_renounceOwnership_keeps_uint_storage
    function testFuzzRenounceOwnershipKeepsUintStorage() public {
        ERC721Iface token = deployToken();
        token.mint(address(this));
        token.renounceOwnership();
        assertEq(token.totalSupply(), 1);
    }

    // tama: mirrors=erc721_renounceOwnership_keeps_balances_and_allowances
    function testFuzzRenounceOwnershipKeepsBalancesAndAllowances(address approved, address operator) public {
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(address(this));
        token.approve(approved, tokenId);
        token.setApprovalForAll(operator, true);
        token.renounceOwnership();
        assertEq(token.balanceOf(address(this)), 1);
        assertEq(token.ownerOf(tokenId), address(this));
        assertEq(token.getApproved(tokenId), approved);
        assertTrue(token.isApprovedForAll(address(this), operator));
    }

    // tama: mirrors=erc721_renounceOwnership_keeps_array_storage
    function testFuzzRenounceOwnershipKeepsArrayStorage() public {
        ERC721Iface token = deployToken();
        bytes32 arraySlot = keccak256(abi.encode(uint256(7)));
        vm.store(address(token), arraySlot, bytes32(uint256(0x1234)));
        token.renounceOwnership();
        assertEq(vm.load(address(token), arraySlot), bytes32(uint256(0x1234)));
    }

    function testFuzzRenounceOwnershipEffect() public {
        ERC721Iface token = deployToken();
        vm.expectEmit(true, true, false, true, address(token));
        emit OwnershipTransferred(address(this), address(0));
        assertTrue(token.renounceOwnership());
        assertEq(token.owner(), address(0));
    }

    // tama: mirrors=erc721_balanceOf_spec
    function testFuzzBalanceOfSpec(address rawHolder) public {
        address holder = nonzero(rawHolder);
        ERC721Iface token = deployToken();
        token.mint(holder);
        assertEq(token.balanceOf(holder), 1);
    }

    // tama: mirrors=erc721_ownerOf_spec
    function testFuzzOwnerOfSpec(address rawHolder) public {
        address holder = nonzero(rawHolder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        assertEq(token.ownerOf(tokenId), holder);
    }

    // tama: mirrors=erc721_getApproved_spec
    function testFuzzGetApprovedSpec(address rawHolder, address approved) public {
        address holder = nonzero(rawHolder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(holder);
        token.approve(approved, tokenId);
        assertEq(token.getApproved(tokenId), approved);
    }

    // tama: mirrors=erc721_isApprovedForAll_spec
    function testFuzzIsApprovedForAllSpec(address operator, bool approved) public {
        ERC721Iface token = deployToken();
        token.setApprovalForAll(operator, approved);
        assertEq(token.isApprovedForAll(address(this), operator), approved);
    }

    // tama: mirrors=erc721_setApprovalForAll_succeeds
    function testFuzzSetApprovalForAllSucceeds(address operator, bool approved) public {
        ERC721Iface token = deployToken();
        assertTrue(token.setApprovalForAll(operator, approved));
    }

    // tama: mirrors=erc721_setApprovalForAll_sets_operator_flag
    function testFuzzSetApprovalForAllSetsOperatorFlag(address operator, bool approved) public {
        ERC721Iface token = deployToken();
        token.setApprovalForAll(operator, approved);
        assertEq(token.isApprovedForAll(address(this), operator), approved);
    }

    // tama: mirrors=erc721_setApprovalForAll_keeps_supply
    function testFuzzSetApprovalForAllKeepsSupply(address operator, bool approved) public {
        ERC721Iface token = deployToken();
        token.mint(address(this));
        token.setApprovalForAll(operator, approved);
        assertEq(token.totalSupply(), 1);
    }

    // tama: mirrors=erc721_setApprovalForAll_keeps_balances_and_owners
    function testFuzzSetApprovalForAllKeepsBalancesAndOwners(address rawHolder, address operator, bool approved) public {
        address holder = nonzero(rawHolder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        token.setApprovalForAll(operator, approved);
        assertEq(token.balanceOf(holder), 1);
        assertEq(token.ownerOf(tokenId), holder);
    }

    function testFuzzSetApprovalForAllEffect(address operator, bool approved) public {
        ERC721Iface token = deployToken();
        vm.expectEmit(true, true, false, true, address(token));
        emit ApprovalForAll(address(this), operator, approved);
        assertTrue(token.setApprovalForAll(operator, approved));
    }

    // tama: mirrors=erc721_approve_reverts_when_token_is_missing
    function testFuzzApproveRevertsWhenTokenIsMissing(uint256 tokenId, address approved) public {
        ERC721Iface token = deployToken();
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Token does not exist"));
        token.approve(approved, tokenId);
    }

    // tama: mirrors=erc721_approve_reverts_when_sender_is_not_authorized
    function testFuzzApproveRevertsWhenSenderIsNotAuthorized(address rawHolder, address rawAttacker, address approved) public {
        address holder = nonzero(rawHolder);
        address attacker = distinctNonzero(rawAttacker, holder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Not authorized"));
        token.approve(approved, tokenId);
    }

    // tama: mirrors=erc721_approve_succeeds_when_sender_is_authorized
    function testFuzzApproveSucceedsWhenSenderIsAuthorized(address rawHolder, address approved) public {
        address holder = nonzero(rawHolder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(holder);
        assertTrue(token.approve(approved, tokenId));
    }

    // tama: mirrors=erc721_approve_sets_token_approval
    function testFuzzApproveSetsTokenApproval(address rawHolder, address approved) public {
        address holder = nonzero(rawHolder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(holder);
        token.approve(approved, tokenId);
        assertEq(token.getApproved(tokenId), approved);
    }

    function testFuzzApproveEffect(address rawHolder, address approved) public {
        address holder = nonzero(rawHolder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.expectEmit(true, true, true, true, address(token));
        emit Approval(holder, approved, tokenId);
        vm.prank(holder);
        assertTrue(token.approve(approved, tokenId));
    }

    // tama: mirrors=erc721_mint_reverts_for_non_owner
    function testFuzzMintRevertsForNonOwner(address rawAttacker, address rawRecipient) public {
        address attacker = distinctNonzero(rawAttacker, address(this));
        address recipient = nonzero(rawRecipient);
        ERC721Iface token = deployToken();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.mint(recipient);
    }

    // tama: mirrors=erc721_mint_reverts_for_zero_recipient
    function testFuzzMintRevertsForZeroRecipient() public {
        ERC721Iface token = deployToken();
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Invalid recipient"));
        token.mint(address(0));
    }

    // tama: mirrors=erc721_mint_reverts_when_next_token_is_already_minted
    function testFuzzMintRevertsWhenNextTokenIsAlreadyMinted() public {
        ERC721Iface token = deployToken();
        token.mint(address(this));
        vm.store(address(token), slot(2), bytes32(uint256(0)));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Token already minted"));
        token.mint(address(this));
    }

    // tama: mirrors=erc721_mint_reverts_when_recipient_balance_would_overflow
    function testFuzzMintRevertsWhenRecipientBalanceWouldOverflow() public {
        ERC721Iface token = deployToken();
        vm.store(address(token), balanceSlot(address(this)), bytes32(type(uint256).max));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Balance overflow"));
        token.mint(address(this));
    }

    // tama: mirrors=erc721_mint_reverts_when_total_supply_would_overflow
    function testFuzzMintRevertsWhenTotalSupplyWouldOverflow() public {
        ERC721Iface token = deployToken();
        vm.store(address(token), slot(1), bytes32(type(uint256).max));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Supply overflow"));
        token.mint(address(this));
    }

    // tama: mirrors=erc721_mint_succeeds_with_next_token_id
    function testFuzzMintSucceedsWithNextTokenId(address rawRecipient) public {
        address recipient = nonzero(rawRecipient);
        ERC721Iface token = deployToken();
        assertEq(token.mint(recipient), 0);
    }

    // tama: mirrors=erc721_mint_assigns_next_token_to_recipient
    function testFuzzMintAssignsNextTokenToRecipient(address rawRecipient) public {
        address recipient = nonzero(rawRecipient);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(recipient);
        assertEq(token.ownerOf(tokenId), recipient);
    }

    // tama: mirrors=erc721_mint_credits_recipient_balance
    function testFuzzMintCreditsRecipientBalance(address rawRecipient) public {
        address recipient = nonzero(rawRecipient);
        ERC721Iface token = deployToken();
        token.mint(recipient);
        assertEq(token.balanceOf(recipient), 1);
    }

    // tama: mirrors=erc721_mint_increases_total_supply
    function testFuzzMintIncreasesTotalSupply(address rawRecipient) public {
        address recipient = nonzero(rawRecipient);
        ERC721Iface token = deployToken();
        token.mint(recipient);
        assertEq(token.totalSupply(), 1);
    }

    // tama: mirrors=erc721_mint_advances_next_token_id
    function testFuzzMintAdvancesNextTokenId() public {
        ERC721Iface token = deployToken();
        uint256 first = token.mint(address(this));
        uint256 second = token.mint(address(this));
        assertEq(first, 0);
        assertEq(second, 1);
    }

    function testFuzzMintEffect(address rawRecipient) public {
        address recipient = nonzero(rawRecipient);
        ERC721Iface token = deployToken();
        vm.expectEmit(true, true, true, true, address(token));
        emit Transfer(address(0), recipient, 0);
        assertEq(token.mint(recipient), 0);
    }

    // tama: mirrors=erc721_transferFrom_reverts_for_zero_recipient
    function testFuzzTransferFromRevertsForZeroRecipient(address rawHolder) public {
        address holder = nonzero(rawHolder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(holder);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Invalid recipient"));
        token.transferFrom(holder, address(0), tokenId);
    }

    // tama: mirrors=erc721_transferFrom_reverts_when_token_is_missing
    function testFuzzTransferFromRevertsWhenTokenIsMissing(address rawFrom, address rawRecipient, uint256 tokenId) public {
        address fromAddr = nonzero(rawFrom);
        address toAddr = distinctNonzero(rawRecipient, fromAddr);
        ERC721Iface token = deployToken();
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Token does not exist"));
        token.transferFrom(fromAddr, toAddr, tokenId);
    }

    // tama: mirrors=erc721_transferFrom_reverts_when_from_is_not_owner
    function testFuzzTransferFromRevertsWhenFromIsNotOwner(address rawHolder, address rawWrongFrom, address rawRecipient) public {
        address holder = nonzero(rawHolder);
        address wrongFrom = distinctNonzero(rawWrongFrom, holder);
        address toAddr = distinctNonzero(rawRecipient, holder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "From is not owner"));
        token.transferFrom(wrongFrom, toAddr, tokenId);
    }

    // tama: mirrors=erc721_transferFrom_reverts_when_sender_is_not_authorized
    function testFuzzTransferFromRevertsWhenSenderIsNotAuthorized(address rawHolder, address rawAttacker, address rawRecipient) public {
        address holder = nonzero(rawHolder);
        address attacker = distinctNonzero(rawAttacker, holder);
        address toAddr = distinctNonzero(rawRecipient, holder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Not authorized"));
        token.transferFrom(holder, toAddr, tokenId);
    }

    // tama: mirrors=erc721_transferFrom_to_self_succeeds
    function testFuzzTransferFromToSelfSucceeds(address rawHolder) public {
        address holder = nonzero(rawHolder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(holder);
        assertTrue(token.transferFrom(holder, holder, tokenId));
    }

    // tama: mirrors=erc721_transferFrom_to_self_keeps_balances
    function testFuzzTransferFromToSelfKeepsBalances(address rawHolder) public {
        address holder = nonzero(rawHolder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(holder);
        token.transferFrom(holder, holder, tokenId);
        assertEq(token.balanceOf(holder), 1);
    }

    // tama: mirrors=erc721_transferFrom_sets_owner_on_self_transfer
    function testFuzzTransferFromSetsOwnerOnSelfTransfer(address rawHolder) public {
        address holder = nonzero(rawHolder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(holder);
        token.transferFrom(holder, holder, tokenId);
        assertEq(token.ownerOf(tokenId), holder);
    }

    // tama: mirrors=erc721_transferFrom_clears_approval_on_self_transfer
    function testFuzzTransferFromClearsApprovalOnSelfTransfer(address rawHolder, address approved) public {
        address holder = nonzero(rawHolder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(holder);
        token.approve(approved, tokenId);
        vm.prank(holder);
        token.transferFrom(holder, holder, tokenId);
        assertEq(token.getApproved(tokenId), address(0));
    }

    // tama: mirrors=erc721_transferFrom_reverts_when_from_balance_is_low
    function testFuzzTransferFromRevertsWhenFromBalanceIsLow(address rawHolder, address rawRecipient) public {
        address holder = nonzero(rawHolder);
        address toAddr = distinctNonzero(rawRecipient, holder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.store(address(token), balanceSlot(holder), bytes32(uint256(0)));
        vm.prank(holder);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient balance"));
        token.transferFrom(holder, toAddr, tokenId);
    }

    // tama: mirrors=erc721_transferFrom_reverts_when_to_balance_would_overflow
    function testFuzzTransferFromRevertsWhenToBalanceWouldOverflow(address rawHolder, address rawRecipient) public {
        address holder = nonzero(rawHolder);
        address toAddr = distinctNonzero(rawRecipient, holder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.store(address(token), balanceSlot(toAddr), bytes32(type(uint256).max));
        vm.prank(holder);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Balance overflow"));
        token.transferFrom(holder, toAddr, tokenId);
    }

    // tama: mirrors=erc721_transferFrom_between_distinct_accounts_succeeds
    function testFuzzTransferFromBetweenDistinctAccountsSucceeds(address rawHolder, address rawRecipient) public {
        address holder = nonzero(rawHolder);
        address toAddr = distinctNonzero(rawRecipient, holder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(holder);
        assertTrue(token.transferFrom(holder, toAddr, tokenId));
    }

    // tama: mirrors=erc721_transferFrom_sets_new_owner
    function testFuzzTransferFromSetsNewOwner(address rawHolder, address rawRecipient) public {
        address holder = nonzero(rawHolder);
        address toAddr = distinctNonzero(rawRecipient, holder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(holder);
        token.transferFrom(holder, toAddr, tokenId);
        assertEq(token.ownerOf(tokenId), toAddr);
    }

    // tama: mirrors=erc721_transferFrom_clears_token_approval
    function testFuzzTransferFromClearsTokenApproval(address rawHolder, address rawRecipient, address approved) public {
        address holder = nonzero(rawHolder);
        address toAddr = distinctNonzero(rawRecipient, holder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(holder);
        token.approve(approved, tokenId);
        vm.prank(holder);
        token.transferFrom(holder, toAddr, tokenId);
        assertEq(token.getApproved(tokenId), address(0));
    }

    // tama: mirrors=erc721_transferFrom_debits_from_balance
    function testFuzzTransferFromDebitsFromBalance(address rawHolder, address rawRecipient) public {
        address holder = nonzero(rawHolder);
        address toAddr = distinctNonzero(rawRecipient, holder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(holder);
        token.transferFrom(holder, toAddr, tokenId);
        assertEq(token.balanceOf(holder), 0);
    }

    // tama: mirrors=erc721_transferFrom_credits_to_balance
    function testFuzzTransferFromCreditsToBalance(address rawHolder, address rawRecipient) public {
        address holder = nonzero(rawHolder);
        address toAddr = distinctNonzero(rawRecipient, holder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(holder);
        token.transferFrom(holder, toAddr, tokenId);
        assertEq(token.balanceOf(toAddr), 1);
    }

    function testFuzzTransferFromEffect(address rawHolder, address rawRecipient) public {
        address holder = nonzero(rawHolder);
        address toAddr = distinctNonzero(rawRecipient, holder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.expectEmit(true, true, true, true, address(token));
        emit Transfer(holder, toAddr, tokenId);
        vm.prank(holder);
        assertTrue(token.transferFrom(holder, toAddr, tokenId));
    }
}
