// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {ERC20Deployer} from "../../../src/generated/verity/ERC20Deployer.sol";
import {ERC20Iface} from "../../../src/generated/verity/ERC20Iface.sol";
import {Test} from "forge-std/Test.sol";

contract ERC20Test is Test {
    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);
    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    function deployToken() internal returns (ERC20Iface token) {
        token = ERC20Deployer.deploy(address(this));
    }

    function small(uint256 raw) internal pure returns (uint256) {
        return raw % 1e30;
    }

    function positive(uint256 raw) internal pure returns (uint256) {
        return (raw % 1e30) + 1;
    }

    function outsider(address account) internal view returns (address) {
        if (account == address(this) || account == address(0)) return address(0xBEEF);
        return account;
    }

    function recipient(address account) internal view returns (address) {
        if (account == address(this)) return address(0xCAFE);
        return account;
    }

    function balanceSlot(address account) internal pure returns (bytes32) {
        return keccak256(abi.encode(account, uint256(2)));
    }

    function supplySlot() internal pure returns (bytes32) {
        return bytes32(uint256(1));
    }

    function storageSlot(uint256 slot) internal pure returns (bytes32) {
        return bytes32(slot);
    }

    // tama: mirrors=erc20_decimals_spec
    function testFuzzDecimalsSpec() public {
        ERC20Iface token = deployToken();
        assertEq(token.decimals(), 18);
    }

    // tama: mirrors=erc20_totalSupply_spec
    function testFuzzTotalSupplySpec(uint256 rawAmount) public {
        ERC20Iface token = deployToken();
        uint256 amount = small(rawAmount);
        token.mint(address(this), amount);
        assertEq(token.totalSupply(), amount);
    }

    // tama: mirrors=erc20_balanceOf_spec
    function testFuzzBalanceOfSpec(address account, uint256 rawAmount) public {
        ERC20Iface token = deployToken();
        uint256 amount = small(rawAmount);
        token.mint(account, amount);
        assertEq(token.balanceOf(account), amount);
    }

    // tama: mirrors=erc20_allowance_spec
    function testFuzzAllowanceSpec(address spender, uint256 amount) public {
        ERC20Iface token = deployToken();
        token.approve(spender, amount);
        assertEq(token.allowance(address(this), spender), amount);
    }

    // tama: mirrors=erc20_owner_spec
    function testFuzzOwnerSpec() public {
        ERC20Iface token = deployToken();
        assertEq(token.owner(), address(this));
    }

    // tama: mirrors=erc20_transferOwnership_reverts_for_non_owner
    function testFuzzTransferOwnershipRevertsForNonOwner(address rawAttacker, address rawNewOwner) public {
        address attacker = outsider(rawAttacker);
        address newOwner = outsider(rawNewOwner);
        ERC20Iface token = deployToken();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.transferOwnership(newOwner);
    }

    // tama: mirrors=erc20_transferOwnership_reverts_for_zero_owner
    function testFuzzTransferOwnershipRevertsForZeroOwner() public {
        ERC20Iface token = deployToken();
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Invalid owner"));
        token.transferOwnership(address(0));
    }

    // tama: mirrors=erc20_transferOwnership_succeeds_for_owner_to_nonzero
    function testFuzzTransferOwnershipSucceedsForOwnerToNonzero(address rawNewOwner) public {
        address newOwner = outsider(rawNewOwner);
        ERC20Iface token = deployToken();
        assertTrue(token.transferOwnership(newOwner));
    }

    // tama: mirrors=erc20_transferOwnership_sets_new_owner
    function testFuzzTransferOwnershipSetsNewOwner(address rawNewOwner) public {
        address newOwner = outsider(rawNewOwner);
        ERC20Iface token = deployToken();
        token.transferOwnership(newOwner);
        assertEq(token.owner(), newOwner);
    }

    // tama: mirrors=erc20_transferOwnership_keeps_other_owner_slots
    function testFuzzTransferOwnershipKeepsOtherOwnerSlots(address rawNewOwner) public {
        address newOwner = outsider(rawNewOwner);
        ERC20Iface token = deployToken();
        vm.store(address(token), storageSlot(5), bytes32(uint256(uint160(address(0xCAFE)))));
        token.transferOwnership(newOwner);
        assertEq(vm.load(address(token), storageSlot(5)), bytes32(uint256(uint160(address(0xCAFE)))));
    }

    // tama: mirrors=erc20_transferOwnership_keeps_uint_storage
    function testFuzzTransferOwnershipKeepsUintStorage(address rawNewOwner, uint256 rawAmount) public {
        address newOwner = outsider(rawNewOwner);
        uint256 amount = small(rawAmount);
        ERC20Iface token = deployToken();
        token.mint(address(this), amount);
        token.transferOwnership(newOwner);
        assertEq(token.totalSupply(), amount);
    }

    // tama: mirrors=erc20_transferOwnership_keeps_balances_and_allowances
    function testFuzzTransferOwnershipKeepsBalancesAndAllowances(address rawNewOwner, address spender, uint256 rawAmount) public {
        address newOwner = outsider(rawNewOwner);
        uint256 amount = small(rawAmount);
        ERC20Iface token = deployToken();
        token.mint(address(this), amount);
        token.approve(spender, amount);
        token.transferOwnership(newOwner);
        assertEq(token.balanceOf(address(this)), amount);
        assertEq(token.allowance(address(this), spender), amount);
    }

    // tama: mirrors=erc20_transferOwnership_keeps_array_storage
    function testFuzzTransferOwnershipKeepsArrayStorage(address rawNewOwner) public {
        address newOwner = outsider(rawNewOwner);
        ERC20Iface token = deployToken();
        bytes32 arraySlot = keccak256(abi.encode(uint256(5)));
        vm.store(address(token), arraySlot, bytes32(uint256(0x1234)));
        token.transferOwnership(newOwner);
        assertEq(vm.load(address(token), arraySlot), bytes32(uint256(0x1234)));
    }

    function testFuzzTransferOwnershipEffect(address newOwner) public {
        newOwner = outsider(newOwner);
        ERC20Iface token = deployToken();
        vm.expectEmit(true, true, false, true, address(token));
        emit OwnershipTransferred(address(this), newOwner);
        assertTrue(token.transferOwnership(newOwner));
        assertEq(token.owner(), newOwner);
    }

    // tama: mirrors=erc20_renounceOwnership_reverts_for_non_owner
    function testFuzzRenounceOwnershipRevertsForNonOwner(address rawAttacker) public {
        address attacker = outsider(rawAttacker);
        ERC20Iface token = deployToken();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.renounceOwnership();
    }

    // tama: mirrors=erc20_renounceOwnership_succeeds_for_owner
    function testFuzzRenounceOwnershipSucceedsForOwner() public {
        ERC20Iface token = deployToken();
        assertTrue(token.renounceOwnership());
    }

    // tama: mirrors=erc20_renounceOwnership_clears_owner
    function testFuzzRenounceOwnershipClearsOwner() public {
        ERC20Iface token = deployToken();
        token.renounceOwnership();
        assertEq(token.owner(), address(0));
    }

    // tama: mirrors=erc20_renounceOwnership_keeps_other_owner_slots
    function testFuzzRenounceOwnershipKeepsOtherOwnerSlots() public {
        ERC20Iface token = deployToken();
        vm.store(address(token), storageSlot(5), bytes32(uint256(uint160(address(0xCAFE)))));
        token.renounceOwnership();
        assertEq(vm.load(address(token), storageSlot(5)), bytes32(uint256(uint160(address(0xCAFE)))));
    }

    // tama: mirrors=erc20_renounceOwnership_keeps_uint_storage
    function testFuzzRenounceOwnershipKeepsUintStorage(uint256 rawAmount) public {
        uint256 amount = small(rawAmount);
        ERC20Iface token = deployToken();
        token.mint(address(this), amount);
        token.renounceOwnership();
        assertEq(token.totalSupply(), amount);
    }

    // tama: mirrors=erc20_renounceOwnership_keeps_balances_and_allowances
    function testFuzzRenounceOwnershipKeepsBalancesAndAllowances(address spender, uint256 rawAmount) public {
        uint256 amount = small(rawAmount);
        ERC20Iface token = deployToken();
        token.mint(address(this), amount);
        token.approve(spender, amount);
        token.renounceOwnership();
        assertEq(token.balanceOf(address(this)), amount);
        assertEq(token.allowance(address(this), spender), amount);
    }

    // tama: mirrors=erc20_renounceOwnership_keeps_array_storage
    function testFuzzRenounceOwnershipKeepsArrayStorage() public {
        ERC20Iface token = deployToken();
        bytes32 arraySlot = keccak256(abi.encode(uint256(5)));
        vm.store(address(token), arraySlot, bytes32(uint256(0x1234)));
        token.renounceOwnership();
        assertEq(vm.load(address(token), arraySlot), bytes32(uint256(0x1234)));
    }

    function testFuzzRenounceOwnershipEffect() public {
        ERC20Iface token = deployToken();
        vm.expectEmit(true, true, false, true, address(token));
        emit OwnershipTransferred(address(this), address(0));
        assertTrue(token.renounceOwnership());
        assertEq(token.owner(), address(0));
    }

    // tama: mirrors=erc20_approve_succeeds
    function testFuzzApproveSucceeds(address spender, uint256 amount) public {
        ERC20Iface token = deployToken();
        assertTrue(token.approve(spender, amount));
    }

    // tama: mirrors=erc20_approve_sets_allowance
    function testFuzzApproveSetsAllowance(address spender, uint256 amount) public {
        ERC20Iface token = deployToken();
        token.approve(spender, amount);
        assertEq(token.allowance(address(this), spender), amount);
    }

    // tama: mirrors=erc20_approve_keeps_balances
    function testFuzzApproveKeepsBalances(address spender, uint256 rawAmount) public {
        ERC20Iface token = deployToken();
        uint256 amount = small(rawAmount);
        token.mint(address(this), amount);
        token.approve(spender, rawAmount);
        assertEq(token.balanceOf(address(this)), amount);
    }

    // tama: mirrors=erc20_approve_keeps_total_supply
    function testFuzzApproveKeepsTotalSupply(address spender, uint256 rawAmount) public {
        ERC20Iface token = deployToken();
        uint256 amount = small(rawAmount);
        token.mint(address(this), amount);
        token.approve(spender, rawAmount);
        assertEq(token.totalSupply(), amount);
    }

    function testFuzzApproveEffect(address spender, uint256 amount) public {
        ERC20Iface token = deployToken();
        vm.expectEmit(true, true, false, true, address(token));
        emit Approval(address(this), spender, amount);
        assertTrue(token.approve(spender, amount));
        assertEq(token.allowance(address(this), spender), amount);
    }

    // tama: mirrors=erc20_transfer_reverts_when_balance_is_low
    function testFuzzTransferRevertsWhenBalanceIsLow(address toAddr, uint256 rawAmount) public {
        ERC20Iface token = deployToken();
        uint256 amount = positive(rawAmount);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient balance"));
        token.transfer(toAddr, amount);
    }

    // tama: mirrors=erc20_transfer_to_self_keeps_balances
    function testFuzzTransferToSelfKeepsBalances(uint256 rawAmount) public {
        ERC20Iface token = deployToken();
        uint256 amount = small(rawAmount);
        token.mint(address(this), amount);
        assertTrue(token.transfer(address(this), amount));
        assertEq(token.balanceOf(address(this)), amount);
    }

    // tama: mirrors=erc20_transfer_reverts_when_recipient_balance_would_overflow
    function testFuzzTransferRevertsWhenRecipientBalanceWouldOverflow() public {
        ERC20Iface token = deployToken();
        address toAddr = address(0xCAFE);
        token.mint(address(this), 1);
        vm.store(address(token), balanceSlot(toAddr), bytes32(type(uint256).max));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Recipient balance overflow"));
        token.transfer(toAddr, 1);
    }

    // tama: mirrors=erc20_transfer_moves_tokens_between_distinct_accounts
    function testFuzzTransferMovesTokensBetweenDistinctAccounts(address rawRecipient, uint256 rawMint, uint256 rawTransfer) public {
        address toAddr = recipient(rawRecipient);
        ERC20Iface token = deployToken();
        uint256 minted = positive(rawMint);
        uint256 amount = rawTransfer % (minted + 1);
        token.mint(address(this), minted);
        uint256 recipientBefore = token.balanceOf(toAddr);
        assertTrue(token.transfer(toAddr, amount));
        assertEq(token.balanceOf(address(this)), minted - amount);
        assertEq(token.balanceOf(toAddr), recipientBefore + amount);
    }

    // tama: mirrors=erc20_transfer_keeps_total_supply
    function testFuzzTransferKeepsTotalSupply(address rawRecipient, uint256 rawMint, uint256 rawTransfer) public {
        address toAddr = recipient(rawRecipient);
        ERC20Iface token = deployToken();
        uint256 minted = positive(rawMint);
        uint256 amount = rawTransfer % (minted + 1);
        token.mint(address(this), minted);
        token.transfer(toAddr, amount);
        assertEq(token.totalSupply(), minted);
    }

    function testFuzzTransferBalancesEffect(address rawRecipient, uint256 rawMint, uint256 rawTransfer) public {
        address toAddr = recipient(rawRecipient);
        ERC20Iface token = deployToken();
        uint256 minted = positive(rawMint);
        uint256 amount = rawTransfer % (minted + 1);
        token.mint(address(this), minted);
        vm.expectEmit(true, true, false, true, address(token));
        emit Transfer(address(this), toAddr, amount);
        assertTrue(token.transfer(toAddr, amount));
    }

    // tama: mirrors=erc20_transferFrom_reverts_when_allowance_is_low
    function testFuzzTransferFromRevertsWhenAllowanceIsLow(address rawSpender, address toAddr, uint256 rawAmount) public {
        address spender = outsider(rawSpender);
        uint256 amount = positive(rawAmount);
        ERC20Iface token = deployToken();
        token.mint(address(this), amount);
        vm.prank(spender);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient allowance"));
        token.transferFrom(address(this), toAddr, amount);
    }

    // tama: mirrors=erc20_transferFrom_reverts_when_balance_is_low
    function testFuzzTransferFromRevertsWhenBalanceIsLow(address rawSpender, address toAddr, uint256 rawAmount) public {
        address spender = outsider(rawSpender);
        uint256 amount = positive(rawAmount);
        ERC20Iface token = deployToken();
        token.approve(spender, amount);
        vm.prank(spender);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient balance"));
        token.transferFrom(address(this), toAddr, amount);
    }

    // tama: mirrors=erc20_transferFrom_reverts_when_recipient_balance_would_overflow
    function testFuzzTransferFromRevertsWhenRecipientBalanceWouldOverflow(address rawSpender) public {
        address spender = outsider(rawSpender);
        address toAddr = address(0xCAFE);
        ERC20Iface token = deployToken();
        token.mint(address(this), 1);
        token.approve(spender, 1);
        vm.store(address(token), balanceSlot(toAddr), bytes32(type(uint256).max));
        vm.prank(spender);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Recipient balance overflow"));
        token.transferFrom(address(this), toAddr, 1);
    }

    // tama: mirrors=erc20_transferFrom_to_self_keeps_balances
    function testFuzzTransferFromToSelfKeepsBalances(address rawSpender, uint256 rawAmount) public {
        address spender = outsider(rawSpender);
        uint256 amount = small(rawAmount);
        ERC20Iface token = deployToken();
        token.mint(address(this), amount);
        token.approve(spender, amount);
        vm.prank(spender);
        assertTrue(token.transferFrom(address(this), address(this), amount));
        assertEq(token.balanceOf(address(this)), amount);
    }

    // tama: mirrors=erc20_transferFrom_moves_tokens_between_distinct_accounts
    function testFuzzTransferFromMovesTokensBetweenDistinctAccounts(address rawSpender, address rawRecipient, uint256 rawMint, uint256 rawSpend) public {
        address spender = outsider(rawSpender);
        address toAddr = recipient(rawRecipient);
        ERC20Iface token = deployToken();
        uint256 minted = positive(rawMint);
        uint256 amount = rawSpend % (minted + 1);
        token.mint(address(this), minted);
        token.approve(spender, minted);
        uint256 recipientBefore = token.balanceOf(toAddr);
        vm.prank(spender);
        assertTrue(token.transferFrom(address(this), toAddr, amount));
        assertEq(token.balanceOf(address(this)), minted - amount);
        assertEq(token.balanceOf(toAddr), recipientBefore + amount);
    }

    // tama: mirrors=erc20_transferFrom_keeps_total_supply
    function testFuzzTransferFromKeepsTotalSupply(address rawSpender, address rawRecipient, uint256 rawMint, uint256 rawSpend) public {
        address spender = outsider(rawSpender);
        address toAddr = recipient(rawRecipient);
        ERC20Iface token = deployToken();
        uint256 minted = positive(rawMint);
        uint256 amount = rawSpend % (minted + 1);
        token.mint(address(this), minted);
        token.approve(spender, minted);
        vm.prank(spender);
        token.transferFrom(address(this), toAddr, amount);
        assertEq(token.totalSupply(), minted);
    }

    // tama: mirrors=erc20_transferFrom_keeps_infinite_allowance
    function testFuzzTransferFromKeepsInfiniteAllowance(address rawSpender, address rawRecipient, uint256 rawMint, uint256 rawSpend) public {
        address spender = outsider(rawSpender);
        address toAddr = recipient(rawRecipient);
        ERC20Iface token = deployToken();
        uint256 minted = positive(rawMint);
        uint256 amount = rawSpend % (minted + 1);
        token.mint(address(this), minted);
        token.approve(spender, type(uint256).max);
        vm.prank(spender);
        token.transferFrom(address(this), toAddr, amount);
        assertEq(token.allowance(address(this), spender), type(uint256).max);
    }

    // tama: mirrors=erc20_transferFrom_spends_finite_allowance
    function testFuzzTransferFromSpendsFiniteAllowance(address rawSpender, address rawRecipient, uint256 rawMint, uint256 rawSpend) public {
        address spender = outsider(rawSpender);
        address toAddr = recipient(rawRecipient);
        ERC20Iface token = deployToken();
        uint256 minted = positive(rawMint);
        uint256 amount = rawSpend % (minted + 1);
        token.mint(address(this), minted);
        token.approve(spender, minted);
        vm.prank(spender);
        token.transferFrom(address(this), toAddr, amount);
        assertEq(token.allowance(address(this), spender), minted - amount);
    }

    function testFuzzTransferFromEffect(address rawSpender, address rawRecipient, uint256 rawMint, uint256 rawSpend) public {
        address spender = outsider(rawSpender);
        address toAddr = recipient(rawRecipient);
        ERC20Iface token = deployToken();
        uint256 minted = positive(rawMint);
        uint256 amount = rawSpend % (minted + 1);
        token.mint(address(this), minted);
        token.approve(spender, minted);
        vm.expectEmit(true, true, false, true, address(token));
        emit Transfer(address(this), toAddr, amount);
        vm.prank(spender);
        assertTrue(token.transferFrom(address(this), toAddr, amount));
    }

    // tama: mirrors=erc20_mint_reverts_for_non_owner
    function testFuzzMintRevertsForNonOwner(address rawAttacker, address account, uint256 amount) public {
        address attacker = outsider(rawAttacker);
        ERC20Iface token = deployToken();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.mint(account, amount);
    }

    // tama: mirrors=erc20_mint_reverts_when_recipient_balance_would_overflow
    function testFuzzMintRevertsWhenRecipientBalanceWouldOverflow() public {
        ERC20Iface token = deployToken();
        token.mint(address(this), type(uint256).max);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Balance overflow"));
        token.mint(address(this), 1);
    }

    // tama: mirrors=erc20_mint_reverts_when_total_supply_would_overflow
    function testFuzzMintRevertsWhenTotalSupplyWouldOverflow() public {
        ERC20Iface token = deployToken();
        token.mint(address(this), type(uint256).max);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Supply overflow"));
        token.mint(address(0xCAFE), 1);
    }

    // tama: mirrors=erc20_mint_succeeds_when_owner_and_no_overflow
    function testFuzzMintSucceedsWhenOwnerAndNoOverflow(address account, uint256 rawAmount) public {
        ERC20Iface token = deployToken();
        assertTrue(token.mint(account, small(rawAmount)));
    }

    // tama: mirrors=erc20_mint_credits_recipient
    function testFuzzMintCreditsRecipient(address account, uint256 rawAmount) public {
        ERC20Iface token = deployToken();
        uint256 amount = small(rawAmount);
        token.mint(account, amount);
        assertEq(token.balanceOf(account), amount);
    }

    // tama: mirrors=erc20_mint_increases_total_supply
    function testFuzzMintIncreasesTotalSupply(address account, uint256 rawAmount) public {
        ERC20Iface token = deployToken();
        uint256 amount = small(rawAmount);
        token.mint(account, amount);
        assertEq(token.totalSupply(), amount);
    }

    // tama: mirrors=erc20_mint_keeps_owner
    function testFuzzMintKeepsOwner(address account, uint256 rawAmount) public {
        ERC20Iface token = deployToken();
        token.mint(account, small(rawAmount));
        assertEq(token.owner(), address(this));
    }

    function testFuzzMintEffect(address account, uint256 rawAmount) public {
        ERC20Iface token = deployToken();
        uint256 amount = small(rawAmount);
        vm.expectEmit(true, true, false, true, address(token));
        emit Transfer(address(0), account, amount);
        assertTrue(token.mint(account, amount));
    }

    // tama: mirrors=erc20_burn_reverts_for_non_owner
    function testFuzzBurnRevertsForNonOwner(address rawAttacker, address account, uint256 rawAmount) public {
        address attacker = outsider(rawAttacker);
        ERC20Iface token = deployToken();
        uint256 amount = small(rawAmount);
        token.mint(account, amount);
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.burn(account, amount);
    }

    // tama: mirrors=erc20_burn_reverts_when_balance_is_low
    function testFuzzBurnRevertsWhenBalanceIsLow(address account, uint256 rawAmount) public {
        ERC20Iface token = deployToken();
        uint256 amount = positive(rawAmount);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient balance"));
        token.burn(account, amount);
    }

    // tama: mirrors=erc20_burn_reverts_when_total_supply_is_low
    function testFuzzBurnRevertsWhenTotalSupplyIsLow() public {
        ERC20Iface token = deployToken();
        address account = address(0xCAFE);
        vm.store(address(token), balanceSlot(account), bytes32(uint256(1)));
        vm.store(address(token), supplySlot(), bytes32(uint256(0)));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient supply"));
        token.burn(account, 1);
    }

    // tama: mirrors=erc20_burn_succeeds_when_owner_has_balance_and_supply
    function testFuzzBurnSucceedsWhenOwnerHasBalanceAndSupply(address account, uint256 rawMint, uint256 rawBurn) public {
        ERC20Iface token = deployToken();
        uint256 minted = positive(rawMint);
        uint256 amount = rawBurn % (minted + 1);
        token.mint(account, minted);
        assertTrue(token.burn(account, amount));
    }

    // tama: mirrors=erc20_burn_debits_account
    function testFuzzBurnDebitsAccount(address account, uint256 rawMint, uint256 rawBurn) public {
        ERC20Iface token = deployToken();
        uint256 minted = positive(rawMint);
        uint256 amount = rawBurn % (minted + 1);
        token.mint(account, minted);
        token.burn(account, amount);
        assertEq(token.balanceOf(account), minted - amount);
    }

    // tama: mirrors=erc20_burn_decreases_total_supply
    function testFuzzBurnDecreasesTotalSupply(address account, uint256 rawMint, uint256 rawBurn) public {
        ERC20Iface token = deployToken();
        uint256 minted = positive(rawMint);
        uint256 amount = rawBurn % (minted + 1);
        token.mint(account, minted);
        token.burn(account, amount);
        assertEq(token.totalSupply(), minted - amount);
    }

    function testFuzzBurnEffect(address account, uint256 rawMint, uint256 rawBurn) public {
        ERC20Iface token = deployToken();
        uint256 minted = positive(rawMint);
        uint256 amount = rawBurn % (minted + 1);
        token.mint(account, minted);
        vm.expectEmit(true, true, false, true, address(token));
        emit Transfer(account, address(0), amount);
        assertTrue(token.burn(account, amount));
    }
}
