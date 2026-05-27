// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {WETHDeployer} from "../../../src/generated/verity/WETHDeployer.sol";
import {WETHIface} from "../../../src/generated/verity/WETHIface.sol";
import {Test} from "forge-std/Test.sol";

contract WETHTest is Test {
    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);
    event Deposit(address indexed dst, uint256 wad);
    event Withdrawal(address indexed src, uint256 wad);

    receive() external payable {}

    function deployToken() internal returns (WETHIface token) {
        token = WETHDeployer.deploy();
    }

    function positive(uint96 raw) internal pure returns (uint256) {
        return uint256(raw) + 1;
    }

    function recipient(address account) internal view returns (address) {
        if (account == address(this)) return address(0xCAFE);
        return account;
    }

    function outsider(address account) internal view returns (address) {
        if (account == address(this) || account == address(0)) return address(0xBEEF);
        return account;
    }

    function balanceSlot(address account) internal pure returns (bytes32) {
        return keccak256(abi.encode(account, uint256(2)));
    }

    function supplySlot() internal pure returns (bytes32) {
        return bytes32(uint256(1));
    }

    // tama: mirrors=weth_decimals_spec
    function testFuzzDecimalsSpec() public {
        WETHIface token = deployToken();
        assertEq(token.decimals(), 18);
    }

    // tama: mirrors=weth_totalSupply_spec
    function testFuzzTotalSupplySpec(uint96 amount) public {
        WETHIface token = deployToken();
        token.deposit{value: amount}();
        assertEq(token.totalSupply(), amount);
    }

    // tama: mirrors=weth_balanceOf_spec
    function testFuzzBalanceOfSpec(uint96 amount) public {
        WETHIface token = deployToken();
        token.deposit{value: amount}();
        assertEq(token.balanceOf(address(this)), amount);
    }

    // tama: mirrors=weth_allowance_spec
    function testFuzzAllowanceSpec(address spender, uint256 amount) public {
        WETHIface token = deployToken();
        token.approve(spender, amount);
        assertEq(token.allowance(address(this), spender), amount);
    }

    // tama: mirrors=weth_approve_succeeds
    function testFuzzApproveSucceeds(address spender, uint256 amount) public {
        WETHIface token = deployToken();
        assertTrue(token.approve(spender, amount));
    }

    // tama: mirrors=weth_approve_sets_allowance
    function testFuzzApproveSetsAllowance(address spender, uint256 amount) public {
        WETHIface token = deployToken();
        token.approve(spender, amount);
        assertEq(token.allowance(address(this), spender), amount);
    }

    // tama: mirrors=weth_approve_keeps_balances
    function testFuzzApproveKeepsBalances(address spender, uint96 amount, uint256 approval) public {
        WETHIface token = deployToken();
        token.deposit{value: amount}();
        token.approve(spender, approval);
        assertEq(token.balanceOf(address(this)), amount);
    }

    // tama: mirrors=weth_approve_keeps_total_supply
    function testFuzzApproveKeepsTotalSupply(address spender, uint96 amount, uint256 approval) public {
        WETHIface token = deployToken();
        token.deposit{value: amount}();
        token.approve(spender, approval);
        assertEq(token.totalSupply(), amount);
    }

    function testFuzzApproveEffect(address spender, uint256 amount) public {
        WETHIface token = deployToken();
        vm.expectEmit(true, true, false, true, address(token));
        emit Approval(address(this), spender, amount);
        assertTrue(token.approve(spender, amount));
    }

    // tama: mirrors=weth_transfer_reverts_when_balance_is_low
    function testFuzzTransferRevertsWhenBalanceIsLow(address toAddr, uint96 rawAmount) public {
        WETHIface token = deployToken();
        uint256 amount = positive(rawAmount);
        vm.expectRevert(abi.encodeWithSelector(bytes4(keccak256("InsufficientBalance()"))));
        token.transfer(toAddr, amount);
    }

    // tama: mirrors=weth_transfer_to_self_keeps_balances
    function testFuzzTransferToSelfKeepsBalances(uint96 amount) public {
        WETHIface token = deployToken();
        token.deposit{value: amount}();
        assertTrue(token.transfer(address(this), amount));
        assertEq(token.balanceOf(address(this)), amount);
    }

    // tama: mirrors=weth_transfer_reverts_when_recipient_balance_would_overflow
    function testFuzzTransferRevertsWhenRecipientBalanceWouldOverflow() public {
        WETHIface token = deployToken();
        address toAddr = address(0xCAFE);
        token.deposit{value: 1}();
        vm.store(address(token), balanceSlot(toAddr), bytes32(type(uint256).max));
        vm.expectRevert(abi.encodeWithSelector(bytes4(keccak256("BalanceOverflow()"))));
        token.transfer(toAddr, 1);
    }

    // tama: mirrors=weth_transfer_moves_tokens_between_distinct_accounts
    function testFuzzTransferMovesTokensBetweenDistinctAccounts(address rawRecipient, uint96 depositAmount, uint96 rawTransfer) public {
        address toAddr = recipient(rawRecipient);
        WETHIface token = deployToken();
        token.deposit{value: depositAmount}();
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawTransfer) % (uint256(depositAmount) + 1);
        uint256 recipientBefore = token.balanceOf(toAddr);
        assertTrue(token.transfer(toAddr, amount));
        assertEq(token.balanceOf(address(this)), uint256(depositAmount) - amount);
        assertEq(token.balanceOf(toAddr), recipientBefore + amount);
    }

    // tama: mirrors=weth_transfer_keeps_total_supply
    function testFuzzTransferKeepsTotalSupply(address rawRecipient, uint96 depositAmount, uint96 rawTransfer) public {
        address toAddr = recipient(rawRecipient);
        WETHIface token = deployToken();
        token.deposit{value: depositAmount}();
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawTransfer) % (uint256(depositAmount) + 1);
        token.transfer(toAddr, amount);
        assertEq(token.totalSupply(), depositAmount);
    }

    // tama: mirrors=weth_transferFrom_reverts_when_allowance_is_low
    function testFuzzTransferFromRevertsWhenAllowanceIsLow(address rawSpender, address toAddr, uint96 rawAmount) public {
        address spender = outsider(rawSpender);
        uint256 amount = rawAmount == 0 ? 1 : uint256(rawAmount);
        WETHIface token = deployToken();
        token.deposit{value: amount}();
        vm.prank(spender);
        vm.expectRevert(abi.encodeWithSelector(bytes4(keccak256("InsufficientAllowance()"))));
        token.transferFrom(address(this), toAddr, amount);
    }

    // tama: mirrors=weth_transferFrom_reverts_when_balance_is_low
    function testFuzzTransferFromRevertsWhenBalanceIsLow(address rawSpender, address toAddr, uint96 rawAmount) public {
        address spender = outsider(rawSpender);
        uint256 amount = positive(rawAmount);
        WETHIface token = deployToken();
        token.approve(spender, amount);
        vm.prank(spender);
        vm.expectRevert(abi.encodeWithSelector(bytes4(keccak256("InsufficientBalance()"))));
        token.transferFrom(address(this), toAddr, amount);
    }

    // tama: mirrors=weth_transferFrom_reverts_when_recipient_balance_would_overflow
    function testFuzzTransferFromRevertsWhenRecipientBalanceWouldOverflow(address rawSpender) public {
        address spender = outsider(rawSpender);
        address toAddr = address(0xCAFE);
        WETHIface token = deployToken();
        token.deposit{value: 1}();
        token.approve(spender, 1);
        vm.store(address(token), balanceSlot(toAddr), bytes32(type(uint256).max));
        vm.prank(spender);
        vm.expectRevert(abi.encodeWithSelector(bytes4(keccak256("BalanceOverflow()"))));
        token.transferFrom(address(this), toAddr, 1);
    }

    // tama: mirrors=weth_transferFrom_to_self_keeps_balances
    function testFuzzTransferFromToSelfKeepsBalances(address rawSpender, uint96 amount) public {
        address spender = outsider(rawSpender);
        WETHIface token = deployToken();
        token.deposit{value: amount}();
        token.approve(spender, amount);
        vm.prank(spender);
        assertTrue(token.transferFrom(address(this), address(this), amount));
        assertEq(token.balanceOf(address(this)), amount);
    }

    // tama: mirrors=weth_transferFrom_moves_tokens_between_distinct_accounts
    function testFuzzTransferFromMovesTokensBetweenDistinctAccounts(address rawSpender, address rawRecipient, uint96 depositAmount, uint96 rawSpend) public {
        address spender = outsider(rawSpender);
        address toAddr = recipient(rawRecipient);
        WETHIface token = deployToken();
        token.deposit{value: depositAmount}();
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawSpend) % (uint256(depositAmount) + 1);
        token.approve(spender, depositAmount);
        uint256 recipientBefore = token.balanceOf(toAddr);
        vm.prank(spender);
        assertTrue(token.transferFrom(address(this), toAddr, amount));
        assertEq(token.balanceOf(address(this)), uint256(depositAmount) - amount);
        assertEq(token.balanceOf(toAddr), recipientBefore + amount);
    }

    // tama: mirrors=weth_transferFrom_keeps_total_supply
    function testFuzzTransferFromKeepsTotalSupply(address rawSpender, address rawRecipient, uint96 depositAmount, uint96 rawSpend) public {
        address spender = outsider(rawSpender);
        address toAddr = recipient(rawRecipient);
        WETHIface token = deployToken();
        token.deposit{value: depositAmount}();
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawSpend) % (uint256(depositAmount) + 1);
        token.approve(spender, depositAmount);
        vm.prank(spender);
        token.transferFrom(address(this), toAddr, amount);
        assertEq(token.totalSupply(), depositAmount);
    }

    // tama: mirrors=weth_transferFrom_keeps_infinite_allowance
    function testFuzzTransferFromKeepsInfiniteAllowance(address rawSpender, address rawRecipient, uint96 depositAmount, uint96 rawSpend) public {
        address spender = outsider(rawSpender);
        address toAddr = recipient(rawRecipient);
        WETHIface token = deployToken();
        token.deposit{value: depositAmount}();
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawSpend) % (uint256(depositAmount) + 1);
        token.approve(spender, type(uint256).max);
        vm.prank(spender);
        token.transferFrom(address(this), toAddr, amount);
        assertEq(token.allowance(address(this), spender), type(uint256).max);
    }

    // tama: mirrors=weth_transferFrom_spends_finite_allowance
    function testFuzzTransferFromSpendsFiniteAllowance(address rawSpender, address rawRecipient, uint96 depositAmount, uint96 rawSpend) public {
        address spender = outsider(rawSpender);
        address toAddr = recipient(rawRecipient);
        WETHIface token = deployToken();
        token.deposit{value: depositAmount}();
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawSpend) % (uint256(depositAmount) + 1);
        token.approve(spender, depositAmount);
        vm.prank(spender);
        token.transferFrom(address(this), toAddr, amount);
        assertEq(token.allowance(address(this), spender), uint256(depositAmount) - amount);
    }

    // tama: mirrors=weth_deposit_reverts_when_sender_balance_would_overflow
    function testFuzzDepositRevertsWhenSenderBalanceWouldOverflow() public {
        WETHIface token = deployToken();
        vm.deal(address(this), 1);
        vm.store(address(token), balanceSlot(address(this)), bytes32(type(uint256).max));
        vm.expectRevert(abi.encodeWithSelector(bytes4(keccak256("BalanceOverflow()"))));
        token.deposit{value: 1}();
    }

    // tama: mirrors=weth_deposit_reverts_when_total_supply_would_overflow
    function testFuzzDepositRevertsWhenTotalSupplyWouldOverflow() public {
        WETHIface token = deployToken();
        vm.deal(address(this), 1);
        vm.store(address(token), supplySlot(), bytes32(type(uint256).max));
        vm.expectRevert(abi.encodeWithSelector(bytes4(keccak256("TotalSupplyOverflow()"))));
        token.deposit{value: 1}();
    }

    // tama: mirrors=weth_deposit_succeeds_when_accounting_does_not_overflow
    function testFuzzDepositSucceedsWhenAccountingDoesNotOverflow(uint96 amount) public {
        WETHIface token = deployToken();
        assertTrue(token.deposit{value: amount}());
    }

    // tama: mirrors=weth_deposit_credits_sender
    function testFuzzDepositCreditsSender(uint96 amount) public {
        WETHIface token = deployToken();
        token.deposit{value: amount}();
        assertEq(token.balanceOf(address(this)), amount);
    }

    // tama: mirrors=weth_deposit_increases_total_supply
    function testFuzzDepositIncreasesTotalSupply(uint96 amount) public {
        WETHIface token = deployToken();
        token.deposit{value: amount}();
        assertEq(token.totalSupply(), amount);
    }

    // tama: mirrors=weth_deposit_preserves_native_backing
    function testFuzzDepositPreservesNativeBacking(uint96 amount) public {
        WETHIface token = deployToken();
        uint256 contractBalanceBefore = address(token).balance;
        assertTrue(token.deposit{value: amount}());
        assertEq(address(token).balance, contractBalanceBefore + amount);
        assertEq(address(token).balance, token.totalSupply());
    }

    function testFuzzDepositEffect(uint96 amount) public {
        WETHIface token = deployToken();
        vm.expectEmit(true, true, false, true, address(token));
        emit Transfer(address(0), address(this), amount);
        vm.expectEmit(true, false, false, true, address(token));
        emit Deposit(address(this), amount);
        assertTrue(token.deposit{value: amount}());
    }

    function testFuzzTransferBalancesEffect(address rawRecipient, uint96 depositAmount, uint96 rawTransfer) public {
        address toAddr = recipient(rawRecipient);
        WETHIface token = deployToken();
        token.deposit{value: depositAmount}();
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawTransfer) % (uint256(depositAmount) + 1);
        vm.expectEmit(true, true, false, true, address(token));
        emit Transfer(address(this), toAddr, amount);
        assertTrue(token.transfer(toAddr, amount));
    }

    function testFuzzTransferFromEffect(address rawSpender, address rawRecipient, uint96 depositAmount, uint96 rawSpend) public {
        address spender = outsider(rawSpender);
        address toAddr = recipient(rawRecipient);
        WETHIface token = deployToken();
        token.deposit{value: depositAmount}();
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawSpend) % (uint256(depositAmount) + 1);
        token.approve(spender, depositAmount);
        vm.expectEmit(true, true, false, true, address(token));
        emit Transfer(address(this), toAddr, amount);
        vm.prank(spender);
        assertTrue(token.transferFrom(address(this), toAddr, amount));
    }

    // tama: mirrors=weth_withdraw_reverts_when_balance_is_low
    function testFuzzWithdrawRevertsWhenBalanceIsLow(uint96 rawAmount) public {
        WETHIface token = deployToken();
        uint256 amount = positive(rawAmount);
        vm.expectRevert(abi.encodeWithSelector(bytes4(keccak256("InsufficientBalance()"))));
        token.withdraw(amount);
    }

    // tama: mirrors=weth_withdraw_reverts_when_total_supply_is_low
    function testFuzzWithdrawRevertsWhenTotalSupplyIsLow() public {
        WETHIface token = deployToken();
        vm.store(address(token), balanceSlot(address(this)), bytes32(uint256(1)));
        vm.store(address(token), supplySlot(), bytes32(uint256(0)));
        vm.expectRevert(abi.encodeWithSelector(bytes4(keccak256("InsufficientSupply()"))));
        token.withdraw(1);
    }

    // tama: mirrors=weth_withdraw_reverts_when_eth_backing_is_low
    function testFuzzWithdrawRevertsWhenEthBackingIsLow() public {
        WETHIface token = deployToken();
        vm.store(address(token), balanceSlot(address(this)), bytes32(uint256(1)));
        vm.store(address(token), supplySlot(), bytes32(uint256(1)));
        vm.expectRevert(abi.encodeWithSelector(bytes4(keccak256("InsufficientEthBacking()"))));
        token.withdraw(1);
    }

    // tama: mirrors=weth_withdraw_reverts_when_native_transfer_fails
    function testFuzzWithdrawRevertsWhenNativeTransferFails() public {
        WETHIface token = deployToken();
        RejectsEth receiver = new RejectsEth();
        vm.deal(address(receiver), 1);
        vm.prank(address(receiver));
        token.deposit{value: 1}();
        vm.expectRevert(abi.encodeWithSelector(bytes4(keccak256("EthTransferFailed()"))));
        vm.prank(address(receiver));
        token.withdraw(1);
    }

    // tama: mirrors=weth_withdraw_succeeds_when_balance_supply_eth_and_transfer_are_enough
    function testFuzzWithdrawSucceedsWhenBalanceSupplyEthAndTransferAreEnough(uint96 depositAmount, uint96 rawWithdraw) public {
        WETHIface token = deployToken();
        token.deposit{value: depositAmount}();
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawWithdraw) % (uint256(depositAmount) + 1);
        assertTrue(token.withdraw(amount));
    }

    // tama: mirrors=weth_withdraw_debits_sender
    function testFuzzWithdrawDebitsSender(uint96 depositAmount, uint96 rawWithdraw) public {
        WETHIface token = deployToken();
        token.deposit{value: depositAmount}();
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawWithdraw) % (uint256(depositAmount) + 1);
        token.withdraw(amount);
        assertEq(token.balanceOf(address(this)), uint256(depositAmount) - amount);
    }

    // tama: mirrors=weth_withdraw_decreases_total_supply
    function testFuzzWithdrawDecreasesTotalSupply(uint96 depositAmount, uint96 rawWithdraw) public {
        WETHIface token = deployToken();
        token.deposit{value: depositAmount}();
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawWithdraw) % (uint256(depositAmount) + 1);
        token.withdraw(amount);
        assertEq(token.totalSupply(), uint256(depositAmount) - amount);
    }

    // tama: mirrors=weth_withdraw_decreases_native_balance
    function testFuzzWithdrawDecreasesNativeBalance(uint96 depositAmount, uint96 rawWithdraw) public {
        WETHIface token = deployToken();
        token.deposit{value: depositAmount}();
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawWithdraw) % (uint256(depositAmount) + 1);
        uint256 contractBalanceBefore = address(token).balance;
        token.withdraw(amount);
        assertEq(address(token).balance + amount, contractBalanceBefore);
    }

    // tama: mirrors=weth_withdraw_preserves_native_backing
    function testFuzzWithdrawPreservesNativeBacking(uint96 depositAmount, uint96 rawWithdraw) public {
        WETHIface token = deployToken();
        token.deposit{value: depositAmount}();
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawWithdraw) % (uint256(depositAmount) + 1);
        assertTrue(token.withdraw(amount));
        assertGe(address(token).balance, token.totalSupply());
    }

    function testFuzzWithdrawTransfersEthToSender(uint96 depositAmount, uint96 rawWithdraw) public {
        WETHIface token = deployToken();
        token.deposit{value: depositAmount}();
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawWithdraw) % (uint256(depositAmount) + 1);
        uint256 senderBalanceBefore = address(this).balance;
        token.withdraw(amount);
        assertEq(address(this).balance, senderBalanceBefore + amount);
    }

    function testFuzzWithdrawEffect(uint96 depositAmount, uint96 rawWithdraw) public {
        WETHIface token = deployToken();
        token.deposit{value: depositAmount}();
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawWithdraw) % (uint256(depositAmount) + 1);
        vm.expectEmit(true, true, false, true, address(token));
        emit Transfer(address(this), address(0), amount);
        vm.expectEmit(true, false, false, true, address(token));
        emit Withdrawal(address(this), amount);
        assertTrue(token.withdraw(amount));
    }
}

contract RejectsEth {}
