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

    // tama: mirrors=weth_decimals_spec,weth_deposit_effect,weth_totalSupply_spec,weth_balanceOf_spec
    function testFuzzDepositMintsWrappedEth(uint96 amount) public {
        WETHIface token = deployToken();
        assertEq(token.decimals(), 18);
        vm.expectEmit(true, true, false, true, address(token));
        emit Transfer(address(0), address(this), amount);
        vm.expectEmit(true, false, false, true, address(token));
        emit Deposit(address(this), amount);
        assertTrue(token.deposit{value: amount}());
        assertEq(token.balanceOf(address(this)), amount);
        assertEq(token.totalSupply(), amount);
    }

    // tama: mirrors=weth_approve_effect,weth_allowance_spec
    function testFuzzApproveUpdatesAllowance(address spender, uint256 amount) public {
        WETHIface token = deployToken();
        vm.expectEmit(true, true, false, true, address(token));
        emit Approval(address(this), spender, amount);
        assertTrue(token.approve(spender, amount));
        assertEq(token.allowance(address(this), spender), amount);
    }

    // tama: mirrors=weth_transfer_balances_effect
    function testFuzzTransferPreservesSupply(address recipient, uint96 depositAmount, uint96 rawTransfer) public {
        WETHIface token = deployToken();
        assertTrue(token.deposit{value: depositAmount}());
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawTransfer) % (uint256(depositAmount) + 1);
        uint256 recipientBefore = token.balanceOf(recipient);
        vm.expectEmit(true, true, false, true, address(token));
        emit Transfer(address(this), recipient, amount);
        assertTrue(token.transfer(recipient, amount));
        if (recipient == address(this)) {
            assertEq(token.balanceOf(address(this)), depositAmount);
        } else {
            assertEq(token.balanceOf(address(this)), uint256(depositAmount) - amount);
            assertEq(token.balanceOf(recipient), recipientBefore + amount);
        }
        assertEq(token.totalSupply(), depositAmount);
    }

    // tama: mirrors=weth_transferFrom_effect
    function testFuzzTransferFromUpdatesAllowance(address spender, address recipient, uint96 depositAmount, uint96 rawSpend) public {
        vm.assume(spender != address(this));
        WETHIface token = deployToken();
        assertTrue(token.deposit{value: depositAmount}());
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawSpend) % (uint256(depositAmount) + 1);
        assertTrue(token.approve(spender, depositAmount));
        vm.expectEmit(true, true, false, true, address(token));
        emit Transfer(address(this), recipient, amount);
        vm.prank(spender);
        assertTrue(token.transferFrom(address(this), recipient, amount));
        assertEq(token.allowance(address(this), spender), uint256(depositAmount) - amount);
        assertEq(token.totalSupply(), depositAmount);
    }

    // tama: mirrors=weth_withdraw_effect
    function testFuzzWithdrawBurnsWrappedEth(uint96 depositAmount, uint96 rawWithdraw) public {
        WETHIface token = deployToken();
        assertTrue(token.deposit{value: depositAmount}());
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawWithdraw) % (uint256(depositAmount) + 1);
        vm.expectEmit(true, true, false, true, address(token));
        emit Transfer(address(this), address(0), amount);
        vm.expectEmit(true, false, false, true, address(token));
        emit Withdrawal(address(this), amount);
        assertTrue(token.withdraw(amount));
        assertEq(token.balanceOf(address(this)), uint256(depositAmount) - amount);
        assertEq(token.totalSupply(), uint256(depositAmount) - amount);
    }

    // tama: mirrors=weth_withdraw_effect
    function testFuzzWithdrawInsufficientReverts(uint96 depositAmount, uint96 extra) public {
        WETHIface token = deployToken();
        assertTrue(token.deposit{value: depositAmount}());
        uint256 amount = uint256(depositAmount) + uint256(extra) + 1;
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient balance"));
        token.withdraw(amount);
        assertEq(token.balanceOf(address(this)), depositAmount);
        assertEq(token.totalSupply(), depositAmount);
    }
}
