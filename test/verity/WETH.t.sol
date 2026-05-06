// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {WETHDeployer} from "../../src/generated/verity/WETHDeployer.sol";
import {WETHIface} from "../../src/generated/verity/WETHIface.sol";
import {Test} from "forge-std/Test.sol";

contract WETHTest is Test {
    receive() external payable {}

    function deployToken() internal returns (WETHIface token) {
        token = WETHDeployer.deploy();
    }

    // tama: mirrors=weth_deposit_effect,weth_totalSupply_spec,weth_balanceOf_spec
    function testFuzzDepositMintsWrappedEth(uint96 amount) public {
        WETHIface token = deployToken();
        assertTrue(token.deposit{value: amount}());
        assertEq(token.balanceOf(address(this)), amount);
        assertEq(token.totalSupply(), amount);
    }

    // tama: mirrors=weth_approve_effect,weth_allowance_spec
    function testFuzzApproveUpdatesAllowance(address spender, uint256 amount) public {
        WETHIface token = deployToken();
        assertTrue(token.approve(spender, amount));
        assertEq(token.allowance(address(this), spender), amount);
    }

    // tama: mirrors=weth_transfer_total_supply_preserved
    function testFuzzTransferPreservesSupply(address recipient, uint96 depositAmount, uint96 rawTransfer) public {
        WETHIface token = deployToken();
        assertTrue(token.deposit{value: depositAmount}());
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawTransfer) % (uint256(depositAmount) + 1);
        assertTrue(token.transfer(recipient, amount));
        assertEq(token.totalSupply(), depositAmount);
    }

    // tama: mirrors=weth_withdraw_effect
    function testFuzzWithdrawBurnsWrappedEth(uint96 depositAmount, uint96 rawWithdraw) public {
        WETHIface token = deployToken();
        assertTrue(token.deposit{value: depositAmount}());
        uint256 amount = depositAmount == 0 ? 0 : uint256(rawWithdraw) % (uint256(depositAmount) + 1);
        assertTrue(token.withdraw(amount));
        assertEq(token.balanceOf(address(this)), uint256(depositAmount) - amount);
        assertEq(token.totalSupply(), uint256(depositAmount) - amount);
    }

    // tama: mirrors=weth_withdraw_insufficient_no_change
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
