// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {ERC20Deployer} from "../../src/generated/verity/ERC20Deployer.sol";
import {ERC20Iface} from "../../src/generated/verity/ERC20Iface.sol";
import {Test} from "forge-std/Test.sol";

contract ERC20Test is Test {
    function deployToken() internal returns (ERC20Iface token) {
        token = ERC20Deployer.deploy(address(this));
    }

    // tama: mirrors=erc20_decimals_spec,erc20_totalSupply_spec,erc20_owner_spec,erc20_balanceOf_spec,erc20_mint_effect
    function testFuzzMintAndViews(address account, uint256 rawAmount) public {
        ERC20Iface token = deployToken();
        uint256 amount = rawAmount % 1e30;
        assertEq(token.decimals(), 18);
        assertEq(token.owner(), address(this));
        assertEq(token.totalSupply(), 0);
        assertTrue(token.mint(account, amount));
        assertEq(token.balanceOf(account), amount);
        assertEq(token.totalSupply(), amount);
    }

    // tama: mirrors=erc20_approve_effect,erc20_allowance_spec
    function testFuzzApproveUpdatesAllowance(address spender, uint256 amount) public {
        ERC20Iface token = deployToken();
        assertTrue(token.approve(spender, amount));
        assertEq(token.allowance(address(this), spender), amount);
        assertEq(token.totalSupply(), 0);
    }

    // tama: mirrors=erc20_transfer_total_supply_preserved,erc20_transfer_balances_effect
    function testFuzzTransferMovesBalancesAndPreservesSupply(address recipient, uint256 rawMint, uint256 rawTransfer) public {
        ERC20Iface token = deployToken();
        uint256 minted = rawMint % 1e30;
        uint256 amount = minted == 0 ? 0 : rawTransfer % (minted + 1);
        assertTrue(token.mint(address(this), minted));
        uint256 recipientBefore = token.balanceOf(recipient);
        assertTrue(token.transfer(recipient, amount));
        if (recipient == address(this)) {
            assertEq(token.balanceOf(address(this)), minted);
        } else {
            assertEq(token.balanceOf(address(this)), minted - amount);
            assertEq(token.balanceOf(recipient), recipientBefore + amount);
        }
        assertEq(token.totalSupply(), minted);
    }

    // tama: mirrors=erc20_transferFrom_total_supply_preserved,erc20_transferFrom_allowance_effect
    function testFuzzTransferFromUpdatesAllowance(address spender, address recipient, uint256 rawMint, uint256 rawSpend) public {
        vm.assume(spender != address(this));
        ERC20Iface token = deployToken();
        uint256 minted = rawMint % 1e30;
        uint256 amount = minted == 0 ? 0 : rawSpend % (minted + 1);
        assertTrue(token.mint(address(this), minted));
        assertTrue(token.approve(spender, minted));
        vm.prank(spender);
        assertTrue(token.transferFrom(address(this), recipient, amount));
        assertEq(token.allowance(address(this), spender), minted - amount);
        assertEq(token.totalSupply(), minted);
    }

    // tama: mirrors=erc20_transferFrom_allowance_effect
    function testFuzzTransferFromKeepsInfiniteAllowance(address spender, address recipient, uint256 rawMint, uint256 rawSpend) public {
        vm.assume(spender != address(this));
        ERC20Iface token = deployToken();
        uint256 minted = rawMint % 1e30;
        uint256 amount = minted == 0 ? 0 : rawSpend % (minted + 1);
        assertTrue(token.mint(address(this), minted));
        assertTrue(token.approve(spender, type(uint256).max));
        vm.prank(spender);
        assertTrue(token.transferFrom(address(this), recipient, amount));
        assertEq(token.allowance(address(this), spender), type(uint256).max);
    }

    // tama: mirrors=erc20_mint_unauthorized_no_change
    function testFuzzMintUnauthorizedReverts(address attacker, address account, uint256 amount) public {
        vm.assume(attacker != address(this));
        ERC20Iface token = deployToken();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.mint(account, amount);
        assertEq(token.balanceOf(account), 0);
        assertEq(token.totalSupply(), 0);
    }

    // tama: mirrors=erc20_burn_effect,erc20_burn_unauthorized_no_change
    function testFuzzBurnOwnerOnly(address account, address attacker, uint256 rawMint, uint256 rawBurn) public {
        vm.assume(attacker != address(this));
        ERC20Iface token = deployToken();
        uint256 minted = rawMint % 1e30;
        uint256 amount = minted == 0 ? 0 : rawBurn % (minted + 1);
        assertTrue(token.mint(account, minted));
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.burn(account, amount);
        assertTrue(token.burn(account, amount));
        assertEq(token.balanceOf(account), minted - amount);
        assertEq(token.totalSupply(), minted - amount);
    }
}
