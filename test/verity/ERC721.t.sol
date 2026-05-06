// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {ERC721Deployer} from "../../src/generated/verity/ERC721Deployer.sol";
import {ERC721Iface} from "../../src/generated/verity/ERC721Iface.sol";
import {Test} from "forge-std/Test.sol";

contract ERC721Test is Test {
    function deployToken() internal returns (ERC721Iface token) {
        token = ERC721Deployer.deploy(address(this));
    }

    // tama: mirrors=erc721_totalSupply_spec,erc721_owner_spec,erc721_balanceOf_spec,erc721_ownerOf_spec,erc721_mint_effect
    function testFuzzMintAndViews(address recipient) public {
        vm.assume(recipient != address(0));
        ERC721Iface token = deployToken();
        assertEq(token.owner(), address(this));
        assertEq(token.totalSupply(), 0);
        uint256 tokenId = token.mint(recipient);
        assertEq(tokenId, 0);
        assertEq(token.ownerOf(tokenId), recipient);
        assertEq(token.balanceOf(recipient), 1);
        assertEq(token.totalSupply(), 1);
    }

    // tama: mirrors=erc721_getApproved_spec,erc721_approve_effect
    function testFuzzApproveToken(address holder, address approved) public {
        vm.assume(holder != address(0));
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(holder);
        assertTrue(token.approve(approved, tokenId));
        assertEq(token.getApproved(tokenId), approved);
    }

    // tama: mirrors=erc721_isApprovedForAll_spec,erc721_setApprovalForAll_effect
    function testFuzzSetApprovalForAll(address operator, bool approved) public {
        ERC721Iface token = deployToken();
        assertTrue(token.setApprovalForAll(operator, approved));
        assertEq(token.isApprovedForAll(address(this), operator), approved);
    }

    // tama: mirrors=erc721_ownerOf_spec,erc721_getApproved_spec
    function testFuzzMissingTokenViewsRevert(uint256 tokenId) public {
        ERC721Iface token = deployToken();
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Token does not exist"));
        token.ownerOf(tokenId);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Token does not exist"));
        token.getApproved(tokenId);
    }

    // tama: mirrors=erc721_mint_unauthorized_no_change
    function testFuzzMintUnauthorizedReverts(address attacker, address recipient) public {
        vm.assume(attacker != address(this));
        vm.assume(recipient != address(0));
        ERC721Iface token = deployToken();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.mint(recipient);
        assertEq(token.totalSupply(), 0);
    }

    // tama: mirrors=erc721_transferFrom_zero_recipient_no_change
    function testFuzzTransferToZeroRevertsWithoutChangingOwner(address recipient) public {
        vm.assume(recipient != address(0));
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(recipient);
        vm.prank(recipient);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Invalid recipient"));
        token.transferFrom(recipient, address(0), tokenId);
        assertEq(token.ownerOf(tokenId), recipient);
        assertEq(token.balanceOf(recipient), 1);
    }
}
