// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {ERC721Deployer} from "../../src/generated/verity/ERC721Deployer.sol";
import {ERC721Iface} from "../../src/generated/verity/ERC721Iface.sol";
import {Test} from "forge-std/Test.sol";

contract ERC721Test is Test {
    event Transfer(address indexed from, address indexed to, uint256 indexed tokenId);
    event Approval(address indexed owner, address indexed approved, uint256 indexed tokenId);
    event ApprovalForAll(address indexed owner, address indexed operator, bool approved);
    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    function deployToken() internal returns (ERC721Iface token) {
        token = ERC721Deployer.deploy(address(this));
    }

    // tama: mirrors=erc721_totalSupply_spec,erc721_owner_spec,erc721_balanceOf_spec,erc721_ownerOf_spec,erc721_mint_effect
    function testFuzzMintAndViews(address recipient) public {
        vm.assume(recipient != address(0));
        ERC721Iface token = deployToken();
        assertEq(token.owner(), address(this));
        assertEq(token.totalSupply(), 0);
        vm.expectEmit(true, true, true, true, address(token));
        emit Transfer(address(0), recipient, 0);
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
        vm.expectEmit(true, true, true, true, address(token));
        emit Approval(holder, approved, tokenId);
        vm.prank(holder);
        assertTrue(token.approve(approved, tokenId));
        assertEq(token.getApproved(tokenId), approved);
    }

    // tama: mirrors=erc721_approve_effect
    function testFuzzApproveUnauthorizedReverts(address holder, address attacker, address approved) public {
        vm.assume(holder != address(0));
        vm.assume(attacker != holder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Not authorized"));
        token.approve(approved, tokenId);
        assertEq(token.getApproved(tokenId), address(0));
    }

    // tama: mirrors=erc721_isApprovedForAll_spec,erc721_setApprovalForAll_effect
    function testFuzzSetApprovalForAll(address operator, bool approved) public {
        ERC721Iface token = deployToken();
        vm.expectEmit(true, true, false, true, address(token));
        emit ApprovalForAll(address(this), operator, approved);
        assertTrue(token.setApprovalForAll(operator, approved));
        assertEq(token.isApprovedForAll(address(this), operator), approved);
    }

    // tama: mirrors=erc721_balanceOf_spec,erc721_ownerOf_spec,erc721_getApproved_spec,erc721_approve_effect
    function testFuzzMissingTokenViewsRevert(uint256 tokenId) public {
        ERC721Iface token = deployToken();
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Invalid owner"));
        token.balanceOf(address(0));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Token does not exist"));
        token.ownerOf(tokenId);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Token does not exist"));
        token.getApproved(tokenId);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Token does not exist"));
        token.approve(address(1), tokenId);
    }

    // tama: mirrors=erc721_mint_effect
    function testFuzzMintUnauthorizedReverts(address attacker, address recipient) public {
        vm.assume(attacker != address(this));
        vm.assume(recipient != address(0));
        ERC721Iface token = deployToken();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.mint(recipient);
        assertEq(token.totalSupply(), 0);
    }

    // tama: mirrors=erc721_transferFrom_effect
    function testFuzzTransferFromMovesToken(address holder, address recipient) public {
        vm.assume(holder != address(0));
        vm.assume(recipient != address(0));
        vm.assume(holder != recipient);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(holder);
        assertTrue(token.approve(address(this), tokenId));
        vm.expectEmit(true, true, true, true, address(token));
        emit Transfer(holder, recipient, tokenId);
        assertTrue(token.transferFrom(holder, recipient, tokenId));
        assertEq(token.ownerOf(tokenId), recipient);
        assertEq(token.balanceOf(holder), 0);
        assertEq(token.balanceOf(recipient), 1);
        assertEq(token.getApproved(tokenId), address(0));
    }

    // tama: mirrors=erc721_transferFrom_effect
    function testFuzzTransferFromUnauthorizedReverts(address holder, address recipient, address attacker) public {
        vm.assume(holder != address(0));
        vm.assume(recipient != address(0));
        vm.assume(attacker != address(0));
        vm.assume(attacker != holder);
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(holder);
        vm.prank(attacker);
        (bool ok, bytes memory data) = address(token).call(
            abi.encodeCall(ERC721Iface.transferFrom, (holder, recipient, tokenId))
        );
        assertFalse(ok);
        assertEq(data, abi.encodeWithSignature("Error(string)", "Not authorized"));
        assertEq(token.ownerOf(tokenId), holder);
    }

    // tama: mirrors=erc721_transferFrom_effect
    function testFuzzTransferToZeroRevertsWithoutChangingOwner(address recipient) public {
        vm.assume(recipient != address(0));
        ERC721Iface token = deployToken();
        uint256 tokenId = token.mint(recipient);
        vm.prank(recipient);
        (bool ok, bytes memory data) = address(token).call(
            abi.encodeCall(ERC721Iface.transferFrom, (recipient, address(0), tokenId))
        );
        assertFalse(ok);
        assertEq(data, abi.encodeWithSignature("Error(string)", "Invalid recipient"));
        assertEq(token.ownerOf(tokenId), recipient);
        assertEq(token.balanceOf(recipient), 1);
    }

    // tama: mirrors=erc721_owner_spec,erc721_transferOwnership_effect,erc721_mint_effect
    function testFuzzTransferOwnershipMovesMintAuthority(address newOwner, address recipient) public {
        vm.assume(newOwner != address(0));
        vm.assume(newOwner != address(this));
        vm.assume(recipient != address(0));
        ERC721Iface token = deployToken();
        vm.expectEmit(true, true, false, true, address(token));
        emit OwnershipTransferred(address(this), newOwner);
        assertTrue(token.transferOwnership(newOwner));
        assertEq(token.owner(), newOwner);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.mint(recipient);
        vm.expectEmit(true, true, true, true, address(token));
        emit Transfer(address(0), recipient, 0);
        vm.prank(newOwner);
        uint256 tokenId = token.mint(recipient);
        assertEq(token.ownerOf(tokenId), recipient);
    }

    // tama: mirrors=erc721_transferOwnership_effect
    function testFuzzTransferOwnershipUnauthorizedReverts(address attacker, address newOwner) public {
        vm.assume(attacker != address(this));
        vm.assume(newOwner != address(0));
        ERC721Iface token = deployToken();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.transferOwnership(newOwner);
        assertEq(token.owner(), address(this));
    }

    // tama: mirrors=erc721_transferOwnership_effect
    function testFuzzTransferOwnershipToZeroReverts() public {
        ERC721Iface token = deployToken();
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Invalid owner"));
        token.transferOwnership(address(0));
        assertEq(token.owner(), address(this));
    }

    // tama: mirrors=erc721_owner_spec,erc721_renounceOwnership_effect,erc721_mint_effect
    function testFuzzRenounceOwnershipDisablesMint() public {
        ERC721Iface token = deployToken();
        vm.expectEmit(true, true, false, true, address(token));
        emit OwnershipTransferred(address(this), address(0));
        assertTrue(token.renounceOwnership());
        assertEq(token.owner(), address(0));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.mint(address(this));
    }

    // tama: mirrors=erc721_renounceOwnership_effect
    function testFuzzRenounceOwnershipUnauthorizedReverts(address attacker) public {
        vm.assume(attacker != address(this));
        ERC721Iface token = deployToken();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.renounceOwnership();
        assertEq(token.owner(), address(this));
    }
}
