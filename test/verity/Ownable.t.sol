// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {OwnableDeployer} from "../../src/generated/verity/OwnableDeployer.sol";
import {OwnableIface} from "../../src/generated/verity/OwnableIface.sol";
import {Test} from "forge-std/Test.sol";

contract OwnableTest is Test {
    function deployOwnable() internal returns (OwnableIface ownable) {
        ownable = OwnableDeployer.deploy(address(this));
    }

    // tama: mirrors=ownable_owner_spec,ownable_transferOwnership_effect
    function testFuzzTransferOwnership(address newOwner) public {
        vm.assume(newOwner != address(0));
        OwnableIface ownable = deployOwnable();
        assertEq(ownable.owner(), address(this));
        assertTrue(ownable.transferOwnership(newOwner));
        assertEq(ownable.owner(), newOwner);
    }

    // tama: mirrors=ownable_transferOwnership_effect
    function testFuzzTransferOwnershipUnauthorizedReverts(address attacker, address newOwner) public {
        vm.assume(attacker != address(this));
        vm.assume(newOwner != address(0));
        OwnableIface ownable = deployOwnable();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        ownable.transferOwnership(newOwner);
        assertEq(ownable.owner(), address(this));
    }

    // tama: mirrors=ownable_transferOwnership_effect
    function testFuzzTransferOwnershipToZeroReverts() public {
        OwnableIface ownable = deployOwnable();
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Invalid owner"));
        ownable.transferOwnership(address(0));
        assertEq(ownable.owner(), address(this));
    }

    // tama: mirrors=ownable_renounceOwnership_effect
    function testFuzzRenounceOwnership() public {
        OwnableIface ownable = deployOwnable();
        assertTrue(ownable.renounceOwnership());
        assertEq(ownable.owner(), address(0));
    }

    // tama: mirrors=ownable_renounceOwnership_effect
    function testFuzzRenounceOwnershipUnauthorizedReverts(address attacker) public {
        vm.assume(attacker != address(this));
        OwnableIface ownable = deployOwnable();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        ownable.renounceOwnership();
        assertEq(ownable.owner(), address(this));
    }
}
