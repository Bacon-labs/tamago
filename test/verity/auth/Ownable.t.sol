// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {OwnableDeployer} from "../../../src/generated/verity/OwnableDeployer.sol";
import {OwnableIface} from "../../../src/generated/verity/OwnableIface.sol";
import {Test} from "forge-std/Test.sol";

contract OwnableTest is Test {
    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    function deployOwnable() internal returns (OwnableIface ownable) {
        ownable = OwnableDeployer.deploy(address(this));
    }

    function nonzero(address account) internal pure returns (address) {
        return account == address(0) ? address(1) : account;
    }

    function outsider(address account) internal view returns (address) {
        return account == address(this) ? address(2) : account;
    }

    function storageSlot(uint256 slot) internal pure returns (bytes32) {
        return bytes32(slot);
    }

    // tama: mirrors=ownable_owner_spec
    function testFuzzOwnerSpec() public {
        OwnableIface ownable = deployOwnable();
        assertEq(ownable.owner(), address(this));
    }

    // tama: mirrors=ownable_transferOwnership_reverts_for_non_owner
    function testFuzzTransferOwnershipRevertsForNonOwner(address attacker, address newOwner) public {
        attacker = outsider(attacker);
        newOwner = nonzero(newOwner);
        OwnableIface ownable = deployOwnable();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSelector(bytes4(keccak256("Unauthorized()"))));
        ownable.transferOwnership(newOwner);
    }

    // tama: mirrors=ownable_transferOwnership_reverts_for_zero_owner
    function testFuzzTransferOwnershipRevertsForZeroOwner() public {
        OwnableIface ownable = deployOwnable();
        vm.expectRevert(abi.encodeWithSelector(bytes4(keccak256("NewOwnerIsZeroAddress()"))));
        ownable.transferOwnership(address(0));
    }

    // tama: mirrors=ownable_transferOwnership_succeeds_for_owner_to_nonzero
    function testFuzzTransferOwnershipSucceedsForOwnerToNonzero(address newOwner) public {
        newOwner = nonzero(newOwner);
        OwnableIface ownable = deployOwnable();
        assertTrue(ownable.transferOwnership(newOwner));
    }

    // tama: mirrors=ownable_transferOwnership_sets_new_owner
    function testFuzzTransferOwnershipSetsNewOwner(address newOwner) public {
        newOwner = nonzero(newOwner);
        OwnableIface ownable = deployOwnable();
        ownable.transferOwnership(newOwner);
        assertEq(ownable.owner(), newOwner);
    }

    // tama: mirrors=ownable_transferOwnership_keeps_other_owner_slots
    function testFuzzTransferOwnershipKeepsOtherOwnerSlots(address newOwner) public {
        newOwner = nonzero(newOwner);
        OwnableIface ownable = deployOwnable();
        vm.store(address(ownable), storageSlot(1), bytes32(uint256(0xabc)));
        ownable.transferOwnership(newOwner);
        assertEq(vm.load(address(ownable), storageSlot(1)), bytes32(uint256(0xabc)));
    }

    // tama: mirrors=ownable_transferOwnership_keeps_uint_storage
    function testFuzzTransferOwnershipKeepsUintStorage(address newOwner) public {
        newOwner = nonzero(newOwner);
        OwnableIface ownable = deployOwnable();
        vm.store(address(ownable), storageSlot(2), bytes32(uint256(123)));
        ownable.transferOwnership(newOwner);
        assertEq(vm.load(address(ownable), storageSlot(2)), bytes32(uint256(123)));
    }

    // tama: mirrors=ownable_transferOwnership_keeps_balances_and_allowances
    function testFuzzTransferOwnershipKeepsMappedStorage(address newOwner) public {
        newOwner = nonzero(newOwner);
        OwnableIface ownable = deployOwnable();
        bytes32 slot = keccak256(abi.encode(address(this), uint256(3)));
        vm.store(address(ownable), slot, bytes32(uint256(456)));
        ownable.transferOwnership(newOwner);
        assertEq(vm.load(address(ownable), slot), bytes32(uint256(456)));
    }

    // tama: mirrors=ownable_transferOwnership_keeps_array_storage
    function testFuzzTransferOwnershipKeepsArrayStorage(address newOwner) public {
        newOwner = nonzero(newOwner);
        OwnableIface ownable = deployOwnable();
        bytes32 slot = keccak256(abi.encode(uint256(4)));
        vm.store(address(ownable), slot, bytes32(uint256(789)));
        ownable.transferOwnership(newOwner);
        assertEq(vm.load(address(ownable), slot), bytes32(uint256(789)));
    }

    function testFuzzTransferOwnershipEffect(address newOwner) public {
        newOwner = nonzero(newOwner);
        OwnableIface ownable = deployOwnable();
        vm.expectEmit(true, true, false, true, address(ownable));
        emit OwnershipTransferred(address(this), newOwner);
        assertTrue(ownable.transferOwnership(newOwner));
        assertEq(ownable.owner(), newOwner);
    }

    // tama: mirrors=ownable_renounceOwnership_reverts_for_non_owner
    function testFuzzRenounceOwnershipRevertsForNonOwner(address attacker) public {
        attacker = outsider(attacker);
        OwnableIface ownable = deployOwnable();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSelector(bytes4(keccak256("Unauthorized()"))));
        ownable.renounceOwnership();
    }

    // tama: mirrors=ownable_renounceOwnership_succeeds_for_owner
    function testFuzzRenounceOwnershipSucceedsForOwner() public {
        OwnableIface ownable = deployOwnable();
        assertTrue(ownable.renounceOwnership());
    }

    // tama: mirrors=ownable_renounceOwnership_clears_owner
    function testFuzzRenounceOwnershipClearsOwner() public {
        OwnableIface ownable = deployOwnable();
        ownable.renounceOwnership();
        assertEq(ownable.owner(), address(0));
    }

    // tama: mirrors=ownable_renounceOwnership_keeps_other_owner_slots
    function testFuzzRenounceOwnershipKeepsOtherOwnerSlots() public {
        OwnableIface ownable = deployOwnable();
        vm.store(address(ownable), storageSlot(1), bytes32(uint256(0xabc)));
        ownable.renounceOwnership();
        assertEq(vm.load(address(ownable), storageSlot(1)), bytes32(uint256(0xabc)));
    }

    // tama: mirrors=ownable_renounceOwnership_keeps_uint_storage
    function testFuzzRenounceOwnershipKeepsUintStorage() public {
        OwnableIface ownable = deployOwnable();
        vm.store(address(ownable), storageSlot(2), bytes32(uint256(123)));
        ownable.renounceOwnership();
        assertEq(vm.load(address(ownable), storageSlot(2)), bytes32(uint256(123)));
    }

    // tama: mirrors=ownable_renounceOwnership_keeps_balances_and_allowances
    function testFuzzRenounceOwnershipKeepsMappedStorage() public {
        OwnableIface ownable = deployOwnable();
        bytes32 slot = keccak256(abi.encode(address(this), uint256(3)));
        vm.store(address(ownable), slot, bytes32(uint256(456)));
        ownable.renounceOwnership();
        assertEq(vm.load(address(ownable), slot), bytes32(uint256(456)));
    }

    // tama: mirrors=ownable_renounceOwnership_keeps_array_storage
    function testFuzzRenounceOwnershipKeepsArrayStorage() public {
        OwnableIface ownable = deployOwnable();
        bytes32 slot = keccak256(abi.encode(uint256(4)));
        vm.store(address(ownable), slot, bytes32(uint256(789)));
        ownable.renounceOwnership();
        assertEq(vm.load(address(ownable), slot), bytes32(uint256(789)));
    }

    function testFuzzRenounceOwnershipEffect() public {
        OwnableIface ownable = deployOwnable();
        vm.expectEmit(true, true, false, true, address(ownable));
        emit OwnershipTransferred(address(this), address(0));
        assertTrue(ownable.renounceOwnership());
        assertEq(ownable.owner(), address(0));
    }
}
