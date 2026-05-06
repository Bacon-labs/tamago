// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {ERC20LiteDeployer} from "../../src/generated/verity/ERC20LiteDeployer.sol";
import {ERC20LiteIface} from "../../src/generated/verity/ERC20LiteIface.sol";
import {Test} from "forge-std/Test.sol";

// These Foundry tests mirror the proof obligations in
// verity/proof/ERC20LiteProof.lean. Run `tama build` first so the generated
// deployer contains bytecode compiled from the Verity/Yul pipeline.
//
// `Test` (from forge-std) provides the `vm` cheatcode entry point, which we
// use below to exercise the negative access-control path with `vm.prank` and
// `vm.expectRevert`. It also inherits from `StdInvariant`, so the invariant
// handler harness still works.
contract ERC20LiteTest is Test {
    ERC20LiteIface internal invariantToken;
    uint256 internal invariantMinted;

    function setUp() public {
        // Invariant handlers exercise mint and transfer across many calls while
        // `invariant_totalSupplyTracksMinted` checks the global property.
        invariantToken = deployToken();
        bytes4[] memory selectors = new bytes4[](2);
        selectors[0] = this.handlerMint.selector;
        selectors[1] = this.handlerTransferFromOwner.selector;
        targetSelector(FuzzSelector({addr: address(this), selectors: selectors}));
    }

    function deployToken() internal returns (ERC20LiteIface token) {
        token = deployToken(address(this));
    }

    function deployToken(address initialOwner) internal returns (ERC20LiteIface token) {
        token = ERC20LiteDeployer.deploy(initialOwner);
    }

    // Deployment mirror: the constructor writes owner and starts supply at zero.
    // tama: mirrors=owner_spec
    function testFuzzDeploymentSetsOwner(address initialOwner) public {
        ERC20LiteIface token = deployToken(initialOwner);
        require(token.owner() == initialOwner, "owner");
        require(token.totalSupply() == 0, "initial supply");
    }

    // Mint mirror: owner minting updates one balance and total supply together.
    // tama: mirrors=mint_owner_preserved,totalSupply_spec
    function testFuzzMintUpdatesBalanceAndSupply(address account, uint256 rawAmount) public {
        ERC20LiteIface token = deployToken();
        uint256 amount = rawAmount % 1e36;
        require(token.mint(account, amount), "mint");
        require(token.balanceOf(account) == amount, "minted balance");
        require(token.totalSupply() == amount, "minted supply");
        require(token.owner() == address(this), "owner preserved");
    }

    // Negative access control mirror: non-owner mint reverts and leaves both
    // totalSupply and the recipient balance unchanged. The revert is
    // matched against the exact `Error(string)` selector + message so a
    // failure on a different code path (out-of-gas, an unrelated check, …)
    // would surface as a test failure rather than pass under a generic
    // `vm.expectRevert()`.
    // tama: mirrors=mint_unauthorized_no_change
    function testFuzzMintRevertsForNonOwner(address attacker, address account, uint256 rawAmount) public {
        vm.assume(attacker != address(this));
        ERC20LiteIface token = deployToken();
        uint256 amount = rawAmount % 1e36;
        uint256 supplyBefore = token.totalSupply();
        uint256 balanceBefore = token.balanceOf(account);
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.mint(account, amount);
        require(token.totalSupply() == supplyBefore, "supply unchanged");
        require(token.balanceOf(account) == balanceBefore, "balance unchanged");
    }

    // Transfer mirror: moving tokens changes balances but preserves supply.
    // tama: mirrors=transfer_total_supply_preserved
    function testFuzzTransferPreservesTotalSupply(address recipient, uint256 rawMint, uint256 rawTransfer) public {
        ERC20LiteIface token = deployToken();
        uint256 minted = rawMint % 1e36;
        uint256 amount = minted == 0 ? 0 : rawTransfer % (minted + 1);
        require(token.mint(address(this), minted), "mint");
        require(token.transfer(recipient, amount), "transfer");
        if (recipient == address(this)) {
            require(token.balanceOf(address(this)) == minted, "self transfer balance");
        } else {
            require(token.balanceOf(address(this)) == minted - amount, "sender balance");
            require(token.balanceOf(recipient) == amount, "recipient balance");
        }
        require(token.totalSupply() == minted, "supply preserved");
    }

    // Transfer effect mirror: covers both branches the spec splits on.
    // The non-self branch debits the sender by `amount` and credits the
    // recipient by `amount`. The self-transfer branch leaves the balance
    // unchanged — the spec demands this explicitly because a naive
    // `balance[a] -= n; balance[b] += n` (without the `if a == b` guard)
    // reads a stale recipient balance after the debit, which has been a
    // recurring source of token-implementation bugs.
    // tama: mirrors=transfer_balances_effect
    function testFuzzTransferDebitAndCredit(address recipient, uint256 rawMint, uint256 rawTransfer) public {
        ERC20LiteIface token = deployToken();
        uint256 minted = rawMint % 1e36;
        uint256 amount = minted == 0 ? 0 : rawTransfer % (minted + 1);
        require(token.mint(address(this), minted), "mint");
        uint256 senderBefore = token.balanceOf(address(this));
        uint256 recipientBefore = token.balanceOf(recipient);
        require(senderBefore >= amount, "precondition: balance");
        require(token.transfer(recipient, amount), "transfer");
        if (recipient == address(this)) {
            // Self-transfer: balance unchanged.
            require(token.balanceOf(address(this)) == senderBefore, "self balance preserved");
        } else {
            require(recipientBefore + amount >= recipientBefore, "precondition: no overflow");
            require(token.balanceOf(address(this)) == senderBefore - amount, "sender debit");
            require(token.balanceOf(recipient) == recipientBefore + amount, "recipient credit");
        }
    }

    // Authorized-path mirror: the current owner can promote a successor,
    // `owner()` then reads back the new address, AND the previous owner has
    // truly lost access — a `transferOwnership` from the previous owner
    // after the rotation must revert. The second half catches a "copies
    // instead of moves" bug class: an implementation that wrote to the new
    // owner slot without invalidating the old owner's authority would pass
    // the `owner()` read but fail the post-rotation revert check.
    // tama: mirrors=transferOwnership_authorized_sets_owner
    function testFuzzTransferOwnershipChangesOwner(address newOwner) public {
        ERC20LiteIface token = deployToken();
        address oldOwner = address(this);
        token.transferOwnership(newOwner);
        require(token.owner() == newOwner, "owner rotated");
        if (newOwner != oldOwner) {
            vm.prank(oldOwner);
            vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
            token.transferOwnership(address(0xDEAD));
            require(token.owner() == newOwner, "old owner cannot regain access");
        }
    }

    // Negative access control mirror: a non-owner cannot transfer ownership
    // and the slot is untouched after the revert. The expected revert is
    // matched against the exact `Error(string)` selector + message so a
    // future change that started reverting for a different reason (gas, a
    // new check, …) would surface as a test failure rather than slip
    // through under a generic `vm.expectRevert()`.
    // tama: mirrors=transferOwnership_unauthorized_owner_unchanged
    function testFuzzTransferOwnershipRevertsForNonOwner(address attacker, address newOwner) public {
        vm.assume(attacker != address(this));
        ERC20LiteIface token = deployToken();
        address ownerBefore = token.owner();
        vm.prank(attacker);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Caller is not the owner"));
        token.transferOwnership(newOwner);
        require(token.owner() == ownerBefore, "owner unchanged");
    }

    // Frame mirror: rotating the owner does not move tokens. Both authorized
    // and unauthorized paths must hold the totalSupply and an account balance
    // constant; the proof case-splits on authorization for the same reason.
    // tama: mirrors=transferOwnership_supply_preserved,transferOwnership_balances_preserved
    function testFuzzTransferOwnershipPreservesTokenState(
        address newOwner,
        address holder,
        uint256 rawMint
    ) public {
        ERC20LiteIface token = deployToken();
        uint256 minted = rawMint % 1e36;
        require(token.mint(holder, minted), "mint");
        uint256 supplyBefore = token.totalSupply();
        uint256 balanceBefore = token.balanceOf(holder);
        token.transferOwnership(newOwner);
        require(token.totalSupply() == supplyBefore, "supply preserved");
        require(token.balanceOf(holder) == balanceBefore, "balance preserved");
    }

    // tama: mirrors=balanceOf_spec
    function testFuzzBalanceOfMirrorsGeneratedBytecode(address account, uint256 rawAmount) public {
        ERC20LiteIface token = deployToken();
        uint256 amount = rawAmount % 1e36;
        require(token.mint(account, amount), "mint");
        require(token.balanceOf(account) == amount, "balanceOf");
    }

    function handlerMint(uint8 accountIndex, uint256 rawAmount) public {
        uint256 amount = rawAmount % 1e24;
        require(invariantToken.mint(invariantAccount(accountIndex), amount), "invariant mint");
        invariantMinted += amount;
    }

    function handlerTransferFromOwner(uint8 accountIndex, uint256 rawAmount) public {
        uint256 balance = invariantToken.balanceOf(address(this));
        uint256 amount = balance == 0 ? 0 : rawAmount % (balance + 1);
        require(invariantToken.transfer(invariantAccount(accountIndex), amount), "invariant transfer");
    }

    // tama: mirrors=totalSupply_spec
    function invariant_totalSupplyTracksMinted() public view {
        require(invariantToken.totalSupply() == invariantMinted, "invariant supply");
    }

    function invariantAccount(uint8 index) internal view returns (address) {
        uint8 account = index % 3;
        if (account == 0) {
            return address(this);
        }
        if (account == 1) {
            return address(0xA11CE);
        }
        return address(0xB0B);
    }
}
