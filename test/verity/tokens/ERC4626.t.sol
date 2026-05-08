// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {ERC20Deployer} from "../../../src/generated/verity/ERC20Deployer.sol";
import {ERC20Iface} from "../../../src/generated/verity/ERC20Iface.sol";
import {ERC4626Deployer} from "../../../src/generated/verity/ERC4626Deployer.sol";
import {ERC4626Iface} from "../../../src/generated/verity/ERC4626Iface.sol";
import {Test} from "forge-std/Test.sol";
import {Vm} from "forge-std/Vm.sol";

contract ERC4626Test is Test {
    bytes32 internal constant TRANSFER_TOPIC = keccak256("Transfer(address,address,uint256)");
    bytes32 internal constant DEPOSIT_TOPIC = keccak256("Deposit(address,address,uint256,uint256)");
    bytes32 internal constant WITHDRAW_TOPIC = keccak256("Withdraw(address,address,address,uint256,uint256)");

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);
    event Deposit(address indexed sender, address indexed owner, uint256 assets, uint256 shares);
    event Withdraw(address indexed sender, address indexed receiver, address indexed owner, uint256 assets, uint256 shares);

    function deployPair() internal returns (ERC20Iface assetToken, ERC4626Iface vault) {
        assetToken = ERC20Deployer.deploy(address(this));
        vault = ERC4626Deployer.deploy(address(assetToken));
    }

    function small(uint256 raw) internal pure returns (uint256) {
        return raw % 1e24;
    }

    function topic(address account) internal pure returns (bytes32) {
        return bytes32(uint256(uint160(account)));
    }

    function assertHasLog2(
        Vm.Log[] memory logs,
        address emitter,
        bytes32 topic0,
        address indexed0,
        address indexed1,
        bytes memory data
    ) internal pure {
        bool found;
        for (uint256 i = 0; i < logs.length; i++) {
            if (
                logs[i].emitter == emitter && logs[i].topics.length == 3 && logs[i].topics[0] == topic0
                    && logs[i].topics[1] == topic(indexed0) && logs[i].topics[2] == topic(indexed1)
                    && keccak256(logs[i].data) == keccak256(data)
            ) {
                found = true;
                break;
            }
        }
        assertTrue(found, "missing expected 2-topic event");
    }

    function assertHasLog3(
        Vm.Log[] memory logs,
        address emitter,
        bytes32 topic0,
        address indexed0,
        address indexed1,
        address indexed2,
        bytes memory data
    ) internal pure {
        bool found;
        for (uint256 i = 0; i < logs.length; i++) {
            if (
                logs[i].emitter == emitter && logs[i].topics.length == 4 && logs[i].topics[0] == topic0
                    && logs[i].topics[1] == topic(indexed0) && logs[i].topics[2] == topic(indexed1)
                    && logs[i].topics[3] == topic(indexed2) && keccak256(logs[i].data) == keccak256(data)
            ) {
                found = true;
                break;
            }
        }
        assertTrue(found, "missing expected 3-topic event");
    }

    function seedDeposit(ERC20Iface assetToken, ERC4626Iface vault, uint256 amount, address owner) internal {
        assetToken.mint(owner, amount);
        vm.prank(owner);
        assetToken.approve(address(vault), amount);
        vm.prank(owner);
        vault.deposit(amount, owner);
    }

    function nonzeroReceiver(address account) internal view returns (address) {
        if (account == address(0) || account == address(this)) return address(0xCAFE);
        return account;
    }

    function balanceSlot(address account) internal pure returns (bytes32) {
        return keccak256(abi.encode(account, uint256(2)));
    }

    function storageSlot(uint256 index) internal pure returns (bytes32) {
        return bytes32(index);
    }

    // tama: mirrors=erc4626_asset_spec
    function testFuzzAssetSpec() public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        assertEq(vault.asset(), address(assetToken));
    }

    // tama: mirrors=erc4626_decimals_spec
    function testFuzzDecimalsSpec() public {
        (, ERC4626Iface vault) = deployPair();
        assertEq(vault.decimals(), 18);
    }

    // tama: mirrors=erc4626_totalSupply_spec
    function testFuzzTotalSupplySpec(uint256 rawAssets) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        seedDeposit(assetToken, vault, assets, address(this));
        assertEq(vault.totalSupply(), assets);
    }

    // tama: mirrors=erc4626_totalAssets_spec
    function testFuzzTotalAssetsSpec(uint256 rawAssets) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        seedDeposit(assetToken, vault, assets, address(this));
        assertEq(vault.totalAssets(), assets);
    }

    // tama: mirrors=erc4626_balanceOf_spec
    function testFuzzBalanceOfSpec(address rawReceiver, uint256 rawAssets) public {
        address owner = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        seedDeposit(assetToken, vault, assets, owner);
        assertEq(vault.balanceOf(owner), assets);
    }

    // tama: mirrors=erc4626_allowance_spec
    function testFuzzAllowanceSpec(address spender, uint256 amount) public {
        (, ERC4626Iface vault) = deployPair();
        vault.approve(spender, amount);
        assertEq(vault.allowance(address(this), spender), amount);
    }

    // tama: mirrors=erc4626_approve_succeeds
    function testFuzzApproveSucceeds(address spender, uint256 amount) public {
        (, ERC4626Iface vault) = deployPair();
        assertTrue(vault.approve(spender, amount));
    }

    // tama: mirrors=erc4626_approve_sets_allowance
    function testFuzzApproveSetsAllowance(address spender, uint256 amount) public {
        (, ERC4626Iface vault) = deployPair();
        vault.approve(spender, amount);
        assertEq(vault.allowance(address(this), spender), amount);
    }

    // tama: mirrors=erc4626_approve_keeps_balances
    function testFuzzApproveKeepsBalances(address spender, uint256 rawDeposit, uint256 approval) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        vault.approve(spender, approval);
        assertEq(vault.balanceOf(address(this)), deposited);
    }

    // tama: mirrors=erc4626_approve_keeps_total_supply
    function testFuzzApproveKeepsTotalSupply(address spender, uint256 rawDeposit, uint256 approval) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        vault.approve(spender, approval);
        assertEq(vault.totalSupply(), deposited);
    }

    function testFuzzApproveEffect(address spender, uint256 amount) public {
        (, ERC4626Iface vault) = deployPair();
        vm.expectEmit(true, true, false, true, address(vault));
        emit Approval(address(this), spender, amount);
        assertTrue(vault.approve(spender, amount));
    }

    // tama: mirrors=erc4626_transfer_reverts_when_balance_is_low
    function testFuzzTransferRevertsWhenBalanceIsLow(address to, uint256 rawAmount) public {
        (, ERC4626Iface vault) = deployPair();
        uint256 amount = small(rawAmount) + 1;
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient balance"));
        vault.transfer(to, amount);
    }

    // tama: mirrors=erc4626_transfer_to_self_keeps_balances
    function testFuzzTransferToSelfKeepsBalances(uint256 rawDeposit, uint256 rawTransfer) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 amount = deposited == 0 ? 0 : rawTransfer % (deposited + 1);
        assertTrue(vault.transfer(address(this), amount));
        assertEq(vault.balanceOf(address(this)), deposited);
    }

    // tama: mirrors=erc4626_transfer_reverts_when_recipient_balance_would_overflow
    function testFuzzTransferRevertsWhenRecipientBalanceWouldOverflow() public {
        address to = address(0xCAFE);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        seedDeposit(assetToken, vault, 1, address(this));
        vm.store(address(vault), balanceSlot(to), bytes32(type(uint256).max));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Recipient balance overflow"));
        vault.transfer(to, 1);
    }

    // tama: mirrors=erc4626_transfer_moves_tokens_between_distinct_accounts
    function testFuzzTransferMovesTokensBetweenDistinctAccounts(address rawReceiver, uint256 rawDeposit, uint256 rawTransfer) public {
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 amount = deposited == 0 ? 0 : rawTransfer % (deposited + 1);
        uint256 receiverBefore = vault.balanceOf(to);
        assertTrue(vault.transfer(to, amount));
        assertEq(vault.balanceOf(address(this)), deposited - amount);
        assertEq(vault.balanceOf(to), receiverBefore + amount);
    }

    // tama: mirrors=erc4626_transfer_keeps_total_supply
    function testFuzzTransferKeepsTotalSupply(address rawReceiver, uint256 rawDeposit, uint256 rawTransfer) public {
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 amount = deposited == 0 ? 0 : rawTransfer % (deposited + 1);
        vault.transfer(to, amount);
        assertEq(vault.totalSupply(), deposited);
    }

    function testFuzzTransferBalancesEffect(address rawReceiver, uint256 rawDeposit, uint256 rawTransfer) public {
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 amount = deposited == 0 ? 0 : rawTransfer % (deposited + 1);
        assertTrue(vault.transfer(to, amount));
    }

    // tama: mirrors=erc4626_transferFrom_reverts_when_allowance_is_low
    function testFuzzTransferFromRevertsWhenAllowanceIsLow(address rawSpender, address to, uint256 rawDeposit, uint256 rawSpend) public {
        address spender = nonzeroReceiver(rawSpender);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit) + 1;
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 amount = (rawSpend % deposited) + 1;
        vm.prank(spender);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient allowance"));
        vault.transferFrom(address(this), to, amount);
    }

    // tama: mirrors=erc4626_transferFrom_reverts_when_balance_is_low
    function testFuzzTransferFromRevertsWhenBalanceIsLow(address rawSpender, address to, uint256 rawAmount) public {
        address spender = nonzeroReceiver(rawSpender);
        uint256 amount = small(rawAmount) + 1;
        (, ERC4626Iface vault) = deployPair();
        vault.approve(spender, amount);
        vm.prank(spender);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient balance"));
        vault.transferFrom(address(this), to, amount);
    }

    // tama: mirrors=erc4626_transferFrom_reverts_when_recipient_balance_would_overflow
    function testFuzzTransferFromRevertsWhenRecipientBalanceWouldOverflow(address rawSpender) public {
        address spender = nonzeroReceiver(rawSpender);
        address to = address(0xCAFE);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        seedDeposit(assetToken, vault, 1, address(this));
        vault.approve(spender, 1);
        vm.store(address(vault), balanceSlot(to), bytes32(type(uint256).max));
        vm.prank(spender);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Recipient balance overflow"));
        vault.transferFrom(address(this), to, 1);
    }

    // tama: mirrors=erc4626_transferFrom_to_self_keeps_balances
    function testFuzzTransferFromToSelfKeepsBalances(address rawSpender, uint256 rawDeposit, uint256 rawSpend) public {
        address spender = nonzeroReceiver(rawSpender);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 amount = deposited == 0 ? 0 : rawSpend % (deposited + 1);
        vault.approve(spender, amount);
        vm.prank(spender);
        assertTrue(vault.transferFrom(address(this), address(this), amount));
        assertEq(vault.balanceOf(address(this)), deposited);
    }

    // tama: mirrors=erc4626_transferFrom_moves_tokens_between_distinct_accounts
    function testFuzzTransferFromMovesTokensBetweenDistinctAccounts(address rawSpender, address rawReceiver, uint256 rawDeposit, uint256 rawSpend) public {
        address spender = nonzeroReceiver(rawSpender);
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 amount = deposited == 0 ? 0 : rawSpend % (deposited + 1);
        vault.approve(spender, deposited);
        uint256 receiverBefore = vault.balanceOf(to);
        vm.prank(spender);
        assertTrue(vault.transferFrom(address(this), to, amount));
        assertEq(vault.balanceOf(address(this)), deposited - amount);
        assertEq(vault.balanceOf(to), receiverBefore + amount);
    }

    // tama: mirrors=erc4626_transferFrom_keeps_total_supply
    function testFuzzTransferFromKeepsTotalSupply(address rawSpender, address rawReceiver, uint256 rawDeposit, uint256 rawSpend) public {
        address spender = nonzeroReceiver(rawSpender);
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 amount = deposited == 0 ? 0 : rawSpend % (deposited + 1);
        vault.approve(spender, deposited);
        vm.prank(spender);
        vault.transferFrom(address(this), to, amount);
        assertEq(vault.totalSupply(), deposited);
    }

    // tama: mirrors=erc4626_transferFrom_keeps_infinite_allowance
    function testFuzzTransferFromKeepsInfiniteAllowance(address rawSpender, address rawReceiver, uint256 rawDeposit, uint256 rawSpend) public {
        address spender = nonzeroReceiver(rawSpender);
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 amount = deposited == 0 ? 0 : rawSpend % (deposited + 1);
        vault.approve(spender, type(uint256).max);
        vm.prank(spender);
        vault.transferFrom(address(this), to, amount);
        assertEq(vault.allowance(address(this), spender), type(uint256).max);
    }

    // tama: mirrors=erc4626_transferFrom_spends_finite_allowance
    function testFuzzTransferFromSpendsFiniteAllowance(address rawSpender, address rawReceiver, uint256 rawDeposit, uint256 rawSpend) public {
        address spender = nonzeroReceiver(rawSpender);
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 amount = deposited == 0 ? 0 : rawSpend % (deposited + 1);
        vault.approve(spender, deposited);
        vm.prank(spender);
        vault.transferFrom(address(this), to, amount);
        assertEq(vault.allowance(address(this), spender), deposited - amount);
    }

    function testFuzzTransferFromEffect(address spender, address rawReceiver, uint256 rawDeposit, uint256 rawSpend) public {
        vm.assume(spender != address(this));
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 amount = deposited == 0 ? 0 : rawSpend % (deposited + 1);
        vault.approve(spender, deposited);
        vm.prank(spender);
        assertTrue(vault.transferFrom(address(this), to, amount));
    }

    // tama: mirrors=erc4626_convertToShares_spec
    function testFuzzConvertToSharesSpec(uint256 rawAssets) public {
        (, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        assertEq(vault.convertToShares(assets), assets);
    }

    // tama: mirrors=erc4626_convertToAssets_spec
    function testFuzzConvertToAssetsSpec(uint256 rawShares) public {
        (, ERC4626Iface vault) = deployPair();
        uint256 shares = small(rawShares);
        assertEq(vault.convertToAssets(shares), shares);
    }

    // tama: mirrors=erc4626_maxDeposit_spec
    function testFuzzMaxDepositSpec(address rawReceiver) public {
        (, ERC4626Iface vault) = deployPair();
        assertEq(vault.maxDeposit(rawReceiver), type(uint256).max);
    }

    // tama: mirrors=erc4626_maxMint_spec
    function testFuzzMaxMintSpec(address rawReceiver) public {
        (, ERC4626Iface vault) = deployPair();
        assertEq(vault.maxMint(rawReceiver), type(uint256).max);
    }

    // tama: mirrors=erc4626_maxWithdraw_spec
    function testFuzzMaxWithdrawSpec(uint256 rawAssets) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        seedDeposit(assetToken, vault, assets, address(this));
        assertEq(vault.maxWithdraw(address(this)), assets);
    }

    // tama: mirrors=erc4626_maxRedeem_spec
    function testFuzzMaxRedeemSpec(uint256 rawAssets) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        seedDeposit(assetToken, vault, assets, address(this));
        assertEq(vault.maxRedeem(address(this)), assets);
    }

    // tama: mirrors=erc4626_previewDeposit_spec
    function testFuzzPreviewDepositSpec(uint256 rawAssets) public {
        (, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        assertEq(vault.previewDeposit(assets), assets);
    }

    // tama: mirrors=erc4626_previewMint_spec
    function testFuzzPreviewMintSpec(uint256 rawShares) public {
        (, ERC4626Iface vault) = deployPair();
        uint256 shares = small(rawShares);
        assertEq(vault.previewMint(shares), shares);
    }

    // tama: mirrors=erc4626_previewWithdraw_spec
    function testFuzzPreviewWithdrawSpec(uint256 rawAssets) public {
        (, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        assertEq(vault.previewWithdraw(assets), assets);
    }

    // tama: mirrors=erc4626_previewRedeem_spec
    function testFuzzPreviewRedeemSpec(uint256 rawShares) public {
        (, ERC4626Iface vault) = deployPair();
        uint256 shares = small(rawShares);
        assertEq(vault.previewRedeem(shares), shares);
    }

    // tama: mirrors=erc4626_deposit_returns_at_least_preview
    function testFuzzDepositReturnsAtLeastPreview(uint256 rawInitial, uint256 rawYield, uint256 rawAssets) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        seedDeposit(assetToken, vault, positiveSmall(rawInitial), address(this));
        distributeYield(assetToken, vault, small(rawYield));
        uint256 assets = small(rawAssets);
        uint256 preview = vault.previewDeposit(assets);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);
        uint256 shares = vault.deposit(assets, address(this));
        assertGe(shares, preview);
    }

    // tama: mirrors=erc4626_mint_pulls_no_more_than_preview
    function testFuzzMintPullsNoMoreThanPreview(uint256 rawInitial, uint256 rawYield, uint256 rawShares) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        seedDeposit(assetToken, vault, positiveSmall(rawInitial), address(this));
        distributeYield(assetToken, vault, small(rawYield));
        uint256 shares = small(rawShares);
        uint256 preview = vault.previewMint(shares);
        assetToken.mint(address(this), preview);
        assetToken.approve(address(vault), preview);
        uint256 assets = vault.mint(shares, address(this));
        assertLe(assets, preview);
    }

    // tama: mirrors=erc4626_withdraw_burns_no_more_than_preview
    function testFuzzWithdrawBurnsNoMoreThanPreview(uint256 rawInitial, uint256 rawYield, uint256 rawWithdraw) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        seedDeposit(assetToken, vault, positiveSmall(rawInitial), address(this));
        distributeYield(assetToken, vault, small(rawYield));
        uint256 maxAssets = vault.maxWithdraw(address(this));
        uint256 assets = maxAssets == 0 ? 0 : rawWithdraw % (maxAssets + 1);
        uint256 preview = vault.previewWithdraw(assets);
        uint256 burnedShares = vault.withdraw(assets, address(this), address(this));
        assertLe(burnedShares, preview);
    }

    // tama: mirrors=erc4626_redeem_returns_at_least_preview
    function testFuzzRedeemReturnsAtLeastPreview(uint256 rawInitial, uint256 rawYield, uint256 rawRedeem) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 initialAssets = positiveSmall(rawInitial);
        seedDeposit(assetToken, vault, initialAssets, address(this));
        distributeYield(assetToken, vault, small(rawYield));
        uint256 shares = rawRedeem % (initialAssets + 1);
        uint256 preview = vault.previewRedeem(shares);
        uint256 assets = vault.redeem(shares, address(this), address(this));
        assertGe(assets, preview);
    }

    // tama: mirrors=erc4626_deposit_reverts_when_receiver_balance_would_overflow
    function testFuzzDepositRevertsWhenReceiverBalanceWouldOverflow(address rawReceiver) public {
        address owner = nonzeroReceiver(rawReceiver);
        (, ERC4626Iface vault) = deployPair();
        vm.store(address(vault), balanceSlot(owner), bytes32(type(uint256).max));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Balance overflow"));
        vault.deposit(1, owner);
    }

    // tama: mirrors=erc4626_deposit_reverts_when_total_supply_would_overflow
    function testFuzzDepositRevertsWhenTotalSupplyWouldOverflow(address rawReceiver) public {
        address owner = nonzeroReceiver(rawReceiver);
        (, ERC4626Iface vault) = deployPair();
        vm.store(address(vault), storageSlot(1), bytes32(type(uint256).max - 1));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Supply overflow"));
        vault.deposit(2, owner);
    }

    // tama: mirrors=erc4626_deposit_reverts_when_total_assets_would_overflow
    function testFuzzDepositRevertsWhenTotalAssetsWouldOverflow(address rawReceiver) public {
        address owner = nonzeroReceiver(rawReceiver);
        (, ERC4626Iface vault) = deployPair();
        vm.store(address(vault), storageSlot(4), bytes32(type(uint256).max - 1));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Total assets overflow"));
        vault.deposit(2, owner);
    }

    // tama: mirrors=erc4626_deposit_succeeds_when_accounting_does_not_overflow
    function testFuzzDepositSucceedsWhenAccountingDoesNotOverflow(address rawReceiver, uint256 rawAssets) public {
        address owner = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);
        assertEq(vault.deposit(assets, owner), assets);
    }

    // tama: mirrors=erc4626_deposit_credits_receiver
    function testFuzzDepositCreditsReceiver(address rawReceiver, uint256 rawAssets) public {
        address owner = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);
        vault.deposit(assets, owner);
        assertEq(vault.balanceOf(owner), assets);
    }

    // tama: mirrors=erc4626_deposit_increases_total_supply
    function testFuzzDepositIncreasesTotalSupply(address rawReceiver, uint256 rawAssets) public {
        address owner = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);
        vault.deposit(assets, owner);
        assertEq(vault.totalSupply(), assets);
    }

    // tama: mirrors=erc4626_deposit_increases_total_assets
    function testFuzzDepositIncreasesTotalAssets(address rawReceiver, uint256 rawAssets) public {
        address owner = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);
        vault.deposit(assets, owner);
        assertEq(vault.totalAssets(), assets);
    }

    // tama: mirrors=erc4626_deposit_keeps_asset
    function testFuzzDepositKeepsAsset(address rawReceiver, uint256 rawAssets) public {
        address owner = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);
        vault.deposit(assets, owner);
        assertEq(vault.asset(), address(assetToken));
    }

    function testFuzzDepositEffect(address rawReceiver, uint256 rawAssets) public {
        address owner = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);
        assertEq(vault.deposit(assets, owner), assets);
    }

    // tama: mirrors=erc4626_mint_reverts_when_receiver_balance_would_overflow
    function testFuzzMintRevertsWhenReceiverBalanceWouldOverflow() public {
        (, ERC4626Iface vault) = deployPair();
        vm.store(address(vault), balanceSlot(address(this)), bytes32(type(uint256).max));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Balance overflow"));
        vault.mint(1, address(this));
    }

    // tama: mirrors=erc4626_mint_reverts_when_total_supply_would_overflow
    function testFuzzMintRevertsWhenTotalSupplyWouldOverflow() public {
        (, ERC4626Iface vault) = deployPair();
        vm.store(address(vault), storageSlot(1), bytes32(type(uint256).max));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Supply overflow"));
        vault.mint(1, address(this));
    }

    // tama: mirrors=erc4626_mint_reverts_when_total_assets_would_overflow
    function testFuzzMintRevertsWhenTotalAssetsWouldOverflow() public {
        (, ERC4626Iface vault) = deployPair();
        vm.store(address(vault), storageSlot(4), bytes32(type(uint256).max - 1));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Total assets overflow"));
        vault.mint(2, address(this));
    }

    // tama: mirrors=erc4626_mint_succeeds_when_accounting_does_not_overflow
    function testFuzzMintSucceedsWhenAccountingDoesNotOverflow(address rawReceiver, uint256 rawShares) public {
        address owner = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 shares = small(rawShares);
        assetToken.mint(address(this), shares);
        assetToken.approve(address(vault), shares);
        assertEq(vault.mint(shares, owner), shares);
    }

    // tama: mirrors=erc4626_mint_credits_receiver
    function testFuzzMintCreditsReceiver(address rawReceiver, uint256 rawShares) public {
        address owner = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 shares = small(rawShares);
        assetToken.mint(address(this), shares);
        assetToken.approve(address(vault), shares);
        vault.mint(shares, owner);
        assertEq(vault.balanceOf(owner), shares);
    }

    // tama: mirrors=erc4626_mint_increases_total_supply
    function testFuzzMintIncreasesTotalSupply(address rawReceiver, uint256 rawShares) public {
        address owner = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 shares = small(rawShares);
        assetToken.mint(address(this), shares);
        assetToken.approve(address(vault), shares);
        vault.mint(shares, owner);
        assertEq(vault.totalSupply(), shares);
    }

    // tama: mirrors=erc4626_mint_increases_total_assets
    function testFuzzMintIncreasesTotalAssets(address rawReceiver, uint256 rawShares) public {
        address owner = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 shares = small(rawShares);
        assetToken.mint(address(this), shares);
        assetToken.approve(address(vault), shares);
        uint256 assets = vault.mint(shares, owner);
        assertEq(vault.totalAssets(), assets);
    }

    // tama: mirrors=erc4626_mint_keeps_asset
    function testFuzzMintKeepsAsset(address rawReceiver, uint256 rawShares) public {
        address owner = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 shares = small(rawShares);
        assetToken.mint(address(this), shares);
        assetToken.approve(address(vault), shares);
        vault.mint(shares, owner);
        assertEq(vault.asset(), address(assetToken));
    }

    function testFuzzMintEffect(address rawReceiver, uint256 rawShares) public {
        address owner = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 shares = small(rawShares);
        assetToken.mint(address(this), shares);
        assetToken.approve(address(vault), shares);
        assertEq(vault.mint(shares, owner), shares);
    }

    // tama: mirrors=erc4626_withdraw_reverts_when_assets_exceed_max
    function testFuzzWithdrawRevertsWhenAssetsExceedMax(uint256 rawDeposit) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Withdraw more than max"));
        vault.withdraw(deposited + 1, address(this), address(this));
    }

    // tama: mirrors=erc4626_withdraw_reverts_when_allowance_is_low
    function testFuzzWithdrawRevertsWhenAllowanceIsLow(address rawSpender, uint256 rawDeposit, uint256 rawWithdraw) public {
        address spender = nonzeroReceiver(rawSpender);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit) + 1;
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 assets = (rawWithdraw % deposited) + 1;
        vm.prank(spender);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient allowance"));
        vault.withdraw(assets, spender, address(this));
    }

    // tama: mirrors=erc4626_withdraw_reverts_when_total_supply_is_low
    function testFuzzWithdrawRevertsWhenTotalSupplyIsLow() public {
        (, ERC4626Iface vault) = deployPair();
        vm.store(address(vault), balanceSlot(address(this)), bytes32(uint256(13946)));
        vm.store(address(vault), storageSlot(1), bytes32(uint256(1)));
        vm.store(address(vault), storageSlot(4), bytes32(uint256(19340)));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient supply"));
        vault.withdraw(19329, address(this), address(this));
    }

    // tama: mirrors=erc4626_withdraw_reverts_when_total_assets_is_low
    function testFuzzWithdrawRevertsWhenTotalAssetsIsLow() public {
        (, ERC4626Iface vault) = deployPair();
        vm.store(address(vault), balanceSlot(address(this)), bytes32(type(uint256).max / 3));
        vm.store(address(vault), storageSlot(1), bytes32(uint256(0)));
        vm.store(address(vault), storageSlot(4), bytes32(uint256(2)));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient assets"));
        vault.withdraw(type(uint256).max - 1, address(this), address(this));
    }

    // tama: mirrors=erc4626_withdraw_succeeds_when_accounting_and_allowance_are_enough
    function testFuzzWithdrawSucceedsWhenAccountingAndAllowanceAreEnough(address rawReceiver, uint256 rawDeposit, uint256 rawWithdraw) public {
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 assets = deposited == 0 ? 0 : rawWithdraw % (deposited + 1);
        assertEq(vault.withdraw(assets, to, address(this)), assets);
    }

    // tama: mirrors=erc4626_withdraw_debits_owner
    function testFuzzWithdrawDebitsOwner(address rawReceiver, uint256 rawDeposit, uint256 rawWithdraw) public {
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 assets = deposited == 0 ? 0 : rawWithdraw % (deposited + 1);
        vault.withdraw(assets, to, address(this));
        assertEq(vault.balanceOf(address(this)), deposited - assets);
    }

    // tama: mirrors=erc4626_withdraw_decreases_total_supply
    function testFuzzWithdrawDecreasesTotalSupply(address rawReceiver, uint256 rawDeposit, uint256 rawWithdraw) public {
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 assets = deposited == 0 ? 0 : rawWithdraw % (deposited + 1);
        vault.withdraw(assets, to, address(this));
        assertEq(vault.totalSupply(), deposited - assets);
    }

    // tama: mirrors=erc4626_withdraw_decreases_total_assets
    function testFuzzWithdrawDecreasesTotalAssets(address rawReceiver, uint256 rawDeposit, uint256 rawWithdraw) public {
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 assets = deposited == 0 ? 0 : rawWithdraw % (deposited + 1);
        vault.withdraw(assets, to, address(this));
        assertEq(vault.totalAssets(), deposited - assets);
    }

    // tama: mirrors=erc4626_withdraw_keeps_owner_or_infinite_allowance
    function testFuzzWithdrawKeepsOwnerOrInfiniteAllowance(address rawSpender, address rawReceiver, uint256 rawDeposit, uint256 rawWithdraw) public {
        address spender = nonzeroReceiver(rawSpender);
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 assets = deposited == 0 ? 0 : rawWithdraw % (deposited + 1);
        vault.approve(spender, type(uint256).max);
        vm.prank(spender);
        vault.withdraw(assets, to, address(this));
        assertEq(vault.allowance(address(this), spender), type(uint256).max);
    }

    // tama: mirrors=erc4626_withdraw_spends_finite_allowance
    function testFuzzWithdrawSpendsFiniteAllowance(address rawSpender, address rawReceiver, uint256 rawDeposit, uint256 rawWithdraw) public {
        address spender = nonzeroReceiver(rawSpender);
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 assets = deposited == 0 ? 0 : rawWithdraw % (deposited + 1);
        vault.approve(spender, deposited);
        vm.prank(spender);
        vault.withdraw(assets, to, address(this));
        assertEq(vault.allowance(address(this), spender), deposited - assets);
    }

    function testFuzzWithdrawEffect(address rawReceiver, uint256 rawDeposit, uint256 rawWithdraw) public {
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 assets = deposited == 0 ? 0 : rawWithdraw % (deposited + 1);
        assertEq(vault.withdraw(assets, to, address(this)), assets);
    }

    // tama: mirrors=erc4626_redeem_reverts_when_shares_exceed_max
    function testFuzzRedeemRevertsWhenSharesExceedMax(uint256 rawDeposit) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Redeem more than max"));
        vault.redeem(deposited + 1, address(this), address(this));
    }

    // tama: mirrors=erc4626_redeem_reverts_when_allowance_is_low
    function testFuzzRedeemRevertsWhenAllowanceIsLow(address rawSpender, uint256 rawDeposit, uint256 rawRedeem) public {
        address spender = nonzeroReceiver(rawSpender);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit) + 1;
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 shares = (rawRedeem % deposited) + 1;
        vm.prank(spender);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient allowance"));
        vault.redeem(shares, spender, address(this));
    }

    // tama: mirrors=erc4626_redeem_reverts_when_total_supply_is_low
    function testFuzzRedeemRevertsWhenTotalSupplyIsLow() public {
        (, ERC4626Iface vault) = deployPair();
        vm.store(address(vault), balanceSlot(address(this)), bytes32(uint256(1)));
        vm.store(address(vault), storageSlot(1), bytes32(uint256(0)));
        vm.store(address(vault), storageSlot(4), bytes32(uint256(1)));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient supply"));
        vault.redeem(1, address(this), address(this));
    }

    // tama: mirrors=erc4626_redeem_succeeds_when_accounting_and_allowance_are_enough
    function testFuzzRedeemSucceedsWhenAccountingAndAllowanceAreEnough(address rawReceiver, uint256 rawDeposit, uint256 rawRedeem) public {
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 shares = deposited == 0 ? 0 : rawRedeem % (deposited + 1);
        assertEq(vault.redeem(shares, to, address(this)), shares);
    }

    // tama: mirrors=erc4626_redeem_debits_owner
    function testFuzzRedeemDebitsOwner(address rawReceiver, uint256 rawDeposit, uint256 rawRedeem) public {
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 shares = deposited == 0 ? 0 : rawRedeem % (deposited + 1);
        vault.redeem(shares, to, address(this));
        assertEq(vault.balanceOf(address(this)), deposited - shares);
    }

    // tama: mirrors=erc4626_redeem_decreases_total_supply
    function testFuzzRedeemDecreasesTotalSupply(address rawReceiver, uint256 rawDeposit, uint256 rawRedeem) public {
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 shares = deposited == 0 ? 0 : rawRedeem % (deposited + 1);
        vault.redeem(shares, to, address(this));
        assertEq(vault.totalSupply(), deposited - shares);
    }

    // tama: mirrors=erc4626_redeem_decreases_total_assets
    function testFuzzRedeemDecreasesTotalAssets(address rawReceiver, uint256 rawDeposit, uint256 rawRedeem) public {
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 shares = deposited == 0 ? 0 : rawRedeem % (deposited + 1);
        vault.redeem(shares, to, address(this));
        assertEq(vault.totalAssets(), deposited - shares);
    }

    // tama: mirrors=erc4626_redeem_keeps_owner_or_infinite_allowance
    function testFuzzRedeemKeepsOwnerOrInfiniteAllowance(address rawSpender, address rawReceiver, uint256 rawDeposit, uint256 rawRedeem) public {
        address spender = nonzeroReceiver(rawSpender);
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 shares = deposited == 0 ? 0 : rawRedeem % (deposited + 1);
        vault.approve(spender, type(uint256).max);
        vm.prank(spender);
        vault.redeem(shares, to, address(this));
        assertEq(vault.allowance(address(this), spender), type(uint256).max);
    }

    // tama: mirrors=erc4626_redeem_spends_finite_allowance
    function testFuzzRedeemSpendsFiniteAllowance(address rawSpender, address rawReceiver, uint256 rawDeposit, uint256 rawRedeem) public {
        address spender = nonzeroReceiver(rawSpender);
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 shares = deposited == 0 ? 0 : rawRedeem % (deposited + 1);
        vault.approve(spender, deposited);
        vm.prank(spender);
        vault.redeem(shares, to, address(this));
        assertEq(vault.allowance(address(this), spender), deposited - shares);
    }

    function testFuzzRedeemEffect(address rawReceiver, uint256 rawDeposit, uint256 rawRedeem) public {
        address to = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 shares = deposited == 0 ? 0 : rawRedeem % (deposited + 1);
        assertEq(vault.redeem(shares, to, address(this)), shares);
    }

    function testFuzzVaultViewsAndPreviews(address receiver, address owner, uint256 rawAssets, uint256 rawShares) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        uint256 shares = small(rawShares);

        assertEq(vault.asset(), address(assetToken));
        assertEq(vault.decimals(), 18);
        assertEq(vault.totalSupply(), 0);
        assertEq(vault.totalAssets(), 0);
        assertEq(vault.balanceOf(owner), 0);
        assertEq(vault.allowance(owner, receiver), 0);
        assertEq(vault.convertToShares(assets), assets);
        assertEq(vault.convertToAssets(shares), shares);
        assertEq(vault.previewDeposit(assets), assets);
        assertEq(vault.previewMint(shares), shares);
        assertEq(vault.previewWithdraw(assets), assets);
        assertEq(vault.previewRedeem(shares), shares);
        assertEq(vault.maxDeposit(receiver), type(uint256).max);
        assertEq(vault.maxMint(receiver), type(uint256).max);
        assertEq(vault.maxWithdraw(owner), 0);
        assertEq(vault.maxRedeem(owner), 0);
    }

    function testFuzzDepositMintsSharesAndTracksAssets(address receiver, uint256 rawAssets) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);

        vm.recordLogs();
        uint256 shares = vault.deposit(assets, receiver);
        Vm.Log[] memory logs = vm.getRecordedLogs();

        assertEq(shares, assets);
        assertEq(vault.balanceOf(receiver), assets);
        assertEq(vault.totalSupply(), assets);
        assertEq(vault.totalAssets(), assets);
        assertEq(assetToken.balanceOf(address(vault)), assets);
        assertHasLog2(logs, address(vault), TRANSFER_TOPIC, address(0), receiver, abi.encode(assets));
        assertHasLog2(logs, address(vault), DEPOSIT_TOPIC, address(this), receiver, abi.encode(assets, assets));
    }

    function testFuzzMintPullsAssetsAndMintsShares(address receiver, uint256 rawShares) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 shares = small(rawShares);
        assetToken.mint(address(this), shares);
        assetToken.approve(address(vault), shares);

        vm.recordLogs();
        uint256 assets = vault.mint(shares, receiver);
        Vm.Log[] memory logs = vm.getRecordedLogs();

        assertEq(assets, shares);
        assertEq(vault.balanceOf(receiver), shares);
        assertEq(vault.totalSupply(), shares);
        assertEq(vault.totalAssets(), assets);
        assertEq(assetToken.balanceOf(address(vault)), assets);
        assertHasLog2(logs, address(vault), TRANSFER_TOPIC, address(0), receiver, abi.encode(shares));
        assertHasLog2(logs, address(vault), DEPOSIT_TOPIC, address(this), receiver, abi.encode(assets, shares));
    }

    function testFuzzApproveUpdatesShareAllowance(address spender, uint256 amount) public {
        (, ERC4626Iface vault) = deployPair();
        vm.expectEmit(true, true, false, true, address(vault));
        emit Approval(address(this), spender, amount);
        assertTrue(vault.approve(spender, amount));
        assertEq(vault.allowance(address(this), spender), amount);
    }

    function testFuzzShareTransferMovesBalances(address receiver, uint256 rawDeposit, uint256 rawTransfer) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 amount = deposited == 0 ? 0 : rawTransfer % (deposited + 1);
        uint256 receiverBefore = vault.balanceOf(receiver);

        vm.expectEmit(true, true, false, true, address(vault));
        emit Transfer(address(this), receiver, amount);
        assertTrue(vault.transfer(receiver, amount));

        if (receiver == address(this)) {
            assertEq(vault.balanceOf(address(this)), deposited);
        } else {
            assertEq(vault.balanceOf(address(this)), deposited - amount);
            assertEq(vault.balanceOf(receiver), receiverBefore + amount);
        }
        assertEq(vault.totalSupply(), deposited);
        assertEq(vault.totalAssets(), deposited);
    }

    function testFuzzShareTransferFromUpdatesAllowance(address spender, address receiver, uint256 rawDeposit, uint256 rawSpend) public {
        vm.assume(spender != address(this));
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 amount = deposited == 0 ? 0 : rawSpend % (deposited + 1);
        assertTrue(vault.approve(spender, deposited));

        vm.expectEmit(true, true, false, true, address(vault));
        emit Transfer(address(this), receiver, amount);
        vm.prank(spender);
        assertTrue(vault.transferFrom(address(this), receiver, amount));

        assertEq(vault.allowance(address(this), spender), deposited - amount);
        assertEq(vault.totalSupply(), deposited);
    }

    function testFuzzShareTransferFromKeepsInfiniteAllowance(address spender, address receiver, uint256 rawDeposit, uint256 rawSpend) public {
        vm.assume(spender != address(this));
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 amount = deposited == 0 ? 0 : rawSpend % (deposited + 1);
        assertTrue(vault.approve(spender, type(uint256).max));

        vm.expectEmit(true, true, false, true, address(vault));
        emit Transfer(address(this), receiver, amount);
        vm.prank(spender);
        assertTrue(vault.transferFrom(address(this), receiver, amount));

        assertEq(vault.allowance(address(this), spender), type(uint256).max);
    }

    function testFuzzWithdrawBurnsSharesAndSendsAssets(address receiver, uint256 rawDeposit, uint256 rawWithdraw) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        vm.assume(receiver != address(0));
        vm.assume(receiver != address(vault));
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 assets = deposited == 0 ? 0 : rawWithdraw % (deposited + 1);
        uint256 receiverBefore = assetToken.balanceOf(receiver);

        vm.recordLogs();
        uint256 shares = vault.withdraw(assets, receiver, address(this));
        Vm.Log[] memory logs = vm.getRecordedLogs();

        assertEq(shares, assets);
        assertEq(vault.balanceOf(address(this)), deposited - shares);
        assertEq(vault.totalSupply(), deposited - shares);
        assertEq(vault.totalAssets(), deposited - assets);
        assertEq(assetToken.balanceOf(receiver), receiverBefore + assets);
        assertHasLog2(logs, address(vault), TRANSFER_TOPIC, address(this), address(0), abi.encode(shares));
        assertHasLog3(logs, address(vault), WITHDRAW_TOPIC, address(this), receiver, address(this), abi.encode(assets, shares));
    }

    function testFuzzRedeemBurnsSharesAndSendsAssets(address receiver, uint256 rawDeposit, uint256 rawRedeem) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        vm.assume(receiver != address(0));
        vm.assume(receiver != address(vault));
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 shares = deposited == 0 ? 0 : rawRedeem % (deposited + 1);
        uint256 receiverBefore = assetToken.balanceOf(receiver);

        vm.recordLogs();
        uint256 assets = vault.redeem(shares, receiver, address(this));
        Vm.Log[] memory logs = vm.getRecordedLogs();

        assertEq(assets, shares);
        assertEq(vault.balanceOf(address(this)), deposited - shares);
        assertEq(vault.totalSupply(), deposited - shares);
        assertEq(vault.totalAssets(), deposited - assets);
        assertEq(assetToken.balanceOf(receiver), receiverBefore + assets);
        assertHasLog2(logs, address(vault), TRANSFER_TOPIC, address(this), address(0), abi.encode(shares));
        assertHasLog3(logs, address(vault), WITHDRAW_TOPIC, address(this), receiver, address(this), abi.encode(assets, shares));
    }

    function testFuzzWithdrawRequiresShareAllowance(address spender, uint256 rawDeposit, uint256 rawWithdraw) public {
        vm.assume(spender != address(this));
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit) + 1;
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 assets = (rawWithdraw % deposited) + 1;

        vm.prank(spender);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient allowance"));
        vault.withdraw(assets, spender, address(this));
        assertEq(vault.balanceOf(address(this)), deposited);
        assertEq(vault.totalAssets(), deposited);
    }

    function testFuzzWithdrawMoreThanMaxReverts(uint256 rawDeposit) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));

        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Withdraw more than max"));
        vault.withdraw(deposited + 1, address(this), address(this));
    }

    function testFuzzRedeemRequiresShareAllowance(address spender, uint256 rawDeposit, uint256 rawRedeem) public {
        vm.assume(spender != address(this));
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit) + 1;
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 shares = (rawRedeem % deposited) + 1;

        vm.prank(spender);
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Insufficient allowance"));
        vault.redeem(shares, spender, address(this));
        assertEq(vault.balanceOf(address(this)), deposited);
        assertEq(vault.totalAssets(), deposited);
    }

    function testFuzzRedeemMoreThanMaxReverts(uint256 rawDeposit) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));

        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Redeem more than max"));
        vault.redeem(deposited + 1, address(this), address(this));
    }

    function positiveSmall(uint256 raw) internal pure returns (uint256) {
        return (raw % 1e18) + 1;
    }

    function shareWealth(ERC20Iface assetToken, ERC4626Iface vault, address account) internal view returns (uint256) {
        return assetToken.balanceOf(account) + vault.convertToAssets(vault.balanceOf(account));
    }

    function donateToVault(ERC20Iface assetToken, ERC4626Iface vault, uint256 amount) internal {
        assetToken.mint(address(this), amount);
        assetToken.transfer(address(vault), amount);
    }

    function distributeYield(ERC20Iface assetToken, ERC4626Iface vault, uint256 amount) internal {
        assetToken.mint(address(vault), amount);
        vm.store(address(vault), storageSlot(4), bytes32(vault.totalAssets() + amount));
    }

    function vaultSurplus(ERC20Iface assetToken, ERC4626Iface vault) internal view returns (uint256) {
        return assetToken.balanceOf(address(vault)) - vault.totalAssets();
    }

    struct ClosedWorldTrace {
        ERC20Iface assetToken;
        ERC4626Iface vault;
        address alice;
        address bob;
        uint256 initialAssets;
        uint256 donationAmount;
        uint256 yieldAmount;
        uint256 fixedShares;
        uint256 fixedValueBefore;
    }

    function runClosedWorldFuzzTrace(
        uint256 rawDeposit,
        uint256 rawDonation,
        uint256 rawYield,
        uint256 rawTransfer,
        uint256 rawTransferFrom,
        uint256 rawWithdraw,
        uint256 rawRedeem,
        uint256 rawFixedShares
    ) internal returns (ClosedWorldTrace memory trace) {
        trace.alice = address(0xA11CE);
        trace.bob = address(0xB0B);
        (trace.assetToken, trace.vault) = deployPair();

        trace.initialAssets = positiveSmall(rawDeposit);
        seedDeposit(trace.assetToken, trace.vault, trace.initialAssets, trace.alice);
        trace.fixedShares = rawFixedShares % (trace.initialAssets + 1);
        trace.fixedValueBefore = trace.vault.convertToAssets(trace.fixedShares);

        trace.donationAmount = small(rawDonation);
        donateToVault(trace.assetToken, trace.vault, trace.donationAmount);

        trace.yieldAmount = small(rawYield);
        distributeYield(trace.assetToken, trace.vault, trace.yieldAmount);

        uint256 transferAmount = rawTransfer % (trace.initialAssets + 1);
        vm.prank(trace.alice);
        trace.vault.transfer(trace.bob, transferAmount);

        uint256 aliceAfterTransfer = trace.vault.balanceOf(trace.alice);
        uint256 transferFromAmount = rawTransferFrom % (aliceAfterTransfer + 1);
        vm.prank(trace.alice);
        trace.vault.approve(trace.bob, transferFromAmount);
        vm.prank(trace.bob);
        trace.vault.transferFrom(trace.alice, trace.bob, transferFromAmount);

        uint256 bobMaxWithdraw = trace.vault.maxWithdraw(trace.bob);
        uint256 withdrawAssets = bobMaxWithdraw == 0 ? 0 : rawWithdraw % (bobMaxWithdraw + 1);
        vm.prank(trace.bob);
        trace.vault.withdraw(withdrawAssets, trace.bob, trace.bob);

        uint256 bobRedeemable = trace.vault.maxRedeem(trace.bob);
        uint256 redeemShares = bobRedeemable == 0 ? 0 : rawRedeem % (bobRedeemable + 1);
        vm.prank(trace.bob);
        trace.vault.redeem(redeemShares, trace.bob, trace.bob);
    }

    // tama: mirrors=erc4626_deposit_pulls_assets_from_sender
    function testFuzzDepositPullsAssetsFromSender(uint256 rawAssets) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);
        uint256 senderBefore = assetToken.balanceOf(address(this));
        vault.deposit(assets, address(this));
        assertEq(assetToken.balanceOf(address(this)), senderBefore - assets);
    }

    // tama: mirrors=erc4626_deposit_increases_vault_asset_balance
    function testFuzzDepositIncreasesVaultAssetBalance(uint256 rawAssets) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);
        uint256 vaultBefore = assetToken.balanceOf(address(vault));
        vault.deposit(assets, address(this));
        assertEq(assetToken.balanceOf(address(vault)), vaultBefore + assets);
    }

    // tama: mirrors=erc4626_mint_pulls_required_assets_from_sender
    function testFuzzMintPullsRequiredAssetsFromSender(uint256 rawShares) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 shares = small(rawShares);
        uint256 requiredAssets = vault.previewMint(shares);
        assetToken.mint(address(this), requiredAssets);
        assetToken.approve(address(vault), requiredAssets);
        uint256 senderBefore = assetToken.balanceOf(address(this));
        vault.mint(shares, address(this));
        assertEq(assetToken.balanceOf(address(this)), senderBefore - requiredAssets);
    }

    // tama: mirrors=erc4626_mint_increases_vault_asset_balance
    function testFuzzMintIncreasesVaultAssetBalance(uint256 rawShares) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 shares = small(rawShares);
        uint256 requiredAssets = vault.previewMint(shares);
        assetToken.mint(address(this), requiredAssets);
        assetToken.approve(address(vault), requiredAssets);
        uint256 vaultBefore = assetToken.balanceOf(address(vault));
        vault.mint(shares, address(this));
        assertEq(assetToken.balanceOf(address(vault)), vaultBefore + requiredAssets);
    }

    // tama: mirrors=erc4626_withdraw_sends_assets_to_receiver
    function testFuzzWithdrawSendsAssetsToReceiver(address rawReceiver, uint256 rawDeposit, uint256 rawWithdraw) public {
        address receiver = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        vm.assume(receiver != address(vault));
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 assets = deposited == 0 ? 0 : rawWithdraw % (deposited + 1);
        uint256 receiverBefore = assetToken.balanceOf(receiver);
        vault.withdraw(assets, receiver, address(this));
        assertEq(assetToken.balanceOf(receiver), receiverBefore + assets);
    }

    // tama: mirrors=erc4626_withdraw_decreases_vault_asset_balance
    function testFuzzWithdrawDecreasesVaultAssetBalance(address rawReceiver, uint256 rawDeposit, uint256 rawWithdraw) public {
        address receiver = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        vm.assume(receiver != address(vault));
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 assets = deposited == 0 ? 0 : rawWithdraw % (deposited + 1);
        uint256 vaultBefore = assetToken.balanceOf(address(vault));
        vault.withdraw(assets, receiver, address(this));
        assertEq(assetToken.balanceOf(address(vault)), vaultBefore - assets);
    }

    // tama: mirrors=erc4626_redeem_sends_redeemed_assets_to_receiver
    function testFuzzRedeemSendsRedeemedAssetsToReceiver(address rawReceiver, uint256 rawDeposit, uint256 rawRedeem) public {
        address receiver = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        vm.assume(receiver != address(vault));
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 shares = deposited == 0 ? 0 : rawRedeem % (deposited + 1);
        uint256 expectedAssets = vault.previewRedeem(shares);
        uint256 receiverBefore = assetToken.balanceOf(receiver);
        vault.redeem(shares, receiver, address(this));
        assertEq(assetToken.balanceOf(receiver), receiverBefore + expectedAssets);
    }

    // tama: mirrors=erc4626_redeem_decreases_vault_asset_balance
    function testFuzzRedeemDecreasesVaultAssetBalance(address rawReceiver, uint256 rawDeposit, uint256 rawRedeem) public {
        address receiver = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        vm.assume(receiver != address(vault));
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 shares = deposited == 0 ? 0 : rawRedeem % (deposited + 1);
        uint256 expectedAssets = vault.previewRedeem(shares);
        uint256 vaultBefore = assetToken.balanceOf(address(vault));
        vault.redeem(shares, receiver, address(this));
        assertEq(assetToken.balanceOf(address(vault)), vaultBefore - expectedAssets);
    }

    // tama: mirrors=erc4626_deposit_revert_keeps_asset_balances
    function testFuzzDepositRevertKeepsAssetBalances(address rawReceiver, uint256 rawAssets) public {
        address receiver = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = positiveSmall(rawAssets);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);
        vm.store(address(vault), balanceSlot(receiver), bytes32(type(uint256).max));
        uint256 senderBefore = assetToken.balanceOf(address(this));
        uint256 vaultBefore = assetToken.balanceOf(address(vault));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Balance overflow"));
        vault.deposit(assets, receiver);
        assertEq(assetToken.balanceOf(address(this)), senderBefore);
        assertEq(assetToken.balanceOf(address(vault)), vaultBefore);
    }

    // tama: mirrors=erc4626_mint_revert_keeps_asset_balances
    function testFuzzMintRevertKeepsAssetBalances(address rawReceiver, uint256 rawShares) public {
        address receiver = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 shares = positiveSmall(rawShares);
        uint256 assets = vault.previewMint(shares);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);
        vm.store(address(vault), balanceSlot(receiver), bytes32(type(uint256).max));
        uint256 senderBefore = assetToken.balanceOf(address(this));
        uint256 vaultBefore = assetToken.balanceOf(address(vault));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Balance overflow"));
        vault.mint(shares, receiver);
        assertEq(assetToken.balanceOf(address(this)), senderBefore);
        assertEq(assetToken.balanceOf(address(vault)), vaultBefore);
    }

    // tama: mirrors=erc4626_withdraw_revert_keeps_asset_balances
    function testFuzzWithdrawRevertKeepsAssetBalances(address rawReceiver, uint256 rawDeposit, uint256 rawExtra) public {
        address receiver = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        uint256 extra = positiveSmall(rawExtra);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 senderBefore = assetToken.balanceOf(address(this));
        uint256 vaultBefore = assetToken.balanceOf(address(vault));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Withdraw more than max"));
        vault.withdraw(deposited + extra, receiver, address(this));
        assertEq(assetToken.balanceOf(address(this)), senderBefore);
        assertEq(assetToken.balanceOf(address(vault)), vaultBefore);
    }

    // tama: mirrors=erc4626_redeem_revert_keeps_asset_balances
    function testFuzzRedeemRevertKeepsAssetBalances(address rawReceiver, uint256 rawDeposit, uint256 rawExtra) public {
        address receiver = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        uint256 extra = positiveSmall(rawExtra);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 senderBefore = assetToken.balanceOf(address(this));
        uint256 vaultBefore = assetToken.balanceOf(address(vault));
        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Redeem more than max"));
        vault.redeem(deposited + extra, receiver, address(this));
        assertEq(assetToken.balanceOf(address(this)), senderBefore);
        assertEq(assetToken.balanceOf(address(vault)), vaultBefore);
    }

    // tama: mirrors=erc4626_no_donation_deposit_preserves_backing
    function testFuzzNoDonationDepositPreservesBacking(uint256 rawAssets) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = small(rawAssets);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);
        vault.deposit(assets, address(this));
        assertEq(assetToken.balanceOf(address(vault)), vault.totalAssets());
    }

    // tama: mirrors=erc4626_no_donation_mint_preserves_backing
    function testFuzzNoDonationMintPreservesBacking(uint256 rawShares) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 shares = small(rawShares);
        uint256 assets = vault.previewMint(shares);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);
        vault.mint(shares, address(this));
        assertEq(assetToken.balanceOf(address(vault)), vault.totalAssets());
    }

    // tama: mirrors=erc4626_no_donation_withdraw_preserves_backing
    function testFuzzNoDonationWithdrawPreservesBacking(uint256 rawDeposit, uint256 rawWithdraw) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 assets = deposited == 0 ? 0 : rawWithdraw % (deposited + 1);
        vault.withdraw(assets, address(this), address(this));
        assertEq(assetToken.balanceOf(address(vault)), vault.totalAssets());
    }

    // tama: mirrors=erc4626_no_donation_redeem_preserves_backing
    function testFuzzNoDonationRedeemPreservesBacking(uint256 rawDeposit, uint256 rawRedeem) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 shares = deposited == 0 ? 0 : rawRedeem % (deposited + 1);
        vault.redeem(shares, address(this), address(this));
        assertEq(assetToken.balanceOf(address(vault)), vault.totalAssets());
    }

    // tama: mirrors=erc4626_donation_permitted_backing_covers_total_assets
    function testFuzzDonationPermittedBackingCoversTotalAssets(uint256 rawDeposit, uint256 rawDonation) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        uint256 donation = small(rawDonation);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 totalAssetsBefore = vault.totalAssets();
        assetToken.mint(address(this), donation);
        assetToken.transfer(address(vault), donation);
        assertEq(vault.totalAssets(), totalAssetsBefore);
        assertGe(assetToken.balanceOf(address(vault)), vault.totalAssets());
    }

    // tama: mirrors=erc4626_transfer_keeps_total_assets_and_backing
    function testFuzzTransferKeepsTotalAssetsAndBacking(address rawReceiver, uint256 rawDeposit, uint256 rawTransfer) public {
        address receiver = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 totalAssetsBefore = vault.totalAssets();
        uint256 amount = deposited == 0 ? 0 : rawTransfer % (deposited + 1);
        vault.transfer(receiver, amount);
        assertEq(vault.totalAssets(), totalAssetsBefore);
        assertGe(assetToken.balanceOf(address(vault)), vault.totalAssets());
    }

    // tama: mirrors=erc4626_transferFrom_keeps_total_assets_and_backing
    function testFuzzTransferFromKeepsTotalAssetsAndBacking(address rawSpender, address rawReceiver, uint256 rawDeposit, uint256 rawSpend) public {
        address spender = nonzeroReceiver(rawSpender);
        address receiver = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 totalAssetsBefore = vault.totalAssets();
        uint256 amount = deposited == 0 ? 0 : rawSpend % (deposited + 1);
        vault.approve(spender, deposited);
        vm.prank(spender);
        vault.transferFrom(address(this), receiver, amount);
        assertEq(vault.totalAssets(), totalAssetsBefore);
        assertGe(assetToken.balanceOf(address(vault)), vault.totalAssets());
    }

    // tama: mirrors=erc4626_approve_keeps_total_assets_and_backing
    function testFuzzApproveKeepsTotalAssetsAndBacking(address spender, uint256 rawDeposit, uint256 allowanceAmount) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 totalAssetsBefore = vault.totalAssets();
        vault.approve(spender, allowanceAmount);
        assertEq(vault.totalAssets(), totalAssetsBefore);
        assertGe(assetToken.balanceOf(address(vault)), vault.totalAssets());
    }

    // tama: mirrors=erc4626_deposit_preserves_fixed_share_value
    function testFuzzDepositPreservesFixedShareValue(uint256 rawInitial, uint256 rawDeposit, uint256 rawFixedShares) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 initialAssets = small(rawInitial);
        uint256 assets = small(rawDeposit);
        uint256 fixedShares = small(rawFixedShares);
        seedDeposit(assetToken, vault, initialAssets, address(this));
        uint256 beforeValue = vault.convertToAssets(fixedShares);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);
        vault.deposit(assets, address(this));
        assertGe(vault.convertToAssets(fixedShares), beforeValue);
    }

    // tama: mirrors=erc4626_mint_preserves_fixed_share_value
    function testFuzzMintPreservesFixedShareValue(uint256 rawInitial, uint256 rawMint, uint256 rawFixedShares) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 initialAssets = small(rawInitial);
        uint256 shares = small(rawMint);
        uint256 fixedShares = small(rawFixedShares);
        seedDeposit(assetToken, vault, initialAssets, address(this));
        uint256 beforeValue = vault.convertToAssets(fixedShares);
        uint256 assets = vault.previewMint(shares);
        assetToken.mint(address(this), assets);
        assetToken.approve(address(vault), assets);
        vault.mint(shares, address(this));
        assertGe(vault.convertToAssets(fixedShares), beforeValue);
    }

    // tama: mirrors=erc4626_withdraw_preserves_fixed_share_value
    function testFuzzWithdrawPreservesFixedShareValue(uint256 rawDeposit, uint256 rawWithdraw, uint256 rawFixedShares) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        uint256 fixedShares = small(rawFixedShares);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 beforeValue = vault.convertToAssets(fixedShares);
        uint256 assets = deposited == 0 ? 0 : rawWithdraw % (deposited + 1);
        vault.withdraw(assets, address(this), address(this));
        assertGe(vault.convertToAssets(fixedShares), beforeValue);
    }

    // tama: mirrors=erc4626_redeem_preserves_fixed_share_value
    function testFuzzRedeemPreservesFixedShareValue(uint256 rawDeposit, uint256 rawRedeem, uint256 rawFixedShares) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        uint256 fixedShares = small(rawFixedShares);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 beforeValue = vault.convertToAssets(fixedShares);
        uint256 shares = deposited == 0 ? 0 : rawRedeem % (deposited + 1);
        vault.redeem(shares, address(this), address(this));
        assertGe(vault.convertToAssets(fixedShares), beforeValue);
    }

    // tama: mirrors=erc4626_transfer_keeps_convertToAssets
    function testFuzzTransferKeepsConvertToAssets(address rawReceiver, uint256 rawDeposit, uint256 rawTransfer, uint256 rawFixedShares) public {
        address receiver = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        uint256 fixedShares = small(rawFixedShares);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 beforeValue = vault.convertToAssets(fixedShares);
        uint256 amount = deposited == 0 ? 0 : rawTransfer % (deposited + 1);
        vault.transfer(receiver, amount);
        assertEq(vault.convertToAssets(fixedShares), beforeValue);
    }

    // tama: mirrors=erc4626_transferFrom_keeps_convertToAssets
    function testFuzzTransferFromKeepsConvertToAssets(address rawSpender, address rawReceiver, uint256 rawDeposit, uint256 rawSpend, uint256 rawFixedShares) public {
        address spender = nonzeroReceiver(rawSpender);
        address receiver = nonzeroReceiver(rawReceiver);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        uint256 fixedShares = small(rawFixedShares);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 beforeValue = vault.convertToAssets(fixedShares);
        uint256 amount = deposited == 0 ? 0 : rawSpend % (deposited + 1);
        vault.approve(spender, deposited);
        vm.prank(spender);
        vault.transferFrom(address(this), receiver, amount);
        assertEq(vault.convertToAssets(fixedShares), beforeValue);
    }

    // tama: mirrors=erc4626_approve_keeps_convertToAssets
    function testFuzzApproveKeepsConvertToAssets(address spender, uint256 rawDeposit, uint256 rawFixedShares, uint256 allowanceAmount) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        uint256 fixedShares = small(rawFixedShares);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 beforeValue = vault.convertToAssets(fixedShares);
        vault.approve(spender, allowanceAmount);
        assertEq(vault.convertToAssets(fixedShares), beforeValue);
    }

    // tama: mirrors=erc4626_deposit_then_redeem_no_profit
    function testFuzzDepositThenRedeemNoProfit(uint256 rawAssets) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = positiveSmall(rawAssets);
        assetToken.mint(address(this), assets);
        uint256 wealthBefore = shareWealth(assetToken, vault, address(this));
        assetToken.approve(address(vault), assets);
        uint256 shares = vault.deposit(assets, address(this));
        vault.redeem(shares, address(this), address(this));
        assertLe(shareWealth(assetToken, vault, address(this)), wealthBefore);
    }

    // tama: mirrors=erc4626_mint_then_redeem_no_profit
    function testFuzzMintThenRedeemNoProfit(uint256 rawShares) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 shares = positiveSmall(rawShares);
        uint256 assets = vault.previewMint(shares);
        assetToken.mint(address(this), assets);
        uint256 wealthBefore = shareWealth(assetToken, vault, address(this));
        assetToken.approve(address(vault), assets);
        vault.mint(shares, address(this));
        vault.redeem(shares, address(this), address(this));
        assertLe(shareWealth(assetToken, vault, address(this)), wealthBefore);
    }

    // tama: mirrors=erc4626_deposit_then_withdraw_no_profit
    function testFuzzDepositThenWithdrawNoProfit(uint256 rawAssets) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 assets = positiveSmall(rawAssets);
        assetToken.mint(address(this), assets);
        uint256 wealthBefore = shareWealth(assetToken, vault, address(this));
        assetToken.approve(address(vault), assets);
        vault.deposit(assets, address(this));
        vault.withdraw(assets, address(this), address(this));
        assertLe(shareWealth(assetToken, vault, address(this)), wealthBefore);
    }

    // tama: mirrors=erc4626_mint_then_withdraw_no_profit
    function testFuzzMintThenWithdrawNoProfit(uint256 rawShares) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 shares = positiveSmall(rawShares);
        uint256 assets = vault.previewMint(shares);
        assetToken.mint(address(this), assets);
        uint256 wealthBefore = shareWealth(assetToken, vault, address(this));
        assetToken.approve(address(vault), assets);
        vault.mint(shares, address(this));
        vault.withdraw(assets, address(this), address(this));
        assertLe(shareWealth(assetToken, vault, address(this)), wealthBefore);
    }

    // tama: mirrors=erc4626_closed_world_donation_keeps_managed_accounting_and_exchange_rate
    function testFuzzClosedWorldDonationKeepsManagedAccountingAndExchangeRate(
        uint256 rawDeposit,
        uint256 rawDonation,
        uint256 rawFixedShares,
        uint256 rawProbeAssets
    ) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = positiveSmall(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 fixedShares = rawFixedShares % (deposited + 1);
        uint256 probeAssets = small(rawProbeAssets);
        uint256 totalAssetsBefore = vault.totalAssets();
        uint256 totalSupplyBefore = vault.totalSupply();
        uint256 fixedValueBefore = vault.convertToAssets(fixedShares);
        uint256 shareQuoteBefore = vault.convertToShares(probeAssets);
        uint256 vaultBalanceBefore = assetToken.balanceOf(address(vault));

        uint256 donation = small(rawDonation);
        donateToVault(assetToken, vault, donation);

        assertEq(vault.totalAssets(), totalAssetsBefore);
        assertEq(vault.totalSupply(), totalSupplyBefore);
        assertEq(vault.convertToAssets(fixedShares), fixedValueBefore);
        assertEq(vault.convertToShares(probeAssets), shareQuoteBefore);
        assertEq(assetToken.balanceOf(address(vault)), vaultBalanceBefore + donation);
    }

    // tama: mirrors=erc4626_closed_world_yield_distribution_preserves_backing_and_supply
    function testFuzzClosedWorldYieldDistributionPreservesBackingAndSupply(
        uint256 rawDeposit,
        uint256 rawYield,
        uint256 rawFixedShares,
        uint256 rawProbeAssets
    ) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = positiveSmall(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        uint256 fixedShares = rawFixedShares % (deposited + 1);
        uint256 probeAssets = small(rawProbeAssets);
        uint256 totalSupplyBefore = vault.totalSupply();
        uint256 fixedValueBefore = vault.convertToAssets(fixedShares);

        distributeYield(assetToken, vault, small(rawYield));

        assertGe(assetToken.balanceOf(address(vault)), vault.totalAssets());
        assertEq(vault.totalSupply(), totalSupplyBefore);
        assertGe(vault.convertToAssets(fixedShares), fixedValueBefore);
        assertLe(vault.convertToShares(probeAssets), probeAssets);
    }

    // tama: mirrors=erc4626_closed_world_deposit_donate_victim_deposit_redeem_no_profit
    function testFuzzClosedWorldDepositDonateVictimDepositRedeemNoProfit(
        uint256 rawAttackerDeposit,
        uint256 rawDonation,
        uint256 rawVictimDeposit
    ) public {
        address attacker = address(0xA77A);
        address victim = address(0xBEEF);
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 attackerDeposit = positiveSmall(rawAttackerDeposit);
        uint256 donation = small(rawDonation);
        uint256 victimDeposit = positiveSmall(rawVictimDeposit);

        assetToken.mint(attacker, attackerDeposit + donation);
        uint256 attackerWealthBefore = assetToken.balanceOf(attacker);
        vm.prank(attacker);
        assetToken.approve(address(vault), attackerDeposit);
        vm.prank(attacker);
        uint256 attackerShares = vault.deposit(attackerDeposit, attacker);
        vm.prank(attacker);
        assetToken.transfer(address(vault), donation);

        assetToken.mint(victim, victimDeposit);
        vm.prank(victim);
        assetToken.approve(address(vault), victimDeposit);
        vm.prank(victim);
        vault.deposit(victimDeposit, victim);

        vm.prank(attacker);
        vault.redeem(attackerShares, attacker, attacker);
        assertLe(assetToken.balanceOf(attacker), attackerWealthBefore);
    }

    // tama: mirrors=erc4626_closed_world_donation_surplus_not_withdrawable_without_yield_recognition
    function testFuzzClosedWorldDonationSurplusNotWithdrawableWithoutYieldRecognition(
        uint256 rawDeposit,
        uint256 rawDonation,
        uint256 rawWithdraw,
        uint256 rawRedeem
    ) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = positiveSmall(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));
        donateToVault(assetToken, vault, small(rawDonation));
        uint256 surplusBefore = vaultSurplus(assetToken, vault);

        uint256 maxAssets = vault.maxWithdraw(address(this));
        uint256 withdrawAssets = maxAssets == 0 ? 0 : rawWithdraw % (maxAssets + 1);
        vault.withdraw(withdrawAssets, address(this), address(this));
        assertEq(vaultSurplus(assetToken, vault), surplusBefore);

        uint256 maxShares = vault.maxRedeem(address(this));
        uint256 redeemShares = maxShares == 0 ? 0 : rawRedeem % (maxShares + 1);
        vault.redeem(redeemShares, address(this), address(this));
        assertEq(vaultSurplus(assetToken, vault), surplusBefore);
    }

    // tama: mirrors=erc4626_closed_world_managed_assets_cover_share_supply
    function testFuzzClosedWorldManagedAssetsCoverShareSupply(
        uint256 rawDeposit,
        uint256 rawDonation,
        uint256 rawYield,
        uint256 rawTransfer,
        uint256 rawTransferFrom,
        uint256 rawWithdraw,
        uint256 rawRedeem,
        uint256 rawFixedShares
    ) public {
        ClosedWorldTrace memory trace = runClosedWorldFuzzTrace(
            rawDeposit, rawDonation, rawYield, rawTransfer, rawTransferFrom, rawWithdraw, rawRedeem, rawFixedShares
        );
        assertGe(trace.vault.totalAssets(), trace.vault.totalSupply());
    }

    // tama: mirrors=erc4626_closed_world_preserves_vault_asset_backing
    function testFuzzClosedWorldPreservesVaultAssetBacking(
        uint256 rawDeposit,
        uint256 rawDonation,
        uint256 rawYield,
        uint256 rawTransfer,
        uint256 rawTransferFrom,
        uint256 rawWithdraw,
        uint256 rawRedeem,
        uint256 rawFixedShares
    ) public {
        ClosedWorldTrace memory trace = runClosedWorldFuzzTrace(
            rawDeposit, rawDonation, rawYield, rawTransfer, rawTransferFrom, rawWithdraw, rawRedeem, rawFixedShares
        );
        assertGe(trace.assetToken.balanceOf(address(trace.vault)), trace.vault.totalAssets());
    }

    // tama: mirrors=erc4626_closed_world_convertToAssets_at_least_identity
    function testFuzzClosedWorldConvertToAssetsAtLeastIdentity(
        uint256 rawDeposit,
        uint256 rawDonation,
        uint256 rawYield,
        uint256 rawTransfer,
        uint256 rawTransferFrom,
        uint256 rawWithdraw,
        uint256 rawRedeem,
        uint256 rawFixedShares
    ) public {
        ClosedWorldTrace memory trace = runClosedWorldFuzzTrace(
            rawDeposit, rawDonation, rawYield, rawTransfer, rawTransferFrom, rawWithdraw, rawRedeem, rawFixedShares
        );
        assertGe(trace.vault.convertToAssets(trace.fixedShares), trace.fixedShares);
    }

    // tama: mirrors=erc4626_closed_world_convertToShares_at_most_identity
    function testFuzzClosedWorldConvertToSharesAtMostIdentity(
        uint256 rawDeposit,
        uint256 rawDonation,
        uint256 rawYield,
        uint256 rawTransfer,
        uint256 rawTransferFrom,
        uint256 rawWithdraw,
        uint256 rawRedeem,
        uint256 rawFixedShares
    ) public {
        ClosedWorldTrace memory trace = runClosedWorldFuzzTrace(
            rawDeposit, rawDonation, rawYield, rawTransfer, rawTransferFrom, rawWithdraw, rawRedeem, rawFixedShares
        );
        assertLe(trace.vault.convertToShares(trace.fixedShares), trace.fixedShares);
    }

    // tama: mirrors=erc4626_closed_world_fixed_share_value_never_decreases
    function testFuzzClosedWorldFixedShareValueNeverDecreases(
        uint256 rawDeposit,
        uint256 rawDonation,
        uint256 rawYield,
        uint256 rawTransfer,
        uint256 rawTransferFrom,
        uint256 rawWithdraw,
        uint256 rawRedeem,
        uint256 rawFixedShares
    ) public {
        ClosedWorldTrace memory trace = runClosedWorldFuzzTrace(
            rawDeposit, rawDonation, rawYield, rawTransfer, rawTransferFrom, rawWithdraw, rawRedeem, rawFixedShares
        );
        assertGe(trace.vault.convertToAssets(trace.fixedShares), trace.fixedValueBefore);
    }

    // tama: mirrors=erc4626_closed_world_caller_wealth_no_unearned_increase
    function testFuzzClosedWorldCallerWealthNoUnearnedIncrease(
        uint256 rawDeposit,
        uint256 rawDonation,
        uint256 rawYield,
        uint256 rawTransfer,
        uint256 rawTransferFrom,
        uint256 rawWithdraw,
        uint256 rawRedeem,
        uint256 rawFixedShares
    ) public {
        ClosedWorldTrace memory trace = runClosedWorldFuzzTrace(
            rawDeposit, rawDonation, rawYield, rawTransfer, rawTransferFrom, rawWithdraw, rawRedeem, rawFixedShares
        );
        address observer = address(0xC0FFEE);
        assertEq(shareWealth(trace.assetToken, trace.vault, observer), 0);
        assertLe(shareWealth(trace.assetToken, trace.vault, trace.alice), trace.initialAssets + trace.yieldAmount);
    }
}
