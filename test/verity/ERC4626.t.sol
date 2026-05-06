// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {ERC20Deployer} from "../../src/generated/verity/ERC20Deployer.sol";
import {ERC20Iface} from "../../src/generated/verity/ERC20Iface.sol";
import {ERC4626Deployer} from "../../src/generated/verity/ERC4626Deployer.sol";
import {ERC4626Iface} from "../../src/generated/verity/ERC4626Iface.sol";
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

    // tama: mirrors=erc4626_asset_spec,erc4626_decimals_spec,erc4626_totalSupply_spec,erc4626_totalAssets_spec,erc4626_balanceOf_spec,erc4626_allowance_spec,erc4626_convertToShares_spec,erc4626_convertToAssets_spec,erc4626_maxDeposit_spec,erc4626_maxMint_spec,erc4626_maxWithdraw_spec,erc4626_maxRedeem_spec,erc4626_previewDeposit_spec,erc4626_previewMint_spec,erc4626_previewWithdraw_spec,erc4626_previewRedeem_spec
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

    // tama: mirrors=erc4626_deposit_effect,erc4626_totalAssets_spec,erc4626_totalSupply_spec,erc4626_balanceOf_spec,erc4626_convertToShares_spec,erc4626_previewDeposit_spec
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

    // tama: mirrors=erc4626_mint_effect,erc4626_totalAssets_spec,erc4626_totalSupply_spec,erc4626_balanceOf_spec,erc4626_previewMint_spec
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

    // tama: mirrors=erc4626_approve_effect,erc4626_allowance_spec
    function testFuzzApproveUpdatesShareAllowance(address spender, uint256 amount) public {
        (, ERC4626Iface vault) = deployPair();
        vm.expectEmit(true, true, false, true, address(vault));
        emit Approval(address(this), spender, amount);
        assertTrue(vault.approve(spender, amount));
        assertEq(vault.allowance(address(this), spender), amount);
    }

    // tama: mirrors=erc4626_transfer_total_supply_preserved,erc4626_transfer_balances_effect
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

    // tama: mirrors=erc4626_transferFrom_total_supply_preserved,erc4626_transferFrom_effect
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

    // tama: mirrors=erc4626_transferFrom_effect
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

    // tama: mirrors=erc4626_withdraw_effect,erc4626_maxWithdraw_spec,erc4626_previewWithdraw_spec
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

    // tama: mirrors=erc4626_redeem_effect,erc4626_maxRedeem_spec,erc4626_previewRedeem_spec
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

    // tama: mirrors=erc4626_withdraw_effect
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

    // tama: mirrors=erc4626_withdraw_effect
    function testFuzzWithdrawMoreThanMaxReverts(uint256 rawDeposit) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));

        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Withdraw more than max"));
        vault.withdraw(deposited + 1, address(this), address(this));
    }

    // tama: mirrors=erc4626_redeem_effect
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

    // tama: mirrors=erc4626_redeem_effect
    function testFuzzRedeemMoreThanMaxReverts(uint256 rawDeposit) public {
        (ERC20Iface assetToken, ERC4626Iface vault) = deployPair();
        uint256 deposited = small(rawDeposit);
        seedDeposit(assetToken, vault, deposited, address(this));

        vm.expectRevert(abi.encodeWithSignature("Error(string)", "Redeem more than max"));
        vault.redeem(deposited + 1, address(this), address(this));
    }
}
