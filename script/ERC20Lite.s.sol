// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Script} from "forge-std/Script.sol";
import {ERC20LiteDeployer} from "../src/generated/verity/ERC20LiteDeployer.sol";
import {ERC20LiteIface} from "../src/generated/verity/ERC20LiteIface.sol";

// Run after `tama build`:
//   forge script script/ERC20Lite.s.sol:DeployERC20Lite --broadcast --rpc-url <url>
//
// The generated deployer embeds bytecode produced from the Verity/Yul build.
// Set ERC20LITE_OWNER to override the initial owner.
contract DeployERC20Lite is Script {
    function run() external returns (ERC20LiteIface token) {
        address initialOwner = vm.envOr("ERC20LITE_OWNER", msg.sender);

        vm.startBroadcast();
        token = ERC20LiteDeployer.deploy(initialOwner);
        vm.stopBroadcast();
    }
}
