// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {FixedPointMathLibDeployer} from "../../src/generated/verity/FixedPointMathLibDeployer.sol";
import {FixedPointMathLibIface} from "../../src/generated/verity/FixedPointMathLibIface.sol";
import {Test} from "forge-std/Test.sol";

contract FixedPointMathLibTest is Test {
    uint256 internal constant WAD = 1e18;

    function deployLib() internal returns (FixedPointMathLibIface lib_) {
        lib_ = FixedPointMathLibDeployer.deploy();
    }

    // tama: mirrors=fixed_WAD_spec
    function testFuzzWad() public {
        FixedPointMathLibIface lib_ = deployLib();
        assertEq(lib_.WAD(), WAD);
    }

    // tama: mirrors=fixed_mulDivDown_spec,fixed_mulDivUp_spec
    function testFuzzMulDiv(uint128 x, uint128 y, uint64 rawDenominator) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 denominator = uint256(rawDenominator) + 1;
        uint256 product = uint256(x) * uint256(y);
        assertEq(lib_.mulDivDown(x, y, denominator), product / denominator);
        assertEq(lib_.mulDivUp(x, y, denominator), (product + denominator - 1) / denominator);
    }

    // tama: mirrors=fixed_mulWadDown_spec,fixed_mulWadUp_spec
    function testFuzzMulWad(uint128 x, uint128 y) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 product = uint256(x) * uint256(y);
        assertEq(lib_.mulWadDown(x, y), product / WAD);
        assertEq(lib_.mulWadUp(x, y), (product + WAD - 1) / WAD);
    }

    // tama: mirrors=fixed_divWadDown_spec,fixed_divWadUp_spec
    function testFuzzDivWad(uint128 x, uint64 rawDenominator) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 denominator = uint256(rawDenominator) + 1;
        uint256 product = uint256(x) * WAD;
        assertEq(lib_.divWadDown(x, denominator), product / denominator);
        assertEq(lib_.divWadUp(x, denominator), (product + denominator - 1) / denominator);
    }

    // tama: mirrors=fixed_ceilDiv_spec
    function testFuzzCeilDiv(uint128 x, uint64 rawDenominator) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 denominator = uint256(rawDenominator) + 1;
        uint256 expected = x == 0 ? 0 : ((uint256(x) - 1) / denominator) + 1;
        assertEq(lib_.ceilDiv(x, denominator), expected);
        assertEq(lib_.ceilDiv(5, 0), 1);
    }
}
