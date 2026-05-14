// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {FixedPointMathLibDeployer} from "../../../src/generated/verity/FixedPointMathLibDeployer.sol";
import {FixedPointMathLibIface} from "../../../src/generated/verity/FixedPointMathLibIface.sol";
import {Test} from "forge-std/Test.sol";

contract FixedPointMathLibTest is Test {
    function deployLib() internal returns (FixedPointMathLibIface lib_) {
        lib_ = FixedPointMathLibDeployer.deploy();
    }

    function pow10(uint256 exponent) internal pure returns (uint256 result) {
        result = 1;
        for (uint256 i; i < exponent; ++i) {
            result *= 10;
        }
    }

    function clzReference(uint256 x) internal pure returns (uint256 result) {
        if (x == 0) {
            return 256;
        }

        while ((x & (uint256(1) << 255)) == 0) {
            ++result;
            x <<= 1;
        }
    }

    // tama: mirrors=fixedPointMathLib_saturatingAdd_returns_exact_sum_when_no_overflow
    function testFuzzSaturatingAddReturnsExactSumWhenNoOverflow(uint256 x, uint256 y) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 addResult = lib_.saturatingAdd(x, y);

        if (x <= type(uint256).max - y) {
            assertEq(addResult, x + y);
        }
    }

    // tama: mirrors=fixedPointMathLib_saturatingAdd_overflow_returns_max
    function testFuzzSaturatingAddOverflowReturnsMax(uint256 x, uint256 y) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 addResult = lib_.saturatingAdd(x, y);

        if (x > type(uint256).max - y) {
            assertEq(addResult, type(uint256).max);
        }
    }

    // tama: mirrors=fixedPointMathLib_saturatingAdd_result_at_least_left_input
    function testFuzzSaturatingAddResultAtLeastLeftInput(uint256 x, uint256 y) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 addResult = lib_.saturatingAdd(x, y);

        assertGe(addResult, x);
    }

    // tama: mirrors=fixedPointMathLib_saturatingAdd_result_at_least_right_input
    function testFuzzSaturatingAddResultAtLeastRightInput(uint256 x, uint256 y) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 addResult = lib_.saturatingAdd(x, y);

        assertGe(addResult, y);
    }

    // tama: mirrors=fixedPointMathLib_saturatingMul_returns_exact_product_when_no_overflow
    function testFuzzSaturatingMulReturnsExactProductWhenNoOverflow(uint256 x, uint256 y) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 mulResult = lib_.saturatingMul(x, y);

        if (x == 0 || y <= type(uint256).max / x) {
            assertEq(mulResult, x * y);
        }
    }

    // tama: mirrors=fixedPointMathLib_saturatingMul_overflow_returns_max
    function testFuzzSaturatingMulOverflowReturnsMax(uint256 x, uint256 y) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 mulResult = lib_.saturatingMul(x, y);

        if (x != 0 && y > type(uint256).max / x) {
            assertEq(mulResult, type(uint256).max);
        }
    }

    // tama: mirrors=fixedPointMathLib_saturatingMul_left_zero_returns_zero
    function testFuzzSaturatingMulLeftZeroReturnsZero(uint256 x, uint256 y) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 mulResult = lib_.saturatingMul(x, y);

        if (x == 0) {
            assertEq(mulResult, 0);
        }
    }

    // tama: mirrors=fixedPointMathLib_saturatingMul_right_zero_returns_zero
    function testFuzzSaturatingMulRightZeroReturnsZero(uint256 x, uint256 y) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 mulResult = lib_.saturatingMul(x, y);

        if (y == 0) {
            assertEq(mulResult, 0);
        }
    }

    // tama: mirrors=fixedPointMathLib_saturatingSub_subtrahend_at_least_input_returns_zero
    function testFuzzSaturatingSubSubtrahendAtLeastInputReturnsZero(uint256 x, uint256 y) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 subResult = lib_.saturatingSub(x, y);

        if (x <= y) {
            assertEq(subResult, 0);
        }
    }

    // tama: mirrors=fixedPointMathLib_saturatingSub_exact_when_input_at_least_subtrahend
    function testFuzzSaturatingSubExactWhenInputAtLeastSubtrahend(uint256 x, uint256 y) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 subResult = lib_.saturatingSub(x, y);

        if (y <= x) {
            assertEq(subResult + y, x);
        }
    }

    // tama: mirrors=fixedPointMathLib_saturatingSub_result_at_most_input
    function testFuzzSaturatingSubResultAtMostInput(uint256 x, uint256 y) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 subResult = lib_.saturatingSub(x, y);

        assertLe(subResult, x);
    }

    // tama: mirrors=fixedPointMathLib_dist_spec
    function testFuzzDistSpec(uint256 x, uint256 y) public {
        FixedPointMathLibIface lib_ = deployLib();

        uint256 distResult = lib_.dist(x, y);

        if (x <= y) {
            assertEq(distResult + x, y);
        }
        if (y <= x) {
            assertEq(distResult + y, x);
        }
    }

    // tama: mirrors=fixedPointMathLib_avg_twice_result_le_sum
    function testFuzzAvgTwiceResultLeSum(uint256 x, uint256 y) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.avg(x, y);
        uint256 expected = x >= y ? y + ((x - y) / 2) : x + ((y - x) / 2);

        assertEq(result, expected);
        if (x <= type(uint256).max - y && result <= type(uint256).max / 2) {
            assertLe(result * 2, x + y);
        }
    }

    // tama: mirrors=fixedPointMathLib_avg_sum_lt_twice_next_result
    function testFuzzAvgSumLtTwiceNextResult(uint256 x, uint256 y) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.avg(x, y);
        uint256 expected = x >= y ? y + ((x - y) / 2) : x + ((y - x) / 2);

        assertEq(result, expected);
        if (x <= type(uint256).max - y && result < type(uint256).max / 2) {
            assertLt(x + y, 2 * (result + 1));
        }
    }

    // tama: mirrors=fixedPointMathLib_clz_zero_returns_256
    function testFuzzClzZeroReturns256(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.clz(x);

        if (x == 0) {
            assertEq(result, 256);
        }
    }

    // tama: mirrors=fixedPointMathLib_clz_nonzero_returns_leading_zero_count
    function testFuzzClzNonzeroReturnsLeadingZeroCount(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.clz(x);

        if (x != 0) {
            assertEq(result, clzReference(x));
        }
    }

    // tama: mirrors=fixedPointMathLib_sqrt_square_le_input
    function testFuzzSqrtSquareLeInput(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.sqrt(x);

        assertLe(result, type(uint128).max);
        assertLe(result * result, x);
    }

    // tama: mirrors=fixedPointMathLib_sqrt_input_lt_next_square
    function testFuzzSqrtInputLtNextSquare(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.sqrt(x);

        assertLe(result, type(uint128).max);
        uint256 next = result + 1;
        assertLt(x / next, next);
    }

    // tama: mirrors=fixedPointMathLib_cbrt_cube_le_input
    function testFuzzCbrtCubeLeInput(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.cbrt(x);

        assertLt(result, 1 << 86);
        if (result != 0) {
            assertLe(result * result, x / result);
        }
    }

    // tama: mirrors=fixedPointMathLib_cbrt_input_lt_next_cube
    function testFuzzCbrtInputLtNextCube(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.cbrt(x);

        assertLt(result, 1 << 86);
        uint256 next = result + 1;
        assertLt(x / (next * next), next);
    }

    // tama: mirrors=fixedPointMathLib_log2_zero_returns_zero
    function testFuzzLog2ZeroReturnsZero(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log2(x);

        if (x == 0) {
            assertEq(result, 0);
        }
    }

    // tama: mirrors=fixedPointMathLib_log2_power_le_input
    function testFuzzLog2PowerLeInput(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log2(x);

        if (x == 0) return;

        assertLe(1 << result, x);
    }

    // tama: mirrors=fixedPointMathLib_log2_input_lt_next_power
    function testFuzzLog2InputLtNextPower(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log2(x);

        if (result < 255) {
            assertLt(x, 1 << (result + 1));
        } else {
            assertEq(result, 255);
        }
    }

    // tama: mirrors=fixedPointMathLib_log2Up_zero_returns_zero
    function testFuzzLog2UpZeroReturnsZero(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log2Up(x);

        if (x == 0) {
            assertEq(result, 0);
        }
    }

    // tama: mirrors=fixedPointMathLib_log2Up_input_le_power
    function testFuzzLog2UpInputLePower(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log2Up(x);

        if (result < 256) {
            assertLe(x, 1 << result);
        } else {
            assertEq(result, 256);
        }
    }

    // tama: mirrors=fixedPointMathLib_log2Up_prev_power_lt_input
    function testFuzzLog2UpPrevPowerLtInput(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log2Up(x);

        if (x > 1) {
            assertLt(1 << (result - 1), x);
        }
    }

    // tama: mirrors=fixedPointMathLib_log10_zero_returns_zero
    function testFuzzLog10ZeroReturnsZero(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log10(x);

        if (x == 0) {
            assertEq(result, 0);
        }
    }

    // tama: mirrors=fixedPointMathLib_log10_power_le_input
    function testFuzzLog10PowerLeInput(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log10(x);

        if (x == 0) return;

        assertLe(pow10(result), x);
    }

    // tama: mirrors=fixedPointMathLib_log10_input_lt_next_power
    function testFuzzLog10InputLtNextPower(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log10(x);

        if (result < 77) {
            assertLt(x, pow10(result + 1));
        } else {
            assertEq(result, 77);
        }
    }

    // tama: mirrors=fixedPointMathLib_log10Up_zero_returns_zero
    function testFuzzLog10UpZeroReturnsZero(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log10Up(x);

        if (x == 0) {
            assertEq(result, 0);
        }
    }

    // tama: mirrors=fixedPointMathLib_log10Up_input_le_power
    function testFuzzLog10UpInputLePower(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log10Up(x);

        if (result <= 77) {
            assertLe(x, pow10(result));
        } else {
            assertEq(result, 78);
        }
    }

    // tama: mirrors=fixedPointMathLib_log10Up_prev_power_lt_input
    function testFuzzLog10UpPrevPowerLtInput(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log10Up(x);

        if (x > 1) {
            assertLt(pow10(result - 1), x);
        }
    }

    // tama: mirrors=fixedPointMathLib_log256_zero_returns_zero
    function testFuzzLog256ZeroReturnsZero(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log256(x);

        if (x == 0) {
            assertEq(result, 0);
        }
    }

    // tama: mirrors=fixedPointMathLib_log256_power_le_input
    function testFuzzLog256PowerLeInput(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log256(x);

        if (x == 0) return;

        assertLe(1 << (8 * result), x);
    }

    // tama: mirrors=fixedPointMathLib_log256_input_lt_next_power
    function testFuzzLog256InputLtNextPower(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log256(x);

        if (result < 31) {
            assertLt(x, 1 << (8 * (result + 1)));
        } else {
            assertEq(result, 31);
        }
    }

    // tama: mirrors=fixedPointMathLib_log256Up_zero_returns_zero
    function testFuzzLog256UpZeroReturnsZero(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log256Up(x);

        if (x == 0) {
            assertEq(result, 0);
        }
    }

    // tama: mirrors=fixedPointMathLib_log256Up_input_le_power
    function testFuzzLog256UpInputLePower(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log256Up(x);

        if (result < 32) {
            assertLe(x, 1 << (8 * result));
        } else {
            assertEq(result, 32);
        }
    }

    // tama: mirrors=fixedPointMathLib_log256Up_prev_power_lt_input
    function testFuzzLog256UpPrevPowerLtInput(uint256 x) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.log256Up(x);

        if (x > 1) {
            assertLt(1 << (8 * (result - 1)), x);
        }
    }

    // tama: mirrors=fixedPointMathLib_clamp_invalid_range_returns_max
    function testFuzzClampInvalidRangeReturnsMax(uint256 x, uint256 minValue, uint256 maxValue) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.clamp(x, minValue, maxValue);

        if (maxValue < minValue) {
            assertEq(result, maxValue);
        }
    }

    // tama: mirrors=fixedPointMathLib_clamp_valid_range_bounds
    function testFuzzClampValidRangeBounds(uint256 x, uint256 minValue, uint256 maxValue) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.clamp(x, minValue, maxValue);

        if (minValue > maxValue) return;

        assertGe(result, minValue);
        assertLe(result, maxValue);
    }

    // tama: mirrors=fixedPointMathLib_clamp_preserves_in_range
    function testFuzzClampPreservesInRange(uint256 x, uint256 minValue, uint256 maxValue) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.clamp(x, minValue, maxValue);

        if (minValue <= x && x <= maxValue) {
            assertEq(result, x);
        }
    }

    // tama: mirrors=fixedPointMathLib_clamp_below_min_returns_min
    function testFuzzClampBelowMinReturnsMin(uint256 x, uint256 minValue, uint256 maxValue) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.clamp(x, minValue, maxValue);

        if (x < minValue && minValue <= maxValue) {
            assertEq(result, minValue);
        }
    }

    // tama: mirrors=fixedPointMathLib_clamp_above_max_returns_max
    function testFuzzClampAboveMaxReturnsMax(uint256 x, uint256 minValue, uint256 maxValue) public {
        FixedPointMathLibIface lib_ = deployLib();
        uint256 result = lib_.clamp(x, minValue, maxValue);

        if (x > maxValue) {
            assertEq(result, maxValue);
        }
    }
}
