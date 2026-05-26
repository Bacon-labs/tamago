// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {SafeTransferLibDeployer} from "../../../src/generated/verity/SafeTransferLibDeployer.sol";
import {SafeTransferLibIface} from "../../../src/generated/verity/SafeTransferLibIface.sol";
import {ERC20Deployer} from "../../../src/generated/verity/ERC20Deployer.sol";
import {ERC20Iface} from "../../../src/generated/verity/ERC20Iface.sol";
import {Test} from "forge-std/Test.sol";

/// Token that follows the modern ABI: returns `true` on success, reverts on
/// failure. Standard ERC-20 case; the optional-bool guard accepts this.
contract StandardReturnToken {
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        require(balanceOf[msg.sender] >= amount, "STANDARD_INSUFFICIENT_BALANCE");
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        return true;
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        require(allowance[from][msg.sender] >= amount, "STANDARD_INSUFFICIENT_ALLOWANCE");
        require(balanceOf[from] >= amount, "STANDARD_INSUFFICIENT_BALANCE");
        allowance[from][msg.sender] -= amount;
        balanceOf[from] -= amount;
        balanceOf[to] += amount;
        return true;
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        allowance[msg.sender][spender] = amount;
        return true;
    }
}

/// USDT-style token: returns no data on success/failure, just succeeds via
/// `STOP`. The optional-bool guard accepts an empty return only when the
/// target has code, which this contract does.
contract UsdtStyleToken {
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
    }

    function transfer(address to, uint256 amount) external {
        require(balanceOf[msg.sender] >= amount, "USDT_INSUFFICIENT_BALANCE");
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
    }

    function transferFrom(address from, address to, uint256 amount) external {
        require(allowance[from][msg.sender] >= amount, "USDT_INSUFFICIENT_ALLOWANCE");
        require(balanceOf[from] >= amount, "USDT_INSUFFICIENT_BALANCE");
        allowance[from][msg.sender] -= amount;
        balanceOf[from] -= amount;
        balanceOf[to] += amount;
    }

    function approve(address spender, uint256 amount) external {
        allowance[msg.sender][spender] = amount;
    }
}

/// Token that returns `false` on every call. The optional-bool guard must
/// reject this — silently treating a `false` return as success is the
/// historical SafeERC20 footgun this library exists to prevent.
contract FalseReturnToken {
    function transfer(address, uint256) external pure returns (bool) {
        return false;
    }

    function transferFrom(address, address, uint256) external pure returns (bool) {
        return false;
    }

    function approve(address, uint256) external pure returns (bool) {
        return false;
    }
}

/// Token whose calls return more than 32 bytes. The optional-bool guard
/// checks the first word — if it isn't `true`, it rejects regardless of
/// trailing data.
contract OversizedReturnToken {
    function transfer(address, uint256) external pure returns (bool, uint256) {
        return (true, 42);
    }

    function transferFrom(address, address, uint256) external pure returns (bool, uint256) {
        return (true, 42);
    }

    function approve(address, uint256) external pure returns (bool, uint256) {
        return (true, 42);
    }
}

/// Token whose calls revert.
contract RevertingToken {
    function transfer(address, uint256) external pure returns (bool) {
        revert("REVERT_ON_TRANSFER");
    }

    function transferFrom(address, address, uint256) external pure returns (bool) {
        revert("REVERT_ON_TRANSFER_FROM");
    }

    function approve(address, uint256) external pure returns (bool) {
        revert("REVERT_ON_APPROVE");
    }
}

/// Fee-on-transfer token. The wrapper has no way to detect that the recipient
/// received less than `amount` — the call returns true and the optional-bool
/// guard accepts it. These tests pin the documented behavior so callers know
/// SafeTransferLib is NOT a fee-on-transfer detector and must do pre/post
/// balance accounting themselves.
contract FeeOnTransferToken {
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    uint256 public feeBps; // basis points fee

    constructor(uint256 _feeBps) {
        feeBps = _feeBps;
    }

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        require(balanceOf[msg.sender] >= amount, "FOT_INSUFFICIENT_BALANCE");
        uint256 fee = (amount * feeBps) / 10000;
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += (amount - fee);
        // Fee silently retained by the token contract.
        return true;
    }

    function transferFrom(address from, address to, uint256 amount) external returns (bool) {
        require(allowance[from][msg.sender] >= amount, "FOT_INSUFFICIENT_ALLOWANCE");
        require(balanceOf[from] >= amount, "FOT_INSUFFICIENT_BALANCE");
        uint256 fee = (amount * feeBps) / 10000;
        allowance[from][msg.sender] -= amount;
        balanceOf[from] -= amount;
        balanceOf[to] += (amount - fee);
        return true;
    }

    function approve(address spender, uint256 amount) external returns (bool) {
        allowance[msg.sender][spender] = amount;
        return true;
    }
}

/// ERC-777-style token that invokes a hook on the recipient before completing
/// the transfer. The hook is an arbitrary external call, so this is the
/// canonical reentrancy vector. SafeTransferLib has no internal state, so
/// reentry against the wrapper itself is harmless — but consumers must guard
/// their own state via CEI or reentrancy locks.
contract HookCallingToken {
    mapping(address => uint256) public balanceOf;

    function mint(address to, uint256 amount) external {
        balanceOf[to] += amount;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        // Invoke a "tokens-received" style hook on the recipient before
        // settlement. Production ERC-777 uses ERC-1820 registry lookup; we
        // simulate it by trying a known selector if the recipient has code.
        if (to.code.length > 0) {
            (bool ok,) = to.call(abi.encodeWithSignature("tokensReceived(uint256)", amount));
            ok; // result ignored; ERC-777 hook is fire-and-forget for testing
        }
        require(balanceOf[msg.sender] >= amount, "ERC777_INSUFFICIENT_BALANCE");
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        return true;
    }

    function transferFrom(address, address, uint256) external pure returns (bool) {
        return true;
    }

    function approve(address, uint256) external pure returns (bool) {
        return true;
    }
}

/// A recipient that attempts to reenter SafeTransferLib's transfer during
/// the ERC-777 hook. Records whether reentry succeeded so the test can
/// assert that SafeTransferLib's own state is untouched.
contract ReentrantRecipient {
    SafeTransferLibIface public lib;
    address public token;
    address public victim;
    uint256 public reentryCount;

    constructor(SafeTransferLibIface _lib) {
        lib = _lib;
    }

    function setToken(address _token, address _victim) external {
        token = _token;
        victim = _victim;
    }

    function tokensReceived(uint256) external {
        reentryCount++;
        // Attempt a nested transfer through the same wrapper.
        // SafeTransferLib has no state to corrupt, so this should succeed
        // without breaking the outer call.
        if (reentryCount < 2) {
            try lib.transfer(token, victim, 0) {} catch {}
        }
    }
}

/// Token whose calls return *fewer* than 32 bytes (e.g. an `int8` or `uint8`
/// return). The Yul optional-bool guard `mload(ptr) == 1` reads 32 bytes from
/// the call's output buffer, but the EVM `CALL` opcode only overwrites the
/// first `returndatasize` bytes of that buffer; the remainder retains the
/// pre-call calldata layout (selector + to + amount). For typical recipient
/// addresses the trailing bytes will not align to the integer `1`, so the
/// guard's outer-condition check falls through to the inner `returndatasize
/// == 0 && extcodesize > 0` clause, which reverts. The mock and test below
/// pin this behaviour so that any future change to the upstream Yul codegen
/// (e.g. pre-zeroing the output buffer) does not silently regress it.
contract ShortReturnToken {
    uint256 public bytesToReturn;

    constructor(uint256 _bytesToReturn) {
        require(_bytesToReturn > 0 && _bytesToReturn < 32, "ShortReturnToken: out of range");
        bytesToReturn = _bytesToReturn;
    }

    fallback() external {
        uint256 len = bytesToReturn;
        assembly {
            // Return `len` zero bytes. The output area at the caller is
            // 32 bytes; the EVM truncates this return to `len`, leaving the
            // upper (32 - len) bytes of the caller's output buffer untouched.
            mstore(0x00, 0)
            return(0x00, len)
        }
    }
}

/// Rebasing token where balanceOf changes async (not tied to transfer calls).
/// The wrapper's transfer succeeds but the recipient's balance may be
/// affected by other balance-rebasing events outside the transfer call.
/// Same documentation-style coverage as fee-on-transfer.
contract RebasingToken {
    mapping(address => uint256) public _rawBalance;
    uint256 public scale = 1e18;

    function balanceOf(address account) external view returns (uint256) {
        return (_rawBalance[account] * scale) / 1e18;
    }

    function mint(address to, uint256 amount) external {
        _rawBalance[to] += amount;
    }

    function rebase(uint256 newScale) external {
        scale = newScale;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        uint256 raw = (amount * 1e18) / scale;
        require(_rawBalance[msg.sender] >= raw, "REBASE_INSUFFICIENT_BALANCE");
        _rawBalance[msg.sender] -= raw;
        _rawBalance[to] += raw;
        return true;
    }

    function transferFrom(address, address, uint256) external pure returns (bool) {
        return true;
    }

    function approve(address, uint256) external pure returns (bool) {
        return true;
    }
}

contract SafeTransferLibTest is Test {
    SafeTransferLibIface internal lib;

    function setUp() public {
        lib = SafeTransferLibDeployer.deploy();
    }

    // ------------------------------------------------------------------
    // Standard ERC-20 (Tamago's own) — happy path.
    // The library's `transfer` returns true, and balance state on the
    // standard token reflects the transfer.
    // ------------------------------------------------------------------

    function testStandardTokenTransferSucceedsAndReturnsTrue() public {
        StandardReturnToken token = new StandardReturnToken();
        token.mint(address(lib), 100);
        bool ok = lib.transfer(address(token), address(0xBEEF), 40);
        assertTrue(ok);
        assertEq(token.balanceOf(address(lib)), 60);
        assertEq(token.balanceOf(address(0xBEEF)), 40);
    }

    function testStandardTokenTransferFromSucceedsAndReturnsTrue() public {
        StandardReturnToken token = new StandardReturnToken();
        token.mint(address(this), 100);
        token.approve(address(lib), 100);
        bool ok = lib.transferFrom(address(token), address(this), address(0xBEEF), 25);
        assertTrue(ok);
        assertEq(token.balanceOf(address(this)), 75);
        assertEq(token.balanceOf(address(0xBEEF)), 25);
    }

    function testStandardTokenApproveSucceedsAndReturnsTrue() public {
        StandardReturnToken token = new StandardReturnToken();
        bool ok = lib.approve(address(token), address(0xBEEF), 12345);
        assertTrue(ok);
        assertEq(token.allowance(address(lib), address(0xBEEF)), 12345);
    }

    // ------------------------------------------------------------------
    // USDT-style — accepted because the call succeeded and the target has
    // code, even though the call returns no data.
    // ------------------------------------------------------------------

    function testUsdtStyleTransferSucceedsWithNoReturnData() public {
        UsdtStyleToken token = new UsdtStyleToken();
        token.mint(address(lib), 100);
        bool ok = lib.transfer(address(token), address(0xBEEF), 40);
        assertTrue(ok);
        assertEq(token.balanceOf(address(lib)), 60);
    }

    function testUsdtStyleTransferFromSucceedsWithNoReturnData() public {
        UsdtStyleToken token = new UsdtStyleToken();
        token.mint(address(this), 100);
        token.approve(address(lib), 100);
        bool ok = lib.transferFrom(address(token), address(this), address(0xBEEF), 25);
        assertTrue(ok);
        assertEq(token.balanceOf(address(0xBEEF)), 25);
    }

    function testUsdtStyleApproveSucceedsWithNoReturnData() public {
        UsdtStyleToken token = new UsdtStyleToken();
        bool ok = lib.approve(address(token), address(0xBEEF), 12345);
        assertTrue(ok);
        assertEq(token.allowance(address(lib), address(0xBEEF)), 12345);
    }

    // ------------------------------------------------------------------
    // False-return — must revert. This is the SafeERC20 footgun: naive
    // ERC-20 callers ignore the return value, treating false as success.
    // ------------------------------------------------------------------

    function testFalseReturnTokenTransferReverts() public {
        FalseReturnToken token = new FalseReturnToken();
        vm.expectRevert();
        lib.transfer(address(token), address(0xBEEF), 1);
    }

    function testFalseReturnTokenTransferFromReverts() public {
        FalseReturnToken token = new FalseReturnToken();
        vm.expectRevert();
        lib.transferFrom(address(token), address(this), address(0xBEEF), 1);
    }

    function testFalseReturnTokenApproveReverts() public {
        FalseReturnToken token = new FalseReturnToken();
        vm.expectRevert();
        lib.approve(address(token), address(0xBEEF), 1);
    }

    // ------------------------------------------------------------------
    // Oversized return data — the optional-bool guard reads only the first
    // 32 bytes of the return buffer, so any return whose first word equals
    // `true` is accepted, regardless of how much trailing data follows.
    // This matches Solidity's `abi.decode(returndata, (bool))` behaviour
    // when returndata.length >= 32 and the first word is `true`. The guard
    // is *not* a length-equals-32 check.
    // ------------------------------------------------------------------

    function testOversizedReturnTokenTransferSucceedsWhenFirstWordIsTrue() public {
        OversizedReturnToken token = new OversizedReturnToken();
        bool ok = lib.transfer(address(token), address(0xBEEF), 1);
        assertTrue(ok);
    }

    function testOversizedReturnTokenTransferFromSucceedsWhenFirstWordIsTrue() public {
        OversizedReturnToken token = new OversizedReturnToken();
        bool ok = lib.transferFrom(address(token), address(this), address(0xBEEF), 1);
        assertTrue(ok);
    }

    function testOversizedReturnTokenApproveSucceedsWhenFirstWordIsTrue() public {
        OversizedReturnToken token = new OversizedReturnToken();
        bool ok = lib.approve(address(token), address(0xBEEF), 1);
        assertTrue(ok);
    }

    // ------------------------------------------------------------------
    // No-code address — the optional-bool guard rejects empty return data
    // when the target has no code (a common rug-pull / cold-token pattern
    // that naive callers would accept silently).
    // ------------------------------------------------------------------

    function testNoCodeAddressTransferReverts() public {
        // 0xDEAD is a well-known unallocated address; vm.etch off keeps it
        // empty. Foundry by default leaves it codeless.
        address eoa = address(0xDEAD);
        vm.expectRevert();
        lib.transfer(eoa, address(0xBEEF), 1);
    }

    function testNoCodeAddressTransferFromReverts() public {
        address eoa = address(0xDEAD);
        vm.expectRevert();
        lib.transferFrom(eoa, address(this), address(0xBEEF), 1);
    }

    function testNoCodeAddressApproveReverts() public {
        address eoa = address(0xDEAD);
        vm.expectRevert();
        lib.approve(eoa, address(0xBEEF), 1);
    }

    // ------------------------------------------------------------------
    // Reverting tokens — propagate the inner revert.
    // ------------------------------------------------------------------

    function testRevertingTokenTransferPropagates() public {
        RevertingToken token = new RevertingToken();
        vm.expectRevert();
        lib.transfer(address(token), address(0xBEEF), 1);
    }

    function testRevertingTokenTransferFromPropagates() public {
        RevertingToken token = new RevertingToken();
        vm.expectRevert();
        lib.transferFrom(address(token), address(this), address(0xBEEF), 1);
    }

    function testRevertingTokenApprovePropagates() public {
        RevertingToken token = new RevertingToken();
        vm.expectRevert();
        lib.approve(address(token), address(0xBEEF), 1);
    }

    // ------------------------------------------------------------------
    // Mirror-test markers for the wrapper-discipline specs. These specs
    // are about the Lean modeling layer (the wrapper returns true and does
    // not touch its own storage). On-chain we mirror them by confirming
    // the call succeeds and the library's own storage layout is unchanged.
    // ------------------------------------------------------------------

    // tama: mirrors=safeTransferLib_transfer_returns_true
    function testFuzzTransferReturnsTrue() public {
        StandardReturnToken token = new StandardReturnToken();
        token.mint(address(lib), 1);
        bool ok = lib.transfer(address(token), address(0xBEEF), 1);
        assertTrue(ok);
    }

    // tama: mirrors=safeTransferLib_transfer_keeps_storage
    function testFuzzTransferKeepsStorage() public {
        StandardReturnToken token = new StandardReturnToken();
        token.mint(address(lib), 1);
        bytes32 before0 = vm.load(address(lib), bytes32(uint256(0)));
        bytes32 before1 = vm.load(address(lib), bytes32(uint256(1)));
        lib.transfer(address(token), address(0xBEEF), 1);
        assertEq(vm.load(address(lib), bytes32(uint256(0))), before0);
        assertEq(vm.load(address(lib), bytes32(uint256(1))), before1);
    }

    // tama: mirrors=safeTransferLib_transferFrom_returns_true
    function testFuzzTransferFromReturnsTrue() public {
        StandardReturnToken token = new StandardReturnToken();
        token.mint(address(this), 1);
        token.approve(address(lib), 1);
        bool ok = lib.transferFrom(address(token), address(this), address(0xBEEF), 1);
        assertTrue(ok);
    }

    // tama: mirrors=safeTransferLib_transferFrom_keeps_storage
    function testFuzzTransferFromKeepsStorage() public {
        StandardReturnToken token = new StandardReturnToken();
        token.mint(address(this), 1);
        token.approve(address(lib), 1);
        bytes32 before0 = vm.load(address(lib), bytes32(uint256(0)));
        bytes32 before1 = vm.load(address(lib), bytes32(uint256(1)));
        lib.transferFrom(address(token), address(this), address(0xBEEF), 1);
        assertEq(vm.load(address(lib), bytes32(uint256(0))), before0);
        assertEq(vm.load(address(lib), bytes32(uint256(1))), before1);
    }

    // tama: mirrors=safeTransferLib_approve_returns_true
    function testFuzzApproveReturnsTrue() public {
        StandardReturnToken token = new StandardReturnToken();
        bool ok = lib.approve(address(token), address(0xBEEF), 1);
        assertTrue(ok);
    }

    // tama: mirrors=safeTransferLib_approve_keeps_storage
    function testFuzzApproveKeepsStorage() public {
        StandardReturnToken token = new StandardReturnToken();
        bytes32 before0 = vm.load(address(lib), bytes32(uint256(0)));
        bytes32 before1 = vm.load(address(lib), bytes32(uint256(1)));
        lib.approve(address(token), address(0xBEEF), 1);
        assertEq(vm.load(address(lib), bytes32(uint256(0))), before0);
        assertEq(vm.load(address(lib), bytes32(uint256(1))), before1);
    }

    // ------------------------------------------------------------------
    // Documented-limitation tests: token shapes the wrapper does NOT detect.
    // These pin the contract's behaviour so callers know SafeTransferLib is
    // a return-value check, not a value-conservation oracle.
    // ------------------------------------------------------------------

    /// Fee-on-transfer: the wrapper accepts a successful call even though the
    /// recipient's balance increased by less than `amount`. Callers must do
    /// their own pre/post balance accounting (the documented OZ pattern).
    function testFeeOnTransferIsNotDetected() public {
        FeeOnTransferToken token = new FeeOnTransferToken(100); // 1% fee
        token.mint(address(lib), 1_000_000);
        bool ok = lib.transfer(address(token), address(0xBEEF), 100_000);
        assertTrue(ok, "wrapper considers the transfer successful");
        // The recipient received 99_000, NOT 100_000 — the wrapper did not
        // detect the fee.
        assertEq(token.balanceOf(address(0xBEEF)), 99_000);
        assertLt(token.balanceOf(address(0xBEEF)), 100_000);
    }

    /// ERC-777-style reentrancy: the recipient's hook reenters the wrapper.
    /// SafeTransferLib has no internal state, so the reentry is harmless to
    /// the wrapper itself. Callers that DO have state must add their own
    /// reentrancy guard (this test confirms only the wrapper's invariants).
    function testErc777HookReentryIsSafeForWrapper() public {
        HookCallingToken token = new HookCallingToken();
        ReentrantRecipient recipient = new ReentrantRecipient(lib);
        recipient.setToken(address(token), address(0xCAFE));
        token.mint(address(lib), 1_000);
        bytes32 before0 = vm.load(address(lib), bytes32(uint256(0)));
        bytes32 before1 = vm.load(address(lib), bytes32(uint256(1)));
        // Transfer triggers the hook, which reenters lib.transfer.
        bool ok = lib.transfer(address(token), address(recipient), 100);
        assertTrue(ok);
        // Wrapper storage unchanged across the reentrant call.
        assertEq(vm.load(address(lib), bytes32(uint256(0))), before0);
        assertEq(vm.load(address(lib), bytes32(uint256(1))), before1);
        // Hook fired and the reentry attempt was made.
        assertEq(recipient.reentryCount(), 1);
    }

    /// Short returndata — the call returns fewer than 32 bytes. The EVM
    /// truncates the output region without zero-filling, so the optional-bool
    /// guard sees mload(ptr) composed of `returndatasize` returned bytes plus
    /// the remaining bytes of the pre-call calldata buffer (selector / to /
    /// amount). For ordinary recipient addresses that combination cannot
    /// equal `1`, and returndatasize > 0 also fails the inner empty-return
    /// allowance, so the wrapper reverts. These tests pin that behaviour
    /// across the [1..31]-byte short-return range.
    function testShortReturn1ByteReverts() public {
        ShortReturnToken token = new ShortReturnToken(1);
        vm.expectRevert();
        lib.transfer(address(token), address(0xBEEF), 1);
    }

    function testShortReturn4BytesReverts() public {
        ShortReturnToken token = new ShortReturnToken(4);
        vm.expectRevert();
        lib.transfer(address(token), address(0xBEEF), 1);
    }

    function testShortReturn31BytesReverts() public {
        ShortReturnToken token = new ShortReturnToken(31);
        vm.expectRevert();
        lib.transfer(address(token), address(0xBEEF), 1);
    }

    /// Rebasing: the wrapper does not protect against post-transfer balance
    /// changes via rebase. Documenting the limitation.
    function testRebasingNotDetected() public {
        RebasingToken token = new RebasingToken();
        token.mint(address(lib), 100);
        bool ok = lib.transfer(address(token), address(0xBEEF), 50);
        assertTrue(ok);
        assertEq(token.balanceOf(address(0xBEEF)), 50);
        // Token rebases to half the scale; the recipient now sees a different
        // amount than what they received from the transfer.
        token.rebase(0.5e18);
        assertEq(token.balanceOf(address(0xBEEF)), 25);
    }
}
