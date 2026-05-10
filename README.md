# Tamago🍳

Tamago is a standard smart contract suite for [Verity](https://veritylang.com), similar to solmate/solady for Solidity.

Tamago uses [Tama](https://tama.tools), a modern toolchain for secure-by-construction Ethereum applications.

All smart contracts in Tamago are **formally verified** via Lean, meaning they're mathematically proven to adhere to the specs. The specs are also double-checked via Foundry mirror tests.

Tamago claims the **first ever** formally verified EVM implementations of `sqrt()`, `cbrt()`, `log10()`, `log256()`, as well as the full `ERC4626` standard.

## Components

- `Ownable`: single-owner authorization with ownership transfer and
  renunciation.
- `ERC20`: fungible token with allowances, owner-controlled minting and
  burning, fixed 18-decimal metadata, and overflow-safe accounting.
- `ERC721`: non-fungible token with ownership, approvals, operator approvals,
  minting, and transfer behavior.
- `WETH`: wrapped ETH with ERC20-compatible accounting, deposits, withdrawals,
  approvals, and transfers.
- `ERC4626`: tokenized vault accounting with share/asset conversion previews,
  deposits, minting, withdrawals, redemptions, and ERC20 share behavior.
- `FixedPointMathLib`: reusable unsigned integer math helpers, including
  saturating arithmetic, distance, averages, roots, logs, and clamping.

Each component has a Verity implementation, a property spec, a Lean proof file,
and mirror tests that connect the proved properties to generated EVM artifacts.

## Install

From a Tama project, add Tamago as a package dependency:

```sh
tama install Bacon-labs/tamago
```

Pin a specific revision for reproducible builds:

```sh
tama install Bacon-labs/tamago@<git-revision>
```

Then refresh and verify the project:

```sh
tama doctor
tama check
tama build --locked
tama test
```

## Usage

Import the source bundle from Lean:

```lean
import Tamago
```

Or import only the components you need:

```lean
import Tamago.Auth.Ownable
import Tamago.Tokens.ERC20
import Tamago.Tokens.ERC721
import Tamago.Tokens.WETH
import Tamago.Tokens.ERC4626
import Tamago.Utils.FixedPointMathLib
```

Reference a component's compilation model from your own Verity code or build
configuration:

```lean
#check Tamago.Auth.Ownable.spec
#check Tamago.Tokens.ERC20.spec
#check Tamago.Tokens.ERC721.spec
#check Tamago.Tokens.WETH.spec
#check Tamago.Tokens.ERC4626.spec
#check Tamago.Utils.FixedPointMathLib.spec
```

Use the generated Solidity deployers from Foundry tests after `tama build`:

```solidity
import {ERC20Deployer} from "tamago/src/generated/verity/ERC20Deployer.sol";
import {ERC20Iface} from "tamago/src/generated/verity/ERC20Iface.sol";

contract ExampleTest {
    function deployToken(address owner) internal returns (ERC20Iface token) {
        token = ERC20Deployer.deploy(owner);
    }
}
```

The same pattern applies to the other generated deployers and interfaces:
`Ownable`, `ERC721`, `WETH`, `ERC4626`, and `FixedPointMathLib`.

## Repository Layout

```text
.
|-- verity/
|   |-- src/
|   |   |-- Tamago.lean                  # Source aggregate module
|   |   `-- Tamago/                      # Contract and library implementations
|   |-- spec/
|   |   `-- Tamago/
|   |       |-- Spec.lean                # Spec aggregate module
|   |       `-- Spec/                    # Property specs
|   |-- proof/
|   |   `-- Tamago/
|   |       |-- Proof.lean               # Proof aggregate module
|   |       `-- Proof/                   # Proofs for the specs
|   `-- common/
|       `-- Tamago/Common/               # Shared events and helper models
|-- src/generated/verity/                # Generated Solidity deployers and interfaces
`-- test/verity/                         # Foundry mirror tests with tama: property links
```

## Development

For local development on Tamago itself, clone with submodules:

```sh
git clone --recurse-submodules git@github.com:Bacon-labs/tamago.git
cd tamago
```

For an existing checkout:

```sh
git submodule update --init --recursive
```

Run the standard verification workflow:

```sh
tama doctor
tama build --locked
tama test
tama audit
```

The CI workflow in `.github/workflows/ci.yml` runs the same checks on pushes to
`main` and on pull requests.

## License

Tamago is released under the MIT License. See [LICENSE](LICENSE).
