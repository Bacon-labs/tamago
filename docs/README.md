# Tama Standard Contracts

This project contains standalone Tama/Verity examples for ERC20, ERC721, WETH,
Ownable, and ERC4626.

## WETH native ETH boundary

The WETH example verifies ERC20-compatible wrapped-balance accounting for
`deposit`, `withdraw`, `approve`, `transfer`, and `transferFrom`. `withdraw`
uses Verity's low-level native ETH `call` to pay the caller and reverts if that
call fails. The Lean `ContractState` model does not mutate per-address native
ETH balances for low-level calls, so the proofs establish wrapped-token
accounting, native backing checks, and the transfer-failure branch; Foundry
mirror tests check the concrete EVM ETH balance deltas.
`tama audit coverage` covers the proof/mirror mapping for these properties.
Full trust-boundary audit still reports the low-level WETH call as an explicit
unsafe boundary unless the project replaces it with an accepted ECM/Yul helper.

Run:

```sh
tama doctor
tama check
tama build
tama test
tama audit
```

## Continuous integration

`.github/workflows/ci.yml` runs `tama doctor`, `tama check`, `tama build
--locked`, `tama test`, and `tama audit` on every push and pull request. The
first run installs Lean (elan), Foundry, solc 0.8.33, and Tama; later runs
reuse caches keyed on `lake-manifest.json` and `tama.lock`.
