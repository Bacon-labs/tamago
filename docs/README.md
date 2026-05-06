# Tama Standard Contracts

This project contains standalone Tama/Verity examples for ERC20, ERC721, WETH,
and FixedPointMathLib.

## WETH native ETH limitation

The WETH example verifies ERC20-compatible wrapped-balance accounting for
`deposit`, `withdraw`, `approve`, `transfer`, and `transferFrom`. Current Tama
audit treats Verity low-level native ETH `call` mechanics as an error, and
`ContractState` does not model per-address native ETH balances. For that reason
this audit-clean V1 does not claim or prove recipient native ETH delivery on
`withdraw`; it proves the wrapped accounting effects and revert branches only.

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
