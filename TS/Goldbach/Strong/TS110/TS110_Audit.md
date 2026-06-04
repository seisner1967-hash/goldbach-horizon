# TS110 Audit - Selberg Dense-To-Diagonal Identity Ledger

## Status

`repo_committed_relative`

TS110 names the dense-to-diagonal Selberg identity connecting the dense finite
quadratic form of TS108 to the diagonal square-sum side of TS109. The identity
is stored as a proposition-valued obligation, not as a proved equality.

This sprint does not prove the dense-to-diagonal identity, the square-sum
majorant, Selberg's sieve, Brun-Titchmarsh, the interval majorant, the budget
comparison, or any prime-count estimate.

## File

```text
TS/Goldbach/Strong/TS110/SelbergDenseToDiagonalIdentityLedger.lean
```

## Key declarations

```lean
TS110.Goldbach.selbergDenseSide
TS110.Goldbach.selbergDiagonalSide
TS110.Goldbach.selbergDenseSide_eq_quadraticForm
TS110.Goldbach.selbergDiagonalSide_eq_squareSum
TS110.Goldbach.SelbergDenseToDiagonalIdentity
TS110.Goldbach.selbergDenseToDiagonalIdentity
TS110.Goldbach.selbergDenseToDiagonalIdentity_obligation_eq
TS110.Goldbach.SelbergDenseToDiagonalIdentityTarget
TS110.Goldbach.selbergDenseToDiagonalIdentityTarget
TS110.Goldbach.SelbergDenseToDiagonalInfrastructure
TS110.Goldbach.SelbergDenseToDiagonalInfrastructureTarget
TS110.Goldbach.diagonalizationInfrastructure_of_denseToDiagonalInfrastructure
TS110.Goldbach.diagonalizationInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
TS110.Goldbach.quadraticFormExpansionInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
TS110.Goldbach.mobiusInversionInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
TS110.Goldbach.finalHorizonInputsTarget_of_denseToDiagonal_trace_mellin
TS110.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_denseToDiagonal_trace_mellin
TS110.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_denseToDiagonal_trace_mellin
```

## Proof summary

The definitions

```lean
TS110.Goldbach.selbergDenseSide
TS110.Goldbach.selbergDiagonalSide
```

name the dense TS108 side and the canonical diagonal TS109 side. The expansion
theorems are definitional equalities.

The structure `SelbergDenseToDiagonalIdentity` stores the proposition

```lean
diagonalization.denseValue = diagonalization.diagonalValue
```

as `identityObligation`, and proves only that this obligation has exactly that
shape. It also records that the TS105 Mobius-delta target and TS106 gcd/lcm
kernel algebra target are the local arithmetic inputs expected for a future
proof.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS110.SelbergDenseToDiagonalIdentityLedger
rg -n "s[o]rry" TS\Goldbach\Strong\TS110
rg -n "a[x]iom" TS\Goldbach\Strong\TS110
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS110
git diff --check -- README.md TS\Goldbach\Strong\TS110\SelbergDenseToDiagonalIdentityLedger.lean TS\Goldbach\Strong\TS110\TS110_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS110-D1 | `selbergDenseSide` | `repo_committed` | names the TS108 dense quadratic-form side |
| TS110-D2 | `selbergDiagonalSide` | `repo_committed` | names the canonical TS109 diagonal square-sum side |
| TS110-I1 | `SelbergDenseToDiagonalIdentity` | `repo_committed_relative` | records the dense-to-diagonal equality as a proposition-valued obligation |
| TS110-I2 | `selbergDenseToDiagonalIdentity_obligation_eq` | `repo_committed_relative` | proves the obligation has the exact dense-equals-diagonal shape |
| TS110-T1 | `diagonalizationInfrastructureTarget_of_denseToDiagonalInfrastructureTarget` | `repo_committed_relative` | transports dense-to-diagonal infrastructure into TS109 |
| TS110-T2 | `paddedScaleAnalyticInfrastructureTarget_of_denseToDiagonal_trace_mellin` | `repo_committed_relative` | transports TS110 plus TS95 and TS83 to TS25 through TS109 |

## Remaining work

TS110 does not close the arithmetic front. The remaining work is to prove the
dense-to-diagonal Selberg identity, the diagonal square-sum majorant, the
interval majorant, the Selberg sieve bound, and the Brun-Titchmarsh budget
comparison.
