# TS135 Audit - Selberg Finite Mobius Reconstruction Expansion Discharge

## Scope

TS135 adds:

```text
TS/Goldbach/Strong/TS135/SelbergFiniteMobiusReconstructionExpansionDischarge.lean
```

It discharges the TS131 finite Fubini expansion obligation:

```text
absorbedDiagonalVector(reconstructedWeight)(d)
=
sum_e Y(e) * chainCoefficient(d,e).
```

Together with the TS134 chain-coefficient collapse, this closes the TS130
finite Mobius reconstruction identity.

## Concrete declarations

TS135 proves:

```lean
TS135.Goldbach.zero_not_dvd_reconstructionSupport
TS135.Goldbach.absorbedCoefficientFromDiagonalVector_expansion
TS135.Goldbach.selbergLCMAbsorbedWeight_reconstructed_expansion
TS135.Goldbach.selbergAbsorbedDiagonalVector_reconstructed_eq_mFirst
TS135.Goldbach.selbergFiniteMobiusReconstruction_mFirst_eq_expandedSide
TS135.Goldbach.selbergFiniteMobiusReconstructionExpansion
TS135.Goldbach.selbergFiniteMobiusReconstructionIdentity
TS135.Goldbach.optimalReconstructedWeight_denseSide_eq_optimal_budget
TS135.Goldbach.selbergFiniteMobiusReconstructionExpansionDischargeTarget
TS135.Goldbach.selbergProperDivisorQuotientReindexingDischargeTarget
```

TS135 defines:

```lean
TS135.Goldbach.SelbergFiniteMobiusReconstructionExpansionDischarge
TS135.Goldbach.selbergFiniteMobiusReconstructionExpansionDischarge
TS135.Goldbach.SelbergFiniteMobiusReconstructionExpansionDischargeTarget
```

## Meaning

TS135 proves the remaining reconstruction expansion by finite sum algebra.
It first rewrites the absorbed diagonal vector of the reconstructed weights as
an `m`-first double sum over the positive reconstruction support:

```text
sum_m 1_{d | m} sum_e 1_{m | e} mu(e/m) * Y(e).
```

Then it uses finite Fubini (`Finset.sum_comm`) and `Finset.mul_sum` to collect
the coefficient of each `Y(e)`, recognizing exactly the TS131 chain
coefficient:

```text
sum_e Y(e) * sum_m 1_{d | m} 1_{m | e} mu(e/m).
```

Since TS134 already proves that this coefficient collapses to the delta on the
positive support, TS135 obtains the full TS130 finite reconstruction identity
for every diagonal vector `Y`.

Specializing to the TS128 optimal diagonal vector, TS135 proves that the
optimal reconstructed original weights attain the exact dense-side budget:

```text
TS110 dense side = 1 / TS122 optimization denominator.
```

## What TS135 does not prove

TS135 does not yet prove:

- the Selberg interval majorant;
- Brun-Titchmarsh;
- the spectral trace package;
- the Mellin-tail package;
- any prime-counting estimate.

## Verification

Commands run:

```powershell
lake env lean TS/Goldbach/Strong/TS135/SelbergFiniteMobiusReconstructionExpansionDischarge.lean
lake build TS.Goldbach.Strong.TS135.SelbergFiniteMobiusReconstructionExpansionDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS135
git diff --check -- TS\Goldbach\Strong\TS135 README.md
```

Expected result:

- Lean file compiles.
- Lake target builds.
- No placeholder proof marker.
- No forbidden constant declaration.
- No non-ASCII characters in TS135.
- Diff whitespace check is clean.

## Status

```text
repo_committed
```

The finite Mobius reconstruction route is now closed. The remaining work is
the interval Selberg majorant and the external analytic packages.
