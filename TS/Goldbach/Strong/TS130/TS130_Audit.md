# TS130 Audit - Selberg Optimal Weight Reconstruction Ledger

## Scope

TS130 opens the inverse triangular step after TS129.

TS129 proves that the original dense side is the TS122 diagonal energy of the
absorbed divisor vector

```text
Y_d = sum_m 1_{d | m} * weight(m) / m.
```

TS130 defines original Selberg weights reconstructed from a prescribed diagonal
vector `Y` by the finite upward Mobius transform. It proves the immediate
support and zero-index facts, then isolates the remaining finite Mobius
reconstruction identity as a local proposition.

## Concrete Lean objects

The sprint adds:

```lean
TS130.Goldbach.selbergReconstructionSupport
TS130.Goldbach.mem_selbergReconstructionSupport_le_level
TS130.Goldbach.mem_selbergReconstructionSupport_pos
TS130.Goldbach.absorbedCoefficientFromDiagonalVector
TS130.Goldbach.reconstructedSelbergWeight
TS130.Goldbach.absorbedCoefficientFromDiagonalVector_zero
TS130.Goldbach.reconstructedSelbergWeight_zero
TS130.Goldbach.not_dvd_of_level_lt_on_reconstructionSupport
TS130.Goldbach.absorbedCoefficientFromDiagonalVector_eq_zero_of_level_lt
TS130.Goldbach.reconstructedSelbergWeight_eq_zero_of_level_lt
TS130.Goldbach.reconstructedSelbergWeight_support_bound
TS130.Goldbach.selbergLCMAbsorbedWeight_reconstructed_eq_absorbedCoefficient
TS130.Goldbach.ReconstructedSelbergWeightSupport
TS130.Goldbach.reconstructedSelbergWeightSupport
TS130.Goldbach.SelbergFiniteMobiusReconstructionIdentity
TS130.Goldbach.SelbergWeightReconstruction
TS130.Goldbach.selbergWeightReconstruction
TS130.Goldbach.optimalReconstructedSelbergWeight
TS130.Goldbach.optimalReconstructedWeight_mobius_constraint_of_reconstruction
TS130.Goldbach.optimalReconstructedWeight_denseSide_eq_optimal_budget_of_reconstruction
TS130.Goldbach.SelbergOptimalWeightReconstruction
TS130.Goldbach.selbergOptimalWeightReconstruction
TS130.Goldbach.SelbergOptimalWeightReconstructionTarget
TS130.Goldbach.selbergOptimalWeightReconstructionTarget
TS130.Goldbach.selbergDiagonalBudgetMajorantTarget
```

## What is proved

TS130 defines the positive reconstruction support as the TS122 optimization
support and proves:

```text
d in support -> d <= level
d in support -> 0 < d
```

For a target diagonal vector `Y`, TS130 defines:

```text
a_m = sum_{m | d} mu(d / m) * Y_d
w_m = m * a_m.
```

The sprint proves:

```text
a_0 = 0
w_0 = 0
m > level -> a_m = 0
m > level -> w_m = 0
w_m / m = a_m for 0 < m
```

Thus the reconstructed original weights have finite support inside `level`.

The remaining local inversion statement is named:

```lean
TS130.Goldbach.SelbergFiniteMobiusReconstructionIdentity
```

It asserts that the absorbed diagonal vector of the reconstructed weights
recovers the target `Y` on the TS122 finite positive support.

## Conditional consequences

Specializing `Y` to the TS128 optimal vector, TS130 proves that if the finite
Mobius reconstruction identity holds, then:

```text
the absorbed vector satisfies the Mobius constraint;
the original dense side of the reconstructed weights equals 1 / D.
```

These are concrete consequences of TS128 and TS129.

## Remaining obligations

TS130 does not yet prove:

```text
* the finite Mobius reconstruction identity;
* the interval Selberg sieve majorant;
* Brun-Titchmarsh;
* any prime-count estimate;
* the spectral trace package;
* the Mellin-tail package.
```

The TS105 Mobius-delta input is explicitly kept available in the reconstruction
ledger for the future finite inversion discharge.

## Verification

Expected checks:

```text
lake build TS.Goldbach.Strong.TS130.SelbergOptimalWeightReconstructionLedger
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS130
git diff --check -- README.md TS\Goldbach\Strong\TS130\SelbergOptimalWeightReconstructionLedger.lean TS\Goldbach\Strong\TS130\TS130_Audit.md
```
