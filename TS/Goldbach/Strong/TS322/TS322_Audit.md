# TS322 Audit - Finite Core and Effective Coefficient Tail

## Scope

TS322 reduces every higher finite TS317 pair envelope to the exact finite
TS321 coefficient-shell core at height `H` plus a real tail error.  It uses
only the coefficient summability and explicit tail rate already proved in
TS292.  It introduces no local pair-correlation hypothesis.

The module deliberately stops before rationalization.  It does not construct
TS313 normalized rational data, a TS181 half-budget, OTSA, or Goldbach.

## Main declarations

```lean
TS322.Goldbach.CoefficientTailIndex
TS322.Goldbach.linearCoefficientTailMass
TS322.Goldbach.finiteLinearCoefficientMass
TS322.Goldbach.linearCoefficientTailMass_le_effective
TS322.Goldbach.finiteLinearCoefficientMass_add_tail
TS322.Goldbach.linearCoefficientTailMass_tendsto_zero

TS322.Goldbach.finiteWeightedLocalCore
TS322.Goldbach.orderedOffDiagonalZeroPairs
TS322.Goldbach.weightedPairIncrement
TS322.Goldbach.weightedPairIncrement_le_finiteMasses

TS322.Goldbach.effectiveWeightedTailError
TS322.Goldbach.effectiveWeightedTailError_le_explicit
TS322.Goldbach.effectiveWeightedTailError_tendsto_zero
TS322.Goldbach.weightedClosePairEnvelope_le_core_add_effectiveTail
TS322.Goldbach.weightedClosePairEnvelopeBound_of_core_tail
TS322.Goldbach.FiniteCoreEffectiveTailData
```

## Exact coefficient tail

The tail index is the subtype of concrete nontrivial zeros outside
`truncatedZeroSet H`.  Its mass is

```text
R(H) = tsum rho outside truncatedZeroSet H, zeroCoefficientMagnitude rho.
```

At arithmetic scale one, `zeroCoefficientMagnitude` is definitionally the
norm of `TS292.infiniteZeroSpectralTerm 1`.  Therefore the existing TS292
finite-subset estimate and `tsum_le_of_sum_le` give, for `1 <= H`,

```text
R(H) <= infiniteZeroResidualTailConstant * logarithmicTailRate H.
```

No new asymptotic statement or zero-counting hypothesis is added.

## Finite mass plus tail

The standard `sum_add_tsum_subtype_compl` identity proves exactly

```text
finiteLinearCoefficientMass H + R(H) = globalLinearSpectralMass.
```

The TS292 truncation finsets tend to `atTop`.  Composing the coefficient
`HasSum` with that exhaustion proves the finite masses converge to the global
mass, hence `R(H)` tends to zero.

## Correction to the pasted skeleton

The TS321 finite shell expression uses `1/k` to majorize the exact gap weight.
It is therefore an upper bound for the envelope at height `H`, not an equal
rewriting of that envelope.  TS322 uses the correct two-step chain:

```text
envelope T = envelope H + pairIncrement(T,H)
envelope H <= finiteWeightedLocalCore H.
```

No false equality between `finiteWeightedLocalCore H` and `envelope H` is
claimed.

## Ordered-pair increment

TS322 rewrites the nested TS317 `erase` sum as a sum over the finite set of
ordered off-diagonal pairs.  Truncation monotonicity then gives an exact
finite-set difference:

```text
envelope T = envelope H + pairIncrement(T,H),  H <= T.
```

The new pairs are partitioned disjointly according to their first coordinate:

```text
first coordinate in the coefficient tail
first coordinate in the core, hence second coordinate in the tail.
```

After dropping the gap weight, which is between zero and one, these two parts
embed respectively in the rectangles

```text
tail(T,H) product truncatedZeroSet T
truncatedZeroSet T product tail(T,H).
```

Finite Fubini factors their coefficient sums.  This proves

```text
pairIncrement(T,H)
  <= 2 * finiteLinearCoefficientMass T * finiteCoefficientTailMass T H
  <= 2 * globalLinearSpectralMass * R(H).
```

The argument covers all near and far gaps at once.  A finer shell-dependent
product-of-tails estimate could improve constants, but is not needed for the
uniform approximation or convergence.

## Main uniform bound

Define

```text
effectiveWeightedTailError H = 2 * globalLinearSpectralMass * R(H).
```

Then for every `H <= T`, TS322 proves

```text
weightedClosePairEnvelope T
  <= finiteWeightedLocalCore H + effectiveWeightedTailError H.
```

The error is nonnegative, tends to zero, and for `1 <= H` is bounded by the
fully explicit real expression

```text
2 * globalLinearSpectralMass
  * (infiniteZeroResidualTailConstant * logarithmicTailRate H).
```

`FiniteCoreEffectiveTailData H` packages the finite real core, real tail
error, uniform envelope bound, and explicit TS292 majorant for downstream
use.

## Fail-closed boundary

The finite core is not proved numerically small.  In particular TS322 does
not provide:

```text
a rational upper bound for the finite core
a rational upper bound for the tail error
NormalizedTraceBudgetData
a TS181 trace budget at most one half
OTSA
Goldbach
```

All rational conversion and the half-budget comparison remain exclusively in
TS323.

## Verification

```text
Targeted build: 3043/3043
Global build:   2664/2664
Lean placeholders (`sorry`, `axiom`, `opaque`, `admit`): none
Non-ASCII characters: none
git diff --check: clean
```
