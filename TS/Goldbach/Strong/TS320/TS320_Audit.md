# TS320 Audit - Uniform Discrete Kusmin-Landau Bound

## Scope

TS320 closes the uniform oscillatory statement left open by TS319.  It proves
a general finite theorem for unit complex phases whose positive increments
are nonincreasing and lie between a fixed positive gap and `1/2`.  The proof
is discrete: it uses an exponential chord bound, reciprocal variation, and an
exact summation-by-parts identity.

The theorem is then instantiated with the logarithmic phase increments from
TS319.  The resulting constant is independent of the zero truncation height.
TS320 does not prove close-pair envelope smallness or a rational half-budget.

## Main declarations

```lean
TS320.Goldbach.phaseStep
TS320.Goldbach.phaseReciprocal
TS320.Goldbach.phaseStep_norm_lower
TS320.Goldbach.phaseReciprocal_norm_le
TS320.Goldbach.phaseReciprocal_sub_norm_le
TS320.Goldbach.phaseReciprocal_totalVariation_le

TS320.Goldbach.sum_Ico_mul_succ_sub
TS320.Goldbach.MonotoneUnitPhaseBoundStatement
TS320.Goldbach.monotoneUnitPhaseBound

TS320.Goldbach.positiveDiscreteLogPhasePartialSumBound
TS320.Goldbach.uniformOscillatoryDiscreteLogPhasePartialSumBound
TS320.Goldbach.uniformNonresonantDiscreteLogPhasePartialSumBound
TS320.Goldbach.uniformWeightedKusminLandauKernelBound
```

## Phase chord and reciprocal variation

For `0 < u <= 1/2`, TS320 proves the conservative chord estimate

```text
u/2 <= norm (exp (I*u) - 1).
```

The proof uses the complex exponential remainder bound

```text
norm (exp x - 1 - x) <= norm x ^ 2
```

with `x = I*u`.  It therefore avoids a dependency on a particular library
form of Jordan's sine inequality.

For `0 < v <= u <= 1/2`, the exact inverse-difference identity and the chord
bound give

```text
norm (phaseReciprocal v - phaseReciprocal u)
  <= 8 * (1/v - 1/u).
```

Along a nonincreasing increment sequence this majorant telescopes.  If every
increment is at least `gap > 0`, the total reciprocal variation is at most
`8/gap`.

## Purely discrete unit-phase theorem

`MonotoneUnitPhaseBoundStatement C` requires:

```text
m < n,
0 < gap,
norm (z k) = 1 for m <= k <= n,
z (k+1) = z k * exp (I * delta k) for m <= k < n,
delta (k+1) <= delta k,
gap <= delta k <= 1/2.
```

The recurrence is available through the terminal difference `k = n-1`, and
the unit-norm hypothesis includes `z n`, so both summation-by-parts boundary
terms are controlled.

TS320 proves the statement with `C = 12`.  The two boundary terms contribute
at most `4/gap`; the reciprocal variation contributes at most `8/gap`.

## Logarithmic phase instantiation

For positive frequency in the TS319 nonresonant range, TS320 sets

```text
z k     = k^(I*t),
delta k = t * log ((k+1)/k),
gap     = t/(2*X).
```

The unit norm, recurrence, monotonicity, and dyadic increment bounds are all
imported from TS319.  Thus

```text
12 / gap = 24 * X / t.
```

Negative frequencies are transported by the TS319 conjugation identity.  The
result inhabits

```text
UniformOscillatoryDiscreteLogPhasePartialSumBoundStatement 24
```

and hence the full uniform nonresonant TS318 contract with the same constant.
Applying the TS318 amplitude transfer closes the TS317 pointwise weighted
kernel contract with constant `96`.

## Fail-closed boundary

The following remain open:

```text
WeightedClosePairEnvelopeBoundStatement smallness
FiniteQuadraticSpectralMomentBoundStatement smallness
NormalizedTraceBudgetData with traceBudget <= 1/2
Gallagher
OTSA
Goldbach
```

The pointwise uniform Kusmin-Landau estimate does not imply close-pair density
or numerical smallness of the complete weighted pair envelope.

## Verification

```text
Targeted build: 3041/3041
Global build:   2664/2664
Lean placeholders (`sorry`, `axiom`, `opaque`, `admit`): none
Non-ASCII characters: none
git diff --check: clean
```
