# TS318 Audit - Weighted Kusmin-Landau Kernel Reduction

## Scope

TS318 separates the exact TS317 pair power into a decreasing real amplitude
and a pure logarithmic phase.  It proves a finite Abel transfer theorem and
shows that a nonresonant partial-sum estimate for the pure phase inhabits the
pointwise TS317 weighted kernel contract.

The module does not prove the pure discrete Kusmin-Landau estimate.  It does
not claim close-pair smallness, a rational half-budget, RH, OTSA, or Goldbach.

## Main declarations

```lean
TS318.Goldbach.offDiagonalRealExponent
TS318.Goldbach.offDiagonalFrequency
TS318.Goldbach.discreteLogPhase
TS318.Goldbach.offDiagonalAmplitude

TS318.Goldbach.cpow_eq_amplitude_mul_phase
TS318.Goldbach.offDiagonalAmplitude_nonnegative
TS318.Goldbach.offDiagonalAmplitude_antitone_of_pos
TS318.Goldbach.offDiagonalAmplitude_le_one

TS318.Goldbach.sum_Ico_sub_succ
TS318.Goldbach.norm_weighted_sum_le_of_partial_sum_bound

TS318.Goldbach.NonresonantDiscreteLogPhasePartialSumBoundStatement
TS318.Goldbach.weightedCpowSum_norm_le_of_partial_sum_bound
TS318.Goldbach.weightedKusminLandauKernelBound_of_partial_sum
```

## Exact amplitude and phase

For concrete zeros `rho` and `sigma`, TS318 proves

```text
rho + conj(sigma) - 2
  = (Re(rho) + Re(sigma) - 2)
      + I * (Im(rho) - Im(sigma)).
```

The real exponent is nonpositive by the concrete critical-strip certificate.
For every positive natural `x`, the exact complex power therefore factors as

```text
x^(rho + conj(sigma) - 2)
  = x^(Re(rho) + Re(sigma) - 2)
      * x^(I * (Im(rho) - Im(sigma))).
```

The first factor is nonnegative, at most one for `x >= 1`, and decreasing on
the positive natural scales used by the dyadic window.  No exponent stronger
than nonpositivity is assumed.

## Finite Abel transfer

The generic theorem `norm_weighted_sum_le_of_partial_sum_bound` proves the
finite Dirichlet-Abel estimate directly from Mathlib's
`Finset.sum_Ico_by_parts`.  If a nonnegative amplitude decreases on `[m,n)`
and every relevant phase partial sum has norm at most `B`, then

```text
norm (sum i in Ico m n, f(i) * g(i)) <= f(m) * B.
```

The total amplitude variation telescopes exactly through
`sum_Ico_sub_succ`.  No extra factor two is lost.

## Nonresonant phase contract

`NonresonantDiscreteLogPhasePartialSumBoundStatement X T C` stores:

```text
4*T <= X,
0 <= C,
abs(t) <= 2*T,
X <= Y <= 2*X
  -> norm (sum x in Ico X Y, x^(I*t))
       <= C*X/max(1,abs(t)).
```

The safe reciprocal is the same `1 / max(1,gap)` used by TS317, so equal
ordinates require no division by a nonzero gap.  Membership in the concrete
TS292 truncation proves `abs(Im(rho)-Im(sigma)) <= 2*T`.

## Reduction to TS317

The exact coefficient product has norm

```text
4 * coefficientMagnitude(rho) * coefficientMagnitude(sigma).
```

Abel transfer bounds the weighted power sum by `C*X*gapWeight`; division by
the dyadic average scale `X` then cancels the spatial factor.  Consequently,

```text
NonresonantDiscreteLogPhasePartialSumBoundStatement X T C
  -> WeightedKusminLandauKernelBoundStatement X T (4*C).
```

The constant contains no global linear or quadratic zero mass.  Those masses
belong only to the later finite pair aggregation.

## Fail-closed boundary

The following remain open:

```text
NonresonantDiscreteLogPhasePartialSumBoundStatement
WeightedClosePairEnvelopeBoundStatement smallness
NormalizedTraceBudgetData with traceBudget <= 1/2
RH
OTSA
Goldbach
```

TS318 is therefore a weighted-kernel reduction, not a completed
Kusmin-Landau theorem.

## Verification

```text
Targeted build: 3039/3039
Global build:   2664/2664
Lean placeholders (`sorry`, `axiom`, `opaque`, `admit`): none
Non-ASCII characters: none
git diff --check: clean
```
