# TS317 Audit - Weighted Off-Diagonal Correlation Reduction

## Scope

TS317 opens the exact TS315 off-diagonal kernel without replacing the project
coefficients.  It proves the normalized complex-power identity, closes a coarse
absolute off-diagonal estimate from TS292 summability, and reduces any sharper
estimate to two finite analytic contracts.

The module does not claim a Kusmin-Landau theorem, close-pair smallness, a
rational half-budget, RH, OTSA, or Goldbach.

## Main declarations

```lean
TS317.Goldbach.exactZeroCoefficient
TS317.Goldbach.offDiagonalComplexExponent
TS317.Goldbach.offDiagonalCoefficientProduct

TS317.Goldbach.normalizedPairTerm_eq_weightedCpow
TS317.Goldbach.normalizedZeroPairCorrelationKernel_eq_weightedCpow_sum

TS317.Goldbach.finiteOffDiagonalCoefficientMass
TS317.Goldbach.offDiagonalNormalizedZeroPairCorrelation_norm_le_mass
TS317.Goldbach.weightedZeroOrdinatePairCorrelationWindowBound_coarse
TS317.Goldbach.finiteQuadraticSpectralMomentBound_coarse

TS317.Goldbach.zeroOrdinateGap
TS317.Goldbach.ordinateGapDecayWeight
TS317.Goldbach.weightedClosePairEnvelope
TS317.Goldbach.WeightedKusminLandauKernelBoundStatement
TS317.Goldbach.WeightedClosePairEnvelopeBoundStatement
TS317.Goldbach.weightedZeroOrdinatePairCorrelationWindowBound_of_reduction
```

## Exact exponent and weights

For a positive natural scale `x`, TS317 proves the exact identity

```text
normalizedTerm(x,rho) * conj(normalizedTerm(x,sigma))
  = 4 * coefficient(rho) * conj(coefficient(sigma))
      * x^(rho + conj(sigma) - 2).
```

Thus the real amplitude and the imaginary phase remain together in the exact
exponent `rho + conj sigma - 2`.  The exponent is not `-4`: the two factors
`2 / x` together contribute exactly `x^(-2)`.

The equality is proved from the TS268 factorization of the concrete TS292 term,
Mathlib complex-power conjugation, and `Complex.cpow_add`/`Complex.cpow_sub`.
No reciprocal zeta derivative or simple-zero model is introduced.

## Finite geometry

Every pair sum remains finite on

```lean
TS315.Goldbach.truncatedZeroSet T
```

with the second index in `erase rho`, exactly as in TS315.  TS317 does not
replace this with a global pair `tsum`.

Distinct concrete zeros need not have distinct imaginary parts.  Accordingly,
the phase-aware weight is

```text
1 / max(1, |Im(rho) - Im(sigma)|).
```

It equals the close-pair branch for gaps at most one and avoids every division
by an unproved nonzero ordinate gap.

## Coarse unconditional bound

TS316 gives

```text
norm(normalizedTerm(x,rho)) <= 2 * coefficientMagnitude(rho).
```

After summing over the `X` points of the dyadic window and dividing by `X`,
TS317 obtains

```text
norm(kernel(X,rho,sigma) / X)
  <= 4 * coefficientMagnitude(rho) * coefficientMagnitude(sigma).
```

The finite ordered off-diagonal coefficient mass is bounded by the square of
the global TS292 linear mass.  Hence, whenever the stored compatibility
`4 * T <= X` holds, TS317 unconditionally inhabits the TS315 contract with the
coarse majorant

```text
4 * globalLinearSpectralMass^2.
```

This proves existence of an off-diagonal majorant, not the smallness required
for a trace budget at most one half.

Combining this estimate with the TS316 diagonal bound also proves the complete
finite-moment contract with

```text
q = 3 * globalLinearSpectralMass.
```

Indeed, both correlation components are at most four times the squared linear
mass, while their sum is at most the square of three times that mass.  This
closes coarse moment finiteness but not Gallagher-scale smallness.

## Phase-aware fail-closed reduction

`WeightedKusminLandauKernelBoundStatement` asks for the pointwise averaged
kernel bound with the exact coefficient weights and the safe gap-decay factor.
It includes `4 * T <= X` and a nonnegative oscillation constant.

`WeightedClosePairEnvelopeBoundStatement` asks for a real upper bound on the
exact finite weighted pair envelope.  TS317 proves a coarse certificate from
the TS292 linear mass but does not prove a sufficiently small one.

The theorem

```lean
weightedZeroOrdinatePairCorrelationWindowBound_of_reduction
```

shows that these two inputs imply the exact TS315
`WeightedZeroOrdinatePairCorrelationWindowBoundStatement`, with majorant equal
to the product of the oscillation constant and pair-envelope majorant.

## Fail-closed boundary

The ledger records:

- exact normalized factorization: proved;
- exact exponent `rho + conj sigma - 2`: proved;
- finite truncation and ordered erase geometry: preserved;
- coarse absolute off-diagonal contract: proved;
- coarse complete finite-moment bound: proved;
- phase-aware reduction to TS315: proved;
- weighted Kusmin-Landau estimate: not proved;
- close-pair smallness: not proved;
- rational half-budget: not proved;
- RH: not assumed;
- OTSA and Goldbach: not claimed.

## Mechanical checks

```text
Targeted build: 3038/3038
Global build:   2664/2664
Placeholders:   none
ASCII:          strict
```
