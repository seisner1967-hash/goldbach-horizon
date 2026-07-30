# TS315 Audit: Discrete Spectral Correlation Identity

## Scope

TS315 opens the exact TS314 quadratic moment and rewrites it as a finite
ordered-pair correlation over the concrete TS292 zero truncation. It keeps the
project's actual multiplicities, signs, and Mellin denominators by defining
each normalized term directly from `infiniteZeroSpectralTerm`.

Main file:

```text
TS/Goldbach/Strong/TS315/DiscreteSpectralCorrelationIdentity.lean
```

No reciprocal zeta derivative, RH assumption, zero-spacing theorem,
Kusmin-Landau estimate, or trace budget is introduced.

## Exact spectral coefficients

The normalized summand is definitionally

```text
(canonicalTraceNormalizationFactor x : Complex) *
  infiniteZeroSpectralTerm x rho.
```

Consequently, TS315 inherits the TS292/TS266 coefficient with its concrete
zero multiplicity and denominator `rho * (rho + 1)`. It does not replace that
coefficient by a simple-zero model and never introduces `1 / zeta'(rho)`.

## Complex square expansion

For every finite complex family, TS315 proves

```text
((norm (sum f))^2 : Complex) =
  sum rho, sum sigma, f rho * conj (f sigma).
```

The proof uses `Complex.mul_conj'` and finite distributivity only. Its
specialization expands the exact `normalizedTruncatedSpectralSize` from TS314.

## Finite Fubini

The pair kernel is the spatial sum over the half-open TS314 dyadic window:

```text
sum x in [X, 2*X),
  normalizedTerm x rho * conj (normalizedTerm x sigma).
```

Two applications of `Finset.sum_comm` then prove that the complex coercion of
the TS314 moment equals the complete ordered-pair correlation average. This is
finite Fubini; no convergence or measure-theoretic interchange is involved.

## Diagonal and off-diagonal split

For each first zero, `Finset.erase rho` isolates the second indices distinct
from `rho`. TS315 proves the exact decomposition

```text
totalCorrelation = diagonalCorrelation + offDiagonalCorrelation.
```

The diagonal is reduced to an explicit finite sum of kernel norms. A concrete
analytic diagonal majorant is deliberately not asserted here.

## Weighted correlation boundary

The open contract is

```text
WeightedZeroOrdinatePairCorrelationWindowBoundStatement
```

It bounds the norm of the complete off-diagonal correlation with all TS292
weights still present. It is not a pointwise kernel bound and not an
unweighted count of close ordinate pairs. The contract also carries the
sufficient technical condition `4*T <= X`; TS315 does not describe this as an
optimal or canonical sampling threshold.

Given a diagonal majorant, this aggregate off-diagonal majorant, and a bound
on their sum by `q^2`, TS315 constructs the exact TS314
`FiniteQuadraticSpectralMomentBoundStatement`.

## Fail-closed boundary

TS315 does not prove:

* a discrete Kusmin-Landau or van der Corput estimate;
* an explicit weighted power-kernel estimate;
* a quantitative diagonal majorant;
* the weighted close-pair zero-correlation contract;
* the finite quadratic moment estimate unconditionally;
* a rational spectral majorant or tail certificate;
* a normalized trace budget at most one half;
* RH, OTSA, or Goldbach.

## Verification commands

```powershell
lake env lean TS\Goldbach\Strong\TS315\DiscreteSpectralCorrelationIdentity.lean
lake build TS.Goldbach.Strong.TS315.DiscreteSpectralCorrelationIdentity
lake build
rg -n "s[o]rry|a[x]iom|o[p]aque|a[d]mit|[^\x00-\x7F]" TS\Goldbach\Strong\TS315
git diff --check
git status --short
```

The source and audit are intended to remain strict ASCII and contain no
placeholder declaration.

Verified build results:

```text
Targeted build: 3036/3036
Global build:   2664/2664
```
