# TS316 Audit: Quantitative Diagonal Zero-Correlation Bound

## Scope

TS316 closes the quantitative diagonal contract left by TS315. It uses the
exact TS292 coefficient at arithmetic scale one and proves that its global
quadratic mass is finite. The resulting real majorant is uniform in both the
zero-truncation height and the positive dyadic scale.

Main file:

```text
TS/Goldbach/Strong/TS316/QuantitativeDiagonalZeroCorrelationBound.lean
```

No zero-simplicity assumption, separate multiplicity estimate, TS290
recounting, RH input, rational numerical bound, or half-budget is introduced.

## Exact coefficient

The coefficient magnitude is defined by

```text
norm (infiniteZeroSpectralTerm 1 rho).
```

TS268 factorization proves that scale one removes the complex-power factor
exactly, leaving the norm of
`concreteMultiplicityDenominatorFactor rho`. Thus multiplicity, sign, and the
Mellin denominator `rho * (rho + 1)` remain definitionally inherited from the
published spectral term.

## Linear to quadratic summability

TS292 already proves absolute summability of

```text
rho |-> norm (infiniteZeroSpectralTerm 1 rho).
```

For a nonnegative summable family `a`, TS316 proves square summability by:

1. applying `Summable.mul_of_nonneg` to the product family
   `(rho,sigma) |-> a rho * a sigma`;
2. restricting that summable family along the injective diagonal map
   `rho |-> (rho,rho)`.

This proves finiteness of

```text
globalQuadraticSpectralMass = tsum (fun rho => a rho ^ 2).
```

TS316 also proves

```text
globalQuadraticSpectralMass <= globalLinearSpectralMass ^ 2.
```

The proof uses the pointwise inequality `a rho <= tsum a` and comparison with
the summable majorant `(tsum a) * a rho`.

## Normalized pointwise bound

For `x >= 1`, TS268 gives

```text
norm (infiniteZeroSpectralTerm x rho) <= x * a rho.
```

The canonical normalization `2/x` therefore yields

```text
norm (normalizedTruncatedZeroTerm x rho) <= 2 * a rho.
```

No estimate of the individual zero multiplicity is used.

## Diagonal kernel

The diagonal kernel is identified exactly with a finite sum of squared norms.
The half-open dyadic window has cardinality `X`, so its norm is bounded by

```text
4 * X * a rho ^ 2.
```

Division by the TS315 outer factor `X` cancels this spatial cardinality. A
finite partial sum is then bounded by the global quadratic `tsum`, giving the
uniform theorem:

```text
DiagonalZeroCorrelationBoundStatement
  X T (4 * globalQuadraticSpectralMass).
```

A coarser exported form uses only the square of the TS292 linear mass.

## Corrected multiplicity boundary

The diagonal does contain squared multiplicities. Nevertheless, a new
multiplicity-growth hypothesis is not required for finiteness: the complete
coefficient, including its denominator, is already an `l1` family by TS292,
and every nonnegative `l1` family is `l2`.

TS290 may still help produce a sharper or explicit numerical constant, but it
is not needed to close the real diagonal bound.

## Fail-closed boundary

TS316 does not prove:

* a rational upper bound for either global spectral mass;
* that the diagonal allocation fits a prescribed fraction of one half;
* a Kusmin-Landau or van der Corput estimate;
* the weighted off-diagonal close-pair correlation contract;
* a complete finite-moment estimate;
* a concrete `NormalizedTraceBudgetData` value;
* RH, OTSA, or Goldbach.

## Verification commands

```powershell
lake env lean TS\Goldbach\Strong\TS316\QuantitativeDiagonalZeroCorrelationBound.lean
lake build TS.Goldbach.Strong.TS316.QuantitativeDiagonalZeroCorrelationBound
lake build
rg -n "s[o]rry|a[x]iom|o[p]aque|a[d]mit|[^\x00-\x7F]" TS\Goldbach\Strong\TS316
git diff --check
git status --short
```

The source and audit are intended to remain strict ASCII and contain no
placeholder declaration.

Verified build results:

```text
Targeted build: 3037/3037
Global build:   2664/2664
```
