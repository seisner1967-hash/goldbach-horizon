# TS291 Audit - Log-Linear Zero-Contribution Assembly

## Scope

TS291 injects the unconditional TS290 global multiplicity-counting contract
into the exact TS271--TS273 finite Abel infrastructure.  It evaluates the
remaining amortized integer-shell expression and obtains a closed bound for
the finite real zero contribution already defined by TS257 and TS265.

No new analytic contract is introduced.

## Finite reciprocal-square estimate

The module proves the elementary bound

```text
sum (n < K) 1 / (n + 1)^2 <= 2
```

by a finite induction with the stronger telescoping estimate

```text
sum (n < K) 1 / (n + 1)^2 <= 2 - 2 / (K + 1).
```

It also proves the exact coefficient inequality

```text
(n + 2) * (1 / (n + 1)^2 - 1 / (n + 2)^2)
  <= 2 / (n + 1)^2.
```

These are finite real inequalities; no infinite series or Stieltjes measure
is used.

## Closed Abel bound

For every nonnegative `C` and every natural truncation height `X`, TS291
proves

```text
shiftedIntegerAmortizedCountBound
    (logLinearMultiplicityCountEnvelope C) X
  <= 5 * C * log (X + 3).
```

The terminal Abel term costs one logarithmic copy.  The finite shell sum costs
at most four copies through the reciprocal-square estimate.

## Concrete TS290 specialization

TS291 defines

```text
xiClosedHighResidualConstant =
  6 * xiGlobalLogLinearConstant.
```

The sixth copy absorbs the exact boundary at imaginary height one.  Using the
actual `TS290.xiGlobalMultiplicityCountingBoundContract`, the module proves

```text
concreteHighImaginaryWeightedResidualMass X
  <= xiClosedHighResidualConstant * log (X + 3)
```

and therefore

```text
concreteHighImaginaryQuadraticEnvelopeMass X
  <= max 1 X * xiClosedHighResidualConstant * log (X + 3).
```

## Final finite zero-contribution bound

The final theorem is unconditional:

```text
abs (triangleSplineZeroContributionFunction ... X)
  <= concreteLowImaginaryWeightedNormMass X
     + max 1 X * xiClosedHighResidualConstant * log (X + 3).
```

For `1 <= X`, a natural-scale facade replaces `max 1 X` by `X`.  The low zone
is deliberately retained as its exact finite mass; TS291 does not assume that
there are no zeta zeros with imaginary part of absolute value below one.

Thus the closed high contribution is `O(X log X)`, stronger than the
provisional `O(X log^2 X)` target.

## Non-claims

TS291 does not prove convergence of an infinite zero sum, a
Riemann-von-Mangoldt asymptotic, the explicit formula, a residual estimate,
Gallagher, an OTSA bridge, or Goldbach.

## Verification

Canonical build target:

```powershell
lake build TS.Goldbach.Strong.TS291.LogLinearZeroContributionAssembly
```

Static checks:

```powershell
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS291
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS291
git diff --check
```

Expected result: the build succeeds and all static scans print no matches.
