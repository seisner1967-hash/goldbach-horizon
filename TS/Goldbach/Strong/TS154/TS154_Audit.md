# TS154 Audit - Selberg Denominator Upper-Bound Obstruction Probe

## Status

`repo_committed`

TS154 proves an unconditional uniform upper bound for the TS122 optimization
denominator and combines it with the exact necessary threshold extracted by
TS153. No asymptotic growth estimate is assumed.

## Denominator rewrite

The denominator summand is rewritten using the squarefree support of the
Mobius square. Every supported squarefree integer divides the product of the
primes at most `level`.

Main declarations:

```lean
TS154.Goldbach.selbergDenominatorSummand_eq_squarefree
TS154.Goldbach.selbergOptimizationDenominator_eq_squarefreeSum
TS154.Goldbach.squarefree_dvd_selbergPrimorial
TS154.Goldbach.selbergOptimizationDenominator_le_primorialDivisorSum
```

## Finite Euler product

The reciprocal Jordan-two function is proved multiplicative. Its divisor sum
over the squarefree primorial is therefore the product of the local factors

```text
p^2 / (p^2 - 1).
```

The prime product is enlarged to all integers from `2` to `level`, whose
product telescopes exactly:

```text
product_{n=2}^level n^2 / (n^2 - 1)
  = 2 * level / (level + 1).
```

Main declarations:

```lean
TS154.Goldbach.inverseJordanTwoFunction_isMultiplicative
TS154.Goldbach.selbergPrimorialDivisorSum_eq_primeProduct
TS154.Goldbach.selbergEulerFactor_product_Icc
TS154.Goldbach.selbergOptimizationDenominator_le_telescopingBound
TS154.Goldbach.selbergOptimizationDenominator_le_two
TS154.Goldbach.selbergOptimizationDenominator_lt_two
```

Thus, for every positive level:

```text
D(level) <= 2 * level / (level + 1) < 2.
```

## TS153 obstruction

A successful refined Selberg/Brun-Titchmarsh comparison already forces the
TS153 necessary threshold below `D(level)`. TS154 therefore proves that the
threshold must be strictly below `2`. Conversely, a threshold at least `2`
rules out every dependent level selection.

Main declarations:

```lean
TS154.Goldbach.necessarySelbergDenominatorLowerBoundRat_lt_two
TS154.Goldbach.dependentRefinedComparison_forces_threshold_lt_two
TS154.Goldbach.no_dependentRefinedComparison_of_two_le_threshold
TS154.Goldbach.SelbergDenominatorUpperBoundObstructionProbe
TS154.Goldbach.selbergDenominatorUpperBoundObstructionProbeTarget
```

## Remaining work

The late-window route must now evaluate the explicit TS153 threshold. If it
reaches `2`, TS154 proves a genuine obstruction to the current Selberg budget,
not a missing choice of level. The cumulative finite-head prime-count input
from TS152 remains a separate obligation.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS154.SelbergDenominatorUpperBoundObstructionProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS154
git diff --check -- README.md TS\Goldbach\Strong\TS154
```

Expected result: build succeeds and both audit commands report no issue.
