# TS313 Audit: Normalized Trace Budget and Rational Packaging Bridge

## Scope

TS313 is the typed bridge between the real/complex infinite explicit identity
and the rational TS181 trace interface.  It fixes the scale normalization,
keeps the spectral and residual pieces separate, certifies the closed residual
bounds from TS311, and proves the rational packaging implication.

Main file:

```text
TS/Goldbach/Strong/TS313/NormalizedTraceBudgetRationalPackagingBridge.lean
```

No new zero estimate, variance estimate, contour estimate, or special-value
evaluation is introduced.

## Main declarations

```lean
TS313.Goldbach.canonicalTraceNormalizationFactor
TS313.Goldbach.normalizedSpectralTrace
TS313.Goldbach.normalizedExceptionalResidual
TS313.Goldbach.normalizedFixedLeftResidual

TS313.Goldbach.NormalizedSpectralTraceBoundStatement
TS313.Goldbach.NormalizedTraceBudgetData

TS313.Goldbach.normalizedZeroTraceContribution
TS313.Goldbach.normalizedResidualTerms
TS313.Goldbach.ts181TraceBudgetAdapterData_of_normalizedBudget
TS313.Goldbach.explicitFormulaTraceBridgeTarget_of_normalizedBudget

TS313.Goldbach.TS313Ledger
TS313.Goldbach.ts313Ledger
```

## Certified normalization

The canonical factor is

```text
2 / x.
```

It sends the TS204 main term `x / 2` to one.  The data structure stores both a
real `normalizationFactor` and the certificate

```lean
normalizationFactor = canonicalTraceNormalizationFactor scale
```

so the scale is not erased when the final non-indexed TS181 ledger is built.
Positivity is proved for every positive natural scale.  TS313 also proves the
effective identity

```text
canonicalTraceNormalizationFactor(x) * triangleSplinePerronMainTerm(x) = 1
```

and its direct version for every `NormalizedTraceBudgetData` value.

## Concrete real quantities

At a scale `x`, TS313 distinguishes:

```text
normalizationFactor * norm(infiniteZeroContribution x)
normalizationFactor * norm(infiniteExceptionalResidueContribution x)
normalizationFactor * norm(normalize(fixedLeftBoundaryLimit x))
```

The spectral comparison with a rational majorant is exactly the parameterized
predicate `NormalizedSpectralTraceBoundStatement`.  It is a pointwise trace
bound, not a Gallagher variance statement.  TS314 must define a genuine
quadratic mean and prove the bridge from that mean to this pointwise output.

The exceptional and fixed-left comparisons are tied to the already proved
closed envelopes:

* `TS306.concreteExceptionalResidueBound`;
* `TS305.fixedLeftUniformBound / (2*pi)`.

TS313 proves that these envelope certificates dominate the actual normalized
complex terms.  It also combines them into a bound for the aggregated TS311
contour residual.

## TS95 semantic allocation

The rational fields are populated as follows:

| TS95 field | TS313 value | Reason |
| --- | --- | --- |
| `zeroContribution.value` | `spectralMajorant` | normalized nontrivial-zero trace |
| `residuals.poleTerm` | `0` | the pole at `1` is already the main term `x / 2` |
| `residuals.trivialZeroTerm` | `0` | the rectangle stops at `Re(s) = -3/2`, before `-2` |
| `residuals.contourError` | `exceptionalMajorant + leftMajorant` | poles `0,-1` plus fixed-left boundary |

Thus neither the main pole nor a trivial zero is counted twice.  The two
analytically distinct residual pieces remain separate in the rich data and
are added only at the legacy TS95 boundary.

## Central packaging result

The constructor

```lean
ts181TraceBudgetAdapterData_of_normalizedBudget
```

maps every `NormalizedTraceBudgetData` to the exact
`TS312.TS181TraceBudgetAdapterData`.  The proof of the final rational budget
comparison is only associativity and the supplied component inequality.

Consequently:

```lean
NormalizedTraceBudgetData ->
  TS95.Goldbach.ExplicitFormulaTraceBridgeTarget
```

is proved through the TS312 adapter theorem.

## Fail-closed boundary

TS313 does not construct a value of `NormalizedTraceBudgetData`.  In
particular, it does not prove:

* `NormalizedSpectralTraceBoundStatement` for a target majorant;
* a genuine Gallagher quadratic-mean variance theorem;
* existence of a suitable TS93 zero-family ledger for this packaging;
* rational majorants fitting together below one half;
* a TS181 half-trace budget;
* RH or any substitute for RH;
* OTSA;
* Goldbach.

The next analytic sprint can focus on the spectral predicate without changing
the rational packaging or the Wall 2 explicit identity.

## Verification commands

```powershell
lake env lean TS\Goldbach\Strong\TS313\NormalizedTraceBudgetRationalPackagingBridge.lean
lake build TS.Goldbach.Strong.TS313.NormalizedTraceBudgetRationalPackagingBridge
lake build
rg -n "s[o]rry|a[x]iom|o[p]aque|a[d]mit|[^\x00-\x7F]" TS\Goldbach\Strong\TS313
git diff --check
git status --short
```

Verified build results:

```text
Targeted build: 3034/3034
Global build:   2664/2664
```

The source and audit are intended to remain strict ASCII and contain no
`s[o]rry`, `a[x]iom`, `o[p]aque`, or `a[d]mit` declaration.
