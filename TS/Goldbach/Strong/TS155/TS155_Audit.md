# TS155 Audit - Brun-Titchmarsh Threshold Obstruction Geometry

## Status

`repo_committed`

TS155 converts the exact rational threshold isolated by TS153 and bounded by
TS154 into a natural-number obstruction involving only the interval scale and
the TS22 ceiling budget.

## Exact obstruction predicates

```lean
TS155.Goldbach.SelbergBTThresholdObstructed
TS155.Goldbach.SelbergBTGeometricObstruction
TS155.Goldbach.SelbergBTGeometricFeasibility
```

They record respectively:

```text
2 <= (intervalScale + 1) / BTceil

0 < BTceil and 2 * BTceil <= intervalScale + 1

intervalScale + 1 < 2 * BTceil
```

## Threshold geometry

TS155 proves that a rational threshold obstruction automatically makes the
BT ceiling positive. It then clears that positive denominator and obtains the
exact equivalence:

```text
SelbergBTThresholdObstructed x Q
  <-> SelbergBTGeometricObstruction x Q.
```

Main declarations:

```lean
TS155.Goldbach.brunTitchmarshCeilBudget_pos_of_thresholdObstructed
TS155.Goldbach.geometricObstruction_of_thresholdObstructed
TS155.Goldbach.thresholdObstructed_of_geometricObstruction
TS155.Goldbach.thresholdObstructed_iff_geometricObstruction
```

## Impossibility theorem

Combining TS153 and TS154, every successful dependent comparison satisfies:

```text
intervalScale x Q + 1 < 2 * brunTitchmarshCeilBudget x Q.
```

Therefore the opposite natural inequality rules out every dependent level
selection, without any asymptotic approximation:

```lean
TS155.Goldbach.dependentRefinedComparison_forces_geometricFeasibility
TS155.Goldbach.no_dependentRefinedComparison_of_geometricObstruction
TS155.Goldbach.no_dependentRefinedComparison_of_twice_budget_le_interval
```

## Package

```lean
TS155.Goldbach.BrunTitchmarshThresholdObstructionGeometry
TS155.Goldbach.brunTitchmarshThresholdObstructionGeometry
TS155.Goldbach.brunTitchmarshThresholdObstructionGeometryTarget
```

## Remaining work

TS156 should evaluate the explicit natural inequality under the actual scale
constraint `Q = Nat.log 2 x * Nat.log 2 x`. TS155 does not claim eventual
obstruction, alter the TS22 ceiling, refactor the Jordan-two denominator, or
discharge the cumulative finite-head prime-count obligation from TS152.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS155.BrunTitchmarshThresholdObstructionGeometry
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS155
git diff --check -- README.md TS\Goldbach\Strong\TS155
```

Expected result: build succeeds and both audit commands report no issue.
