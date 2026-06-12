# TS156 Audit - Brun-Titchmarsh Threshold Evaluation

## Status

`repo_committed_relative`

TS156 evaluates the exact TS22 ceiling inside the natural obstruction proved
by TS155. It does not replace the ceiling by an asymptotic approximation.

## Exact TS22 formula

The sprint works with the repository definition

```text
BTceil(x,Q) = ceil(4 * intervalScale(x,Q) / Real.log(Q+1)).
```

In particular, the numerator is `4 * intervalScale`, not
`4 * (intervalScale + 1)`.

## Finite sufficient regime

TS156 proves that the following two hypotheses are sufficient:

```text
2 <= intervalScale x Q
16 <= Real.log(Q+1).
```

The ceiling estimate is handled directly:

```text
ceil(4*h/log(Q+1)) < h/4 + 1,
```

and for `h >= 2` this gives

```text
2 * BTceil(x,Q) <= h + 1.
```

Main declarations:

```lean
TS156.Goldbach.brunTitchmarshCeilBudget_pos_of_log_sixteen
TS156.Goldbach.twice_brunTitchmarshCeilBudget_le_interval_of_log_sixteen
TS156.Goldbach.geometricObstruction_of_log_sixteen
TS156.Goldbach.geometricObstruction_of_exp_sixteen_le
```

## Goldbach-scale specialization

TS156 defines

```lean
TS156.Goldbach.goldbachScaleQ
TS156.Goldbach.GoldbachThresholdObstructionRegime
```

where the finite regime requires

```text
2 * (Nat.log 2 x)^2 <= x
Real.exp 16 <= ((Nat.log 2 x)^2 : Real) + 1.
```

Under `LargeX x`, these conditions imply the TS155 geometric obstruction at
the actual scale `Q = (Nat.log 2 x)^2`. Therefore no dependent Selberg level
selection can satisfy the TS150 comparison there.

Main declarations:

```lean
TS156.Goldbach.goldbachScaleQ_pos
TS156.Goldbach.two_le_intervalScale_goldbachScaleQ
TS156.Goldbach.geometricObstruction_at_goldbachScale
TS156.Goldbach.no_dependentRefinedComparison_at_goldbachScale
```

## Remaining work

TS156 does not prove that `GoldbachThresholdObstructionRegime x` holds for all
sufficiently large `x`, nor does it give an optimized numerical threshold.
That requires explicit bridges between `Nat.log 2 x`, the real exponential,
and the inequality `2 * (Nat.log 2 x)^2 <= x`.

The cumulative finite-head prime-count obligation from TS152 also remains
separate. No Selberg denominator or TS22 budget definition is changed.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS156.BrunTitchmarshThresholdEvaluation
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS156
git diff --check -- README.md TS\Goldbach\Strong\TS156
```

Expected result: build succeeds and both audit commands report no issue.
