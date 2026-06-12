# TS157 Audit - Goldbach Scale Eventual Obstruction

## Status

`repo_committed`

TS157 closes the eventual-regime task left by TS156 with the explicit natural
threshold

```text
goldbachObstructionThreshold = 2^3000.
```

For every `x` above this threshold, the Goldbach scale
`Q = (Nat.log 2 x)^2` lies in the finite obstruction regime of TS156.

## Certified real-exponential bound

TS157 imports Mathlib's certified rational estimate on `Real.exp 1` and proves

```text
Real.exp 16 < 9,000,001 = 3000^2 + 1.
```

No floating-point evaluation or external numerical certificate is used.

Main declaration:

```lean
TS157.Goldbach.exp_sixteen_lt_nine_million_one
```

## Elementary power domination

TS157 proves by induction that

```text
2 * n^2 <= 2^n
```

for every `n >= 8`.

Main declaration:

```lean
TS157.Goldbach.two_mul_sq_le_two_pow
```

## Eventual Goldbach regime

From `2^3000 <= x`, Mathlib's natural-log Galois connection gives

```text
3000 <= Nat.log 2 x.
```

The exponential estimate supplies

```text
Real.exp 16 <= (Nat.log 2 x)^2 + 1,
```

while power domination and `2^(Nat.log 2 x) <= x` supply

```text
2 * (Nat.log 2 x)^2 <= x.
```

Thus `TS156.Goldbach.GoldbachThresholdObstructionRegime x` holds throughout
the explicit tail.

Main declarations:

```lean
TS157.Goldbach.goldbachObstructionExponent
TS157.Goldbach.goldbachObstructionThreshold
TS157.Goldbach.obstructionExponent_le_log
TS157.Goldbach.goldbachThresholdObstructionRegime_of_threshold_le
```

## Final impossibility theorem

TS157 combines the eventual regime with TS156 and proves that for every
dependent Selberg level selection and every `x >= 2^3000`, the TS150 dependent
budget comparison is impossible.

```lean
TS157.Goldbach.geometricObstruction_of_goldbachObstructionThreshold_le
TS157.Goldbach.no_dependentRefinedComparison_of_goldbachObstructionThreshold_le
```

The package is exposed through:

```lean
TS157.Goldbach.GoldbachScaleEventualObstruction
TS157.Goldbach.goldbachScaleEventualObstruction
TS157.Goldbach.goldbachScaleEventualObstructionTarget
```

## Scope

TS157 certifies an impossibility result for the current TS150 comparison and
the current TS122 Jordan-two denominator. It does not prove that no other
Selberg sieve formulation can establish Brun-Titchmarsh, and it does not
alter or discharge the cumulative finite-head prime-count obligation from
TS152.

The next architectural task is to choose between refactoring the denominator
or budget interface and pivoting to another analytic front.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS157.GoldbachScaleEventualObstruction
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS157
git diff --check -- README.md TS\Goldbach\Strong\TS157
```

Expected result: build succeeds and both audit commands report no issue.
