# TS182 Audit - Triangle Spline Discrete Sieve-Trace Bridge

## Scope

TS182 connects the continuous triangle spline to the natural-number scale used
by later sieve and prime-sum ledgers.

The sprint defines the discrete smoothing weight

```lean
triangleSplineDiscreteWeight X n =
  TS42.MellinJackson.triangleSpline ((n : Real) / (X : Real))
```

and proves its elementary evaluation and support facts for positive `X`.

## Main file

```text
TS/Goldbach/Strong/TS182/TriangleSplineDiscreteSieveTraceBridge.lean
```

## Main declarations

```lean
TS182.Goldbach.triangleSplineDiscreteWeight
TS182.Goldbach.triangleSplineDiscreteWeight_nonneg
TS182.Goldbach.triangleSplineDiscreteWeight_eq_one_sub
TS182.Goldbach.triangleSplineDiscreteWeight_eq_zero_of_X_le_n
TS182.Goldbach.triangleSplineDiscreteWeight_self
TS182.Goldbach.triangleSplineDiscreteWeight_one_sub_at_boundary
TS182.Goldbach.TriangleSplineDiscreteBridgeStatus
TS182.Goldbach.TriangleSplineDiscreteSieveTraceBridgeLedger
TS182.Goldbach.triangleSplineDiscreteSieveTraceBridgeLedger
TS182.Goldbach.TriangleSplineDiscreteSieveTraceBridgeTarget
TS182.Goldbach.triangleSplineDiscreteSieveTraceBridgeTarget
```

## What is proved

For `0 < X`:

- if `n <= X`, then
  `triangleSplineDiscreteWeight X n = 1 - (n : Real) / (X : Real)`;
- if `X <= n`, then `triangleSplineDiscreteWeight X n = 0`;
- at the boundary, `triangleSplineDiscreteWeight X X = 0`;
- the affine and zero boundary formulas agree;
- the weight is nonnegative at every scale.

## Non-claims

TS182 does not define or prove:

- a von Mangoldt weighted sum;
- unconditional Plancherel;
- construction of the zeta-zero family;
- the Riemann-von Mangoldt explicit formula;
- any Goldbach conclusion.

## Verification commands

```powershell
lake env lean TS\Goldbach\Strong\TS182\TriangleSplineDiscreteSieveTraceBridge.lean
lake build TS.Goldbach.Strong.TS182.TriangleSplineDiscreteSieveTraceBridge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS182
git diff --check
git status --short
```

Expected result: build succeeds, no forbidden proof placeholders, no forbidden
declaration placeholders, no non-ASCII characters, and no whitespace errors.
