# TS175 Audit - Triangle Spline Spatial L2 Energy Evaluation

## Sprint Scope

TS175 evaluates the elementary spatial square-energy of the triangle spline:

```lean
int_{-1}^{1} triangleSpline(x)^2 dx = 2 / 3
```

This is the squared L2 energy on the time side.  It does not evaluate the
`eLpNorm` object from TS174, prove Plancherel, prove spectral sinc
integrability, prove the explicit formula, or prove Goldbach.

## Main Declarations

- `TS175.Goldbach.triangleSplineSpatialSquareEnergy`
- `TS175.Goldbach.TriangleSplineSpatialSquareEnergyStatement`
- `TS175.Goldbach.leftBranchSquareIntegral_eq_one_third`
- `TS175.Goldbach.rightBranchSquareIntegral_eq_one_third`
- `TS175.Goldbach.triangleSplineSquare_intervalIntegrable_left`
- `TS175.Goldbach.triangleSplineSquare_intervalIntegrable_right`
- `TS175.Goldbach.triangleSplineSquare_left_eq_branch`
- `TS175.Goldbach.triangleSplineSquare_right_eq_branch`
- `TS175.Goldbach.triangleSplineSpatialSquareEnergy_eq_two_thirds`
- `TS175.Goldbach.TriangleSplineSpatialL2EnergyEvaluationLedger`
- `TS175.Goldbach.triangleSplineSpatialL2EnergyEvaluationLedger`
- `TS175.Goldbach.TriangleSplineSpatialL2EnergyEvaluationTarget`
- `TS175.Goldbach.triangleSplineSpatialL2EnergyEvaluationTarget`

## What Is Proved

TS175 proves:

```lean
TS175.Goldbach.TriangleSplineSpatialSquareEnergyStatement
```

The proof splits the interval at `0`, uses the TS56 affine branch formulae
`triangleSpline = 1 + x` on `[-1,0]` and `triangleSpline = 1 - x` on `[0,1]`,
then computes both polynomial square integrals as `1/3`.

## Explicit Non-Claims

TS175 does not prove:

- the `eLpNorm` value of the triangle spline;
- Plancherel;
- L2 finiteness or integrability of the squared-sinc candidate;
- the Riemann-von Mangoldt explicit formula;
- any Goldbach theorem.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS175.TriangleSplineSpatialL2EnergyEvaluation
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS175
git diff --check
```

Expected result: build succeeds, no `s[o]rry`, no `a[x]iom`, no non-ASCII, and
no whitespace errors.

## Status

`repo_committed`
