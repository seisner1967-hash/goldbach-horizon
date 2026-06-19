# TS176 Audit - Triangle Spline Time L2 eLpNorm Bridge

## Sprint Scope

TS176 lifts the TS175 interval square-energy constant to the global Lebesgue
square-energy of the triangle spline.  It proves both the real-valued and
complexified global square-energy statements:

```text
integral x, triangleSpline x ^ 2 = 2 / 3
integral x, ||triangleSplineAsComplex x|| ^ 2 = 2 / 3
```

The sprint deliberately stops before converting this global square-energy into
the concrete `eLpNorm` value named in TS174.

## Main Declarations

- `TS176.Goldbach.triangleSplineGlobalRealSquareEnergy`
- `TS176.Goldbach.triangleSplineGlobalComplexSquareEnergy`
- `TS176.Goldbach.TriangleSplineGlobalRealSquareEnergyStatement`
- `TS176.Goldbach.TriangleSplineGlobalComplexSquareEnergyStatement`
- `TS176.Goldbach.TriangleSplineTimeELpNormValueStatement`
- `TS176.Goldbach.triangleSplineSquare_support_subset_Ioc`
- `TS176.Goldbach.triangleSplineSpatialSquareEnergy_eq_globalRealSquareEnergy`
- `TS176.Goldbach.triangleSplineGlobalRealSquareEnergy_eq_two_thirds`
- `TS176.Goldbach.triangleSplineAsComplex_norm_sq_eq_real_sq`
- `TS176.Goldbach.triangleSplineGlobalComplexSquareEnergy_eq_real`
- `TS176.Goldbach.triangleSplineGlobalComplexSquareEnergy_eq_two_thirds`
- `TS176.Goldbach.TriangleSplineTimeL2ELpNormBridgeLedger`
- `TS176.Goldbach.triangleSplineTimeL2ELpNormBridgeLedger`
- `TS176.Goldbach.TriangleSplineTimeL2ELpNormBridgeTarget`
- `TS176.Goldbach.triangleSplineTimeL2ELpNormBridgeTarget`

## What Is Proved

1. The squared real triangle spline is supported in `(-1, 1]`.
2. The TS175 directed interval integral over `[-1,1]` equals the global
   Lebesgue integral over `volume`.
3. The global real square-energy is exactly `2 / 3`.
4. The squared complex norm of the complexified spline is pointwise equal to
   the square of the real spline.
5. The global complex square-energy is exactly `2 / 3`.

## Explicit Non-Claims

TS176 does not prove:

- the concrete `eLpNorm` value
  `triangleSplineTimeL2Energy = ENNReal.ofReal (Real.sqrt (2 / 3))`;
- Plancherel;
- spectral sinc integrability;
- the Riemann-von Mangoldt explicit formula;
- any Goldbach theorem.

## Verification

```powershell
lake env lean TS\Goldbach\Strong\TS176\TriangleSplineTimeL2ELpNormBridge.lean
lake build TS.Goldbach.Strong.TS176.TriangleSplineTimeL2ELpNormBridge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS176
git diff --check
```

Expected: build succeeds, no `s[o]rry`, no `a[x]iom`, no non-ASCII,
whitespace clean.

## Status

`repo_committed`
