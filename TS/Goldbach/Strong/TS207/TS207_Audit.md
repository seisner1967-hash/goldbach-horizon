# TS207 Audit - Naive Haar Energy Divergence Obstruction

## Scope

TS207 proves that the naive Haar-weighted square energy of the triangle spline
has a logarithmic lower-bound obstruction near the lower endpoint.

The sprint responds to the false tempting statement that the TS198 `dx` energy
value `X / 3` should also be a Haar `dx / x` energy.  It shows instead that on
the lower half of the positive scale, the triangle spline is bounded below by
`1 / 2`, so the naive Haar square density dominates `1 / (4*x)`.

## Main Declarations

- `TS207.Goldbach.naiveTriangleSplineHaarEnergyDensity`
- `TS207.Goldbach.naiveTriangleSplineHaarEnergyTruncated`
- `TS207.Goldbach.triangleSpline_scaled_eq_one_sub_of_le_half`
- `TS207.Goldbach.half_le_triangleSpline_scaled_of_le_half`
- `TS207.Goldbach.naiveTriangleSplineHaarEnergyDensity_lower_bound_on_half`
- `TS207.Goldbach.integral_one_div_eq_log_sub`
- `TS207.Goldbach.naiveTriangleSplineHaarEnergy_lower_bound`
- `TS207.Goldbach.NaiveTriangleSplineHaarEnergyLogLowerBoundStatement`
- `TS207.Goldbach.naiveTriangleSplineHaarEnergyLogLowerBoundStatement`
- `TS207.Goldbach.NaiveHaarEnergyDivergenceObstructionLedger`
- `TS207.Goldbach.naiveHaarEnergyDivergenceObstructionTarget`

## What TS207 Proves

For `0 < X`, `0 < epsilon`, and `epsilon <= X / 2`, TS207 proves

```lean
naiveTriangleSplineHaarEnergyTruncated X epsilon >=
  (1 / 4 : Real) * (Real.log ((X : Real) / 2) - Real.log epsilon)
```

The proof uses the TS56 right-branch formula for the triangle spline on
`0 <= x / X <= 1`, specializes it to the lower half interval, applies
`intervalIntegral.integral_mono_on`, and evaluates the comparison integral
`int_epsilon^(X/2) dx/x` by the FTC for `Real.log`.

## Non-Claims

TS207 does not construct a standalone improper Haar integral.
TS207 does not prove a global Haar transport theorem.
TS207 does not contradict TS198, because TS198 concerns `dx` energy, not naive
`dx / x` energy.
TS207 does not prove Mellin/Fourier compatibility.
TS207 does not prove Plancherel.
TS207 does not prove the explicit formula.
TS207 does not prove Gallagher or circle-method correlation.
TS207 does not prove Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS207.NaiveHaarEnergyDivergenceObstruction
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS207
git diff --check
git status --short
```
