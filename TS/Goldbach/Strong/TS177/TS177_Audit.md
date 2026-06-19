# TS177 Audit - Triangle Spline Time eLpNorm Value

## Scope

TS177 closes the time-side `eLpNorm` value left open by TS176.
It converts the global complex square-energy identity

```lean
integral volume
  (fun x => norm (TS166.Goldbach.triangleSplineAsComplex x) ^ 2) = 2 / 3
```

into the exact TS174 time-side L2 energy value

```lean
TS174.Goldbach.triangleSplineTimeL2Energy =
  ENNReal.ofReal (Real.sqrt (2 / 3))
```

No Plancherel theorem, spectral sinc integrability, explicit formula, or
Goldbach conclusion is claimed.

## Main Declarations

```lean
TS177.Goldbach.triangleSplineAsComplex_aestronglyMeasurable
TS177.Goldbach.triangleSplineRealSquare_integrableOn_Ioc
TS177.Goldbach.triangleSplineComplexNormSq_integrableOn_Ioc
TS177.Goldbach.triangleSplineComplexNormSq_support_subset_Ioc
TS177.Goldbach.triangleSplineComplexNormSq_integrable
TS177.Goldbach.triangleSplineTimeELpNormValue
TS177.Goldbach.triangleSplineTimeELpNormValueLedger
TS177.Goldbach.triangleSplineTimeELpNormValueTarget
```

## What Is Proved

1. The complexified triangle spline is a.e. strongly measurable.
2. The real squared spline is integrable on `Set.Ioc (-1) 1`, using the
   TS175 branch integrability facts.
3. The squared norm of the complexified spline is globally integrable, using
   TS176 support control.
4. The TS174 time-side `eLpNorm` has the exact value
   `ENNReal.ofReal (Real.sqrt (2 / 3))`.

The final step unfolds `eLpNorm`, rewrites the defining `lintegral` as the
`ENNReal.ofReal` of the TS176 global integral, and uses
`Real.sqrt_eq_rpow` together with `ENNReal.ofReal_rpow_of_nonneg`.

## Explicit Non-Claims

TS177 deliberately does not prove:

```text
Plancherel
spectral sinc integrability
Riemann-von Mangoldt explicit formula
Goldbach
```

These remain future obligations after the time-side energy has been fixed.

## Verification Commands

```powershell
lake env lean TS\Goldbach\Strong\TS177\TriangleSplineTimeELpNormValue.lean
lake build TS.Goldbach.Strong.TS177.TriangleSplineTimeELpNormValue
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS177
git diff --check
```

## Audit Result

```text
Status: repo_committed
Build: pass
s[o]rry/a[x]iom scan: pass
ASCII scan: pass
Whitespace scan: pass
```
