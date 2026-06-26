# TS208 Audit - Triangle Spline Plancherel Evidence Probe

## Scope

TS208 probes Wall 1 in a triangle-spline-specific way.  Instead of proving a
general Plancherel theorem for Mathlib's `Real.fourierIntegral`, it isolates the
direct scalar spectral identity that would be enough for this kernel:

```lean
integral volume (fun xi => triangleSplineSincRealWeight xi ^ 2) = 2 / 3
```

The sprint proves that this future `sinc^4` integral identity implies the exact
TS174 spectral `eLpNorm` value, the concrete TS174 triangle-spline Plancherel
statement, and the TS204 triangle-spline Plancherel input evidence.

## Main Declarations

- `TS208.Goldbach.TriangleSplineSincFourthIntegralValueStatement`
- `TS208.Goldbach.TriangleSplineDirectSpectralValueStatement`
- `TS208.Goldbach.sincComplexELpNorm_eq_sqrt_two_thirds_of_sincFourthIntegral`
- `TS208.Goldbach.directSpectralValue_of_sincFourthIntegral`
- `TS208.Goldbach.triangleSplinePlancherel_of_sincFourthIntegral`
- `TS208.Goldbach.triangleSplinePlancherelInputEvidence_of_sincFourthIntegral`
- `TS208.Goldbach.TriangleSplinePlancherelEvidenceProbeLedger`
- `TS208.Goldbach.triangleSplinePlancherelEvidenceProbeTarget`

## What TS208 Proves

TS208 proves the conditional chain:

```lean
TriangleSplineSincFourthIntegralValueStatement
  -> TriangleSplineDirectSpectralValueStatement
  -> TS174.Goldbach.TriangleSplinePlancherelIsometryStatement
  -> TS204.Goldbach.TriangleSplinePlancherelInputEvidence
       TS204.Goldbach.triangleSplinePlancherelInputContract
```

The proof reuses TS178 spectral integrability to convert the real scalar
integral into the complex `eLpNorm`, then combines TS174 Fourier/sinc
identification and TS177 time-side `eLpNorm` value.

## Non-Claims

TS208 does not prove the direct `sinc^4` integral.
TS208 does not prove a general Plancherel theorem.
TS208 does not prove the explicit formula.
TS208 does not prove Gallagher or circle-method correlation.
TS208 does not prove Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS208.TriangleSplinePlancherelEvidenceProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS208
git diff --check
git status --short
```
