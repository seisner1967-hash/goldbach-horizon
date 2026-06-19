# TS179 Audit - Triangle Spline Plancherel API Probe

## Scope

TS179 probes the local Mathlib Plancherel API surface for the triangle-spline
Fourier route.

The probe confirmed that the concrete Fourier objects are available:

- `Real.fourierIntegral`
- `Real.fourierIntegralInv`
- `Real.fourierChar`

The expected ready-made Plancherel/isometry names were not available in the
current Mathlib surface:

- `Real.fourierIntegral_isometry`
- `Real.fourierIntegral_plancherel`
- `fourierIntegral_Plancherel`
- `fourierIntegral_isometry`

TS179 therefore does not claim an unconditional Plancherel theorem.  It keeps
the concrete TS174 Plancherel statement as the single analytic input and proves
the final conditional energy-value consumption theorem.

## Main Theorem

```lean
TS179.Goldbach.triangleSplineSincL2Energy_eq_sqrt_two_thirds_of_plancherel
    (hplancherel :
      TS174.Goldbach.TriangleSplinePlancherelIsometryStatement) :
    TS174.Goldbach.triangleSplineSincL2Energy =
      ENNReal.ofReal (Real.sqrt (2 / 3))
```

The proof combines:

- TS174: supplied Plancherel transfers sinc energy to time energy;
- TS177: time energy equals `ENNReal.ofReal (Real.sqrt (2 / 3))`;
- TS178: sinc spectral energy is finite and therefore analytically consumable.

## Explicit Non-Claims

TS179 does not prove:

- unconditional Plancherel;
- exact spectral energy without the TS174 Plancherel input;
- the Riemann-von Mangoldt explicit formula;
- zeta-zero summability;
- Goldbach.

## Verification

Commands:

```powershell
lake env lean TS\Goldbach\Strong\TS179\TriangleSplinePlancherelAPIProbe.lean
lake build TS.Goldbach.Strong.TS179.TriangleSplinePlancherelAPIProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS179
git diff --check
```

Result:

- Lean file check: pass.
- Lake build: pass.
- Local audit scan: pass, no matches.
- Whitespace audit: pass.

