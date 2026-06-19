# TS178 Audit - Triangle Spline Sinc Spectral Integrability

## Scope

TS178 proves that the pi-scale squared-sinc spectral candidate from TS166/TS174
has finite `eLpNorm` at exponent `2`.

The sprint is deliberately local. It proves spectral finiteness only. It does
not prove Plancherel, does not evaluate the spectral norm, does not open the
Riemann-von Mangoldt explicit formula, and does not prove Goldbach.

## Main Theorems

```lean
TS178.Goldbach.triangleSplineSincL2Energy_lt_top :
  TS174.Goldbach.triangleSplineSincL2Energy < (Top.top : ENNReal)

TS178.Goldbach.triangleSplineSincL2Energy_ne_top :
  Not
    (TS174.Goldbach.triangleSplineSincL2Energy =
      (Top.top : ENNReal))
```

## Proof Ingredients

TS178 defines:

```lean
triangleSplineSincRealWeight
triangleSplineSincComplexWeight
```

for the pi-scale squared-sinc candidate. It then proves:

- measurability and a.e. strong measurability;
- nonnegativity;
- the pointwise bound `triangleSplineSincRealWeight xi <= 1`;
- the global domination
  `triangleSplineSincRealWeight xi <= 2 * (1 / (1 + xi ^ 2))`;
- integrability of the real weight by `integrable_inv_one_add_sq`;
- integrability of the square by `0 <= w <= 1`, hence `w ^ 2 <= w`;
- integrability of the squared norm of the complex lift;
- finiteness of the corresponding `eLpNorm` via the `lintegral`/`integral`
  bridge for nonnegative integrable functions.

## Explicit Non-Claims

TS178 does not prove:

- Plancherel;
- the exact spectral norm value;
- the Riemann-von Mangoldt explicit formula;
- zeta-zero summability;
- Goldbach.

## Verification

Commands:

```powershell
lake env lean TS\Goldbach\Strong\TS178\TriangleSplineSincSpectralIntegrability.lean
lake build TS.Goldbach.Strong.TS178.TriangleSplineSincSpectralIntegrability
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS178
git diff --check
```

Result:

- Lean file check: pass.
- Lake build: pass.
- Local audit scan: pass, no matches.
- Whitespace audit: pass.

