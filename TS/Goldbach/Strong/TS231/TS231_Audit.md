# TS231 Audit - Laplace Sine Transform Discharge

## Scope

TS231 discharges the first analytic input isolated by TS230: the one-sided
Laplace transform of the sine function.

The sprint proves the transform by an explicit primitive on finite intervals
and an exponential boundary decay at `+infty`.  It does not prove the remaining
Fubini/arctangent bridge or any Abel-to-cutoff theorem.

## Main declarations

- `laplaceSinePrimitive`
- `one_add_sq_pos`
- `one_add_sq_ne_zero`
- `hasDerivAt_laplaceSinePrimitive`
- `laplaceSinePartialIntegral_eq_boundary`
- `laplaceSineBoundaryTerm_tendsto_zero`
- `laplaceSineTransform`
- `LaplaceSineTransformDischargeLedger`
- `laplaceSineTransformDischargeTarget`

## What is proved

TS231 proves the local primitive identity:

```text
HasDerivAt
  (laplaceSinePrimitive s)
  (TS230.Goldbach.laplaceSineKernel s x)
  x
```

It then applies the finite-interval FTC to obtain:

```text
laplaceSinePartialIntegral s T =
  1 / (1 + s^2)
    - exp (-(s*T)) * (s * sin T + cos T) / (1 + s^2)
```

Finally, for `s > 0`, it proves the exponential boundary term tends to zero
at `+infty` and discharges:

```text
TS230.Goldbach.LaplaceSineTransformStatement
```

that is:

```text
int_0^T exp(-s*x) * sin x dx -> 1 / (1 + s^2)
```

as `T -> +infty`, for every `s > 0`.

## Non-claims

TS231 does not prove the Fubini/arctangent bridge.

TS231 does not prove the damped Dirichlet evaluation target, the Abel-to-cutoff
bridge, the TS228 atTop Dirichlet cutoff value, the TS227 unit product-filter
value unconditionally, the TS219 third-derivative cutoff value
unconditionally, `cosSquareImproperIntegral = pi/6`, the canonical `sinc^4`
value `2*pi/3`, Plancherel evidence, the explicit formula, Gallagher, or
Goldbach.

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS231.LaplaceSineTransformDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS231
git diff --check
```

## Expected result

The build succeeds.  The scan finds no `s[o]rry`, no `a[x]iom`, and no
non-ASCII characters in TS231.  `git diff --check` reports no whitespace
errors.
