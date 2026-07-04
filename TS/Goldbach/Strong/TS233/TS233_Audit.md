# TS233 Audit - Compact Fubini Identity Discharge

## Scope

TS233 discharges the first analytic obligation isolated by TS232:
the compact Fubini identity on the finite rectangle `[b, A] x [0, T]`.

The sprint stays finite and compact.  It proves the parameter primitive,
the parameter integral identity, integrability on the restricted rectangle,
the compact Fubini swap, and finally
`TS232.Goldbach.CompactFubiniIdentityStatement`.

## Main declarations

- `compactFubiniKernel`
- `compactFubiniKernel_continuous`
- `compactFubiniPrimitiveS`
- `hasDerivAt_compactFubiniPrimitiveS`
- `parameterIntegral_eq_dampedDifferenceKernel`
- `parameterSetIntegral_eq_dampedDifferenceKernel`
- `laplaceSinePartialIntegral_eq_compactFubiniSetIntegral`
- `dampedDirichletKernel_intervalIntegrable`
- `compactFubiniKernel_integrable_restrictRectangle`
- `compactFubiniKernel_integral_swap`
- `compactFubiniIdentity`
- `CompactFubiniIdentityDischargeLedger`
- `compactFubiniIdentityDischargeTarget`

## What is proved

For `0 < b`, `b < A`, and `0 <= T`, TS233 proves:

```text
dampedPartialIntegral b T - dampedPartialIntegral A T
  =
intervalIntegral
  (fun s => TS230.Goldbach.laplaceSinePartialIntegral s T)
  b A volume
```

The proof proceeds by:

1. defining the compact kernel `exp((-x) * s) * sin x`;
2. proving the parameter primitive in `s`;
3. converting the parameter integral to the damped-kernel difference;
4. proving integrability on the finite rectangle by continuity on a compact;
5. applying `integral_integral_swap`;
6. rewriting the swapped integrals back to the TS232 statement.

## Non-claims

TS233 does not prove `LaplaceBoundaryUniformLimitStatement`.

TS233 does not prove `DampedDifferenceAtTopStatement`.

TS233 does not prove `AuxiliaryDampingUniformBoundStatement`.

TS233 does not prove `CorrectedFubiniExecutionStatement`, the damped
Dirichlet evaluation target, the Abel-to-cutoff bridge, the TS228 atTop
Dirichlet cutoff value, the TS227 unit product-filter value unconditionally,
the TS219 third-derivative cutoff value unconditionally,
`cosSquareImproperIntegral = pi/6`, the canonical `sinc^4` value `2*pi/3`,
Plancherel evidence, the explicit formula, Gallagher, or Goldbach.

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS233.CompactFubiniIdentityDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS233
git diff --check
```

## Expected result

The build succeeds.  The scan finds no `s[o]rry`, no `a[x]iom`, and no
non-ASCII characters in TS233.  `git diff --check` reports no whitespace
errors.
