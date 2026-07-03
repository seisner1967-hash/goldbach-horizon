# TS220 Audit - Cos-Square IPP Primitive Derivative Bridge

Status: repo_committed_relative

## Scope

- `TS/Goldbach/Strong/TS220/CosSquareIPPPrimitiveDerivativeBridge.lean`

## Build

- `lake env lean TS\Goldbach\Strong\TS220\CosSquareIPPPrimitiveDerivativeBridge.lean`
- `lake build TS.Goldbach.Strong.TS220.CosSquareIPPPrimitiveDerivativeBridge`

## What TS220 Proves

TS220 proves the local derivative identity behind the TS219 finite triple-IPP
cutoff route. It defines

```text
P(x) = -f(x)/(3*x^3) - f'(x)/(6*x^2) - f''(x)/(6*x)
```

for `f(x) = (1 - cos x)^2`, using the TS214 derivative models, and proves:

```lean
HasDerivAt
  cosSquareIPPPrimitive
  (TS213.Goldbach.cosSquareHaarKernel x -
    (1 / 6 : Real) * TS213.Goldbach.cosSquareThirdDerivativeKernel x)
  x
```

for every `x` with `x != 0`.

This is the compact calculus core required before proving the future finite
interval FTC form of `TS219.Goldbach.CosSquareFiniteTripleIPPStatement`.

## Supporting Lemmas

- `cosSquareRemainder_hasDerivAt`
- `cosSquareFirstDerivativeModel_hasDerivAt`
- `cosSquareSecondDerivativeModel_hasDerivAt`
- `cosSquareIPPPrimitive_hasDerivAt`

## Non-Claims

TS220 does not prove `TS219.Goldbach.CosSquareFiniteTripleIPPStatement`.
It does not prove that the primitive jump equals the TS219 boundary sum.
It does not prove boundary vanishing.
It does not prove the third-derivative cutoff value.
It does not prove the Dirichlet cutoff or Abel value.
It does not prove the canonical `sinc^4` value.
It does not prove Plancherel evidence, the explicit formula, Gallagher, or
Goldbach.

## Audit Commands

```powershell
lake env lean TS\Goldbach\Strong\TS220\CosSquareIPPPrimitiveDerivativeBridge.lean
lake build TS.Goldbach.Strong.TS220.CosSquareIPPPrimitiveDerivativeBridge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS220
git diff --check
```

