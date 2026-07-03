# TS226 Audit - Third-Derivative Finite Linearization Discharge

## Scope

TS226 discharges the finite algebra obligation left open by TS225:

```lean
TS225.Goldbach.ThirdDerivativeCutoffLinearizationStatement
```

It proves that, eventually along the TS219 product cutoff filter, the finite
interval integral of the TS213 third-derivative kernel is the linear
combination of the two finite Dirichlet integrals at frequencies `1` and `2`.

The proof works on the explicit cutoff event `0 < eps < 1 < T`, so the compact
interval `[eps, T]` stays inside the positive half-line and avoids the
singularity at zero.

## Main declarations

- `TS226.Goldbach.thirdDerivativeCutoffLinearization`
- `TS226.Goldbach.ThirdDerivativeFiniteLinearizationDischargeLedger`
- `TS226.Goldbach.thirdDerivativeFiniteLinearizationDischargeLedger`
- `TS226.Goldbach.ThirdDerivativeFiniteLinearizationDischargeTarget`
- `TS226.Goldbach.thirdDerivativeFiniteLinearizationDischargeTarget`

## Proof summary

The proof first establishes interval integrability for
`sineDirichletKernel 1`, `sineDirichletKernel 2`, and
`cosSquareThirdDerivativeKernel` on compact positive intervals by continuity.

Then it rewrites the third-derivative kernel using the TS225 pointwise identity

```lean
cosSquareThirdDerivativeKernel x =
  (-2 : Real) * sineDirichletKernel 1 x +
    4 * sineDirichletKernel 2 x
```

and applies finite interval-integral linearity:

```lean
intervalIntegral.integral_add
intervalIntegral.integral_const_mul
```

Finally, the product cutoff filter supplies the eventual region
`0 < eps < 1 < T`, yielding the TS225 finite linearization statement.

## Non-claims

TS226 does not prove the product-filter Dirichlet cutoff values at frequencies
`1` or `2`.  It does not prove the TS219 third-derivative cutoff value
unconditionally, `cosSquareImproperIntegral = pi/6`, the canonical `sinc^4`
value, Plancherel evidence, the explicit formula, Gallagher, or Goldbach.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS226.ThirdDerivativeFiniteLinearizationDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS226
git diff --check
```

## Status

`repo_committed`
