# TS225 Audit - Third-Derivative Cutoff Value Reduction

## Scope

TS225 reduces the TS219 third-derivative cutoff value to product-filter
Dirichlet cutoff values at frequencies `1` and `2`.

The TS219 residual kernel is

```text
(-2 * sin x + 4 * sin (2*x)) / x
```

so the expected cutoff value is the Dirichlet combination

```text
-2 * (pi / 2) + 4 * (pi / 2) = pi.
```

TS225 proves this combination as a Lean `Tendsto` consequence of the two
frequency cutoffs.  It also records the finite-integral linearization needed to
identify the TS219 residual integral with the combined Dirichlet expression.
That linearization remains an explicit future obligation; no convergence proof
is hidden in the reduction.

## Main declarations

- `TS225.Goldbach.dirichletProductCutoffIntegral`
- `TS225.Goldbach.DirichletProductCutoffValueStatement`
- `TS225.Goldbach.ThirdDerivativeDirichletProductCutoffEvidence`
- `TS225.Goldbach.cosSquareThirdDerivativeKernel_eq_dirichletCombination`
- `TS225.Goldbach.thirdDerivativeDirichletCombination`
- `TS225.Goldbach.thirdDerivativeDirichletCombination_tendsto`
- `TS225.Goldbach.ThirdDerivativeCutoffLinearizationStatement`
- `TS225.Goldbach.cosSquareThirdDerivativeCutoffValue_of_dirichletProductCutoffs`
- `TS225.Goldbach.ThirdDerivativeCutoffValueReductionEvidence`
- `TS225.Goldbach.cosSquareThirdDerivativeCutoffValue_of_reductionEvidence`
- `TS225.Goldbach.ThirdDerivativeCutoffValueReductionLedger`
- `TS225.Goldbach.thirdDerivativeCutoffValueReductionLedger`
- `TS225.Goldbach.ThirdDerivativeCutoffValueReductionTarget`
- `TS225.Goldbach.thirdDerivativeCutoffValueReductionTarget`

## Proof summary

The pointwise kernel identity is discharged by unfolding the TS213 definitions
and normalizing the ring expression:

```lean
TS213.Goldbach.cosSquareThirdDerivativeKernel x =
  (-2 : Real) * TS213.Goldbach.sineDirichletKernel 1 x +
    4 * TS213.Goldbach.sineDirichletKernel 2 x
```

The main reduction theorem takes evidence that the product-filter cutoff
Dirichlet integrals at frequencies `1` and `2` both tend to `pi / 2`.  Applying
`Tendsto.const_mul` and `Tendsto.add` gives the combined limit, and a final
ring normalization proves that the target value is `pi`.

The bridge to `TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement`
requires the finite linearization statement:

```lean
ThirdDerivativeCutoffLinearizationStatement
```

This keeps the finite interval-integral algebra separate from the analytic
Dirichlet convergence inputs.

## Non-claims

TS225 does not prove the finite linearization statement.  It does not prove
Dirichlet cutoff convergence or Abel convergence.  It does not prove
`cosSquareImproperIntegral = pi/6`, the canonical `sinc^4` value, Plancherel
evidence, the explicit formula, Gallagher, or Goldbach.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS225.ThirdDerivativeCutoffValueReduction
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS225
git diff --check
```

## Status

`repo_committed_relative`
