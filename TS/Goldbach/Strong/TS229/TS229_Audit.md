# TS229 Audit - Dirichlet Exponential Regularization Setup

## Scope

TS229 prepares the Abel regularization route for the final TS228 one-variable
Dirichlet cutoff target.

It defines the exponentially damped unit-frequency Dirichlet kernel and records
the two remaining Abel-route inputs:

- the damped integral evaluation for positive damping;
- the Abel-to-cutoff bridge from damped convergence to ordinary cutoff
  convergence.

TS229 also proves the elementary scalar Abel limit

```text
pi/2 - arctan b -> pi/2 as b -> 0+.
```

## Main declarations

- `dampedDirichletKernel`
- `DampedDirichletIntegralStatement`
- `DampedDirichletEvaluationTarget`
- `DampedDirichletAbelLimitStatement`
- `dampedDirichletAbelLimit`
- `AbelToCutoffBridgeStatement`
- `DirichletAbelCutoffRouteEvidence`
- `dirichletUnitPartialIntegralAtTop_of_abelEvidence`
- `dirichletProductCutoffUnitValue_of_abelEvidence`
- `cosSquareThirdDerivativeCutoffValue_of_abelEvidence`
- `DirichletExponentialRegularizationSetupLedger`
- `dirichletExponentialRegularizationSetupTarget`

## What is proved

TS229 proves that the scalar Abel expression tends to the expected value:

```text
Tendsto (fun b => pi/2 - arctan b) (nhdsWithin 0 (Ioi 0)) (nhds (pi/2)).
```

It also proves the purely logical routing:

```text
DirichletAbelCutoffRouteEvidence
  -> TS228 DirichletUnitPartialIntegralAtTopStatement
  -> TS227 DirichletProductCutoffUnitValueStatement
  -> TS219 CosSquareThirdDerivativeCutoffValueStatement.
```

The last implication uses the already proved TS228, TS227, TS226, and TS225
bridges.

## Non-claims

TS229 does not prove the damped integral evaluation.

TS229 does not prove the Abel-to-cutoff bridge, the TS228 atTop Dirichlet
cutoff value, the TS227 unit product-filter value unconditionally, the TS219
third-derivative cutoff value unconditionally, `cosSquareImproperIntegral =
pi/6`, the canonical `sinc^4` value `2*pi/3`, Plancherel evidence, the explicit
formula, Gallagher, or Goldbach.

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS229.DirichletExponentialRegularizationSetup
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS229
git diff --check
```

## Expected result

The build succeeds.  The scan finds no `s[o]rry`, no `a[x]iom`, and no
non-ASCII characters in TS229.  `git diff --check` reports no whitespace
errors.
