# TS238 Audit - Abel-to-Cutoff Bridge Frontier

## Scope

TS238 records the exact state after TS237:

- `TS229.Goldbach.DampedDirichletEvaluationTarget` is proved by TS237.
- `TS229.Goldbach.DampedDirichletAbelLimitStatement` is proved by TS229.
- `TS229.Goldbach.AbelToCutoffBridgeStatement` remains the unique open
  bridge needed to obtain the ordinary cutoff value from the Abel route.

TS238 does not prove the Abel-to-cutoff bridge.  It proves the conditional
routing that supplying this bridge activates the existing TS229, TS228, TS227,
TS226, and TS225 chain.

## Main Declarations

- `AbelToCutoffBridgeFrontierStatement`
- `abelCutoffRouteEvidence_of_bridge`
- `dirichletUnitPartialIntegralAtTop_of_bridge`
- `dirichletProductCutoffUnitValue_of_bridge`
- `cosSquareThirdDerivativeCutoffValue_of_bridge`
- `AbelToCutoffBridgeFrontierLedger`
- `abelToCutoffBridgeFrontierTarget`

## What Is Proved

TS238 proves that, assuming:

```lean
TS229.Goldbach.AbelToCutoffBridgeStatement
```

one obtains:

```lean
TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement
TS227.Goldbach.DirichletProductCutoffUnitValueStatement
TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement
```

using the already proved damped evaluation from TS237 and the scalar Abel limit
from TS229.

## Non-claims

TS238 does not prove the Abel-to-cutoff bridge, the ordinary Dirichlet cutoff
value, the cos-square value, the canonical sinc-fourth value, Plancherel
evidence, the explicit formula input, Gallagher estimate, or Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS238.AbelToCutoffBridgeFrontier
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS238
git diff --check
```

## Expected Audit Result

The TS238 directory contains no placeholder proofs, no forbidden declarations,
and no non-ASCII characters.  `git diff --check` reports no whitespace errors.
