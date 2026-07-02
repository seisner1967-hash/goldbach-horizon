# TS216 Audit - Dirichlet Unit-Frequency Value Probe

## Scope

TS216 continues the TS215 Dirichlet sine integral probe by focusing on the
unit-frequency side of the TS213 scalar route.

The sprint does not prove the Dirichlet value.  It records that no ready-made
local Mathlib theorem was located for the value
`integral_0^infty sin x / x = pi / 2`, names the current TS215 Lebesgue target,
and also names two future classical formulations: cutoff-improper convergence
and Abel regularization.

## Main Declarations

- `TS216.Goldbach.DirichletUnitFrequencyProbeStatus`
- `TS216.Goldbach.DirichletUnitFrequencyLebesgueStatement`
- `TS216.Goldbach.DirichletUnitFrequencyCutoffStatement`
- `TS216.Goldbach.DirichletUnitFrequencyAbelStatement`
- `TS216.Goldbach.unitFrequencyKernel_eq_sin_div`
- `TS216.Goldbach.dirichletUnitFrequencyLebesgueStatement_eq_ts215`
- `TS216.Goldbach.dirichletSineIntegral_of_unitLebesgue_and_scaling`
- `TS216.Goldbach.DirichletUnitFrequencyValueProbeLedger`
- `TS216.Goldbach.dirichletUnitFrequencyValueProbeLedger`
- `TS216.Goldbach.DirichletUnitFrequencyValueProbeTarget`
- `TS216.Goldbach.dirichletUnitFrequencyValueProbeTarget`

## What TS216 Proves

TS216 proves the pointwise frequency-one kernel simplification:

```lean
TS213.Goldbach.sineDirichletKernel 1 x = Real.sin x / x
```

It also proves that the TS216 Lebesgue target is definitionally the TS215
unit-frequency target, and that this target plus the TS215 positive-frequency
scaling slot would still imply the TS213 Dirichlet sine integral statement.

## Non-Claims

TS216 does not prove:

- the unit-frequency Dirichlet value;
- cutoff-improper convergence;
- Abel-regularized convergence;
- positive-frequency scaling for the singular Dirichlet kernel;
- `TS213.Goldbach.DirichletSineIntegralStatement`;
- improper triple integration by parts;
- the `sinc^4` scaling or evenness identities;
- the canonical `sinc^4` value;
- Plancherel, the explicit formula, Gallagher, or Goldbach.

## Verification Commands

```text
lake env lean TS\Goldbach\Strong\TS216\DirichletUnitFrequencyValueProbe.lean
lake build TS.Goldbach.Strong.TS216.DirichletUnitFrequencyValueProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS216
git diff --check
git status --short
```

