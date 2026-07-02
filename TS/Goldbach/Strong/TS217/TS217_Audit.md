# TS217 Audit - Dirichlet Improper Reformulation Bridge

## Scope

TS217 corrects the status of the Dirichlet sine integral route after TS215 and
TS216.  The old unit-frequency Lebesgue statement is retained as a legacy
target, but it is no longer treated as the final analytic route.  The future
targets are cutoff-improper convergence and Abel regularization.

The sprint defines evidence wrappers for both corrected routes and proves that
either wrapper supplies the corrected TS217 target.  It does not prove either
route.

## Main Declarations

- `TS217.Goldbach.DirichletImproperReformulationStatus`
- `TS217.Goldbach.LegacyDirichletUnitFrequencyLebesgueStatement`
- `TS217.Goldbach.DirichletUnitFrequencyCutoffTarget`
- `TS217.Goldbach.DirichletUnitFrequencyAbelTarget`
- `TS217.Goldbach.DirichletPositiveFrequencyCutoffStatement`
- `TS217.Goldbach.DirichletPositiveFrequencyAbelStatement`
- `TS217.Goldbach.DirichletCutoffEvidence`
- `TS217.Goldbach.DirichletAbelEvidence`
- `TS217.Goldbach.DirichletImproperRouteEvidence`
- `TS217.Goldbach.CorrectedDirichletSineIntegralTarget`
- `TS217.Goldbach.correctedDirichletTarget_of_cutoffEvidence`
- `TS217.Goldbach.correctedDirichletTarget_of_abelEvidence`
- `TS217.Goldbach.DirichletImproperReformulationLedger`
- `TS217.Goldbach.dirichletImproperReformulationLedger`
- `TS217.Goldbach.DirichletImproperReformulationTarget`
- `TS217.Goldbach.dirichletImproperReformulationTarget`

## What TS217 Proves

TS217 proves only routing facts:

```lean
DirichletCutoffEvidence -> CorrectedDirichletSineIntegralTarget
DirichletAbelEvidence -> CorrectedDirichletSineIntegralTarget
```

It also records definitional equalities connecting the TS217 unit-frequency
targets to the TS216 cutoff, Abel, and legacy Lebesgue statements.

## Non-Claims

TS217 does not prove:

- non-integrability of the old Lebesgue target;
- the Dirichlet sine integral value;
- cutoff convergence;
- Abel convergence;
- the old TS213 Lebesgue Dirichlet statement;
- improper triple integration by parts;
- the `sinc^4` scaling or evenness identities;
- the canonical `sinc^4` value;
- Plancherel, the explicit formula, Gallagher, or Goldbach.

## Verification Commands

```text
lake env lean TS\Goldbach\Strong\TS217\DirichletImproperReformulationBridge.lean
lake build TS.Goldbach.Strong.TS217.DirichletImproperReformulationBridge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS217
git diff --check
git status --short
```

