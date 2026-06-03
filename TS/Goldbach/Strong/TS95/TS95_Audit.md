# TS95 - Explicit Formula Trace Bridge Ledger

## Status

`repo_committed_relative`

TS95 refines the `ExplicitFormulaTraceBridge` component introduced in TS92. It
does not prove the Riemann-von Mangoldt explicit formula and does not prove the
spectral trace estimate. Instead, it records the local analytic contract tying
the TS93 zero-family ledger and the TS94 trace-kernel ledger to a rational trace
budget.

## Lean artifacts

File:

```text
TS/Goldbach/Strong/TS95/ExplicitFormulaTraceBridgeLedger.lean
```

Key declarations:

```lean
TS95.Goldbach.NontrivialZeroTraceContribution
TS95.Goldbach.ExplicitFormulaResidualTerms
TS95.Goldbach.ExplicitFormulaResidualTerms.total
TS95.Goldbach.ExplicitFormulaTraceBridgeLedger
TS95.Goldbach.ExplicitFormulaTraceBridgeRoadmap
TS95.Goldbach.explicitFormulaTraceBridgeRoadmap
TS95.Goldbach.explicitFormulaTraceBridge_of_ledger
TS95.Goldbach.ExplicitFormulaTraceBridgeRoadmapTarget
TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget
TS95.Goldbach.ExplicitFormulaTraceBridgeTarget
TS95.Goldbach.explicitFormulaTraceBridgeRoadmapTarget
TS95.Goldbach.explicitFormulaTraceBridgeTarget_of_ledgerTarget
TS95.Goldbach.zetaZeroFamilyLedgerTarget_of_explicitFormulaTraceBridgeLedgerTarget
TS95.Goldbach.traceKernelSpectralDataLedgerTarget_of_explicitFormulaTraceBridgeLedgerTarget
```

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS95.ExplicitFormulaTraceBridgeLedger

rg -n "s[o]rry" TS\Goldbach\Strong\TS95
rg -n "a[x]iom" TS\Goldbach\Strong\TS95
```

Expected result:

```text
no forbidden placeholder matches
```

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS95-Z1 | `NontrivialZeroTraceContribution` | `analytic_infrastructure_obligation` | rational contribution of the non-trivial zeta zeros |
| TS95-R1 | `ExplicitFormulaResidualTerms` | `analytic_infrastructure_obligation` | pole, trivial-zero, and contour/error residual budgets |
| TS95-C1 | `ExplicitFormulaTraceBridgeLedger` | `analytic_infrastructure_obligation` | explicit-formula comparison, zero-sum bridge, residual control, and rational trace budget |
| TS95-R2 | `ExplicitFormulaTraceBridgeRoadmap` | `repo_committed_relative` | status ledger for the explicit-formula bridge front |
| TS95-P1 | `explicitFormulaTraceBridgeTarget_of_ledgerTarget` | `repo_committed_relative` | a concrete explicit-formula ledger supplies the TS92 bridge marker |
| TS95-P2 | `zetaZeroFamilyLedgerTarget_of_explicitFormulaTraceBridgeLedgerTarget` | `repo_committed_relative` | the explicit-formula ledger carries the TS93 zero-family ledger |
| TS95-P3 | `traceKernelSpectralDataLedgerTarget_of_explicitFormulaTraceBridgeLedgerTarget` | `repo_committed_relative` | the explicit-formula ledger carries the TS94 kernel-data ledger |

## Summary

TS95 names the explicit-formula bridge needed by the future `Ct <= 1/2` trace
estimate while keeping the analytic theorem itself external and explicit.
