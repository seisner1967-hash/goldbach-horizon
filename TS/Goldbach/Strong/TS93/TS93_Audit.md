# TS93 - Zeta Zero Family Ledger

## Status

`repo_committed_relative`

TS93 refines the `ZetaZeroFamily` component introduced in TS92. It does not
prove any theorem about the Riemann zeta function and does not select a
concrete Mathlib zeta-zero API. Instead, it records the local zero-family facts
that a future explicit-formula trace proof must provide.

## Lean artifacts

File:

```text
TS/Goldbach/Strong/TS93/ZetaZeroFamilyLedger.lean
```

Key declarations:

```lean
TS93.Goldbach.ZetaZero
TS93.Goldbach.ZetaZero.symmetry
TS93.Goldbach.ZetaZero.multiplicity
TS93.Goldbach.ZetaZeroFamilyLedger
TS93.Goldbach.ZetaZeroFamilyLedgerRoadmap
TS93.Goldbach.zetaZeroFamilyLedgerRoadmap
TS93.Goldbach.zetaZeroFamily_of_ledger
TS93.Goldbach.ZetaZeroFamilyLedgerRoadmapTarget
TS93.Goldbach.ZetaZeroFamilyLedgerTarget
TS93.Goldbach.ZetaZeroFamilyTarget
TS93.Goldbach.zetaZeroFamilyLedgerRoadmapTarget
TS93.Goldbach.zetaZeroFamilyTarget_of_ledgerTarget
```

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS93.ZetaZeroFamilyLedger

rg -n "s[o]rry" TS\Goldbach\Strong\TS93
rg -n "a[x]iom" TS\Goldbach\Strong\TS93
```

Expected result:

```text
no forbidden placeholder matches
```

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS93-Z1 | `ZetaZero` | `repo_committed_relative` | wrapper for complex zero candidates |
| TS93-Z2 | `ZetaZero.symmetry` | `repo_committed_relative` | records the functional-equation partner `rho -> 1 - rho` |
| TS93-Z3 | `ZetaZeroFamilyLedger` | `analytic_infrastructure_obligation` | zero set, multiplicity, strip, conjugation, and symmetry obligations |
| TS93-R1 | `ZetaZeroFamilyLedgerRoadmap` | `repo_committed_relative` | status ledger for the zero-family front |
| TS93-P1 | `zetaZeroFamilyTarget_of_ledgerTarget` | `repo_committed_relative` | a concrete zero-family ledger supplies the TS92 zero-family marker |

## Summary

TS93 names the zeta-zero vocabulary needed by the future `Ct <= 1/2` trace
estimate while keeping the analytic theorem itself external and explicit.
