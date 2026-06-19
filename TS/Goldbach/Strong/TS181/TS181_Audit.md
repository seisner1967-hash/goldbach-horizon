# TS181 Audit - Explicit Formula Trace Blueprint

## Scope

TS181 opens the TS95 explicit-formula front after the TS180 triangle-spline
kernel evidence ledger.

This sprint does not prove Plancherel, does not construct a concrete zeta-zero
family, and does not prove the Riemann-von Mangoldt explicit formula.  It names
the local contracts needed to consume the TS180 kernel evidence as a concrete
TS95 explicit-formula bridge.

## Main file

```text
TS/Goldbach/Strong/TS181/ExplicitFormulaTraceBlueprint.lean
```

## Main declarations

```lean
TS181.Goldbach.ExplicitFormulaTraceBlueprintStatus
TS181.Goldbach.TriangleSplineExplicitFormulaContracts
TS181.Goldbach.explicitFormulaTraceBridgeLedger_of_contracts
TS181.Goldbach.explicitFormulaTraceBridgeTarget_of_contracts
TS181.Goldbach.explicitFormulaTraceBridgeLedgerTarget_of_contracts
TS181.Goldbach.zetaZeroFamilyLedgerTarget_of_contracts
TS181.Goldbach.traceKernelSpectralDataLedgerTarget_of_ts180
TS181.Goldbach.TriangleSplineExplicitFormulaTraceBlueprintLedger
TS181.Goldbach.triangleSplineExplicitFormulaTraceBlueprintLedger
TS181.Goldbach.TriangleSplineExplicitFormulaTraceBlueprintTarget
TS181.Goldbach.triangleSplineExplicitFormulaTraceBlueprintTarget
```

## What is proved

TS181 proves wiring facts:

- a supplied `TriangleSplineExplicitFormulaContracts` package and TS180
  kernel evidence build a concrete `TS95.ExplicitFormulaTraceBridgeLedger`;
- the same supplied contracts give the TS95 bridge target;
- the contracts expose the TS93 zero-family target;
- the TS180 evidence exposes the TS94 kernel-data ledger target.

## Local contracts named

`TriangleSplineExplicitFormulaContracts` contains:

- a TS93 zeta-zero family ledger;
- a TS95 nontrivial-zero trace contribution;
- TS95 residual terms;
- a rational trace budget with positivity and `<= 1 / 2`;
- the three TS95 readiness markers;
- the budget inequality controlling zero contribution plus residuals.

## Non-claims

TS181 does not prove:

- unconditional Plancherel;
- construction of the zeta-zero family;
- zeta-zero summability;
- the Riemann-von Mangoldt explicit formula;
- any Goldbach conclusion.

## Verification commands

```powershell
lake env lean TS\Goldbach\Strong\TS181\ExplicitFormulaTraceBlueprint.lean
lake build TS.Goldbach.Strong.TS181.ExplicitFormulaTraceBlueprint
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS181
git diff --check
git status --short
```

Expected result: build succeeds, no forbidden proof placeholders, no forbidden
declaration placeholders, no non-ASCII characters, and no whitespace errors.
