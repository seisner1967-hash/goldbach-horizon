# TS248 Audit - Wall One Final Analytic Input Consumption

## Scope

TS248 consumes the concrete triangle-spline Plancherel evidence assembled by
TS247 in the final TS204 analytic input package.

It reduces construction of the final analytic evidence from three supplied
evidence families to two: the effective explicit formula and Gallagher.

## Main Declarations

- `finalAnalyticContractsWithWallOne`
- `finalAnalyticEvidence_of_remainingInputs`
- `finalAnalyticContractsForEffectiveExplicitFormula`
- `finalAnalyticEvidence_of_effectiveExplicitFormulaGallagher`
- `otsaInputEvidence_of_remainingAnalyticInputs`
- `binaryGoldbach_of_remainingAnalyticInputs`
- `WallOneFinalAnalyticInputConsumptionLedger`
- `wallOneFinalAnalyticInputConsumptionTarget`

## What Is Proved

The Plancherel field of the reduced TS204 contract bundle is definitionally
the concrete triangle-spline contract populated by TS247.

Supplying evidence for the effective explicit-formula and Gallagher contracts
constructs a complete

```lean
TS204.Goldbach.FinalTriangleSplineAnalyticInputEvidence
```

with no additional Plancherel hypothesis.  Supplying the TS205 adapter then
constructs the five-slot TS200 OTSA input evidence.  Supplying the separate
TS200 conclusion bridge yields the conditional binary Goldbach output.

TS248 also specializes the construction to the concrete TS206 effective
explicit-formula contract family.

## Non-Claims

TS248 does not prove evidence for the TS206 effective explicit formula or for
the Gallagher contract.  It does not prove the TS205 analytic-to-OTSA adapter,
the TS200 conclusion bridge, or Goldbach unconditionally.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS248.WallOneFinalAnalyticInputConsumption
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS248
git diff --check
```

## Expected Audit Result

The build succeeds.  The TS248 directory contains no placeholder proofs, no
forbidden declarations, and no non-ASCII characters.  `git diff --check`
reports no whitespace errors.
