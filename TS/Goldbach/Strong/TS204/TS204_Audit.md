# TS204 Audit - Final Analytic Inputs Specification

## Scope

TS204 starts the conditional-reduction phase by specifying the three final
analytic input families for the Horizon-Goldbach OTSA bridge:

- triangle-spline Plancherel;
- effective explicit formula for the triangle-spline weight;
- Gallagher / large-sieve comparison for the smoothed two-prime correlation.

The sprint separates contract types from evidence types.  The effective
explicit-formula and Gallagher fields are named as propositions to be populated
by future work; they are not replaced by `True`.

## Main Declarations

- `TS204.Goldbach.TriangleSplinePlancherelInputContract`
- `TS204.Goldbach.TriangleSplinePlancherelInputEvidence`
- `TS204.Goldbach.triangleSplinePlancherelInputContract`
- `TS204.Goldbach.triangleSplinePlancherelEnergyTransport_available`
- `TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputContract`
- `TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputEvidence`
- `TS204.Goldbach.TriangleSplineGallagherInputContract`
- `TS204.Goldbach.TriangleSplineGallagherInputEvidence`
- `TS204.Goldbach.FinalTriangleSplineAnalyticInputContracts`
- `TS204.Goldbach.FinalTriangleSplineAnalyticInputEvidence`
- `TS204.Goldbach.FinalAnalyticInputsSpecificationLedger`
- `TS204.Goldbach.finalAnalyticInputsSpecificationLedger`
- `TS204.Goldbach.FinalAnalyticInputsSpecificationTarget`
- `TS204.Goldbach.finalAnalyticInputsSpecificationTarget`

## What TS204 Proves

TS204 proves only routing and availability facts:

- final analytic evidence exposes its Plancherel, explicit-formula, and
  Gallagher fields;
- the concrete triangle-spline Plancherel transport statement is available
  from TS188;
- the TS203 truncated Haar transport statement is recorded as already
  available input for future Wall 0 work.

## Non-Claims

TS204 does not prove:

- the triangle-spline Plancherel isometry;
- the effective explicit formula;
- zero-contribution bounds;
- residual bounds;
- Gallagher or large-sieve comparison;
- any OTSA input slot from TS200;
- the final OTSA inequality;
- the combinatorial reduction;
- Goldbach.

TS204 also does not consume `BinaryGoldbachStatement` as an input.  Goldbach
remains an output of the TS200 non-circular interface.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS204.FinalAnalyticInputsSpecification
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS204
git diff --check
git status --short
```
