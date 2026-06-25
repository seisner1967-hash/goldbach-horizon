# TS206 Audit - Explicit Formula Effective Statement

## Scope

TS206 makes the Wall 2 effective explicit-formula target concrete for the
triangle-spline von Mangoldt weight.  It uses the existing TS184 smoothed von
Mangoldt sum as the left-hand side and defines right-hand data consisting of a
main term, a nontrivial-zero contribution, and a residual term.

The sprint also defines an effective constants package and a contract family
which instantiates the TS204
`TriangleSplineExplicitFormulaEffectiveInputContract`.

## Main Declarations

- `TS206.Goldbach.TriangleSplineExplicitFormulaData`
- `TS206.Goldbach.TriangleSplineExplicitFormulaConstants`
- `TS206.Goldbach.triangleSplineExplicitFormulaLeftSide`
- `TS206.Goldbach.triangleSplineExplicitFormulaIdentity`
- `TS206.Goldbach.triangleSplineExplicitFormulaMainTermIdentification`
- `TS206.Goldbach.triangleSplineExplicitFormulaZeroContributionBound`
- `TS206.Goldbach.triangleSplineExplicitFormulaResidualBound`
- `TS206.Goldbach.triangleSplineExplicitFormulaConstantsAdmissible`
- `TS206.Goldbach.TriangleSplineExplicitFormulaTS181CompatibilityStatement`
- `TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract`
- `TS206.Goldbach.ExplicitFormulaEffectiveStatementLedger`
- `TS206.Goldbach.explicitFormulaEffectiveStatementLedger`
- `TS206.Goldbach.ExplicitFormulaEffectiveStatementTarget`
- `TS206.Goldbach.explicitFormulaEffectiveStatementTarget`

## What TS206 Proves

TS206 proves no analytic estimate.  It proves only that the concrete statement
family is well typed and can be packaged as a TS204 effective explicit-formula
contract.

The compatibility field is not filled by `True`; it is the proposition

```lean
Nonempty TS181.Goldbach.TriangleSplineExplicitFormulaContracts
```

and remains unproved.

## Non-Claims

TS206 does not prove:

- the explicit-formula identity;
- the main-term identification;
- zero-contribution bounds;
- residual bounds;
- admissibility of any constants package;
- compatibility with the TS181/TS95 blueprint;
- any TS204 evidence;
- any TS200 OTSA input;
- Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS206.ExplicitFormulaEffectiveStatement
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS206
git diff --check
git status --short
```
