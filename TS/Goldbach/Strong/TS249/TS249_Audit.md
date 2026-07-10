# TS249 Audit - Effective Explicit Formula Constants Discharge

## Scope

TS249 discharges the effective-constants admissibility field of the TS206
triangle-spline explicit-formula contract.

The constants remain flexible: the main-term model and all powers are
arbitrary, the two nonnegative constants are supplied as `NNReal`, and the
positive lower scale is represented as an offset plus one.

## Main Declarations

- `admissibleExplicitFormulaConstants`
- `admissibleExplicitFormulaConstants_admissible`
- `TriangleSplineExplicitFormulaCoreEvidence`
- `explicitFormulaEvidence_of_core`
- `explicitFormulaEvidence_of_admissibleConstants`
- `finalAnalyticEvidence_of_coreCompatibilityGallagher`
- `EffectiveExplicitFormulaConstantsDischargeLedger`
- `effectiveExplicitFormulaConstantsDischargeTarget`

## What Is Proved

Every package built by `admissibleExplicitFormulaConstants` satisfies

```lean
TS206.Goldbach.triangleSplineExplicitFormulaConstantsAdmissible
```

without an additional proof argument.  A complete TS206 explicit-formula
evidence term can therefore be built from four core analytic fields and the
separate TS181 compatibility field.  Supplying that reduced evidence together
with Gallagher evidence constructs the TS248 final analytic evidence bundle;
the Wall 1 evidence and constants admissibility are already populated.

## Non-Claims

TS249 does not prove the explicit-formula identity, main-term identification,
zero-contribution bound, residual bound, or TS181 compatibility.  It does not
prove Gallagher evidence, either OTSA bridge, or Goldbach unconditionally.

The local Mathlib version exposes `riemannZeta` and `RiemannHypothesis`, but the
repository audit did not locate an effective explicit-formula or zero-density
theorem that would populate the remaining fields automatically.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS249.EffectiveExplicitFormulaConstantsDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS249
git diff --check
```

## Expected Audit Result

The build succeeds.  The TS249 directory contains no placeholder proofs, no
forbidden declarations, and no non-ASCII characters.  `git diff --check`
reports no whitespace errors.
