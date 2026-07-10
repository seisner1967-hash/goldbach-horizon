# TS254 Audit - Fully Corrected Explicit Formula Contract Installation

## Scope

TS254 installs the fully corrected TS253 analytic statement as a parallel
TS204 explicit-formula contract.

## Main Declarations

- `fullyCorrectedExplicitFormulaEffectiveContract`
- `fullyCorrected_identity_eq_mainTerm_slot`
- `fullyCorrected_identity_eq_zeroBound_slot`
- `fullyCorrected_identity_eq_residualBound_slot`
- `FullyCorrectedExplicitFormulaEffectiveEvidence`
- `fullyCorrectedExplicitFormulaEvidence_of_core`
- `fullyCorrectedExplicitFormulaEvidence_of_analyticCore`
- `fullyCorrectedFinalAnalyticContracts`
- `finalAnalyticEvidence_of_fullyCorrectedCoreGallagher`
- `finalAnalyticEvidence_of_analyticCoreGallagher`
- `FullyCorrectedExplicitFormulaContractInstallationLedger`
- `fullyCorrectedExplicitFormulaContractInstallationTarget`

## Contract Installation

All four analytic slots of
`fullyCorrectedExplicitFormulaEffectiveContract K` are definitionally equal to
`TS253.Goldbach.FullyCorrectedExplicitFormulaStatement K`.

The slots are not replaced by `True`.  Constructing evidence requires one
proof that, at every admissible scale, a single explicit-formula data witness
satisfies identity, main-term identification, the zero-contribution bound, and
the residual bound simultaneously.

Constants admissibility keeps the TS206 proposition.  Structural TS181
compatibility keeps the proposition discharged by TS250.

## Routing

`fullyCorrectedExplicitFormulaEvidence_of_core` copies the same TS253 core
proof into all four analytic evidence fields.  The specialized constructor
also supplies TS249 admissibility and TS250 structural compatibility.

The two final constructors route this evidence and separately supplied
Gallagher evidence through the generic TS248 Wall 1 bundle.

## Historical Contracts

TS206, TS252, and all historical modules remain unchanged.  TS254 claims no
bridge from fully corrected evidence to either obstructed historical contract.

## Non-Claims

TS254 installs a type-correct analytic obligation.  It does not prove the
fully corrected explicit formula, construct an actual zeta-zero family,
introduce RH, prove Gallagher evidence, prove either OTSA bridge, or prove
Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS254.FullyCorrectedExplicitFormulaContractInstallation
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS254
git diff --check
```

## Expected Audit Result

The build succeeds.  The TS254 directory contains no placeholder proofs, no
forbidden declarations, and no non-ASCII characters.  `git diff --check`
reports no whitespace errors.
