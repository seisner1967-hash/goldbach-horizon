# TS252 Audit - Corrected Explicit Formula Contract Installation

## Scope

TS252 installs a corrected explicit-formula contract beside the obstructed
TS206 family.  Historical modules are not modified.

## Main Declarations

- `correctedExplicitFormulaEffectiveContract`
- `corrected_identity_eq_mainTerm_slot`
- `CorrectedExplicitFormulaEffectiveEvidence`
- `correctedExplicitFormulaEvidence_of_core`
- `correctedExplicitFormulaEvidence_of_analyticCore`
- `correctedFinalAnalyticContracts`
- `finalAnalyticEvidence_of_correctedCoreGallagher`
- `finalAnalyticEvidence_of_analyticCoreGallagher`
- `CorrectedExplicitFormulaContractInstallationLedger`
- `correctedExplicitFormulaContractInstallationTarget`

## Corrected Contract

The corrected TS204 contract uses

```lean
TS251.Goldbach.ExplicitFormulaIdentityWithMainTermStatement K
```

for both its identity and main-term slots.  The two fields therefore refer to
the same existential data witness and are definitionally equal.

The zero and residual bound fields retain the TS206 statement shapes.
Constants admissibility and structural TS181 compatibility are supplied by
TS249 and TS250 in the specialized constructor.

## TS204 and TS248 Integration

TS252 uses `TS248.finalAnalyticContractsWithWallOne` directly with the corrected
contract.  It does not attempt to convert corrected evidence into evidence for
the impossible historical TS206 contract.

Supplying corrected core evidence and Gallagher evidence now constructs
`FinalTriangleSplineAnalyticInputEvidence` with concrete Wall 1 evidence.

## Non-Claims

TS252 does not modify TS206, prove the corrected joint identity, prove either
analytic bound, or establish an effective TS206-to-TS181 alignment.  It does
not construct the actual zeta-zero family, prove Gallagher evidence, either
OTSA bridge, or Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS252.CorrectedExplicitFormulaContractInstallation
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS252
git diff --check
```

## Expected Audit Result

The build succeeds.  The TS252 directory contains no placeholder proofs, no
forbidden declarations, and no non-ASCII characters.  `git diff --check`
reports no whitespace errors.
