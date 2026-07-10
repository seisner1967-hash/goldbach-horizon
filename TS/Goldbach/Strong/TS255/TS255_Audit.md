# TS255 Audit - Fully Corrected Explicit Formula Analytic Decomposition

## Scope

TS255 factors the TS253 fully corrected existential statement through two
named real functions and three concrete analytic obligations.

## Main Declarations

- `ZeroContributionFunction`
- `ResidualTermFunction`
- `decomposedExplicitFormulaData`
- `decomposedExplicitFormulaData_mainTerm`
- `NamedExplicitFormulaIdentityStatement`
- `NamedZeroContributionBoundStatement`
- `NamedResidualBoundStatement`
- `DecomposedExplicitFormulaObligations`
- `fullyCorrectedCoreEvidence_of_decomposed`
- `fullyCorrectedExplicitFormulaEvidence_of_decomposed`
- `fullyCorrectedExplicitFormulaEvidence_of_specializedDecomposed`
- `ExplicitFormulaAnalyticDecompositionLedger`
- `explicitFormulaAnalyticDecompositionTarget`

## Canonical Data

`decomposedExplicitFormulaData K zeroFn residualFn X` fixes

```text
mainTerm = K.mainTermModel X
zeroContribution = zeroFn X
residualTerm = residualFn X
```

Main-term identification is therefore definitional.

## Named Obligations

The identity and both bounds use the existing TS206 predicates on the same
canonical data.  They do not restate the formulas or majorants manually.

`DecomposedExplicitFormulaObligations K` stores the two named functions and
proofs of those three statements.  The functions cannot vary independently
between the identity and bound proofs.

## Assembly

`fullyCorrectedCoreEvidence_of_decomposed` constructs the TS253 existential
witness at each admissible scale.  The identity and two bounds come from the
named obligations; main-term identification is definitional.

The next two constructors route that core through TS254.  The specialized
version additionally supplies TS249 admissibility and TS250 structural
compatibility.

The ledger stores the actual typed core and effective-evidence assemblers, not
only `True` markers.

## Non-Claims

TS255 does not construct either named function, prove the named identity or
bounds, construct a zeta-zero sum, define contour residual terms, prove
Gallagher evidence, prove either OTSA bridge, introduce RH, or prove Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS255.FullyCorrectedExplicitFormulaAnalyticDecomposition
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS255
git diff --check
```

## Expected Audit Result

The build succeeds.  The TS255 directory contains no placeholder proofs, no
forbidden declarations, and no non-ASCII characters.  `git diff --check`
reports no whitespace errors.
