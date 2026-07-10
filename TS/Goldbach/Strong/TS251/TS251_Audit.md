# TS251 Audit - Explicit Formula Main-Term Contract Obstruction

## Scope

TS251 audits the quantifiers of the TS206 main-term identification field.  It
proves that the field is false for every TS206-admissible constants package.

## Main Declarations

- `shiftedMainTermData`
- `shiftedMainTermData_identity`
- `mainTermIdentificationStatement_not_provable`
- `coreEvidence_not_nonempty`
- `ExplicitFormulaIdentityWithMainTermStatement`
- `CorrectedTriangleSplineExplicitFormulaCoreEvidence`
- `ExplicitFormulaMainTermContractObstructionLedger`
- `explicitFormulaMainTermContractObstructionTarget`

## Obstruction

The current identity is

```text
leftSide = mainTerm - zeroContribution + residualTerm.
```

For any scale `X`, TS251 selects

```text
mainTerm        = K.mainTermModel X + 1
zeroContribution = K.mainTermModel X + 1 - leftSide X
residualTerm    = 0.
```

This data satisfies the identity, but its main term is not
`K.mainTermModel X`.  Since an admissible package has a positive lower scale,
the universal TS206 main-term statement produces a contradiction at that
scale.

Consequently, `TriangleSplineExplicitFormulaCoreEvidence K` is uninhabited for
every admissible `K`.  The TS250 constructors are correctly typed, but their
core argument cannot be supplied under the current TS206 contract.

## Corrected Target

TS251 defines `ExplicitFormulaIdentityWithMainTermStatement`, where the data
witness selected by the identity must also satisfy the main-term model.  The
corrected core contains this joint statement plus the zero and residual bounds.

The corrected target is not installed into TS206 or TS204 in this sprint.

## Non-Claims

TS251 does not prove the corrected explicit-formula identity, identify a
triangle-spline main term, or prove any zero or residual bound.  In particular,
the TS246 sinc-fourth integral does not inhabit the current TS206 universal
main-term field, whose type concerns arbitrary explicit-formula data at every
admissible scale.

TS251 does not prove Gallagher evidence, either OTSA bridge, or Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS251.ExplicitFormulaMainTermContractObstruction
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS251
git diff --check
```

## Expected Audit Result

The build succeeds.  The TS251 directory contains no placeholder proofs, no
forbidden declarations, and no non-ASCII characters.  `git diff --check`
reports no whitespace errors.
