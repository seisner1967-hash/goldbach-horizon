# TS237 Audit - Corrected Fubini Execution Assembly

## Scope

TS237 discharges `TS232.Goldbach.CorrectedFubiniExecutionStatement`.

It also derives:

```lean
TS230.Goldbach.DampedDirichletFubiniBridgeStatement
TS229.Goldbach.DampedDirichletEvaluationTarget
```

from the four TS232 sub-obligations discharged in TS233--TS236 and the TS231
Laplace sine transform.

## Proof Strategy

The central theorem is:

```lean
dampedEvaluationTarget_of_difference_and_auxiliaryBound
```

For a fixed `b > 0`, it proves the damped partial-integral limit by:

1. choosing `A` large enough so that
   `arctan A - arctan b` is close to `pi / 2 - arctan b`;
2. choosing `A` large enough so that `1 / A` is small;
3. using TS235 to make
   `dampedPartialIntegral b T - dampedPartialIntegral A T`
   close to `arctan A - arctan b` for large `T`;
4. using TS236 to bound `|dampedPartialIntegral A T| <= 1 / A`;
5. combining the three errors by the triangle inequality.

Thus TS237 is an assembly and limiting-connective sprint. It introduces no new
integral calculation, Fubini theorem, or compact analytic estimate.

## Main Declarations

- `arctanDifference_atTop`
- `one_div_atTop_zero`
- `dampedEvaluationTarget_of_difference_and_auxiliaryBound`
- `correctedFubiniExecution`
- `dampedDirichletFubiniBridge`
- `dampedDirichletEvaluationTarget`
- `CorrectedFubiniExecutionAssemblyLedger`
- `correctedFubiniExecutionAssemblyTarget`

## Non-claims

TS237 does not prove any Abel-to-cutoff bridge, ordinary Dirichlet cutoff
value, cos-square value, canonical sinc-fourth value, Plancherel evidence,
explicit formula input, Gallagher estimate, or Goldbach statement.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS237.CorrectedFubiniExecutionAssembly
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS237
git diff --check
```

## Expected Audit Result

The TS237 directory contains no placeholder proofs, no forbidden declarations,
and no non-ASCII characters. `git diff --check` reports no whitespace errors.
