# TS232 Audit - Damped Dirichlet Fubini Bridge Reduction

## Scope

TS232 records the corrected interval-integral route for the remaining
Fubini/arctangent bridge after TS231 proved the Laplace sine transform input.

The sprint is deliberately fail-closed.  It does not prove the compact Fubini
identity, the uniform Laplace-boundary limit, the auxiliary high-damping bound,
the damped Dirichlet evaluation target, or the Abel-to-cutoff bridge.

## Main declarations

- `dampedPartialIntegral`
- `DampedPartialIntegralAtTopStatement`
- `dampedPartialIntegralAtTopStatement_eq_ts229`
- `DampedDirichletFubiniEvaluationStatement`
- `dampedDirichletFubiniEvaluationStatement_eq_ts229`
- `CompactFubiniIdentityStatement`
- `LaplaceBoundaryUniformLimitStatement`
- `DampedDifferenceAtTopStatement`
- `AuxiliaryDampingUniformBoundStatement`
- `CorrectedFubiniExecutionStatement`
- `dampedDirichletFubiniBridge_of_evaluation`
- `dampedDirichletEvaluation_of_ts231_and_fubiniBridge`
- `DampedDirichletFubiniBridgeReductionLedger`
- `dampedDirichletFubiniBridgeReductionTarget`

## What is proved

TS232 proves that its damped partial-integral statement is definitionally the
TS229 damped integral statement:

```text
DampedPartialIntegralAtTopStatement b value =
  TS229.Goldbach.DampedDirichletIntegralStatement b value
```

It also proves that, after TS231, a future proof of the TS230 Fubini bridge is
the only remaining input needed by the TS230 reduction:

```text
TS230.Goldbach.DampedDirichletFubiniBridgeStatement
  -> TS229.Goldbach.DampedDirichletEvaluationTarget
```

The corrected future bridge is decomposed into interval-integral obligations:

```text
CompactFubiniIdentityStatement
LaplaceBoundaryUniformLimitStatement
DampedDifferenceAtTopStatement
AuxiliaryDampingUniformBoundStatement
```

These are recorded as explicit future inputs, not silently asserted.

## Non-claims

TS232 does not prove the compact Fubini identity.

TS232 does not prove the uniform Laplace-boundary limit, the damped difference
limit, the auxiliary high-damping bound, the corrected Fubini execution
statement, the damped Dirichlet evaluation target, the Abel-to-cutoff bridge,
the TS228 atTop Dirichlet cutoff value, the TS227 unit product-filter value
unconditionally, the TS219 third-derivative cutoff value unconditionally,
`cosSquareImproperIntegral = pi/6`, the canonical `sinc^4` value `2*pi/3`,
Plancherel evidence, the explicit formula, Gallagher, or Goldbach.

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS232.DampedDirichletFubiniBridgeReduction
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS232
git diff --check
```

## Expected result

The build succeeds.  The scan finds no `s[o]rry`, no `a[x]iom`, and no
non-ASCII characters in TS232.  `git diff --check` reports no whitespace
errors.
