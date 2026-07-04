# TS230 Audit - Damped Dirichlet Evaluation Reduction

## Scope

TS230 refines the Abel route introduced in TS229.  It does not prove the full
damped Dirichlet evaluation.  Instead, it proves the scalar arctangent tail and
isolates the remaining analytic obligations needed to evaluate the damped
Dirichlet integral.

The sprint is deliberately fail-closed: the Laplace sine transform and the
Fubini/arctangent bridge remain explicit inputs.

## Main declarations

- `laplaceSineKernel`
- `laplaceSinePartialIntegral`
- `LaplaceSineTransformStatement`
- `ArctanTailEvaluationStatement`
- `DampedDirichletFubiniBridgeStatement`
- `arctan_intervalIntegral_inv_one_add_sq`
- `arctanTailEvaluation`
- `DampedDirichletEvaluationReductionEvidence`
- `dampedDirichletEvaluation_of_reductionInputs`
- `dampedDirichletEvaluationReductionTarget`

## What is proved

TS230 proves the scalar arctangent tail:

```text
Tendsto
  (fun A => intervalIntegral (fun s => 1 / (1 + s^2)) b A volume)
  atTop
  (nhds (pi/2 - arctan b))
```

for every `b > 0`.  This uses Mathlib's interval-integral evaluation of
`1 / (1 + s^2)` and the atTop limit of `arctan`.

TS230 also proves the logical reduction:

```text
LaplaceSineTransformStatement
  -> DampedDirichletFubiniBridgeStatement
  -> TS229.DampedDirichletEvaluationTarget.
```

Thus the damped Dirichlet evaluation is now reduced to two named analytic
inputs: the Laplace sine transform and the Fubini/arctangent bridge.

## Non-claims

TS230 does not prove the Laplace sine transform.

TS230 does not prove the Fubini/arctangent bridge, the damped Dirichlet
evaluation target, the Abel-to-cutoff bridge, the TS228 atTop Dirichlet cutoff
value, the TS227 unit product-filter value unconditionally, the TS219
third-derivative cutoff value unconditionally, `cosSquareImproperIntegral =
pi/6`, the canonical `sinc^4` value `2*pi/3`, Plancherel evidence, the explicit
formula, Gallagher, or Goldbach.

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS230.DampedDirichletEvaluationReduction
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS230
git diff --check
```

## Expected result

The build succeeds.  The scan finds no `s[o]rry`, no `a[x]iom`, and no
non-ASCII characters in TS230.  `git diff --check` reports no whitespace
errors.
