# TS236 Audit - Auxiliary Damping Uniform Bound Discharge

## Scope

TS236 discharges `TS232.Goldbach.AuxiliaryDampingUniformBoundStatement`.

It proves that for `0 < A` and `0 <= T`,

```lean
|TS232.Goldbach.dampedPartialIntegral A T| <= (1 : Real) / A
```

This is the final analytic sub-obligation isolated by TS232 before the
corrected Fubini execution can be assembled.

## Proof Strategy

The proof is elementary and finite.

1. Use the TS228 bound `|D_1(x)| <= 1` to dominate the damped Dirichlet kernel:

```lean
norm (TS229.Goldbach.dampedDirichletKernel A x) <= Real.exp ((-A) * x)
```

2. Evaluate the finite exponential majorant integral:

```lean
int_0^T exp((-A) * x) dx = (1 - exp((-A) * T)) / A
```

3. For `0 < A` and `0 <= T`, use `exp((-A) * T) <= 1` to obtain:

```lean
int_0^T exp((-A) * x) dx <= 1 / A
```

4. Combine this with `intervalIntegral.norm_integral_le_of_norm_le`.

No improper limit, Fubini argument, dominated convergence theorem, or
Abel-to-cutoff bridge is used in TS236.

## Main Declarations

- `dampingMajorantIntegral_eq`
- `dampingMajorantIntegral_le_inv`
- `dampedDirichletKernel_norm_le_exp`
- `dampedPartialIntegral_abs_le_majorant`
- `auxiliaryDampingUniformBound`
- `AuxiliaryDampingUniformBoundDischargeLedger`
- `auxiliaryDampingUniformBoundDischargeTarget`

## Non-claims

TS236 does not prove `TS232.Goldbach.CorrectedFubiniExecutionStatement`.
TS236 does not prove `TS229.Goldbach.DampedDirichletEvaluationTarget`.
TS236 does not prove any Abel-to-cutoff bridge, Dirichlet cutoff value,
cos-square value, canonical sinc-fourth value, Plancherel evidence, explicit
formula input, Gallagher estimate, or Goldbach statement.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS236.AuxiliaryDampingUniformBoundDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS236
git diff --check
```

## Expected Audit Result

The TS236 directory contains no placeholder proofs, no forbidden declarations,
and no non-ASCII characters. `git diff --check` reports no whitespace errors.
