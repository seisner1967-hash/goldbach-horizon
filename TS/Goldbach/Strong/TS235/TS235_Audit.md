# TS235 Audit - Damped Difference AtTop Discharge

## Scope

TS235 discharges the third analytic obligation isolated by TS232:

```lean
TS232.Goldbach.DampedDifferenceAtTopStatement
```

It proves that, for `0 < b < A`,

```lean
Tendsto
  (fun T : Real =>
    TS232.Goldbach.dampedPartialIntegral b T -
      TS232.Goldbach.dampedPartialIntegral A T)
  atTop
  (nhds (Real.arctan A - Real.arctan b))
```

## Proof strategy

TS235 avoids re-proving any uniform convergence estimate.  The proof uses the
already discharged inputs:

- TS231: the exact finite Laplace sine formula with boundary term;
- TS230: the interval integral of `1 / (1 + s^2)` is an arctangent difference;
- TS234: the integrated boundary term tends to zero;
- TS233: the compact Fubini identity, eventually on `atTop` where `0 <= T`.

The central decomposition is:

```lean
int_b^A laplaceSinePartialIntegral s T ds =
  (arctan A - arctan b) -
    int_b^A laplaceBoundaryTerm s T ds
```

Taking `T -> +infty` and using TS234 gives the parameter-integral limit.  Then
TS233 rewrites the damped difference to that parameter integral eventually.

## Main declarations

- `laplaceBoundaryTerm`
- `laplaceParameterIntegral_eq_arctan_sub_boundary`
- `dampedDifferenceAtTop`
- `DampedDifferenceAtTopDischargeLedger`
- `dampedDifferenceAtTopDischargeTarget`

## Non-claims

TS235 does not prove `TS232.Goldbach.AuxiliaryDampingUniformBoundStatement`.

TS235 does not prove `TS232.Goldbach.CorrectedFubiniExecutionStatement`.

TS235 does not prove `TS229.Goldbach.DampedDirichletEvaluationTarget`.

TS235 does not prove any Abel-to-cutoff bridge, Dirichlet cutoff value,
cos-square value, canonical sinc-fourth value, Plancherel evidence, explicit
formula input, Gallagher estimate, or Goldbach statement.

## Verification commands

```powershell
lake build TS.Goldbach.Strong.TS235.DampedDifferenceAtTopDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS235
git diff --check
```

## Expected audit result

The TS235 directory contains no placeholder proofs, no forbidden declarations,
and no non-ASCII characters.  `git diff --check` reports no whitespace errors.
