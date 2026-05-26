# TS19 - OTSA Residual Discharge

## Status

TS19 promotes the OTSA residual estimate from `local_obligation_compiled`
to `repo_committed_relative`.

It does not prove the spectral-kernel, trace, pole, or Mellin-tail estimates.
Instead, those ingredients are isolated as explicit local structures.

## Lean Files

- `OTSAResidualFunctional.lean`
  - defines `OTSAResidualFunctional`;
  - defines `OTSAResidualBound`.
- `KernelSpectralControl.lean`
  - defines `KernelSpectralControl` and the constant `Ck`.
- `TraceContributionControl.lean`
  - defines `TraceContributionControl` and the constant `Ct`.
- `MellinTailDecay.lean`
  - defines `MellinTailDecay` and the constant `Cm`.
- `OTSAResidualDischarge.lean`
  - defines `coupledConstant = Ck * Ct + Cm`;
  - proves `coupledConstant_nonneg`;
  - defines `OTSACouplingHypothesis`;
  - proves `otsa_residual_bound_26`.

## Ledger

| ID | Object | Previous Status | TS19 Status | Comment |
| --- | --- | --- | --- | --- |
| TS19-G41 | `OTSAResidualBound` | `local_obligation_compiled` | `repo_committed_relative` | proved relative to three controls plus local coupling |
| TS19-K1 | `KernelSpectralControl` | absent | `analytic_infrastructure_obligation` | spectral kernel constant |
| TS19-T1 | `TraceContributionControl` | absent | `analytic_infrastructure_obligation` | trace and pole constant |
| TS19-M1 | `MellinTailDecay` | absent | `analytic_infrastructure_obligation` | Mellin-tail constant |
| TS19-C1 | `OTSACouplingHypothesis` | absent | `analytic_infrastructure_obligation` | residual coupling estimate |

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS19.OTSAResidualFunctional `
  TS.Goldbach.Strong.TS19.KernelSpectralControl `
  TS.Goldbach.Strong.TS19.TraceContributionControl `
  TS.Goldbach.Strong.TS19.MellinTailDecay `
  TS.Goldbach.Strong.TS19.OTSAResidualDischarge

rg -n "s[o]rry" TS\Goldbach\Strong\TS19
rg -n "a[x]iom" TS\Goldbach\Strong\TS19
```

Expected result:

```text
0 unresolved placeholders
0 global assumptions
```

## Conclusion

After TS19, the OTSA residual estimate is decomposed as:

```text
residual <= (Ck * Ct + Cm) * scale
```

and, if `Ck * Ct + Cm <= 26`, then:

```text
residual <= 26 * scale
```

The constant 26 is now an explicit threshold condition, not a hidden constant.
