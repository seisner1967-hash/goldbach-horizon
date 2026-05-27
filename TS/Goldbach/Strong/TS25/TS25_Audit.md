# TS25 - Padded Scale OTSA Feasibility

## Status

TS25 specializes the TS23 OTSA scale-propagation layer to the padded
closed-form Brun-Titchmarsh scale constructed in TS24.

Status: `repo_committed_relative`.

It does not prove Brun-Titchmarsh, OTSA spectral estimates, or the final
Goldbach theorem. It records the exact local infrastructure needed for the
padded scale to enter the OTSA residual layer.

## Lean Files

- `PaddedScaleOTSAFeasibility.lean`:
  - defines `PaddedScaleAnalyticInfrastructure`;
  - proves `Problem_E1Scale_from_padded_infrastructure`;
  - exposes `OTSA_viability_from_padded_scale`;
  - proves `OTSA_residual_from_padded_scale` relative to the local OTSA
    coupling estimate.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS25.PaddedScaleOTSAFeasibility

rg -n "s[o]rry" TS\Goldbach\Strong\TS25
rg -n "a[x]iom" TS\Goldbach\Strong\TS25
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
|----|--------|--------|---------|
| TS25-P1 | `PaddedScaleAnalyticInfrastructure` | `analytic_infrastructure_obligation` | packages interval BT, scale transfer, constants, and admissibility |
| TS25-P2 | `Problem_E1Scale_from_padded_infrastructure` | `repo_committed_relative` | padded BT scale gives scaled E1 |
| TS25-P3 | `OTSA_viability_from_padded_scale` | `repo_committed_relative` | exposes scaled OTSA admissibility |
| TS25-P4 | `OTSA_residual_from_padded_scale` | `repo_committed_relative` | padded scaled E1 plus local OTSA coupling implies residual bound |

## Conclusion

TS25 provides the single padded-scale entry point for future OTSA numerical and
analytic certificates:

```text
BrunTitchmarshNatIntervalBound
  + ScaleToOTSAControl brunTitchmarshPaddedClosedFormScale
  + ScaledOTSAAdmissible
  + local OTSA coupling
  => OTSAResidualBound
```
