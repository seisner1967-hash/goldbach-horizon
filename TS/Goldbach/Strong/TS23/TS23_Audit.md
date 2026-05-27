# TS23 - OTSA Scale Propagation

## Status

TS23 records how a TS22 short-interval scale enters the TS19 OTSA residual
layer.

Status: `repo_committed_relative`.

It does not prove the spectral kernel, trace, Mellin-tail, or coupling
estimates. It packages their scale-aware constants and reduces the final OTSA
residual bound to a local admissibility inequality.

## Lean Files

- `OTSAScalePropagation.lean`:
  - defines `ScaleToOTSAControl`;
  - defines `ScaledOTSAConstants`;
  - defines `ScaledOTSAAdmissible`;
  - converts scaled constants into TS19 controls;
  - proves `OTSA_residual_from_scaled_constants`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS23.OTSAScalePropagation

rg -n "s[o]rry" TS\Goldbach\Strong\TS23
rg -n "a[x]iom" TS\Goldbach\Strong\TS23
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
|----|--------|--------|---------|
| TS23-S1 | `ScaleToOTSAControl` | `analytic_infrastructure_obligation` | transports a TS22 scale into OTSA |
| TS23-S2 | `ScaledOTSAConstants` | `repo_committed` | packages scale-aware OTSA constants |
| TS23-S3 | `ScaledOTSAAdmissible` | `repo_committed` | local threshold inequality |
| TS23-S4 | `OTSA_residual_from_scaled_constants` | `repo_committed_relative` | scaled E1 plus coupling plus admissibility implies OTSA residual bound |

## Conclusion

TS23 keeps the OTSA layer honest: scale propagation is now explicit, while the
genuinely analytic ingredients remain local obligations. The key reduction is:

```text
Problem_E1Scale S K
  + ScaleToOTSAControl S
  + scaled OTSA coupling
  + ScaledOTSAAdmissible
  => OTSAResidualBound
```
