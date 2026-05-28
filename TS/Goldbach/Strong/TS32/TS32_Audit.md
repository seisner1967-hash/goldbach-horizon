# TS32 - OTSA Trace Majorant Roadmap

## Status

TS32 introduces a conditional trace-majorant interface for the OTSA constant
ledger.

Status: `repo_committed_relative`.

TS32 does not prove the trace contribution bound, the spectral estimate, the
Mellin-tail bound, the scale-transfer bound, OTSA, or Goldbach. It records that
if a future trace analysis supplies a rational bound `Ct <= 1/2`, then the
candidate-v2 OTSA rational certificate is admissible.

## Lean Files

- `OTSATraceMajorantRoadmap.lean`:
  - defines `TraceMajorantContract`;
  - defines the target value `Ct_target_v2 = 1/2`;
  - proves the target scaled value `103/100`;
  - proves admissibility for any contracted `Ct <= 1/2`;
  - defines `OTSACert_candidate_v2`;
  - defines `OTSARegister_candidate_v2`;
  - defines `OTSAProvenance_candidate_v2`;
  - proves `candidate_v2_scaledOTSAAdmissible`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS32.OTSATraceMajorantRoadmap

rg -n "s[o]rry" TS\Goldbach\Strong\TS32
rg -n "a[x]iom" TS\Goldbach\Strong\TS32
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
|----|--------|--------|---------|
| TS32-T1 | `TraceMajorantContract` | `analytic_infrastructure_obligation` | future trace estimate with `Ct <= 1/2` |
| TS32-T2 | `Ct_target_v2` | `candidate_target` | target trace value `1/2` |
| TS32-T3 | `candidate_v2_target_scaled_value` | `repo_committed_relative` | target value is `103/100` |
| TS32-T4 | `OTSACert_candidate_v2` | `repo_committed_relative` | conditional rational certificate |
| TS32-T5 | `OTSAProvenance_candidate_v2` | `analytic_candidate` | marks trace as conditional, not certified |
| TS32-T6 | `candidate_v2_scaledOTSAAdmissible` | `repo_committed_relative` | candidate v2 feeds TS23 via TS26 |

## Conclusion

TS32 keeps the trace estimate honest:

```text
TraceMajorantContract with Ct <= 1/2
=> Cscale * (Ck * Ct + Cm) <= 26
=> ScaledOTSAAdmissible
```

The target value `Ct = 1/2` would give:

```text
1 * ((3/50) * (1/2) + 1) = 103/100 <= 26.
```

The trace placeholder is not upgraded to a certified analytic derivation until
the contract is instantiated by a sourced proof.
