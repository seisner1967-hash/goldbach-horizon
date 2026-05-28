# TS33 - OTSA Final Majorants Roadmap

## Status

TS33 introduces conditional contracts for the final two OTSA asymptotic
majorants: the Mellin-tail contribution and the padded-scale transfer cost.

Status: `repo_committed_relative`.

TS33 does not prove the trace estimate, Mellin-tail estimate, scale-transfer
estimate, OTSA residual bound, or Goldbach theorem. It proves by exact rational
arithmetic that any constants satisfying:

```text
Ck = 3/50
Ct <= 1/2
Cm <= 1
Cscale <= 2
```

satisfy the TS23 admissibility threshold.

## Lean Files

- `OTSAFinalMajorantsRoadmap.lean`:
  - defines `MellinTailMajorantContract`;
  - defines `ScaleTransferMajorantContract`;
  - proves the saturated target value `103/50`;
  - proves admissibility for any contracted `Ct`, `Cm`, and `Cscale`;
  - defines `OTSACert_candidate_v3`;
  - defines `OTSARegister_candidate_v3`;
  - defines `OTSAProvenance_candidate_v3`;
  - proves `candidate_v3_scaledOTSAAdmissible`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS33.OTSAFinalMajorantsRoadmap

rg -n "s[o]rry" TS\Goldbach\Strong\TS33
rg -n "a[x]iom" TS\Goldbach\Strong\TS33
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
|----|--------|--------|---------|
| TS33-M1 | `MellinTailMajorantContract` | `analytic_infrastructure_obligation` | future Mellin-tail estimate with `Cm <= 1` |
| TS33-S1 | `ScaleTransferMajorantContract` | `analytic_infrastructure_obligation` | future scale-transfer estimate with `Cscale <= 2` |
| TS33-C1 | `candidate_v3_target_scaled_value` | `repo_committed_relative` | saturated value is exactly `103/50` |
| TS33-C2 | `OTSACert_candidate_v3` | `repo_committed_relative` | conditional rational admissibility certificate |
| TS33-P1 | `OTSAProvenance_candidate_v3` | `analytic_candidate` | contract-supplied conditional bounds, not certified derivations |
| TS33-A1 | `candidate_v3_scaledOTSAAdmissible` | `repo_committed_relative` | candidate v3 feeds TS23 via TS26 |

## Conclusion

TS33 replaces raw placeholders for `Cm` and `Cscale` by explicit local
contracts:

```text
TraceMajorantContract
+ MellinTailMajorantContract
+ ScaleTransferMajorantContract
=> ScaledOTSAAdmissible
```

The saturated v3 score is:

```text
2 * ((3/50) * (1/2) + 1) = 103/50 <= 26.
```

The contracts must still be instantiated by sourced analytic derivations or
Lean-certified proofs before any final OTSA certificate can be claimed.
