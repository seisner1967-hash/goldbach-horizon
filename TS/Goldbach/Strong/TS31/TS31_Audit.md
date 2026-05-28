# TS31 - OTSA Asymptotic Majorants

## Status

TS31 records the first asymptotic-majorant candidate package for the scaled
OTSA constants after the TS29 provenance ledger.

Status: `repo_committed_relative`.

TS31 does not prove the spectral kernel, trace contribution, Mellin-tail
decay, scale-transfer cost, OTSA residual bound, or Goldbach theorem. It only
checks that the current rational candidate package satisfies the TS23
admissibility inequality and records which constants still lack analytic
provenance.

## Lean Files

- `OTSAAsymptoticMajorants.lean`:
  - defines `Ck_v1 = 3/50`;
  - defines placeholder values `Ct_v1 = 1`, `Cm_v1 = 1`, `Cscale_v1 = 1`;
  - proves the exact rational value `53/50`;
  - proves `53/50 <= 26`;
  - defines `OTSACert_candidate_v1`;
  - defines `OTSARegister_candidate_v1`;
  - defines `OTSAProvenance_candidate_v1`;
  - proves `candidate_v1_scaledOTSAAdmissible`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS31.OTSAAsymptoticMajorants

rg -n "s[o]rry" TS\Goldbach\Strong\TS31
rg -n "a[x]iom" TS\Goldbach\Strong\TS31
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
|----|--------|--------|---------|
| TS31-A1 | `Ck_v1` | `narrative_source` | padded spectral narrative bound `3/50` |
| TS31-A2 | `Ct_v1` | `placeholder` | trace contribution majorant still to source |
| TS31-A3 | `Cm_v1` | `placeholder` | Mellin-tail majorant still to source |
| TS31-A4 | `Cscale_v1` | `placeholder` | padded-scale transfer majorant still to source |
| TS31-A5 | `OTSACert_candidate_v1` | `repo_committed_relative` | rational admissibility certificate for candidate v1 |
| TS31-A6 | `OTSAProvenance_candidate_v1` | `analytic_candidate` | typed provenance register |
| TS31-A7 | `candidate_v1_scaledOTSAAdmissible` | `repo_committed_relative` | candidate v1 feeds TS23 via TS26 |

## Conclusion

The current rational candidate has large numerical slack:

```text
Cscale * (Ck * Ct + Cm) = 53/50 <= 26
```

However, only `Ck` has a narrative source. The next real analytic task is to
replace the placeholders for `Ct`, `Cm`, and `Cscale` with sourced rational
upper bounds.
