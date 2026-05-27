# TS28 - OTSA Constants Candidate

## Status

TS28 introduces a typed-status register for OTSA rational constants and records
`OTSACert_candidate_v0`.

Status: `repo_committed_relative`.

It does not certify the spectral, trace, Mellin-tail, scale-transfer, coupling,
or Goldbach theorems. The candidate-v0 package is a rationally checked
admissibility candidate whose analytic provenance is still incomplete.

## Lean Files

- `OTSAConstantsCandidate.lean`:
  - defines `ConstantStatus`;
  - defines `LabelledOTSAConstantRegister`;
  - defines `OTSACert_candidate_v0`;
  - defines `OTSARegister_candidate_v0`;
  - proves `candidate_v0_scaledOTSAAdmissible`;
  - proves `candidate_v0_status`;
  - proves `candidate_v0_register_scaledOTSAAdmissible`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS28.OTSAConstantsCandidate

rg -n "s[o]rry" TS\Goldbach\Strong\TS28
rg -n "a[x]iom" TS\Goldbach\Strong\TS28
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
|----|--------|--------|---------|
| TS28-C1 | `ConstantStatus` | `repo_committed` | distinguishes smoke tests, candidates, and certified packages |
| TS28-C2 | `LabelledOTSAConstantRegister` | `repo_committed` | typed-status register for rational OTSA constants |
| TS28-C3 | `OTSACert_candidate_v0` | `analytic_candidate` | rationally checked candidate, not final |
| TS28-C4 | `OTSARegister_candidate_v0` | `analytic_candidate` | labelled candidate-v0 register |
| TS28-C5 | `candidate_v0_scaledOTSAAdmissible` | `repo_committed_relative` | candidate rational inequality implies TS23 admissibility |

## Candidate-v0 Constants

```text
Ck     = 3/50
Ct     = 1
Cm     = 1
Cscale = 1
```

Only `Ck` has a narrative source at this stage (`C0 ~= 0.058`). The other
entries must be replaced by sourced rational majorants before any final
certificate claim.
