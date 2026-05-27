# TS29 - OTSA Constant Provenance

## Status

TS29 records provenance metadata for OTSA rational constants.

Status: `repo_committed_relative`.

It does not prove or certify any analytic constant. It records which constants
are placeholders, narrative-source candidates, numerical experiments, analytic
derivations, or Lean-certified bounds.

## Lean Files

- `OTSAConstantProvenance.lean`:
  - defines `ConstantProvenance`;
  - defines `SourcedRatBound`;
  - defines `OTSAConstantProvenanceRegister`;
  - defines `OTSAProvenance_candidate_v0`;
  - proves `candidate_v0_not_certified`;
  - records the provenance status of `Ck`, `Ct`, `Cm`, and `Cscale`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS29.OTSAConstantProvenance

rg -n "s[o]rry" TS\Goldbach\Strong\TS29
rg -n "a[x]iom" TS\Goldbach\Strong\TS29
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
|----|--------|--------|---------|
| TS29-P1 | `ConstantProvenance` | `repo_committed` | metadata status for each rational upper bound |
| TS29-P2 | `SourcedRatBound` | `repo_committed` | rational value plus provenance and label |
| TS29-P3 | `OTSAConstantProvenanceRegister` | `repo_committed` | provenance package for `Ck`, `Ct`, `Cm`, `Cscale` |
| TS29-P4 | `OTSAProvenance_candidate_v0` | `analytic_candidate` | `Ck` narrative, other constants placeholders |
| TS29-P5 | `candidate_v0_not_certified` | `repo_committed` | proves the v0 package is not marked certified |

## Candidate-v0 Provenance

```text
Ck     : narrative_source
Ct     : placeholder
Cm     : placeholder
Cscale : placeholder
```

This is a provenance ledger only. The next meaningful update is to replace the
placeholder entries with sourced rational majorants.
