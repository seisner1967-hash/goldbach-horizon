# TS89 - Farey Counting Proof

## Status

`repo_committed`

TS89 discharges the TS87 Farey counting marker with a concrete finite counting
bound. It defines a finite square of numerator/denominator pairs and filters
the admissible reduced Farey pairs from it. The filtered set has cardinality at
most the square, hence at most `(Q + 1) * (Q + 1)`.

TS89 does not prove the Farey covering contract and does not prove the dual
large-sieve variance bound.

## Lean artifacts

File:

```text
TS/Goldbach/Strong/TS89/FareyCountingProof.lean
```

Key declarations:

```lean
TS89.Goldbach.fareyCandidatePairs
TS89.Goldbach.fareyReducedWindowPairs
TS89.Goldbach.fareyCandidatePairs_card
TS89.Goldbach.fareyReducedWindowPairs_card_le_candidate
TS89.Goldbach.FareyCountingStatement
TS89.Goldbach.fareyCountingStatement
TS89.Goldbach.fareyCountingContract
TS89.Goldbach.fareyCountingContractTarget
TS89.Goldbach.FareyCountingProofTarget
TS89.Goldbach.fareyCountingProofTarget
TS89.Goldbach.fareySpacingContractTarget_of_covering
TS89.Goldbach.fareySpacingInfrastructureTarget_of_covering
TS89.Goldbach.scaleTransferMajorantAPIContractsTarget_of_covering_paddedDualLargeSieveTarget
```

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS89.FareyCountingProof

rg -n "s[o]rry" TS\Goldbach\Strong\TS89
rg -n "a[x]iom" TS\Goldbach\Strong\TS89
```

Expected result:

```text
no forbidden placeholder matches
```

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS89-P1 | `fareyCandidatePairs_card` | `repo_committed` | counts the ambient square of bounded numerator/denominator pairs |
| TS89-P2 | `fareyReducedWindowPairs_card_le_candidate` | `repo_committed` | admissible reduced pairs are a filtered subset of the ambient square |
| TS89-P3 | `fareyCountingStatement` | `repo_committed` | proves the concrete `(Q + 1)^2` counting bound |
| TS89-P4 | `fareyCountingContractTarget` | `repo_committed` | discharges the TS87 counting target |
| TS89-P5 | `fareySpacingContractTarget_of_covering` | `repo_committed_relative` | after TS88 and TS89, covering alone completes TS87 Farey spacing |
| TS89-P6 | `scaleTransferMajorantAPIContractsTarget_of_covering_paddedDualLargeSieveTarget` | `repo_committed_relative` | covering plus dual large sieve implies the TS84 scale-transfer API target |

## Summary

TS89 removes the Farey counting obligation from the scale-transfer front. The
remaining Farey-side geometric input is the covering contract; the analytic
input below TS86 remains the compatible dual large-sieve variance bound.
