# TS88 - Farey Separation Proof

## Status

`repo_committed`

TS88 proves the Farey separation contract isolated in TS87. For two distinct
embedded rational points `a/q` and `a'/q'`, the proof uses the integer
cross-difference `a*q' - a'*q`. If the embedded values are distinct, this
integer is nonzero, so its real absolute value is at least one. Dividing by the
positive denominator product gives the classical lower bound.

TS88 does not prove Farey covering, Farey counting, or the dual large-sieve
variance bound.

## Lean artifacts

File:

```text
TS/Goldbach/Strong/TS88/FareySeparationProof.lean
```

Key declarations:

```lean
TS88.Goldbach.fareyCrossDiff
TS88.Goldbach.one_le_abs_int_cast
TS88.Goldbach.fareyCrossDiff_ne_zero_of_valueDistinct
TS88.Goldbach.farey_value_sub_eq_crossDiff_div
TS88.Goldbach.fareySeparationStatement
TS88.Goldbach.fareySeparationContract
TS88.Goldbach.fareySeparationContractTarget
TS88.Goldbach.FareySeparationProofTarget
TS88.Goldbach.fareySeparationProofTarget
TS88.Goldbach.fareySpacingContractTarget_of_covering_counting
TS88.Goldbach.fareySpacingInfrastructureTarget_of_covering_counting
TS88.Goldbach.paddedGrandSieveVarianceInfrastructureTarget_of_covering_counting_paddedDualLargeSieveTarget
TS88.Goldbach.scaleTransferMajorantAPIContractsTarget_of_covering_counting_paddedDualLargeSieveTarget
```

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS88.FareySeparationProof

rg -n "s[o]rry" TS\Goldbach\Strong\TS88
rg -n "a[x]iom" TS\Goldbach\Strong\TS88
```

Expected result:

```text
no forbidden placeholder matches
```

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS88-P1 | `one_le_abs_int_cast` | `repo_committed` | nonzero integer has real absolute value at least one |
| TS88-P2 | `fareyCrossDiff_ne_zero_of_valueDistinct` | `repo_committed` | distinct embedded values give nonzero cross-difference |
| TS88-P3 | `farey_value_sub_eq_crossDiff_div` | `repo_committed` | rational-value difference equals cross-difference divided by denominator product |
| TS88-P4 | `fareySeparationStatement` | `repo_committed` | proves the TS87 Farey separation statement |
| TS88-P5 | `fareySeparationContractTarget` | `repo_committed` | discharges the TS87 separation target |
| TS88-P6 | `fareySpacingContractTarget_of_covering_counting` | `repo_committed_relative` | separation is now supplied, leaving covering and counting on the Farey side |
| TS88-P7 | `scaleTransferMajorantAPIContractsTarget_of_covering_counting_paddedDualLargeSieveTarget` | `repo_committed_relative` | covering, counting, and dual large sieve imply the TS84 scale-transfer API target |

## Summary

TS88 converts one TS87 arithmetic infrastructure obligation into an
unconditional Lean theorem. The remaining Farey-side obligations are covering
and counting; the analytic side still needs the compatible dual large-sieve
variance bound.
