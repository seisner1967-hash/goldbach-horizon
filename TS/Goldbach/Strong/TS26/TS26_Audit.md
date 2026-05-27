# TS26 - OTSA Numerical Feasibility

## Status

TS26 provides a rational numerical certificate layer for the scaled OTSA
admissibility inequality.

Status: `repo_committed_relative`.

It does not prove the spectral, trace, Mellin-tail, coupling, or Goldbach
theorems. It only turns rational upper-bound constants into a Lean-checkable
`ScaledOTSAAdmissible` proof.

## Lean Files

- `OTSANumericalFeasibility.lean`:
  - defines `OTSARationalCertificate`;
  - defines `scaledConstantsOfRat`;
  - proves `scaledCoupledConstant_of_rat`;
  - proves `scaledOTSAAdmissible_of_rat`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS26.OTSANumericalFeasibility

rg -n "s[o]rry" TS\Goldbach\Strong\TS26
rg -n "a[x]iom" TS\Goldbach\Strong\TS26
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
|----|--------|--------|---------|
| TS26-N1 | `OTSARationalCertificate` | `repo_committed` | rational constants and admissibility inequality |
| TS26-N2 | `scaledConstantsOfRat` | `repo_committed` | converts rational constants to TS23 real constants |
| TS26-N3 | `scaledCoupledConstant_of_rat` | `repo_committed` | identifies real and rational coupled constants |
| TS26-N4 | `scaledOTSAAdmissible_of_rat` | `repo_committed_relative` | rational inequality implies TS23 admissibility |

## Conclusion

TS26 is the exact arithmetic crash-test layer for OTSA constants:

```text
OTSARationalCertificate
  => ScaledOTSAConstants
  => ScaledOTSAAdmissible
```

Concrete OTSA majorants can now be checked with rational arithmetic, without
floating-point assumptions.
