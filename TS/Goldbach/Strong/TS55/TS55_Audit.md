# TS55 - Triangle Spline Sobolev Agreement Ledger

## Status

TS55 decomposes the TS49 Sobolev-agreement infrastructure into local
weak-derivative obligations for the triangle spline.

Status: `repo_committed_relative`.

TS55 does not prove the distributional derivative identity, does not choose a
test-function or Sobolev API, does not prove Plancherel, and does not
instantiate the Fourier-tail comparison. It records the exact local bridge from
the piecewise derivative representative to the TS41 Sobolev derivative slot.

## Lean Files

- `TriangleSplineSobolevAgreementLedger.lean`:
  - defines `TriangleSplineSobolevAgreementLedger`;
  - records branch-derivative, boundary, and distributional-identity markers;
  - records the exact a.e. agreement with the TS41 Sobolev derivative slot;
  - defines `triangleSplineSobolevAgreementInfrastructure`;
  - proves that the TS55 ledger target implies the TS49 target.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS55.TriangleSplineSobolevAgreementLedger

rg -n "s[o]rry" TS\Goldbach\Strong\TS55
rg -n "a[x]iom" TS\Goldbach\Strong\TS55
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS55-S1 | `TriangleSplineSobolevAgreementLedger` | `analytic_infrastructure_obligation` | decomposed weak-derivative route for the triangle spline |
| TS55-S2 | `triangleSplineSobolevAgreementInfrastructure` | `repo_committed_relative` | ledger gives TS49 infrastructure |
| TS55-S3 | `TriangleSplineSobolevAgreementLedgerTarget` | `repo_committed_relative` | target proposition for the decomposed route |
| TS55-S4 | `triangleSplineSobolevAgreementTarget_of_ledgerTarget` | `repo_committed_relative` | TS55 target implies TS49 target |

## Conclusion

TS55 advances the `Cm <= 1` route without depending on the blocked Plancherel
step. The next Sobolev-side sprint can strengthen the branch derivative,
boundary, and distributional markers one at a time.
