# TS49 - Triangle Spline Sobolev Agreement

## Status

TS49 isolates the Sobolev-agreement step in the triangle-spline route toward
the Mellin-tail majorant.

Status: `repo_committed_relative`.

TS49 does not prove the Sobolev derivative identity, Plancherel, or
Fourier-tail decay. It records the exact local infrastructure needed to connect
the TS41 abstract Sobolev derivative slot to the explicit weak-derivative
representative `triangleSplineDeriv`.

## Lean Files

- `TriangleSplineSobolevAgreement.lean`:
  - defines `TriangleSplineSobolevAgreementInfrastructure`;
  - defines `TriangleSplineSobolevAgreementTarget`;
  - proves `TriangleSplineSobolevAgreementTarget.of_infrastructure`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS49.TriangleSplineSobolevAgreement

rg -n "s[o]rry" TS\Goldbach\Strong\TS49
rg -n "a[x]iom" TS\Goldbach\Strong\TS49
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS49-S1 | `TriangleSplineSobolevAgreementInfrastructure` | `analytic_infrastructure_obligation` | agreement between TS41 Sobolev derivative and `triangleSplineDeriv` |
| TS49-S2 | `TriangleSplineSobolevAgreementTarget` | `repo_committed_relative` | target proposition for the Sobolev-agreement step |
| TS49-S3 | `TriangleSplineSobolevAgreementTarget.of_infrastructure` | `repo_committed_relative` | supplied infrastructure gives the target |

## Conclusion

TS49 separates the Sobolev-agreement obligation from the already proved TS48
`snorm` bound. The remaining spline route can now assemble norm control,
Sobolev agreement, and Fourier-tail comparison in later sprints.
