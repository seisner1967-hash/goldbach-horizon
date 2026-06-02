# TS81 - Triangle Spline Sobolev Slot API Binding

## Status

TS81 isolates the final API-level binding needed after TS80. It states the
exact agreement required from a chosen TS41 Fourier/Sobolev ledger:

```lean
api.sobolevDerivative 1 triangleSpline =m[volume] triangleSplineDeriv
```

When this binding is supplied, TS81 mechanically produces the TS80
Sobolev-slot assembly target, then the TS55 ledger target, then the TS49
Sobolev-agreement target.

Status: `repo_committed_relative`.

TS81 does not choose a concrete Mathlib Fourier/Sobolev API, does not prove
weak-derivative uniqueness, and does not prove Plancherel or Fourier-tail
estimates.

## Lean Files

- `TriangleSplineSobolevSlotAPIBinding.lean`:
  - defines `TriangleSplineSobolevSlotAPIBinding`;
  - defines `triangleSplineSobolevSlotAssembly_of_apiBinding`;
  - defines `TriangleSplineSobolevSlotAPIBindingTarget`;
  - proves `triangleSplineSobolevSlotAssemblyTarget_of_apiBindingTarget`;
  - proves `triangleSplineSobolevAgreementLedgerTarget_of_apiBindingTarget`;
  - proves `triangleSplineSobolevAgreementTarget_of_apiBindingTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS81.TriangleSplineSobolevSlotAPIBinding

rg -n "s[o]rry" TS\Goldbach\Strong\TS81
rg -n "a[x]iom" TS\Goldbach\Strong\TS81
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS81-C1 | `TriangleSplineSobolevSlotAPIBinding` | `analytic_infrastructure_obligation` | exact TS41 Sobolev API binding |
| TS81-P1 | `triangleSplineSobolevSlotAssemblyTarget_of_apiBindingTarget` | `repo_committed_relative` | TS81 binding implies TS80 target |
| TS81-P2 | `triangleSplineSobolevAgreementLedgerTarget_of_apiBindingTarget` | `repo_committed_relative` | TS81 binding implies TS55 target |
| TS81-P3 | `triangleSplineSobolevAgreementTarget_of_apiBindingTarget` | `repo_committed_relative` | TS81 binding implies TS49 target |

## Conclusion

TS81 sharpens the remaining Sobolev obligation to a single API binding:
the selected TS41 `sobolevDerivative` must recognize the TS79 weak derivative
of `triangleSpline` as `triangleSplineDeriv` almost everywhere.
