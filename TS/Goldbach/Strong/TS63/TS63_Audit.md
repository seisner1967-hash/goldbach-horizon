# TS63 - Triangle Spline Concrete Distributional Contract

## Status

TS63 specializes the abstract TS61 distributional derivative contract to the
concrete TS62 test-function API.

Status: `repo_committed_relative`.

TS63 does not prove the distributional derivative identity, does not prove
integration by parts, and does not prove Sobolev-slot agreement, Plancherel, or
Fourier-tail estimates. It records the exact concrete weak-derivative identity
that future integration-by-parts sprints must prove.

## Lean Files

- `TriangleSplineConcreteDistributionalContract.lean`:
  - defines `TriangleSplineConcreteDistributionalContract`;
  - defines `distributionalContract_of_concrete`;
  - defines `TriangleSplineConcreteDistributionalContractTarget`;
  - proves `distributionalDerivativeTarget_of_concreteTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS63.TriangleSplineConcreteDistributionalContract

rg -n "s[o]rry" TS\Goldbach\Strong\TS63
rg -n "a[x]iom" TS\Goldbach\Strong\TS63
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS63-D1 | `TriangleSplineConcreteDistributionalContract` | `analytic_infrastructure_obligation` | concrete weak-derivative identity |
| TS63-D2 | `distributionalContract_of_concrete` | `repo_committed_relative` | concrete contract implies TS61 contract |
| TS63-D3 | `TriangleSplineConcreteDistributionalContractTarget` | `repo_committed_relative` | target proposition |
| TS63-D4 | `distributionalDerivativeTarget_of_concreteTarget` | `repo_committed_relative` | concrete target implies TS61 target |

## Conclusion

TS63 is the typed bridge from the concrete TS62 `C1` compact-support test
functions back to the abstract TS61 distributional ledger. The future proof
work is now a single concrete integration-by-parts identity.
