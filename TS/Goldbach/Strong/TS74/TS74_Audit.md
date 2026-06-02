# TS74 - Triangle Spline IPP Recombination From Affine Branches

## Status

TS74 proves that the local affine branch IPP contract from TS73 is sufficient
to discharge the concrete distributional contract from TS63.

Status: `repo_committed_relative`.

TS74 does not prove the local affine integration-by-parts identities
themselves. It proves the recombination step: using TS68, TS70, and TS72, the
global left IPP integral is rewritten as the sum of the two branch integrals;
the two TS73 branch identities are applied; the boundary terms `phi.toFun 0`
and `- phi.toFun 0` cancel; and the right IPP integral is reassembled back to
the global integral.

TS74 does not prove affine integration by parts, Sobolev-slot agreement,
Plancherel, or Fourier-tail estimates.

## Lean Files

- `TriangleSplineIPPRecombinationFromAffine.lean`:
  - defines `concreteDistributionalContract_of_affineBranchContract`;
  - defines `TriangleSplineConcreteDistributionalFromAffineTarget`;
  - proves `triangleSplineConcreteDistributionalFromAffineTarget`;
  - proves `concreteDistributionalTarget_of_affineBranchTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS74.TriangleSplineIPPRecombinationFromAffine

rg -n "s[o]rry" TS\Goldbach\Strong\TS74
rg -n "a[x]iom" TS\Goldbach\Strong\TS74
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS74-R1 | `concreteDistributionalContract_of_affineBranchContract` | `repo_committed_relative` | conditional recombination from TS73 to TS63 |
| TS74-R2 | `TriangleSplineConcreteDistributionalFromAffineTarget` | `repo_committed_relative` | target proposition for the conditional route |
| TS74-R3 | `triangleSplineConcreteDistributionalFromAffineTarget` | `repo_committed_relative` | theorem proving the conditional route |
| TS74-R4 | `concreteDistributionalTarget_of_affineBranchTarget` | `repo_committed_relative` | TS73 target implies TS63 target |

## Conclusion

TS74 removes the future recombination burden from the affine IPP proof. The
remaining local work is now concentrated in proving the two TS73 affine branch
identities.
