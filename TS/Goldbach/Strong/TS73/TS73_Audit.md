# TS73 - Triangle Spline IPP Affine Branch Contract

## Status

TS73 records the local affine integration-by-parts contract for the two closed
triangle-spline branches.

Status: `repo_committed_relative`.

TS73 uses the branch split from TS70 and the right-branch closed bridge from
TS72 as inputs. It then fixes the exact local theorem shape needed for the
future affine IPP proof: the left branch contributes `phi.toFun 0`, and the
right branch contributes `- phi.toFun 0`.

TS73 does not prove either affine branch IPP identity, does not recombine the
branches, and does not prove the concrete TS63 distributional contract,
Sobolev-slot agreement, Plancherel, or Fourier-tail estimates.

## Lean Files

- `TriangleSplineIPPAffineBranchContract.lean`:
  - defines `TriangleSplineIPPAffineBranchContract`;
  - defines `TriangleSplineIPPAffineBranchInputs`;
  - defines `triangleSplineIPPAffineBranchInputs`;
  - defines `TriangleSplineIPPAffineBranchContractTarget`;
  - defines `TriangleSplineIPPAffineBranchInputsTarget`;
  - proves `triangleSplineIPPAffineBranchInputsTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS73.TriangleSplineIPPAffineBranchContract

rg -n "s[o]rry" TS\Goldbach\Strong\TS73
rg -n "a[x]iom" TS\Goldbach\Strong\TS73
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS73-C1 | `TriangleSplineIPPAffineBranchContract` | `analytic_infrastructure_obligation` | local affine IPP identities on `[-1, 0]` and `[0, 1]` |
| TS73-C2 | `TriangleSplineIPPAffineBranchInputs` | `repo_committed` | TS70 branch split and TS72 right-closed bridge inputs |
| TS73-C3 | `triangleSplineIPPAffineBranchInputs` | `repo_committed` | concrete input package |
| TS73-C4 | `TriangleSplineIPPAffineBranchContractTarget` | `repo_committed_relative` | target proposition for the affine branch IPP step |

## Conclusion

TS73 fixes the two local affine IPP identities that must be proved before the
branch contributions can be recombined. The next sprint can attack either the
left branch `[-1, 0]` identity or the right branch `[0, 1]` identity directly.
