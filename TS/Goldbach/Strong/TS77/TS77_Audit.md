# TS77 - Triangle Spline IPP Affine Branch Proof

## Status

TS77 discharges the two affine branch integration-by-parts identities isolated
in TS73.

Status: `repo_committed`.

The proof uses the TS76 interval-integral bridge, Mathlib's finite-interval
integration-by-parts theorem, the TS56 affine branch formulae for
`triangleSpline`, and the TS43 pointwise values of `triangleSplineDeriv` away
from the null endpoints included by `intervalIntegral`.

TS77 does not itself perform the TS74 recombination to the concrete TS63
distributional contract, and does not prove Sobolev-slot agreement,
Plancherel, or Fourier-tail estimates.

## Lean Files

- `TriangleSplineIPPAffineBranchProof.lean`:
  - defines `leftAffine`;
  - defines `rightAffine`;
  - proves `testFunction_hasDerivAt`;
  - proves `leftAffine_hasDerivAt`;
  - proves `rightAffine_hasDerivAt`;
  - proves `left_affine_interval_ipp`;
  - proves `right_affine_interval_ipp`;
  - proves the branchwise interval congruence lemmas;
  - proves `left_affine_ipp`;
  - proves `right_affine_ipp`;
  - defines `triangleSplineIPPAffineBranchContract`;
  - proves `triangleSplineIPPAffineBranchContractTarget`;
  - proves `triangleSplineIPPAffineBranchProofTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS77.TriangleSplineIPPAffineBranchProof

rg -n "s[o]rry" TS\Goldbach\Strong\TS77
rg -n "a[x]iom" TS\Goldbach\Strong\TS77
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS77-P1 | `left_affine_interval_ipp` | `repo_committed` | interval-integral IPP on the left affine branch |
| TS77-P2 | `right_affine_interval_ipp` | `repo_committed` | interval-integral IPP on the right affine branch |
| TS77-P3 | `left_affine_ipp` | `repo_committed` | TS73 left affine branch identity |
| TS77-P4 | `right_affine_ipp` | `repo_committed` | TS73 right affine branch identity |
| TS77-P5 | `triangleSplineIPPAffineBranchContract` | `repo_committed` | concrete discharge of the TS73 contract |

## Conclusion

TS77 closes the local affine integration-by-parts step. Together with TS74,
this makes the concrete TS63 distributional contract mechanically reachable in
the next sprint.
