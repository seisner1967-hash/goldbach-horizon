# TS68 - Triangle Spline IPP Integral Restriction Proof

## Status

TS68 discharges the integral-restriction contract introduced in TS67.

Status: `repo_committed`.

TS68 proves that each global Bochner integral over `volume` for the two
concrete triangle-spline IPP products is equal to the corresponding integral
over `(volume : Measure Real).restrict (Icc (-1 : Real) 1)`.

TS68 does not split `[-1, 1]` into branches, does not prove affine integration
by parts, does not prove the TS63 concrete distributional contract, and does
not prove Sobolev-slot agreement, Plancherel, or Fourier-tail estimates.

## Lean Files

- `TriangleSplineIPPIntegralRestrictionProof.lean`:
  - proves `left_global_eq_restrict`;
  - proves `right_global_eq_restrict`;
  - defines `triangleSplineIPPIntegralRestriction`;
  - defines `TriangleSplineIPPIntegralRestrictionProofTarget`;
  - proves `triangleSplineIPPIntegralRestrictionTarget`;
  - proves `triangleSplineIPPIntegralRestrictionProofTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS68.TriangleSplineIPPIntegralRestrictionProof

rg -n "s[o]rry" TS\Goldbach\Strong\TS68
rg -n "a[x]iom" TS\Goldbach\Strong\TS68
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS68-R1 | `left_global_eq_restrict` | `repo_committed` | restricts the left IPP integral to `[-1, 1]` |
| TS68-R2 | `right_global_eq_restrict` | `repo_committed` | restricts the right IPP integral to `[-1, 1]` |
| TS68-R3 | `triangleSplineIPPIntegralRestriction` | `repo_committed` | concrete discharge of TS67 |
| TS68-R4 | `triangleSplineIPPIntegralRestrictionTarget` | `repo_committed` | TS68 proves the TS67 target |

## Conclusion

TS68 turns TS66 pointwise support restriction into integral-level restriction
using Mathlib's `setIntegral_eq_integral_of_forall_compl_eq_zero`. The next
sprint can prepare the branchwise split of the restricted integrals over
`[-1, 0]` and `[0, 1]`.
