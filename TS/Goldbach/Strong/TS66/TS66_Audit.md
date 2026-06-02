# TS66 - Triangle Spline IPP Product Support Restriction

## Status

TS66 proves that the two concrete integration-by-parts products vanish outside
the triangle-spline support interval `[-1, 1]`.

Status: `repo_committed`.

TS66 does not restrict the global Bochner integrals to `[-1, 1]`, does not
split the interval into branches, and does not prove the integration-by-parts
identity. It only records the pointwise support facts needed before those
future integral manipulations.

## Lean Files

- `TriangleSplineIPPProductSupportRestriction.lean`:
  - proves `left_ipp_product_zero_outside_Icc`;
  - proves `right_ipp_product_zero_outside_Icc`;
  - defines `TriangleSplineIPPProductSupportRestriction`;
  - defines `triangleSplineIPPProductSupportRestriction`;
  - proves `triangleSplineIPPProductSupportRestrictionTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS66.TriangleSplineIPPProductSupportRestriction

rg -n "s[o]rry" TS\Goldbach\Strong\TS66
rg -n "a[x]iom" TS\Goldbach\Strong\TS66
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS66-S1 | `left_ipp_product_zero_outside_Icc` | `repo_committed` | `triangleSpline * phi'` vanishes outside `[-1, 1]` |
| TS66-S2 | `right_ipp_product_zero_outside_Icc` | `repo_committed` | `triangleSplineDeriv * phi` vanishes outside `[-1, 1]` |
| TS66-S3 | `TriangleSplineIPPProductSupportRestriction` | `repo_committed` | packaged product-support facts |
| TS66-S4 | `triangleSplineIPPProductSupportRestrictionTarget` | `repo_committed` | target proposition discharged |

## Conclusion

TS66 removes the pointwise support side conditions for the future IPP route.
The next branch can focus on turning these support facts plus TS65 integrability
into global integral restriction to `[-1, 1]`.
