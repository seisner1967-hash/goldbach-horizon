# TS183 Audit - Triangle Spline Finite Weighted Prime Sum Interface

## Scope

TS183 turns the TS182 pointwise discrete triangle-spline weight into a finite
arithmetic sum interface.

The sprint deliberately starts with a generic arithmetic weight
`A : Nat -> Real`, then names a local `VonMangoldtWeightContract` for the later
specialization to the exact von Mangoldt API.

## Main file

```text
TS/Goldbach/Strong/TS183/TriangleSplineFiniteWeightedPrimeSumInterface.lean
```

## Main declarations

```lean
TS183.Goldbach.triangleSplineWeightedNatSum
TS183.Goldbach.triangleSplineWeightedNatSum_eq_range_succ
TS183.Goldbach.triangleSplineWeightedNatSum_range_eq_of_le
TS183.Goldbach.triangleSplineWeightedNatSum_affine
TS183.Goldbach.triangleSplineWeightedNatSum_nonneg
TS183.Goldbach.VonMangoldtWeightContract
TS183.Goldbach.triangleSplineVonMangoldtWeightedSum
TS183.Goldbach.triangleSplineVonMangoldtWeightedSum_nonneg
TS183.Goldbach.triangleSplineVonMangoldtWeightedSum_affine
TS183.Goldbach.TriangleSplineFiniteWeightedSumStatus
TS183.Goldbach.TriangleSplineFiniteWeightedPrimeSumInterfaceLedger
TS183.Goldbach.triangleSplineFiniteWeightedPrimeSumInterfaceLedger
TS183.Goldbach.TriangleSplineFiniteWeightedPrimeSumInterfaceTarget
TS183.Goldbach.triangleSplineFiniteWeightedPrimeSumInterfaceTarget
```

## What is proved

- `triangleSplineWeightedNatSum` is a finite sum over `Finset.range (X + 1)`.
- If `0 < X` and `X + 1 <= N`, extending the range to `N` does not change the
  sum, because TS182 makes all added weights vanish.
- For positive `X`, the finite weighted sum can be rewritten using the affine
  formula `1 - n / X` on the support range.
- If the arithmetic weight is nonnegative, the weighted sum is nonnegative.
- A local von Mangoldt weight contract can consume the generic interface.

## Non-claims

TS183 does not prove:

- the exact Mathlib von Mangoldt API identification;
- any estimate for the weighted sum;
- the explicit formula;
- construction of zeta zeros;
- Plancherel;
- Goldbach.

## Verification commands

```powershell
lake env lean TS\Goldbach\Strong\TS183\TriangleSplineFiniteWeightedPrimeSumInterface.lean
lake build TS.Goldbach.Strong.TS183.TriangleSplineFiniteWeightedPrimeSumInterface
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS183
git diff --check
git status --short
```

Expected result: build succeeds, no forbidden proof placeholders, no forbidden
declaration placeholders, no non-ASCII characters, and no whitespace errors.
