# TS209 Audit - Triangle Spline Sinc-Fourth Scale Reduction

## Scope

TS209 continues the Wall 1 Plancherel evidence probe from TS208.  TS208 had
reduced the triangle-spline Plancherel input to the pi-scaled scalar identity

```lean
integral volume (fun xi => triangleSplineSincRealWeight xi ^ 2) = 2 / 3
```

TS209 removes the remaining normalization ambiguity.  It defines the canonical
unscaled squared-sinc profile

```lean
canonicalSincSq t = if t = 0 then 1 else (Real.sin t / t) ^ 2
```

and proves that the canonical identity

```lean
integral volume (fun t => canonicalSincSq t ^ 2) = (2 * Real.pi) / 3
```

implies the TS208 pi-scaled statement exactly.

## Main Declarations

- `TS209.Goldbach.canonicalSincSq`
- `TS209.Goldbach.CanonicalSincFourthIntegralValueStatement`
- `TS209.Goldbach.triangleSplineSincRealWeight_eq_canonical_comp_pi`
- `TS209.Goldbach.ts208SincFourthIntegral_of_canonicalSincFourthIntegral`
- `TS209.Goldbach.triangleSplinePlancherelInputEvidence_of_canonicalSincFourthIntegral`
- `TS209.Goldbach.TriangleSplineSincFourthScaleReductionLedger`
- `TS209.Goldbach.triangleSplineSincFourthScaleReductionLedger`
- `TS209.Goldbach.TriangleSplineSincFourthScaleReductionTarget`
- `TS209.Goldbach.triangleSplineSincFourthScaleReductionTarget`

## What TS209 Proves

TS209 proves the project-specific scale reduction:

```lean
CanonicalSincFourthIntegralValueStatement ->
  TS208.Goldbach.TriangleSplineSincFourthIntegralValueStatement
```

The proof identifies the TS178 spectral weight as `canonicalSincSq (Real.pi *
xi)` and applies Mathlib's global scaling lemma
`Measure.integral_comp_mul_left`.  Since `Real.pi > 0`, the absolute scaling
factor is `1 / Real.pi`; substituting the canonical value `(2 * Real.pi) / 3`
gives the TS208 value `2 / 3`.

TS209 also proves that the same canonical identity would populate the TS204
triangle-spline Plancherel input evidence by passing through the TS208 bridge.

## Non-Claims

TS209 does not prove the canonical sinc-fourth integral.
TS209 does not prove a general Plancherel theorem.
TS209 does not prove the explicit formula.
TS209 does not prove Gallagher or large-sieve bounds.
TS209 does not prove Goldbach.

## Verification Commands

```powershell
lake env lean TS\Goldbach\Strong\TS209\TriangleSplineSincFourthScaleReduction.lean
lake build TS.Goldbach.Strong.TS209.TriangleSplineSincFourthScaleReduction
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS209
git diff --check
git status --short
```
