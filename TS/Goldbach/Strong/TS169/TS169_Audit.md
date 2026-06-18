# TS169 Audit - Triangle Spline Branch Closed-Form Recombination

## Sprint Scope

TS169 discharges the final algebraic obligation in the TS168 fallback route:
the two intended branch closed forms recombine to the TS166 pi-scale
squared-sinc target.

This sprint does not evaluate either Fourier branch integral.  It only proves
that the closed forms selected in TS168 are algebraically compatible with the
TS166 target.

## Main Declarations

- `TS169.Goldbach.exp_I_mul_add_exp_neg_I_mul`
- `TS169.Goldbach.two_sub_two_mul_cos_two_mul_div_sq_eq_sinc_sq`
- `TS169.Goldbach.branchClosedFormRecombination_nonzero`
- `TS169.Goldbach.branchClosedFormRecombination`
- `TS169.Goldbach.TriangleSplineBranchClosedFormRecombinationLedger`
- `TS169.Goldbach.triangleSplineBranchClosedFormRecombinationLedger`
- `TS169.Goldbach.TriangleSplineBranchClosedFormRecombinationTarget`
- `TS169.Goldbach.triangleSplineBranchClosedFormRecombinationTarget`

## What Is Proved

TS169 proves:

```lean
TS168.Goldbach.BranchClosedFormRecombinationStatement
```

That is, for every `xi : Real`,

```lean
leftBranchClosedForm xi + rightBranchClosedForm xi =
  TS166.Goldbach.triangleSplineScaledSincCandidate xi
```

The proof splits the zero-frequency case from the nonzero-frequency case.  In
the nonzero case it uses the elementary Euler identity
`exp(i*a) + exp(-i*a) = 2*cos(a)` and the real half-angle identity behind
`sinc^2`.

## Explicit Non-Claims

TS169 does not prove:

- the branch split of the Fourier integral;
- the left branch integral evaluation;
- the right branch integral evaluation;
- the full TS166 Fourier identification;
- Plancherel;
- the Riemann-von Mangoldt explicit formula.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS169.TriangleSplineBranchClosedFormRecombination
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS169
git diff --check
```

Expected result: build succeeds, no `s[o]rry`, no `a[x]iom`, no non-ASCII, and
no whitespace errors.

## Status

`repo_committed`
