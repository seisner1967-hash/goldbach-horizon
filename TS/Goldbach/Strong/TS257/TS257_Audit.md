# TS257 Audit - Triangle Spline Mellin Spectral Summand

## Scope

TS257 defines the corrected Mellin kernel and spectral summand used by the
finite TS256 zeta-zero contribution.

## Main Declarations

- `triangleSplineMellinKernel`
- `triangleSplinePositiveMellinIntegral`
- `TriangleSplineMellinIntegralEvaluationStatement`
- `triangleSplineMellinKernel_eq_sub`
- `complex_ne_zero_of_re_pos`
- `complex_add_one_ne_zero_of_re_pos`
- `triangleSplineMellinKernel_denominator_ne_zero_of_re_pos`
- `triangleSplineMellinKernel_denominator_ne_zero_at_nontrivialZero`
- `triangleSplineZeroSpectralSummand`
- `triangleSplineZeroSpectralSummand_spec`
- `triangleSplineZeroSpectralSummand_eq_scale_mul_kernel`
- `triangleSplineZeroContourResidueTerm`
- `triangleSplineZeroContourResidueTerm_spec`
- `TriangleSplineZeroSpectralSummandConjugationStatement`
- `triangleSplineZeroContributionFunction`
- `triangleSplineZeroTruncatedComplexSum`
- `triangleSplineZeroContributionFunction_identification`
- `TriangleSplineMellinSpectralSummandLedger`
- `triangleSplineMellinSpectralSummandTarget`

## Corrected Normalization

The positive triangle Mellin kernel is

```text
1 / (s * (s + 1)) = 1 / s - 1 / (s + 1).
```

The TS206 identity already subtracts `zeroContribution`.  Therefore the
TS256 summand is stored with positive sign:

```text
X^rho / (rho * (rho + 1)).
```

The opposite-signed contour residue is named separately.  No second `1/rho`
factor is introduced.

## Proved Facts

TS257 proves the partial-fraction identity, nonvanishing of both denominator
factors when the real part is positive, nonvanishing at every TS185 nontrivial
zero, the closed summand forms, and the TS256 identification of the resulting
zero function.

## Open Analytic Targets

The Bochner interval integral is defined, but its equality with the Mellin
kernel is only the named
`TriangleSplineMellinIntegralEvaluationStatement`.  Mellin/Fourier
equivalence, contour-residue identification, conjugation compatibility,
reality of the finite sum, the explicit-formula identity, and all analytic
bounds remain open.

## Non-Claims

TS257 does not prove a Mellin integral evaluation, apply a residue theorem,
prove RH, construct a finite zero truncation, prove the explicit formula,
prove either analytic bound, Gallagher evidence, either OTSA bridge, or
Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS257.TriangleSplineMellinSpectralSummand
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS257
git diff --check
```

## Expected Audit Result

The build succeeds.  The TS257 directory contains no placeholder proofs, no
forbidden declarations, and no non-ASCII characters.  `git diff --check`
reports no whitespace errors.
