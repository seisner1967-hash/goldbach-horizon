# TS258 Audit

## Scope

TS258 proves the conjugation law for the concrete triangle-spline zero
summand and derives the reality of each finite TS256 zero sum from one explicit
premise: multiplicities are invariant under conjugation.

## Proved

- `ZeroMultiplicityConjugationInvariantStatement` names the missing TS185
  premise without adding it as a postulate.
- `triangleSplineZeroSpectralSummand_star` proves conjugation compatibility of
  `X^rho / (rho * (rho + 1))`.
- `truncation_zeros_star_mem` proves that TS256 truncations are conjugation
  closed using TS185 closure and TS256 completeness.
- `triangleSplineZeroTruncatedComplexSum_star` proves that the weighted finite
  sum is fixed by conjugation under multiplicity invariance.
- `triangleSplineZeroTruncatedComplexSum_im_eq_zero` proves that the finite sum
  has zero imaginary part.
- `truncatedZeroSumReality_of_multiplicity_conjugation` discharges the TS256
  reality target conditionally on the named multiplicity premise.
- `triangleSplineZeroContributionFunction_coe_eq_complexSum` proves that the
  real projection used by TS255 loses no information under that premise.

## Not proved

- Multiplicity invariance under conjugation is not derived from TS185.
- TS185 is not modified.
- No Mellin integral evaluation is claimed.
- No explicit-formula identity is proved.
- No zero-contribution or residual bound is proved.
- No Gallagher estimate or Goldbach statement is proved.

## Commands

```powershell
lake build TS.Goldbach.Strong.TS258.ZeroSummandConjugationFiniteReality
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS258
git diff --check
```

The scan is expected to return no matches.
