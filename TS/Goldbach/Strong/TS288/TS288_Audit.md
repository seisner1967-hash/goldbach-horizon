# TS288 Audit - Completed Zeta Theta-Mellin Circle Growth

## Scope

TS288 constructs an unconditional radial circle majorant for Mathlib's
entire regularized completed zeta function.  It uses the same modified theta
kernel and Mellin transform from which Mathlib defines that function.

This route deliberately avoids two unsound or fragile reductions:

* the functional equation does not move the critical line into a right
  half-plane;
* Gamma and ordinary zeta should not be bounded separately across the poles
  whose cancellations make the completed function entire.

## Exact Mellin representation

The ASCII kernel alias is:

```text
completedZetaModifiedThetaKernel =
  (HurwitzZeta.hurwitzEvenFEPair 0).f_modif.
```

The module proves definitionally:

```text
completedRiemannZetaZero(s)
  = mellin completedZetaModifiedThetaKernel (s / 2) / 2.
```

The associated strong functional-equation pair supplies Mellin convergence
at every complex exponent.

## Radial envelope

For `x > 0` and `abs s = R`, TS288 proves:

```text
abs ((x : Complex) ^ (s / 2 - 1))
  <= max (x ^ (R / 2 - 1)) (x ^ (-R / 2 - 1)).
```

The proof uses `abs (re s) <= abs s` and the opposite exponent monotonicity
of real powers on `(0, 1]` and `[1, infinity)`.

Both endpoint envelopes are integrable because the modified theta kernel has
a Mellin transform at `R / 2` and `-R / 2`.  Their maximum is therefore
integrable as well.

## Constructed majorant

The radial function is:

```text
completedZetaThetaMellinMajorant(R)
  = (1 / 2) * integral over x > 0 of
      max (x ^ (R / 2 - 1)) (x ^ (-R / 2 - 1))
        * norm(completedZetaModifiedThetaKernel(x)).
```

It is nonnegative and satisfies, for every radius:

```text
abs s = R ->
  abs completedRiemannZetaZero(s)
    <= completedZetaThetaMellinMajorant(R).
```

Consequently TS288 constructs a genuine
`TS287.Goldbach.CompletedZetaZeroCircleGrowthStatement` rather than adding a
new analytic hypothesis.

## Jensen routing

The new majorant is routed through TS287 and the complete xi factorization:

```text
xiThetaMellinBoundaryNormStatement
xi_finiteJensenBoundaryEstimate_thetaMellin
xi_zero_count_le_thetaMellin_majorant
```

Thus the finite xi-zero multiplicity count now has an unconditional,
fully specified theta-integral Jensen budget.

## Non-claims

TS288 does not prove a closed elementary upper bound for the theta integral,
an `exp(C * R * log(R + 2))` envelope, a log-linear zero-counting estimate,
the explicit formula, Gallagher, an OTSA bridge, or Goldbach.

The next quantitative lock is to combine Mathlib's Jacobi-theta exponential
bounds with the piecewise definition of `f_modif` and evaluate the two real
endpoint integrals.

## Verification

Canonical build target:

```powershell
lake build TS.Goldbach.Strong.TS288.CompletedZetaThetaMellinCircleGrowth
```

Static checks:

```powershell
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS288
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS288
git diff --check
```

Expected result: the build succeeds and all scans print no matches.
