# TS289 Audit - Closed Completed-Zeta Theta Integral Bound

## Scope

TS289 turns the unconditional radial theta-Mellin majorant from TS288 into
an explicit elementary function of the radius.  It uses the exact modified
kernel already present in Mathlib and introduces no new analytic hypothesis.

For every `R >= 2`, the main bound is:

```text
completedZetaThetaMellinMajorant(R)
  <= (2 / (1 - exp(-pi))) * exp(R * log(R + 2)).
```

## Exact kernel algebra

For `x > 1`, the modified kernel is the nonconstant part of the even Jacobi
theta kernel:

```text
completedZetaModifiedThetaKernel(x) = evenKernel(0,x) - 1.
```

The integer theta sum is split into its nonnegative and negative parts.  This
gives an exact identity with `2 * F_nat 0 1 x`, preserving both copies of
every nonzero integer term.

The strong functional-equation pair also gives the exact inversion law:

```text
K(1/x) = x^(1/2) * K(x),  x > 0.
```

Thus the rapid decay at zero is not replaced by the false crude estimate
`x^(-1/2)`; the cancelling theta tail is retained exactly.

## Exponential right tail

Mathlib's geometric theta estimate yields, for `x > 1`:

```text
norm K(x) <= 2 * exp(-pi*x) / (1 - exp(-pi*x)).
```

Monotonicity of the denominator then gives the uniform closed bound on
`[1,infinity)`:

```text
norm K(x) <= Ctheta * exp(-pi*x),
Ctheta = 2 / (1 - exp(-pi)).
```

The value at `x = 1` is zero by the deliberate gap in `f_modif`, so the
closed endpoint is handled without a limiting argument.

## Tail inversion

The substitution theorem `integral_comp_rpow_Ioi` with exponent `-1` proves
the exact identity:

```text
integral_(0,1) x^(-R/2-1) * norm K(x)
  = integral_(1,infinity) x^(R/2-1/2) * norm K(x).
```

The radial maximum from TS288 equals the lower endpoint power on `(0,1)` and
the upper endpoint power on `[1,infinity)`.  The original upper exponent
`R/2-1` is bounded by `R/2-1/2` on the right half-line.  Consequently both
halves of the TS288 integral are controlled by the same upper tail.

## Elementary closed envelope

No Stirling formula is needed.  For `R >= 2`, applying
`log y <= y - 1` to `y = x/(R+2)` gives:

```text
x^(R/2-1/2) * exp(-pi*x)
  <= exp(R*log(R+2)) * exp(-x).
```

The remaining integral over `(1,infinity)` is `exp(-1) <= 1`.  Combining
this with the kernel constant proves the main closed bound.

## Jensen routing

TS289 defines:

```text
completedZetaThetaClosedMajorant
completedZetaThetaClosedCircleGrowth
xiThetaClosedBoundaryNormStatement
xi_finiteJensenBoundaryEstimate_thetaClosed
xi_zero_count_le_thetaClosed_majorant
```

The closed function therefore fills the TS287 completed-zeta circle-growth
contract and reaches the concrete xi/Jensen multiplicity count with no
remaining growth input.

## Non-claims

TS289 does not prove a sharp Riemann-von Mangoldt asymptotic, transport from
the finite xi disk count to the TS270 global multiplicity-count contract, the
explicit formula, Gallagher, an OTSA bridge, or Goldbach.

## Verification

Canonical build target:

```powershell
lake build TS.Goldbach.Strong.TS289.CompletedZetaThetaIntegralClosedBound
```

Static checks:

```powershell
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS289
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS289
git diff --check
```

Expected result: the build succeeds and all scans print no matches.
