# TS307 Audit: Fixed-Left Archimedean Logarithmic Rate

## Scope

TS307 closes the sole analytic input left open by TS305. It proves a
logarithmic bound for the explicit reflection correction on the line
`Re(s) = 5/2`, constructs an unconditional
`TS305.FixedLeftArchimedeanBoundData`, and routes it into the fixed-left
boundary results and the TS298 contour interface.

The proof uses Euler's finite `Complex.GammaSeq`. It does not use Binet's
formula, Stirling asymptotics, a digamma API, or a Weierstrass product.

## Finite Gamma logarithmic derivative

For `n != 0` and `0 < Re(s)`, the module proves that `GammaSeq(s,n)` is
nonzero and differentiable, and establishes the exact identity

```text
logDeriv (GammaSeq(.,n)) s
  = log(n) - sum_{j=0}^n 1/(s+j).
```

The proof differentiates the finite power-product quotient directly. No
limit or infinite product is involved at this stage.

## Locally uniform Euler convergence

Mathlib's pointwise `GammaSeq_tendsto_Gamma` is strengthened to
`TendstoLocallyUniformlyOn` on `Re(s) > 0`.

On a compact real-part strip `delta <= Re(s) <= upper`, the Euler integral is
dominated by

```text
exp(-x) * (x^(delta-1) + x^(upper-1)).
```

The finite Euler coefficient converges pointwise to `exp(-x)` and is bounded
between `0` and `exp(-x)`. Dominated convergence therefore yields a scalar
error integral tending to zero, uniformly for every `s` in the strip. This
supplies exactly the locally uniform hypothesis required by
`Complex.logDeriv_tendsto`.

Consequently the finite logarithmic derivatives converge to
`logDeriv Complex.Gamma s` throughout the right half-plane.

## Harmonic cutoff

At the reflected point `s = 5/2 - i*t`, TS307 uses

```text
J(t) = ceil(|t| + 2).
```

The finite identity is rewritten using

```text
1/(j+1) - 1/(s+j) = (s-1)/((j+1)(s+j)).
```

The terms below `J` are bounded by twice the harmonic kernel. The terms from
`J` onward are bounded by `J/(j+1)^2`; a finite telescoping estimate bounds
this quadratic tail by `1`. The elementary harmonic estimates then give

```text
norm (logDeriv Gamma (5/2-i*t))
  <= 7 * (1 + log(|t|+2)).
```

No Euler constant is evaluated or introduced.

## Trigonometric correction

The module proves exactly

```text
norm (tan (pi * (5/2-i*t) / 2)) = 1.
```

The proof uses conjugation, tangent periodicity, and the identity
`tan(pi/4 + i*y) * tan(pi/4 - i*y) = 1`. Hence the trigonometric contribution
has constant norm `pi/2`.

## Reflection correction

The logarithmic derivative of the TS305 reflection factor is computed
exactly:

```text
zetaLeftReflectionCorrection(s)
  = -log(2*pi) + logDeriv Gamma(s) - (pi/2) * tan(pi*s/2).
```

At `s = 5/2-i*t`, the preceding Gamma and tangent estimates produce the
closed constant

```text
fixedLeftArchimedeanConstant
  = norm(log(2*pi)) + 7 + pi/2.
```

Thus `fixedLeftArchimedeanBoundData` unconditionally inhabits the contract
introduced by TS305.

## TS305 and TS298 routing

The module exports unconditional forms of:

- absolute integrability of the fixed-left Perron integrand;
- convergence of symmetric truncations to the fixed improper integral;
- a height-independent bound for the fixed-left limit;
- vanishing of the strong-height truncation residual;
- `TS298.FixedLeftSideBoundData` for every `T >= 1`.

The fixed-left limit is not claimed to vanish. Only its truncation residual
tends to zero, exactly as required by TS305.

## Non-claims

TS307 does not prove:

- a sharp `log(T)/T` rate for the fixed-left truncation tail;
- exhaustive classification of singularities in the Perron rectangle;
- Perron inversion;
- the meromorphic rectangle residue theorem;
- an infinite explicit formula;
- Gallagher, OTSA, or Goldbach.

## Hygiene

The module and audit are ASCII. The implementation contains no `sorry`,
`axiom`, `opaque`, or `admit` declaration.
