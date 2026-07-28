# TS309 Audit: Meromorphic Rectangle Residue Theorem

## Scope

TS309 closes the global finite residue theorem for the Perron rectangle. It
consumes the complete local census from TS308 and proves that the normalized,
positively oriented rectangle boundary integral equals

```text
x/2 - realHeightZeroContribution + exceptionalResidueContribution.
```

The locked Mathlib revision has Cauchy-Goursat for a differentiable function
on a rectangle, but no ready theorem that accepts a finite set of certified
simple poles. TS309 therefore proves the required finite meromorphic theorem
by explicit principal-part subtraction.

It does not prove Perron inversion or the passage to an infinite explicit
formula.

## Rectangle orientation

`rectangleBoundaryIntegral f a b c d` uses the exact positive orientation

```text
bottom - top + I * right - I * left.
```

The module proves that this expression agrees with
`TS293.Goldbach.perronRectangleBoundaryIntegral`, including the `ds = I dt`
factors on the vertical sides. After division by `2*pi*I`, it also agrees
with `normalizedPerronRectangleBoundary`.

## Simple-pole kernel

For

```text
simplePoleKernel p z = 1 / (z - p),
```

TS309 first evaluates the four sides of a square centered at zero. The odd
real part integrates to zero, while the even Cauchy kernel integrates to
`pi/2` on each quarter contribution. Hence the square boundary integral is
exactly `2*pi*I`.

Translation moves the result to a square centered at an arbitrary pole.
Repeated Cauchy-Goursat deformation through four pole-free strips then proves
that the kernel integral is `2*pi*I` on every rectangle containing the pole
strictly in its interior. No winding-number or Laurent-series API is used.

## Finite regularization

Given a finite pole set `S` and one `PerronLocalResidueData` certificate at
each point, TS309 defines the finite principal part

```text
sum p in S, residue(p) / (z - p).
```

Away from `S`, the regularized Perron integrand is the original integrand
minus this sum. At a pole, it is filled by the certified analytic regular
part minus the principal parts of the other poles.

The local punctured-neighborhood identity from each certificate proves that
this piecewise function is analytic at the pole. Regularity away from `S`
is immediate from the original integrand and the rational principal parts.
Consequently Cauchy-Goursat gives zero boundary integral for the regularized
function.

Linearity and the simple-pole kernel calculation yield the generic theorem

```text
finite_simple_pole_rectangle_residue_theorem
```

with conclusion

```text
boundaryIntegral f = (2*pi*I) * sum p in S, residue(p).
```

## TS308 instantiation

`completeCensusResidueData` converts the dependent local certificates in
`CompletePerronResidueCensus` into the single family required by the generic
theorem. It dispatches exactly among:

- the main pole `1`;
- the exceptional poles `0` and `-1`;
- the image of the concrete nontrivial zeros.

The total Finset is partitioned without overlap. The zero image is reindexed
back to the concrete zero Finset, and the exceptional sum is reindexed back
to the TS306 inventory. The resulting residue sum is exactly the accounting
identity already proved by TS308; no residue is recomputed or inserted by
convention.

The interior regularity supplied by TS308 is extended to the closed rectangle
by a four-case boundary analysis using `PerronBoundaryAnalyticData`.

## Final theorem

For every positive natural `x` and every quantitative clean contour `D`,

```text
canonical_triangleSplineRectangleResidueStatement
```

inhabits `TS293.Goldbach.TriangleSplineRectangleResidueStatement` for the
canonical TS308 census. Thus the formerly named rectangle-residue obligation
is now unconditional.

## Non-claims

TS309 does not prove:

- Mellin-Perron inversion on the infinite right line;
- the infinite explicit formula;
- the final spectral limit assembly;
- Gallagher, OTSA, or Goldbach.

## Hygiene

The implementation contains no `sorry`, `axiom`, `opaque`, or `admit`
declaration.
