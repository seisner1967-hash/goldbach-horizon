# TS308 Audit: Complete Perron Singularity Census

## Scope

TS308 closes the local and finite singularity census for the fixed Perron
rectangle. It proves regularity away from the enumerated points, constructs
local residue certificates at the main pole and every concrete nontrivial
zeta zero, reuses the exact exceptional inventory from TS306, and packages
the resulting finite accounting for a future global rectangle theorem.

It does not prove the meromorphic rectangle residue theorem or Perron
inversion.

## Regular points

For `x > 0`, the Perron integrand is analytic at `p` under the four explicit
conditions

```text
p != 1, zeta(p) != 0, p != 0, p != -1.
```

This immediately inhabits the TS306 exceptional-completeness statement for
the concrete inventory `{0, -1}`.

Inside the fixed rectangle, every zeta zero is proved to be a concrete
nontrivial zero. The proof uses the zero-free half-plane on the right, the
functional equation on the left, and the exact values at `0` and `-1`; it
does not assume that a zero has nonzero imaginary part.

## Main pole

The function

```text
zetaPoleRemoved(s) = (s - 1) * zeta(s)
```

is filled at `s = 1` by the zeta residue. It is analytic and nonzero there.
Its logarithmic derivative gives the exact local decomposition of the Perron
integrand as an analytic numerator divided by `s - 1`.

The resulting `PerronLocalResidueData` has residue

```text
(x : Complex) / 2.
```

The main term is therefore certified locally rather than inserted into the
later residue sum by convention.

## Nontrivial zeros

For every concrete nontrivial zero `rho`, the TS264 multiplicity is identified
with the analytic order of zeta. The order factorization theorem supplies a
local analytic nonzero factor `g_rho` satisfying

```text
zeta(s) = (s - rho)^m * g_rho(s).
```

Differentiating this neighborhood identity gives

```text
logDeriv zeta(s) = m / (s - rho) + logDeriv g_rho(s)
```

on a punctured neighborhood. Hence TS308 constructs exact local residue data
at `rho` with residue

```text
-TS292.Goldbach.infiniteZeroSpectralTerm x rho.
```

This is the historical TS292 spectral term itself, not a newly defined
surrogate. Summing the local zero residues therefore yields exactly

```text
-TS293.Goldbach.realHeightZeroContribution x tau.
```

## Finite geometry

The total candidate pole set is the explicit Finset

```text
{1, 0, -1} union realHeightZeroValues(tau).
```

TS308 proves:

- `1` is not a concrete nontrivial zero value;
- `{0, -1}` is disjoint from all nontrivial zero values;
- the main pole, every truncated zero, and both exceptional poles lie
  strictly inside the fixed clean rectangle;
- every strictly interior point outside the total Finset is analytic.

The strict vertical inclusion of the zero values uses the clean top and
bottom edges: equality with either height would contradict the corresponding
zero-free boundary certificate.

## Boundary regularity

`PerronBoundaryAnalyticData` proves analyticity of the integrand at every
point on all four sides:

- top and bottom use the clean-height zero-free fields;
- left uses the fixed zero-free left edge;
- right uses zeta nonvanishing on `Re(s) > 1`.

The kernel poles `0` and `-1`, and the zeta pole `1`, are excluded on each
edge directly from the rectangle geometry.

## Complete census package

`CompletePerronResidueCensus` contains:

- the exact total Finset;
- the main local residue certificate;
- one exact local certificate for every truncated nontrivial zero;
- the main-term-separated exceptional inventory from TS306;
- exceptional completeness;
- strict interior and disjointness certificates;
- regularity off the Finset;
- analytic boundary data;
- the exact residue accounting identity

```text
main residue + zero residues + exceptional residues
  = x/2 - realHeightZeroContribution + exceptionalContribution.
```

This is the complete local input expected by TS309.

## Non-claims

TS308 does not prove:

- a global meromorphic residue theorem on the rectangle;
- equality between the contour integral and the finite residue sum;
- Perron inversion;
- an infinite explicit formula;
- Gallagher, OTSA, or Goldbach.

## Hygiene

The module and audit are ASCII. The implementation contains no `sorry`,
`axiom`, `opaque`, or `admit` declaration.
