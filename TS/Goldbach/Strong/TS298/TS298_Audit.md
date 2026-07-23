# TS298 Audit - Right-Line Cutoff and Horizontal Integration

## Scope

TS298 closes the Perron cutoff on the fixed absolutely convergent line
`re(s) = 2` and integrates the exact TS297 pointwise envelopes over the two
fixed horizontal sides. It routes both reductions into the TS294 contour
component interface.

The left side, exceptional residues, and the three unresolved horizontal
rates remain explicit inputs. No contour identity is populated by defining a
residual tautologically.

## Results proved

### Absolutely convergent right line

The explicit real constant

```text
rightLineVonMangoldtMass
  = sum_n |LSeries.term vonMangoldt 2 n|
```

is finite by the Mathlib absolute-convergence theorem for the von Mangoldt
L-series. On `s = 2 + it`, TS298 proves:

```text
|LSeries vonMangoldt s| <= rightLineVonMangoldtMass,
|x^s| = x^2,
|1 / (s(s+1))| <= 1 / (1+t^2).
```

The resulting Perron integrand is continuous and integrable on the full real
line.

### Exact cutoff tail and closed bound

The difference between the full and finite right-line Perron integrals is
identified with the integral over the complement of `(-tau,tau]`. The two
tails satisfy

```text
integral_{|t| > tau} 1 / (1+t^2) dt <= 2 / tau.
```

After the exact contour normalization, this gives

```text
|rightCutoff(x,D)|
  <= rightLineCutoffConstant * max(1,x^2) / D.tau,

rightLineCutoffConstant
  = rightLineVonMangoldtMass / pi.
```

For the canonical TS296 strong height, `D.tau >= T`, hence

```text
|rightCutoff(x,T)|
  <= rightLineCutoffConstant * max(1,x^2) / T.
```

This estimate is unconditional and independent of the unresolved clean-gap
rate.

### Integrated horizontal reduction

`HorizontalUniformEnvelopeData` records uniform upper bounds for the exact
TS297 top and bottom pointwise envelopes on the fixed interval
`[-3/2,2]`. TS298 proves that this interval has width exactly `7/2` and
deduces

```text
|topIntegral|    <= (7/2) * topBound,
|bottomIntegral| <= (7/2) * bottomBound.
```

No asymptotic estimate is hidden in this structure: its fields still expose
the reciprocal zero load, local logarithm sphere bound, and completion
correction through the TS297 envelopes.

### TS294 routing

`integratedHorizontalNonRightSideBounds` fills the top and bottom fields of
`TS294.PerronNonRightSideBounds`, leaving the fixed-left estimate as an
explicit certificate. `canonicalContourComponentBounds` additionally fills
the unconditional right-cutoff field of
`TS294.TriangleSplineContourComponentBounds`, while retaining a separately
certified exceptional-residue bound.

The existing TS294 residual theorem is then available through
`canonicalContourResidualComplex_norm_le`.

## Dependency hygiene

The right-line proof uses only absolute convergence of the von Mangoldt
L-series, elementary complex norms, and real improper-integral comparison.
The horizontal proof consumes the exact TS297 pointwise theorems and the
fixed TS294 geometry. It does not use a zero-density rate, Borel-Caratheodory,
Stirling, an infinite Hadamard product, or contour residues.

## Open frontier

The following remain intentionally unproved:

- a uniform closed rate for the horizontal envelopes;
- a closed rate for the reciprocal zero load;
- an effective local logarithm sphere rate;
- a completion-correction rate;
- the fixed-left boundary estimate;
- completeness and evaluation of the exceptional residue inventory;
- Perron inversion and the meromorphic rectangle residue theorem;
- an infinite explicit formula;
- Gallagher, OTSA, or Goldbach.

## Verification

- Target build: `2992/2992`.
- Global build: `2664/2664`.
- No `sorry`, `axiom`, or `opaque` declarations in TS298.
- Source and audit are ASCII-only.
- Git whitespace validation is clean.
