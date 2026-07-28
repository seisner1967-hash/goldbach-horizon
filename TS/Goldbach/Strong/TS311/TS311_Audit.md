# TS311 Audit - Infinite Explicit Identity

## Scope

TS311 passes the unconditional truncated Perron identity of TS310 to the
infinite-height limit along the quantitative finite-grid contours of TS299.
It is a limit-assembly module: no new density estimate, zero-counting theorem,
Gamma estimate, or contour theorem is introduced.

The primary theorem keeps the exceptional residues and the fixed-left
improper integral separate.  Their sum is also exported as an aggregated
facade for downstream modules.

## Canonical sequence

The contour at sequence index `T` is

```text
finiteGridStrongPerronContourData (T + 1).
```

Its real height is strictly larger than `T + 1`, hence tends to infinity.
The shift guarantees every contour is admissible without a separate initial
case.

## Routed limits

TS311 assembles the following previously closed inputs:

- the natural zero truncations converge to `infiniteZeroContribution` (TS292);
- the natural-height to selected-height correction is squeezed by the closed
  TS294 logarithmic tail envelope;
- the complete bottom-minus-top horizontal pair tends to zero (TS304);
- the selected fixed-left truncations converge to the absolutely integrable
  `fixedLeftBoundaryLimit` (TS305 and TS307);
- the right-line cutoff is squeezed by the TS298 `1 / tau` estimate;
- the exceptional contribution is exactly independent of the contour by the
  symbolic TS306 residue identity.

No direct use of the zero-counting function appears in TS311.  Its earlier
uses are encapsulated by the terminal convergence theorems above.

## Sign of the left boundary

TS293 defines the non-right boundary as

```text
bottom - top - leftForward.
```

The contour residual contains the negative normalized non-right boundary.
The two minus signs therefore make the limiting fixed-left contribution
positive:

```text
normalizeContourIntegral (fixedLeftBoundaryLimit x).
```

## Canonical expanded identity

For every positive natural `x`, TS311 proves the complex identity

```text
weightedSum(x)
  = x/2
    - infiniteZeroContribution(x)
    - zeta'(0)/zeta(0)
    + x^(-1) * zeta'(-1)/zeta(-1)
    + normalizeContourIntegral(fixedLeftBoundaryLimit(x)).
```

The corresponding real identity is obtained by applying `Complex.re` to this
theorem.  The special value at zero remains in symbolic logarithmic-derivative
form; its classical rewriting as `-log(2*pi)` is deliberately outside TS311.

## Aggregated facade and bound

`infiniteContourResidualComplex` combines only

```text
infiniteExceptionalResidueContribution(x)
  + normalizeContourIntegral(fixedLeftBoundaryLimit(x)).
```

The canonical theorem remains the expanded one.  The aggregate is accompanied
by the componentwise bound

```text
concreteExceptionalResidueBound(x)
  + fixedLeftUniformBound(x) / (2*pi).
```

In particular, the aggregate is not claimed to be `O(x^(-3/2))`: it contains
the constant residue at `s = 0` and the inverse-scale residue at `s = -1`.

## Fail-closed boundary

TS311 does not prove:

- the closed-form evaluation of `zeta'(0)/zeta(0)`;
- Gallagher's estimate;
- the OTSA bridge;
- Goldbach.

## Integrity checks

- no `sorry`, `axiom`, `opaque`, or `admit` is introduced;
- no Riemann Hypothesis or local zero-density hypothesis is used;
- the fixed-left limit is retained and not silently discarded;
- the compact identity is a rewrite of the expanded theorem, not a second
  limit argument.

## Build verification

- targeted: `lake build TS.Goldbach.Strong.TS311.InfiniteExplicitIdentity`
  completed at `3032/3032`;
- global: `lake build` completed at `2664/2664`;
- the TS311 source scan found no unchecked placeholder.

