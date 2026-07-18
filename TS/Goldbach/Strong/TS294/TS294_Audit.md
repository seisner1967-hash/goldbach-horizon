# TS294 Audit - Quantitative Clean Contour Estimates

## Scope

TS294 refines the TS293 contour interface and proves the exact quantitative
assembly theorem.  It keeps the two error mechanisms separate:

```text
TS292: spectral cutoff adjustment
TS294: exceptional residues + boundary integrals + right-line cutoff
```

The TS292 tail is used only for the spectral component.  It is not presented
as a bound for a contour integral.

## Fixed geometry

The first effective rectangle is fixed at

```text
left  = -3/2
right = 2.
```

The elementary inequalities `left < -1` and `1 < right` are proved, and zeta
nonvanishing on the right edge follows from Mathlib's
`riemannZeta_ne_zero_of_one_lt_re`.

`QuantitativelyCleanPerronContourData` extends the TS293 clean contour with:

* the two fixed-edge identities;
* a positive separation parameter;
* separation from every concrete nontrivial zero with height at most `T+2`.

This distinction is essential.  Pointwise nonvanishing on a compact side does
not by itself provide an effective bound for `zeta'/zeta`.

## Spectral adjustment

For `tau >= T`, the exact TS293 adjustment is proved to be

```text
- sum over {rho : T < |Im rho| <= tau}.
```

The finite shell is reindexed into the TS292 complementary subtype.  The
uniform finite-tail theorem then gives the unconditional bound

```text
norm(spectralHeightCutoffAdjustment(x,T,tau))
  <= max(1,x)
     * infiniteZeroResidualTailConstant
     * logarithmicTailRate(T).
```

No infinite-series subtraction or contour estimate is used in this proof.

## Non-right boundary

`PerronNonRightSideBounds` records independent norm bounds for the bottom,
top, and left integrals.  TS294 proves:

```text
norm(nonRightBoundary)
  <= bottomBound + topBound + leftBound
```

and, after the exact TS293 normalization,

```text
norm(normalizedNonRightBoundary)
  <= (bottomBound + topBound + leftBound) / (2*pi).
```

Thus the normalization constant is not hidden in a later contract.

## Full residual assembly

`TriangleSplineContourComponentBounds` contains only the three remaining
analytic inputs:

1. a bound for the certified exceptional-residue sum;
2. bounds for the three non-right sides;
3. a bound for the right-line cutoff.

The spectral component is not a field: it is supplied automatically by
TS292.  TS294 proves both the complex norm estimate and the real absolute
estimate for the exact TS293 residual:

```text
abs(triangleSplineContourResidual(x,T))
  <= exceptionalBound
     + normalizedNonRightBound
     + rightCutoffBound
     + spectralHeightAdjustmentEnvelope(x,T).
```

The residual remains the concrete TS293 object.  It is never redefined as the
difference between the two sides of an intended explicit formula.

## Locked analytic boundary

The locked Mathlib revision supplies right-half-plane zeta nonvanishing and
the finite integral/norm algebra used here.  It does not supply the required
effective horizontal and left-edge estimates for `zeta'/zeta`.

TS290 proves a cumulative `O(T log T)` zero count.  That theorem does not
silently imply the sharper local density estimate often used to choose a
classical clean height.  Quantitative clean-height existence therefore
remains a named proposition.

## Non-claims

TS294 does not prove:

* quantitative clean-height existence;
* horizontal or left-edge logarithmic-derivative bounds;
* the right-line cutoff estimate;
* completeness of the exceptional residue inventory;
* Perron inversion;
* the meromorphic rectangle residue theorem;
* an infinite explicit formula;
* Gallagher, OTSA, or Goldbach.

The intended continuation is:

```text
TS295: targeted zeta'/zeta and right-line component estimates
TS296: Perron inversion and residue-inventory completeness
TS297: infinite explicit formula using the independent TS292 tail
```

## Verification

Canonical build target:

```powershell
lake build TS.Goldbach.Strong.TS294.QuantitativeCleanContourEstimates
```

Static checks:

```powershell
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS294
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS294
git diff --check
```

Expected result: the build succeeds and all static scans print no matches.
