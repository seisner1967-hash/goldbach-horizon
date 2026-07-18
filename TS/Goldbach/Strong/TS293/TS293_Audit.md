# TS293 Audit - Truncated Perron Contour Residual

## Scope

TS293 starts the contour side of the explicit formula.  It deliberately keeps
this work separate from the TS292 spectral tail:

```text
TS292 controls Z_infinite(x) - Z_T(x).
TS293 defines the Perron contour residual.
```

The two errors are not identified.

## Concrete objects

The module defines the actual logarithmic-derivative integrand

```text
-(zeta'(s) / zeta(s)) * x^s / (s * (s + 1)).
```

On `re s > 1`, Mathlib's
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`
rewrites it to the von Mangoldt L-series integrand.

The rectangle is positively oriented.  Its bottom, top, right, and left
integrals include the correct `ds` factors and signs.  The full right-line
integral is a genuine Bochner integral over `Real`; the finite cutoff error is
its difference from the finite right side.

## Real contour height

The contour height `tau` is real and is required to lie in `[T,T+1]`.
The exact nontrivial-zero contribution up to `tau` is obtained by filtering a
known finite natural-height zero set.  The adjustment

```text
truncatedContribution(x,T) - realHeightContribution(x,tau)
```

is therefore a concrete finite spectral shell, not an unnamed error.

## Exceptional residues

Poles not represented by the nontrivial-zero sum are supplied through a
finite inventory.  Every entry contains:

* its location;
* its residue coefficient;
* an analytic regular part;
* the local principal-part identity on a punctured neighborhood;
* proof that the pole lies in the open rectangle.

The exceptional contribution is the finite sum of those certified
coefficients.  It is not defined from the desired explicit formula.

## Assembly theorem

Two precise analytic statements remain:

1. `TriangleSplinePerronInversionStatement`;
2. `TriangleSplineRectangleResidueStatement`.

Given those statements, TS293 proves

```text
vonMangoldtTriangleSum(x)
  = x / 2
    - re(truncatedZeroContribution(x,T))
    + triangleSplineContourResidual(x,T).
```

The residual is explicitly the sum of:

```text
exceptional residues
- normalized non-right boundary
+ right-line cutoff
+ exact spectral height adjustment.
```

A scale-indexed contour family routes the identity directly into
`TS255.NamedExplicitFormulaIdentityStatement`.

## Locked Mathlib boundary

Mathlib 4.15 provides:

* the von Mangoldt logarithmic-derivative identity for `re s > 1`;
* zeta nonvanishing there;
* rectangular Cauchy-Goursat for holomorphic functions.

The locked revision does not expose a ready global meromorphic residue theorem
that sums all zeta-zero residues in a rectangle.  TS293 records that missing
step as a real proposition rather than hiding it in a definition.

## Non-claims

TS293 does not prove clean-height existence, Perron inversion, the
meromorphic rectangle residue theorem, a contour residual bound, the infinite
explicit formula, Gallagher, OTSA, or Goldbach.

The intended continuation is:

```text
TS294: clean-height and effective contour estimates
TS295: infinite explicit formula using the independent TS292 tail
```

## Verification

Canonical build target:

```powershell
lake build TS.Goldbach.Strong.TS293.TruncatedPerronContourResidual
```

Static checks:

```powershell
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS293
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS293
git diff --check
```

Expected result: the build succeeds and all static scans print no matches.
