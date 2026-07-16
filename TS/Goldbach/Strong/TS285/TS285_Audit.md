# TS285 Audit - Riemann Xi Finite Quotient Assembly

## Scope

TS285 constructs the finite analytic quotient for the complete xi-zero
specification from TS284 and activates the canonical TS280 Jensen estimates
for the actual xi candidate.

## Quotient construction

For a TS282 finite-zero specification `S`, the module defines the product of
all selected factors except a distinguished root `rho`:

```text
xiComplementaryZeroPolynomial S rho z.
```

This product is analytic everywhere and nonzero at `rho`.  The local normal
form stored by `S` supplies an analytic nonzero factor at each selected root.
The global quotient is then defined by:

```text
xiRootLocalQuotient S z z                  if z is a selected root,
riemannXiCandidate z / zeroPolynomial z    otherwise.
```

The complement of the finite root set is open.  Near a selected root, the
complement of the erased root set excludes all other roots, and the local
normal form cancels the distinguished powered factor.  Therefore the two
quotient expressions agree in a neighborhood of every root.

## Proved properties

The module proves:

* `riemannXiFiniteQuotient` is analytic at every complex point;
* `riemannXiCandidate = zeroPolynomial * quotient` globally;
* the quotient is nonzero throughout the analytic closed ball;
* every positive inner radius yields a concrete
  `XiBufferedQuotientAssembly` and `XiBufferedFactorizationConstruction`.

The construction is finite and local.  It does not use a global Hadamard or
Weierstrass product.

## Jensen activation

TS285 exposes the actual xi-candidate theorems:

```text
riemannXi_finiteJensenBoundaryEstimate_canonical
riemannXi_finiteJensenMultiplicityCount_le_canonical
```

These consume the generic TS282/TS280 facades with the newly constructed
quotient.  The canonical boundary norm remains noncomputable and no explicit
radius-growth estimate is claimed.

## Non-claims

TS285 does not prove effective xi growth, a quantitative zero-counting bound,
the explicit formula, Gallagher, an OTSA bridge, or Goldbach.

## Verification

Canonical build target:

```powershell
lake build TS.Goldbach.Strong.TS285.RiemannXiFiniteQuotientAssembly
```

Static checks:

```powershell
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS285
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS285
git diff --check
```

Expected result: the build succeeds and all scans print no matches.
