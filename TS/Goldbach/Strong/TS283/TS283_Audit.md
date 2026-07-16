# TS283 Audit - Riemann Xi Finite Zero Geometry

## Scope

TS283 constructs the finite geometric zero data needed before analytic
multiplicities and quotient assembly can be added to the TS282 xi
factorization specification.

## Closed discreteness and compact finiteness

The module defines the global zero set of `riemannXiCandidate`.  Entirety from
TS282 and the nonzero value `xi(0) = 1/2` exclude local identically-zero
behavior.  The isolated-zero dichotomy then proves that the zero set is closed
and discrete.

As in TS265, the subtype inclusion tends from the cofinite filter to the
cocompact filter.  Therefore every compact intersection with the xi-zero set
is finite.  In particular, the module constructs the exact noncomputable
`Finset`:

```text
riemannXiCandidateZerosInClosedBall T
```

with membership equivalent to `abs z <= T` and `riemannXiCandidate z = 0`.

## Explicit zero-free collar

For a prescribed positive inner radius `r`, set `T = r + 3`.  TS283 forms the
finite set of xi-zero radii strictly below `T`, inserts `r`, and takes its
maximum `L`.  Finiteness gives `L < T`.  The explicit radii

```text
R = (2 * L + T) / 3
S = (L + 2 * T) / 3
```

satisfy `r < R < S < T`.  Every xi zero of modulus at most `S` has modulus at
most `L`, so the closed collar `R <= abs z <= S` contains no xi zero.

## Constructed data

`XiFiniteZeroGeometryData` records:

* a genuine TS275 `JensenDiskConfiguration` centered at zero;
* exact finite inner and factor zero selections;
* inclusion of the inner selection in the factor selection;
* the inner-disk and factor open-disk bounds;
* exact zero membership throughout the analytic closed ball;
* nonvanishing of xi on the full averaging-to-analytic collar.

`xiFiniteZeroGeometryData r hr` constructs these data for every `0 < r`.

## Non-claims

TS283 does not construct analytic multiplicities, prove local normal forms,
assemble the analytic nonvanishing quotient, prove effective xi growth, prove
a zero-counting estimate, prove the explicit formula, prove Gallagher, close
an OTSA bridge, or claim Goldbach.

## Verification

Canonical build target:

```powershell
lake build TS.Goldbach.Strong.TS283.RiemannXiFiniteZeroGeometry
```

Static checks:

```powershell
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS283
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS283
git diff --check
```

Expected result: the build succeeds and all scans print no matches.
