# TS280 Audit - Canonical Boundary Norm

## Scope

TS280 fills the final generic boundary-norm input left after TS279.  For every
already-constructed TS275 `BufferedJensenFactorizationData`, it defines a
canonical finite majorant for `|D.f|` on the averaging sphere and uses it to
obtain the complete finite Jensen counting quotient.

The majorant is noncomputable.  This sprint proves compact existence, not an
effective formula in the radius.

## Canonical majorant

The boundary value set is

```text
{ |D.f z| : |z - center| = averagingRadius }.
```

The canonical norm is

```text
max 1 (sSup boundaryNormValues).
```

This definition is independent of a chosen maximizing point.  The `max 1`
term gives strict positivity required by the TS275 boundary contract.

## Compactness route

1. The complex averaging sphere is compact.
2. The sphere lies in the TS275 analytic closed ball because `R < S`.
3. `D.f_analytic` therefore makes `D.f` continuous on the sphere.
4. Complex absolute value preserves continuity.
5. The boundary norm value set is a continuous image of a compact set.
6. The compact real image is bounded above.
7. Every boundary value is at most its `sSup` by `le_csSup`.

## Main results

The module constructs:

```text
canonicalBoundaryNormStatement
```

which inhabits:

```text
BoundaryNormOnAveragingSphereStatement D (canonicalBoundaryNorm D).
```

It then exposes the two facade theorems:

```text
finiteJensenBoundaryEstimate_canonical
finiteJensenMultiplicityCount_le_canonical
```

Thus, for every supplied buffered factorization datum, the complete finite
Jensen weighted estimate and multiplicity-count quotient are unconditional.

## Meaning of unconditional

The theorem is unconditional relative to an existing value of type
`BufferedJensenFactorizationData`.  TS280 does not construct such data for a
specific analytic function.  In particular, it does not prove completeness
of a concrete factor-zero family or identify concrete analytic
multiplicities.

## Non-claims

- no concrete buffered factorization is constructed
- no maximizing boundary point is computed
- no computable or closed-form boundary majorant is supplied
- no effective dependence on the radius is proved
- no concrete Riemann xi function is defined
- no effective zeta zero-counting estimate is proved
- no explicit formula, Gallagher estimate, or OTSA bridge is proved
- Goldbach is not claimed

## Verification

```powershell
lake build TS.Goldbach.Strong.TS280.CanonicalBoundaryNorm
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS280
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS280
git diff --check
```
