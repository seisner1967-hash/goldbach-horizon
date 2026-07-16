# TS284 Audit - Riemann Xi Multiplicity and Local Normal Form

## Scope

TS284 enriches the finite xi-zero geometry from TS283 with the canonical
analytic multiplicities and local normal forms required by the exact TS282
`XiFiniteZeroFactorizationSpec`.

## Canonical multiplicity

The module defines

```text
riemannXiCandidateMultiplicity(rho) =
  (riemannXiCandidate_analyticAt rho).order.toNat.
```

TS283 excludes eventual local vanishing at every point, so
`AnalyticAt.order_eq_top_iff` proves that this order is never top.  At an
actual xi zero, order zero would give a local factor analytic and nonzero at
the point while the factorization evaluates to zero, a contradiction.
Consequently the natural multiplicity is strictly positive at every xi zero.

The coercion theorem

```text
(riemannXiCandidateMultiplicity rho : ENat) =
  (riemannXiCandidate_analyticAt rho).order
```

follows from `ENat.coe_toNat` and finite order.

## Local normal form

Mathlib's `AnalyticAt.order_eq_nat_iff` supplies an analytic function `h`,
nonzero at `rho`, such that eventually near `rho`:

```text
riemannXiCandidate z =
  (z - rho) ^ riemannXiCandidateMultiplicity rho * h z.
```

This normal form is available at every point; positivity of its exponent is
used only when the point is an actual zero.

## TS282 assembly

For every positive inner radius, `xiFiniteZeroFactorizationSpec` combines:

* the exact TS283 configuration and finite zero selections;
* `riemannXiCandidateMultiplicity`;
* strict positivity on selected factor zeros;
* the exact local normal form.

It is a genuine `TS282.Goldbach.XiFiniteZeroFactorizationSpec`, not a new
parallel contract.

## Non-claims

TS284 does not assemble the finite analytic quotient, prove it nonvanishing on
the buffered disk, prove effective xi growth, prove a zero-counting estimate,
prove the explicit formula, prove Gallagher, close an OTSA bridge, or claim
Goldbach.

## Verification

Canonical build target:

```powershell
lake build TS.Goldbach.Strong.TS284.RiemannXiMultiplicityAndLocalNormalForm
```

Static checks:

```powershell
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS284
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS284
git diff --check
```

Expected result: the build succeeds and all scans print no matches.
