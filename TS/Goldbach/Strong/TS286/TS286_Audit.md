# TS286 Audit - Riemann Xi Master API

## Scope

TS286 publishes the stable downstream interface of the concrete xi/Jensen
pipeline completed by TS285.  It deliberately adds no new analytic contract
and does not duplicate the buffered factorization structures.

## Public API

The namespace `TS.Goldbach.MasterAPI` exposes:

```text
xi
xi_entire
xi_zero
xi_one
xi_functional_eq
xi_certificate
xi_geometry
xi_zero_spec
xi_disk_data
xi_factorization
xi_boundary_norm
xi_boundary_norm_positive
xi_abs_le_boundary_norm
xi_finiteJensenBoundaryEstimate_canonical
xi_zero_count_le_log_budget
```

Every definition is a thin alias to the concrete TS282--TS285 construction.
Every theorem is proved by the existing implementation.  Downstream modules
therefore need not depend on the details of the finite complementary product,
the removable-value filling, or the quotient nonvanishing proof.

## Boundary type correction

`xi_boundary_norm` is real-valued:

```text
xi_boundary_norm (r : Real) (hr : 0 < r) : Real.
```

This matches `TS280.Goldbach.canonicalBoundaryNorm`.  No `ENNReal` coercion is
introduced.  The pointwise facade `xi_abs_le_boundary_norm` is the intended
substitution point for a future explicit radius-growth estimate.

## Non-claims

TS286 does not prove an effective xi growth estimate, quantitative zero
counting, the explicit formula, Gallagher, an OTSA bridge, or Goldbach.

## Verification

Canonical build target:

```powershell
lake build TS.Goldbach.Strong.TS286.RiemannXiMasterAPI
```

Static checks:

```powershell
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS286
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS286
git diff --check
```

Expected result: the build succeeds and all scans print no matches.
