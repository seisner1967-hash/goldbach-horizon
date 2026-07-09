# TS234 Audit - Laplace Boundary Uniform Limit Discharge

## Scope

TS234 discharges the second analytic obligation isolated by TS232:

```lean
TS232.Goldbach.LaplaceBoundaryUniformLimitStatement
```

It proves that the TS231 finite Laplace boundary term, after integration over
the compact parameter interval `[b, A]`, tends to zero as `T -> +infty`.

## Main theorem

```lean
theorem TS234.Goldbach.laplaceBoundaryUniformLimit :
    TS232.Goldbach.LaplaceBoundaryUniformLimitStatement
```

For `0 < b` and `b < A`, this is the statement:

```lean
Tendsto
  (fun T : Real =>
    intervalIntegral
      (fun s : Real =>
        Real.exp (-(s * T)) *
          (s * Real.sin T + Real.cos T) /
            (1 + s ^ 2))
      b
      A
      volume)
  atTop
  (nhds (0 : Real))
```

## Proof strategy

TS234 defines the boundary kernel

```lean
laplaceBoundaryKernel s T =
  exp (-(s*T)) * ((s * sin T + cos T) / (1 + s^2))
```

and proves the pointwise bound on `s in uIoc b A`, for `0 < b < A` and
`0 <= T`:

```lean
|laplaceBoundaryKernel s T| <= exp (-(b*T)) * (A + 1)
```

The ingredients are:

- `b <= s <= A` on the unordered interval `uIoc b A`;
- `|sin T| <= 1` and `|cos T| <= 1`;
- `1 <= 1 + s^2`;
- `exp (-(s*T)) <= exp (-(b*T))` when `0 <= T`.

The interval-integral norm bound then gives

```lean
|int_b^A laplaceBoundaryKernel s T ds|
  <= (exp (-(b*T)) * (A + 1)) * |A - b|
```

and the scalar majorant tends to zero because `b > 0`.

## Non-claims

TS234 does not prove `TS232.Goldbach.DampedDifferenceAtTopStatement`.

TS234 does not prove `TS232.Goldbach.AuxiliaryDampingUniformBoundStatement`.

TS234 does not prove `TS232.Goldbach.CorrectedFubiniExecutionStatement`.

TS234 does not prove `TS229.Goldbach.DampedDirichletEvaluationTarget`.

TS234 does not prove any Abel-to-cutoff bridge, Dirichlet cutoff value,
cos-square value, canonical sinc-fourth value, Plancherel evidence, explicit
formula input, Gallagher estimate, or Goldbach statement.

## Verification commands

```powershell
lake build TS.Goldbach.Strong.TS234.LaplaceBoundaryUniformLimitDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS234
git diff --check
```

## Expected audit result

The TS234 directory contains no placeholder proofs, no forbidden declarations,
and no non-ASCII characters.  `git diff --check` reports no whitespace errors.
