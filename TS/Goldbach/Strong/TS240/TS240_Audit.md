# TS240 Audit - Dirichlet Tail Bound Discharge

## Scope

TS240 discharges the direct quantitative fallback target exposed by TS239:

```lean
TS239.Goldbach.DirichletTailBoundStatement
```

Equivalently, for all `0 < T <= U`,

```lean
|F U - F T| <= 2 / T
```

where `F(T)` is `TS228.Goldbach.dirichletUnitPartialIntegral T`.

The sprint works only on strictly positive intervals `[T, U]`.  It does not
use the TS239 `normalizedSinc` surrogate, because the repository Dirichlet
kernel has no singularity on this interval.

## Main Declarations

- `dirichletTailPrimitive`
- `dirichletPartialIntegral_sub_eq_tail`
- `sineDirichletKernel_one_eq_sin_div`
- `hasDerivAt_dirichletTailPrimitive`
- `dirichletTailIntegral_eq`
- `inverseSquareIntervalIntegral`
- `cosOverSquareIntegral_abs_le`
- `dirichletTailBound`
- `DirichletTailBoundDischargeLedger`
- `dirichletTailBoundDischargeTarget`

## What Is Proved

TS240 proves the finite tail decomposition:

```lean
F U - F T =
  intervalIntegral
    (fun x => TS213.Goldbach.sineDirichletKernel 1 x)
    T U volume
```

It then uses the primitive

```lean
dirichletTailPrimitive x = -Real.cos x / x
```

and proves that away from zero its derivative is

```lean
TS213.Goldbach.sineDirichletKernel 1 x + Real.cos x / x ^ 2
```

The FTC on `[T, U]` gives the exact identity

```lean
F U - F T =
  Real.cos T / T -
    Real.cos U / U -
      intervalIntegral (fun x => Real.cos x / x ^ 2) T U volume
```

The residual term is bounded by evaluating the positive majorant exactly:

```lean
intervalIntegral (fun x => (1 : Real) / x ^ 2) T U volume =
  (1 : Real) / T - (1 : Real) / U
```

Together with `|cos x| <= 1`, this yields:

```lean
|F U - F T| <= 2 / T
```

## Non-claims

TS240 does not prove Cauchy convergence of `F(T)`, does not construct the
cutoff limit, does not identify the cutoff value as `Real.pi / 2`, does not
prove the Abel-to-cutoff bridge, does not prove the cos-square value, does not
prove the canonical sinc-fourth value, does not prove Plancherel evidence, the
explicit formula input, Gallagher estimate, or Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS240.DirichletTailBoundDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS240
git diff --check
```

## Expected Audit Result

The TS240 directory contains no placeholder proofs, no forbidden declarations,
and no non-ASCII characters.  `git diff --check` reports no whitespace errors.
