# TS241 Audit - Dirichlet Cutoff Cauchy Convergence Discharge

## Scope

TS241 discharges the Cauchy convergence consequence of the TS240 direct tail
bound.  It proves that the unit Dirichlet partial integral

```lean
TS228.Goldbach.dirichletUnitPartialIntegral
```

is a `CauchySeq` along `atTop`, hence has a real limit by completeness of
`Real`.

The sprint constructs a canonical limit

```lean
dirichletCutoffLimit
```

and proves convergence to that limit.  It does not identify this limit with
`Real.pi / 2`.

## Main Declarations

- `DirichletUnitPartialIntegralConvergesStatement`
- `dirichletUnitPartialIntegral_cauchySeq`
- `dirichletUnitPartialIntegralConverges`
- `dirichletCutoffLimit`
- `tendsto_dirichletCutoffLimit`
- `DirichletCutoffCauchyConvergenceDischargeLedger`
- `dirichletCutoffCauchyConvergenceDischargeTarget`

## What Is Proved

Using TS240,

```lean
|F U - F T| <= 2 / T
```

for `0 < T <= U`, TS241 proves the `Metric.cauchySeq_iff` criterion.

Given `epsilon > 0`, it chooses

```lean
N = 4 / epsilon
```

For `m, n >= N`, both endpoints are positive.  If `m <= n`, TS240 bounds
`|F n - F m|` by `2 / m`; if `n <= m`, it bounds `|F m - F n|` by `2 / n`.
In both cases monotonicity of `x |-> 2 / x` on positive reals gives a bound
by `2 / N = epsilon / 2 < epsilon`.

The result is:

```lean
CauchySeq TS228.Goldbach.dirichletUnitPartialIntegral
```

Completeness of `Real` then yields:

```lean
Exists fun L : Real =>
  Tendsto TS228.Goldbach.dirichletUnitPartialIntegral atTop (nhds L)
```

The canonical witness is recorded as `dirichletCutoffLimit`.

## Non-claims

TS241 does not prove that the cutoff limit is `Real.pi / 2`, does not identify
the direct cutoff limit with the Abel value, does not prove the Abel-to-cutoff
bridge, does not prove the cos-square value, does not prove the canonical
sinc-fourth value, does not prove Plancherel evidence, the explicit formula
input, Gallagher estimate, or Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS241.DirichletCutoffCauchyConvergenceDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS241
git diff --check
```

## Expected Audit Result

The TS241 directory contains no placeholder proofs, no forbidden declarations,
and no non-ASCII characters.  `git diff --check` reports no whitespace errors.
