# TS242 Audit - Dirichlet Abel Summation Identity Discharge

## Scope

TS242 proves the finite Abel summation identity connecting the damped
Dirichlet partial integral

```lean
TS232.Goldbach.dampedPartialIntegral b T
```

to the direct cutoff partial integral

```lean
TS228.Goldbach.dirichletUnitPartialIntegral T
```

and its Abel average.  It also proves that the boundary term

```lean
Real.exp (-b * T) * TS228.Goldbach.dirichletUnitPartialIntegral T
```

tends to zero as `T -> +infty` for every `b > 0`.

The sprint does not identify the TS241 cutoff limit with `Real.pi / 2`.

## Main Declarations

- `dirichletAbelAverage`
- `sineDirichletKernel_one_continuousAt_of_ne`
- `hasDerivAt_dirichletUnitPartialIntegral_of_ne`
- `dirichletUnitPartialIntegral_zero`
- `dirichletUnitPartialIntegral_lipschitz`
- `dirichletUnitPartialIntegral_continuous`
- `hasDerivAt_exp_neg_mul`
- `dampedPartialIntegral_eq_boundary_add_abelAverage`
- `dampedCutoffBoundary_tendsto_zero`
- `DirichletAbelSummationIdentityDischargeLedger`
- `dirichletAbelSummationIdentityDischargeTarget`

## What Is Proved

The finite identity is:

```lean
TS232.Goldbach.dampedPartialIntegral b T =
  Real.exp (-b * T) *
    TS228.Goldbach.dirichletUnitPartialIntegral T +
      dirichletAbelAverage b T
```

for `0 < b` and `0 <= T`.

The proof applies the interval-integral integration-by-parts theorem to
`u x = exp(-b*x)` and `v x = F x`, where `F` is the TS228 partial integral.
The derivative of `F` is required only on the open interval `(0,T)`, so no
derivative claim is made at the endpoint `0`.

The boundary vanishing follows from TS241:

```lean
F(T) -> dirichletCutoffLimit
```

and from exponential decay:

```lean
exp(-b*T) -> 0
```

for `b > 0`.

## Non-claims

TS242 does not prove that the cutoff limit is `Real.pi / 2`, does not identify
the direct cutoff limit with the Abel value, does not prove the Abel-to-cutoff
bridge, does not prove the cos-square value, does not prove the canonical
sinc-fourth value, does not prove Plancherel evidence, the explicit formula
input, Gallagher estimate, or Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS242.DirichletAbelSummationIdentityDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS242
git diff --check
```

## Expected Audit Result

The TS242 directory contains no placeholder proofs, no forbidden declarations,
and no non-ASCII characters.  `git diff --check` reports no whitespace errors.
