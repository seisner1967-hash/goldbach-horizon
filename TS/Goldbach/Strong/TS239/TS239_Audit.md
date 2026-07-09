# TS239 Audit - Dirichlet Cutoff API and Direct Route Probe

## Scope

TS239 records a bounded direct-cutoff API probe after TS238.  It checks the
locked Mathlib revision used by this repository, rather than a newer external
Mathlib snapshot.

The locked Mathlib revision does not expose `Real.sinc`, the suggested
`Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc` module, or a ready-made
ordinary Dirichlet cutoff theorem in the probed modules.  TS239 therefore does
not prove the cutoff value.  Instead, it creates a local `normalizedSinc`
surrogate and proves that replacing the historical repository kernel by this
surrogate does not change the TS228 interval partial integrals.

## Main Declarations

- `DirichletCutoffAPIProbeOutcome`
- `dirichletCutoffProbedModules`
- `dirichletCutoffSearchTerms`
- `normalizedSinc`
- `NormalizedSincCutoffAtTopStatement`
- `DirectDirichletCutoffAtTopStatement`
- `DirichletTailBoundStatement`
- `sineDirichletKernel_one_eq_normalizedSinc_of_ne_zero`
- `dirichletUnitPartialIntegral_eq_normalizedSincIntegral`
- `dirichletUnitPartialIntegralAtTop_of_normalizedSinc`
- `dirichletProductCutoffUnitValue_of_normalizedSinc`
- `cosSquareThirdDerivativeCutoffValue_of_normalizedSinc`
- `DirichletCutoffAPIDirectRouteProbeLedger`
- `dirichletCutoffAPIDirectRouteProbeTarget`

## What Is Proved

TS239 proves that the repository unit Dirichlet kernel agrees with
`normalizedSinc` away from zero:

```lean
TS213.Goldbach.sineDirichletKernel 1 x = normalizedSinc x
```

under the hypothesis `x = 0 -> False`.

It also proves the interval-integral bridge:

```lean
TS228.Goldbach.dirichletUnitPartialIntegral T =
  intervalIntegral normalizedSinc 0 T volume
```

for every real `T`.  The proof uses `intervalIntegral.integral_congr_ae` and
the fact that the singleton `{0}` is null for Lebesgue measure.

Consequently, any future direct proof of
`NormalizedSincCutoffAtTopStatement` immediately supplies:

```lean
TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement
TS227.Goldbach.DirichletProductCutoffUnitValueStatement
TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement
```

through the existing TS228 and TS227 routing.

## Probe Result

The direct cutoff symbol and `Real.sinc` compatibility symbol were not located
in the bounded set of probed modules recorded by `dirichletCutoffProbedModules`
and `dirichletCutoffSearchTerms`.

This is audit metadata about this local probe.  It is not a theorem about all
of Mathlib.

## Non-claims

TS239 does not prove `Real.sinc` exists in the locked Mathlib revision, does
not prove the ordinary Dirichlet cutoff value, does not prove the direct tail
bound, does not prove the Abel-to-cutoff bridge, does not prove the cos-square
value, does not prove the canonical sinc-fourth value, does not prove
Plancherel evidence, the explicit formula input, Gallagher estimate, or
Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS239.DirichletCutoffAPIDirectRouteProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS239
git diff --check
```

## Expected Audit Result

The TS239 directory contains no placeholder proofs, no forbidden declarations,
and no non-ASCII characters.  `git diff --check` reports no whitespace errors.
