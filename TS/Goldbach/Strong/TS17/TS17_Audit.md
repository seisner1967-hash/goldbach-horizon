# TS17 - Mellin-Jackson Discharge by Fourier Tail Projection

## Status

TS17 promotes the TS15 Mellin-Jackson interface from `interface_compiled`
to `repo_committed_relative`.

It does not claim a full Mathlib proof of the Mellin/Fourier L2 bridge,
Plancherel, or the Fourier derivative identity. Instead, those analytic
ingredients are isolated as explicit local structures.

## Lean Files

- `MellinFourierChangeOfVariables.lean`
  - proves the concrete Bochner change-of-variables lemma for `x = exp u`;
  - records the image, injectivity, and derivative facts needed by the Jacobian theorem.
- `MellinFourierWeightedMeasure.lean`
  - defines the weighted Mellin measure `muWeighted`;
  - defines the representative operators `TsigmaFun` and `TsigmaInvFun`;
  - proves pointwise inverse identities on representatives;
  - proves the pre-quotient norm-square integral identity.
- `MellinFourierNormBridge.lean`
  - proves measurability of the Mellin density;
  - proves that `muWeighted` is supported almost everywhere on `(0, infinity)`;
  - upgrades the pointwise inverse identities to almost-everywhere identities.
- `MellinJacksonInfrastructure.lean`
  - defines `LogPullback`;
  - defines abstract norms `l2Norm`, `fourierTailNorm`, and `derivativeL2Norm`;
  - defines `MellinFourierNormBridge`.
- `FourierTailBound.lean`
  - defines `FourierTailInfrastructure`;
  - proves `fourier_tail_bound` relative to that infrastructure.
- `MellinJacksonDischarge.lean`
  - proves `mellin_jackson_projection_bound`;
  - returns `TS15.MellinJackson.MellinJacksonProjectionBound`.

## Ledger

| ID | Object | Previous Status | TS17 Status | Comment |
| --- | --- | --- | --- | --- |
| TS17-G40 | `MellinJacksonProjectionBound` | `interface_compiled` | `repo_committed_relative` | proved relative to two analytic bridges |
| TS17-B1 | `MellinFourierNormBridge` | absent | `analytic_infrastructure_obligation` | logarithmic pullback and Theta bridge |
| TS17-B2 | `FourierTailInfrastructure` | absent | `analytic_infrastructure_obligation` | Fourier tail and Plancherel infrastructure |
| TS17-C1 | TS16 combinatorial discharge | `repo_committed` | unchanged | combinatorial debt remains closed |
| TS17-G38 | `ShortIntervalPrimeSecondMoment` | `analytic_open_problem` | unchanged | final analytic lock remains open |

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS17.MellinFourierChangeOfVariables `
  TS.Goldbach.Strong.TS17.MellinFourierWeightedMeasure `
  TS.Goldbach.Strong.TS17.MellinFourierNormBridge `
  TS.Goldbach.Strong.TS17.MellinJacksonInfrastructure `
  TS.Goldbach.Strong.TS17.FourierTailBound `
  TS.Goldbach.Strong.TS17.MellinJacksonDischarge

rg -n "s[o]rry" TS\Goldbach\Strong\TS17
rg -n "a[x]iom" TS\Goldbach\Strong\TS17
```

Expected result:

```text
0 unresolved placeholders
0 global assumptions
```

## Conclusion

After TS17:

```text
Mellin-Jackson =
  MellinFourierNormBridge
  + FourierTailInfrastructure
  => MellinJacksonProjectionBound
```

The debt is not erased, but it is smaller, named, local, and testable.
