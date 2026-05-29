# Horizon Goldbach

Lean 4 formal specification programme for a conditional architecture around the
binary Goldbach conjecture.

This repository does **not** claim an unconditional proof of Goldbach. Its goal
is narrower and auditable: decompose the proof architecture into Lean-checked
modules, prove the finite/combinatorial layer, and expose the remaining
analytic work as named local infrastructure obligations.

## Current Focus: TS15--TS56

The current sprint chain lives under:

```text
TS/Goldbach/Strong/
  TS15/
  TS16/
  TS17/
  TS18/
  TS19/
  TS20/
  TS21/
  TS22/
  TS23/
  TS24/
  TS25/
  TS26/
  TS27/
  TS28/
  TS29/
  TS30/
  TS31/
  TS32/
  TS33/
  TS34/
  TS35/
  TS36/
  TS37/
  TS38/
  TS39/
  TS40/
  TS41/
  TS42/
  TS43/
  TS44/
  TS45/
  TS46/
  TS47/
  TS48/
  TS49/
  TS50/
  TS51/
  TS52/
  TS53/
  TS54/
  TS55/
  TS56/
```

Status summary:

| Sprint | Object | Status | Meaning |
| --- | --- | --- | --- |
| TS15 | Short-interval reduction | `interface_compiled` | typed Lean interface for the local analytic residue |
| TS16 | Combinatorial discharge | `repo_committed` | finite counting lemma proved unconditionally |
| TS17 | Mellin-Jackson projection | `repo_committed_relative` | reduced to Mellin/Fourier infrastructure |
| TS18 | Short-interval second moment | `repo_committed_relative` | reduced to character bridge and large sieve infrastructure |
| TS19 | OTSA residual bound | `repo_committed_relative` | reduced to spectral, trace, and Mellin-tail controls |
| TS20 | Synthesis manuscript | documentation | final ledger and project roadmap |
| TS21 | Short-interval constant budget | `repo_committed_relative` | transports explicit constants such as Brun-Titchmarsh `K = 20` |
| TS22 | Energy scale renormalization | `repo_committed_relative` | makes the short-interval normalization scale explicit |
| TS23 | OTSA scale propagation | `repo_committed_relative` | transports TS22 scales into the OTSA residual ledger |
| TS24 | Closed-form scale bridge | `repo_committed` | proves the ceiling-budget scale is dominated by a padded closed form |
| TS25 | Padded-scale OTSA feasibility | `repo_committed_relative` | specializes OTSA propagation to the TS24 padded scale |
| TS26 | OTSA numerical feasibility | `repo_committed_relative` | converts rational OTSA certificates into scaled admissibility |
| TS27 | OTSA constant register | `repo_committed_relative` | registers non-final rational OTSA smoke-test constants |
| TS28 | OTSA constants candidate | `repo_committed_relative` | adds a typed-status candidate-v0 OTSA register |
| TS29 | OTSA constant provenance | `repo_committed_relative` | records provenance status for OTSA rational bounds |
| TS30 | Brun-Titchmarsh Selberg roadmap | `repo_committed_relative` | decomposes BT into Selberg majorant and budget comparison |
| TS31 | OTSA asymptotic majorants | `repo_committed_relative` | records candidate-v1 rational majorants and provenance gaps |
| TS32 | OTSA trace majorant roadmap | `repo_committed_relative` | records the conditional trace target `Ct <= 1/2` |
| TS33 | OTSA final majorants roadmap | `repo_committed_relative` | replaces final raw placeholders by Mellin-tail and scale-transfer contracts |
| TS34 | Mellin-Fourier measure transport | `repo_committed_relative` | isolates a.e. transport under weighted, restricted, exp, and log measures |
| TS35 | Mellin-Fourier AEEqFun transport | `repo_committed_relative` | descends `TsigmaFun` and `TsigmaInvFun` through the a.e. quotient layer |
| TS36 | Mellin-Fourier L2 isometry roadmap | `repo_committed_relative` | packages the remaining `Lp`-level inputs for the future isometry |
| TS37 | Mellin-Fourier Lp norm inputs | `repo_committed_relative` | isolates `Memℒp` and `snorm` preservation for the future isometry |
| TS38 | Mellin-Fourier Lp linearity inputs | `repo_committed_relative` | isolates a.e. additivity and scalar compatibility for the future isometry |
| TS39 | Mellin-Fourier Lp isometry spec | `repo_committed_relative` | specifies the final `LinearIsometryEquiv` and its a.e. representative behaviour |
| TS40 | Fourier tail roadmap | `repo_committed_relative` | records Plancherel, derivative-control, and high-frequency tail obligations |
| TS41 | Fourier API probe | `repo_committed_relative` | records Fourier API normalization slots before concrete Mathlib binding |
| TS42 | Mellin tail spline roadmap | `repo_committed_relative` | records the triangle-spline route to the `Cm <= 1` Mellin-tail contract |
| TS43 | Triangle spline pointwise facts | `repo_committed` | proves elementary branch values and the pointwise derivative bound |
| TS44 | Triangle spline measurability and support | `repo_committed` | proves measurability and support containment for the derivative representative |
| TS45 | Triangle spline derivative snorm roadmap | `repo_committed_relative` | packages TS43/TS44 inputs and isolates the derivative `snorm <= 2` obligation |
| TS46 | Triangle spline support measure | `repo_committed` | proves the Lebesgue measure of `[-1, 1]` is exactly `2` |
| TS47 | Triangle spline snorm discharge bridge | `repo_committed_relative` | reduces the derivative `snorm <= 2` estimate to a generic bounded-support lemma |
| TS48 | Bounded-support snorm lemma | `repo_committed` | proves the generic bounded-support `snorm` lemma and discharges the TS45 triangle derivative target |
| TS49 | Triangle spline Sobolev agreement | `repo_committed_relative` | isolates agreement between the TS41 Sobolev derivative slot and `triangleSplineDeriv` |
| TS50 | Triangle spline tail assembly | `repo_committed_relative` | assembles TS48 norm control and TS49 Sobolev agreement into the TS42 spline-tail route |
| TS51 | Triangle spline Fourier-tail comparison | `repo_committed_relative` | replaces the TS50 tail marker by an explicit high-frequency `snorm <= 1` comparison package |
| TS52 | Fourier Mathlib API binding roadmap | `repo_committed_relative` | records the binding layer between TS41 normalization slots and future Mathlib Fourier theorem instances |
| TS53 | Fourier concrete symbols probe | `repo_committed_relative` | checks `Real.fourierIntegral`, its inverse, kernel formulas, and the derivative-rule symbol |
| TS54 | Fourier Plancherel L2 gap ledger | `repo_committed_relative` | records the missing compatible `snorm`/L2 Plancherel contract after TS53 |
| TS55 | Triangle spline Sobolev agreement ledger | `repo_committed_relative` | decomposes the TS49 weak-derivative agreement into local Sobolev-side obligations |
| TS56 | Triangle spline branch formulae | `repo_committed` | proves the affine branch formulae for `triangleSpline` and its vanishing outside `[-1, 1]` |

## What Is Proved

TS16 proves the finite combinatorial comparison:

```lean
TS16.Goldbach.pair_count_le_energy
```

This removes the previous local counting obligation from TS15. The proof uses
only finite sets, products, sigma finsets, and cardinality comparison: close
pairs are injected into energetic triples.

TS17, TS18, and TS19 are relative discharges. They do not hide assumptions as
global axioms; instead they pass the remaining analytic inputs as explicit
structures.

TS21 adds a budgeted version of the short-interval second-moment interface:

```lean
TS21.Goldbach.Problem_E1K
TS21.Goldbach.ShortIntervalPrimeSecondMomentK
TS21.Goldbach.BrunTitchmarshShortInterval
TS21.Goldbach.BrunTitchmarshLocalWindowBudget
```

This lets later threshold computations carry a concrete constant, currently
`K = 20`, instead of forcing the TS18-style estimate into the rigid `C <= 1`
shape too early. TS21 also records the scale-correct local-window transport:
a uniform bound `shortPrimeLocalCount x Q n <= B` implies
`shortPrimeEnergy x Q <= (x+1) * B^2`.

TS22 generalizes the downstream target by introducing:

```lean
TS22.Goldbach.ShortIntervalScale
TS22.Goldbach.Problem_E1Scale
TS22.Goldbach.brunTitchmarshClosedFormScale
TS22.Goldbach.BrunTitchmarshNatIntervalBound
TS22.Goldbach.ScaledLargeSieveInfrastructure
```

This keeps the raw TS15 energy intact while allowing Brun-Titchmarsh and large
sieve inputs to use their natural normalization scales. TS22 also provides an
interval bridge from a future natural-number Brun-Titchmarsh theorem to the
local window budget used by TS21, and a scale-aware large-sieve discharge:

```lean
TS18.Goldbach.DirichletCharacterBridge
  + TS22.Goldbach.ScaledLargeSieveInfrastructure S
  => TS22.Goldbach.Problem_E1Scale S K
```

TS23 connects the TS22 scale layer to the TS19 OTSA residual ledger:

```lean
TS22.Goldbach.Problem_E1Scale S K
  + TS23.Goldbach.ScaleToOTSAControl S
  + scaled OTSA coupling
  + TS23.Goldbach.ScaledOTSAAdmissible
  => TS19.OTSA.OTSAResidualBound R
```

TS24 closes the arithmetic scale-domination layer for Brun-Titchmarsh budgets:

```lean
TS22.Goldbach.BrunTitchmarshNatIntervalBound
  => TS24.Goldbach.Problem_E1Scale_from_natIntervalBound_paddedClosedForm
```

The padded closed form keeps the unavoidable `+1` loss from `Nat.ceil`
explicit, so no unproved rounding claim is smuggled into the closed-form scale.

TS25 packages the padded-scale OTSA entry point:

```lean
TS22.Goldbach.BrunTitchmarshNatIntervalBound
  + TS23.Goldbach.ScaleToOTSAControl
      TS24.Goldbach.brunTitchmarshPaddedClosedFormScale
  + TS23.Goldbach.ScaledOTSAAdmissible
  + local OTSA coupling
  => TS19.OTSA.OTSAResidualBound R
```

TS26 adds an exact rational certificate layer for OTSA numerical feasibility:

```lean
TS26.Goldbach.OTSARationalCertificate
  => TS26.Goldbach.scaledConstantsOfRat
  => TS26.Goldbach.scaledOTSAAdmissible_of_rat
```

The admissibility inequality is checked over `Rat` and then transported to the
real-valued TS23 constants, avoiding floating-point certificates.

TS27 adds a labelled register for candidate OTSA constants and a deliberately
non-final smoke test:

```lean
TS27.Goldbach.OTSACert_smoke_test
TS27.Goldbach.OTSARegister_smoke_test
TS27.Goldbach.smoke_test_scaledOTSAAdmissible
```

The smoke-test constants verify the TS26-to-TS23 plumbing only. They are not
claimed as certified spectral, trace, Mellin-tail, or scale-transfer values.

TS28 adds a typed-status register and a candidate-v0 package:

```lean
TS28.Goldbach.ConstantStatus
TS28.Goldbach.OTSACert_candidate_v0
TS28.Goldbach.OTSARegister_candidate_v0
TS28.Goldbach.candidate_v0_scaledOTSAAdmissible
```

The candidate-v0 rational inequality is Lean-checked, but the package is not a
final OTSA certificate until each constant has a sourced analytic majorant.

TS29 adds a provenance ledger for the candidate-v0 constants:

```lean
TS29.Goldbach.ConstantProvenance
TS29.Goldbach.SourcedRatBound
TS29.Goldbach.OTSAConstantProvenanceRegister
TS29.Goldbach.OTSAProvenance_candidate_v0
TS29.Goldbach.candidate_v0_not_certified
```

At this point `Ck` is marked as a narrative-source bound, while `Ct`, `Cm`, and
`Cscale` remain explicit placeholders.

TS30 refines the remaining Brun-Titchmarsh obligation into Selberg-facing
sub-obligations:

```lean
TS30.Goldbach.SelbergSieveIntervalBound
TS30.Goldbach.SelbergMajorantBudgetComparison
TS30.Goldbach.SelbergBrunTitchmarshInfrastructure
TS30.Goldbach.brunTitchmarshNatIntervalBound_from_selberg
```

This keeps Brun-Titchmarsh external, but identifies the exact future Mathlib
target: a Selberg-sieve interval majorant plus the arithmetic comparison with
the TS22 ceiling budget.

TS31 adds a first asymptotic-majorant candidate package after the TS29
provenance ledger:

```lean
TS31.Goldbach.OTSACert_candidate_v1
TS31.Goldbach.OTSARegister_candidate_v1
TS31.Goldbach.OTSAProvenance_candidate_v1
TS31.Goldbach.candidate_v1_scaledOTSAAdmissible
```

The rational admissibility calculation is exact:

```text
Cscale * (Ck * Ct + Cm) = 53/50 <= 26.
```

Only `Ck` is currently attached to a narrative source. `Ct`, `Cm`, and
`Cscale` remain explicit placeholders until sourced rational upper bounds are
available.

TS32 isolates the trace contribution as an explicit local contract:

```lean
TS32.Goldbach.TraceMajorantContract
TS32.Goldbach.Ct_target_v2
TS32.Goldbach.OTSACert_candidate_v2
TS32.Goldbach.OTSAProvenance_candidate_v2
TS32.Goldbach.candidate_v2_scaledOTSAAdmissible
```

It proves that any future trace contract with `Ct <= 1/2` gives a rational
OTSA certificate. If the target value `Ct = 1/2` is supplied, the scaled value
is:

```text
1 * ((3/50) * (1/2) + 1) = 103/100 <= 26.
```

The trace constant is deliberately marked as conditional evidence, not as a
certified analytic derivation.

TS33 adds the last two asymptotic-majorant contracts:

```lean
TS33.Goldbach.MellinTailMajorantContract
TS33.Goldbach.ScaleTransferMajorantContract
TS33.Goldbach.OTSACert_candidate_v3
TS33.Goldbach.OTSAProvenance_candidate_v3
TS33.Goldbach.candidate_v3_scaledOTSAAdmissible
```

It proves that the contracted bounds

```text
Ck = 3/50, Ct <= 1/2, Cm <= 1, Cscale <= 2
```

imply the exact rational OTSA threshold:

```text
2 * ((3/50) * (1/2) + 1) = 103/50 <= 26.
```

This removes raw placeholder constants from the v3 package by replacing them
with explicit local contracts. Those contracts still need genuine analytic
instantiations before a final certificate can be claimed.

TS34 begins the harmonic-analysis front by isolating the measure-transport
layer needed for the concrete Mellin/Fourier bridge:

```lean
TS34.MellinJackson.MellinFourierMeasureTransport
TS34.MellinJackson.tsigmaFun_congr_of_measureTransport
TS34.MellinJackson.tsigmaInvFun_congr_of_measureTransport
```

It does not construct the `Lp`-level isometry. It records the four local
almost-everywhere transport facts needed to move between the weighted Mellin
measure, Lebesgue measure restricted to `(0, infinity)`, and Lebesgue measure
under `exp`/`log`.

TS35 crosses the almost-everywhere quotient layer:

```lean
TS35.MellinJackson.MellinFourierMeasurabilityTransport
TS35.MellinJackson.MellinFourierAEEqTransport
TS35.MellinJackson.TsigmaAEEqFun
TS35.MellinJackson.TsigmaInvAEEqFun
TS35.MellinJackson.TsigmaInvAEEqFun_left
TS35.MellinJackson.TsigmaInvAEEqFun_right
```

It reuses the existing TS17 quotient construction by feeding it the TS34
congruence lemmas and a local strong-measurability contract. It still stops
before the `Lp` quotient, the `L²` isometry, Plancherel, and the Fourier-tail
infrastructure.

TS36 packages the remaining `Lp`-level obligations needed to construct the
future Mellin-Fourier `L²` isometry:

```lean
TS36.MellinJackson.MellinFourierLpIsometryInfrastructure
TS36.MellinJackson.MellinFourierLpIsometryRoadmap
TS36.MellinJackson.MellinFourierLpIsometryTarget
TS36.MellinJackson.ae_transport_of_roadmap
```

It records preservation of `Memℒp`, equality of `snorm`, and a.e. linearity for
the representative operators. It deliberately does not construct the final
`LinearIsometryEquiv`; that remains the next concrete `Lp`-API sprint.

TS37 isolates the norm side of the TS36 roadmap:

```lean
TS37.MellinJackson.MellinFourierLpNormInputs
TS37.MellinJackson.normInputsOfRoadmap
TS37.MellinJackson.MellinFourierLpNormInputsTarget
TS37.MellinJackson.normInputsTarget_of_roadmap
```

It focuses only on `Memℒp` preservation and `snorm` preservation for
`TsigmaFun` and `TsigmaInvFun`. Quotient linearity, the final
`LinearIsometryEquiv`, and Fourier-tail/Plancherel remain in later sprints.

TS38 isolates the linearity side of the TS36 roadmap:

```lean
TS38.MellinJackson.MellinFourierLpLinearityInputs
TS38.MellinJackson.lpInfrastructureOfNormAndLinearity
TS38.MellinJackson.linearityInputsOfRoadmap
TS38.MellinJackson.MellinFourierLpLinearityInputsTarget
TS38.MellinJackson.linearityTarget_of_roadmap
```

It records the a.e. additivity and scalar-compatibility inputs for `TsigmaFun`
and `TsigmaInvFun`. Together, TS37 and TS38 reconstruct the full TS36
`MellinFourierLpIsometryInfrastructure`, leaving the final
`LinearIsometryEquiv` assembly to TS39.

TS39 gives the final specification of the Mellin-Fourier `L²` isometry:

```lean
TS39.MellinJackson.MellinFourierLpIsometry
TS39.MellinJackson.MellinFourierLpIsometryTarget
TS39.MellinJackson.weakTarget_of_isometryTarget
```

The specification includes the `LinearIsometryEquiv`, but also requires that
its forward and inverse maps agree a.e. with `TsigmaFun` and `TsigmaInvFun`.
This keeps the contract tied to the Mellin-Fourier transport rather than to an
unrelated abstract isometry.

TS40 records the Fourier-tail side of the TS17 harmonic front:

```lean
TS40.MellinJackson.FourierTailInfrastructure
TS40.MellinJackson.FourierTailTarget
TS40.MellinJackson.FourierTailTarget.of_infrastructure
```

It keeps the Fourier transform and Sobolev derivative representatives abstract
until Mathlib's Fourier normalization is inspected. It records the needed
Plancherel `snorm` control, a derivative-control marker, and the high-frequency
tail estimate. TS40 completes the architectural roadmap of the TS17 harmonic
front; it does not discharge the other analytic obligations such as
Brun-Titchmarsh/Selberg, Dirichlet character bridges, large sieve inputs, or
OTSA analytic constants.

TS41 starts the concrete-instantiation phase for the Fourier front by recording
the normalization choices that must be fixed before TS40 can be implemented
against Mathlib:

```lean
TS41.MellinJackson.FourierAPINormalizationLedger
TS41.MellinJackson.FourierAPINormalizationTarget
TS41.MellinJackson.FourierAPINormalizationTarget.of_ledger
```

It keeps the Fourier transform and Sobolev derivative representatives abstract
while reserving explicit positive constants for Plancherel normalization and
the derivative multiplier. This avoids committing to a `2 * pi` convention
before the concrete Mathlib Fourier API is inspected.

TS42 records the triangle-spline route toward the TS33 Mellin-tail contract:

```lean
TS42.MellinJackson.triangleSpline
TS42.MellinJackson.triangleSplineDeriv
TS42.MellinJackson.TriangleSplineTailInfrastructure
TS42.MellinJackson.mellinTailContract_from_triangleSpline
TS42.MellinJackson.TriangleSplineTailTarget
TS42.MellinJackson.mellinTailContract_target_of_triangleSplineTarget
```

It defines the smoothing profile and its piecewise weak-derivative
representative, then keeps the derivative norm calculation, Sobolev agreement,
and final tail comparison as explicit local infrastructure fields. No local
hidden assumption is used to claim the Mellin-tail estimate.

TS43 proves the first concrete facts about the TS42 weak-derivative
representative:

```lean
TS43.MellinJackson.triangleSplineDeriv_eq_one_of_left
TS43.MellinJackson.triangleSplineDeriv_eq_neg_one_of_right
TS43.MellinJackson.triangleSplineDeriv_eq_zero_of_not_left_not_right
TS43.MellinJackson.abs_triangleSplineDeriv_le_one
```

These are pointwise order/algebra facts only. They prepare the later Lebesgue
norm calculation without invoking Sobolev theory or Fourier analysis.

TS44 proves the support and measurability side of the same derivative
representative:

```lean
TS44.MellinJackson.triangleSplineDeriv_eq_zero_of_le_neg_one
TS44.MellinJackson.triangleSplineDeriv_eq_zero_of_one_le
TS44.MellinJackson.triangleSplineDeriv_zero_outside_Icc
TS44.MellinJackson.triangleSplineDeriv_measurable
TS44.MellinJackson.TriangleSplineDerivativeSupportInputs
TS44.MellinJackson.triangleSplineDerivativeSupportInputs
TS44.MellinJackson.triangleSplineDerivativeSupportTarget
```

It still does not compute any Lebesgue integral. It prepares that computation
by proving that the derivative representative is measurable and vanishes
outside `[-1, 1]`.

TS45 isolates the `L2`/`snorm` side of the triangle-spline derivative route:

```lean
TS45.MellinJackson.TriangleSplineDerivativeSnormInputs
TS45.MellinJackson.triangleSplineDerivativeSnormInputs
TS45.MellinJackson.TriangleSplineDerivativeSnormInfrastructure
TS45.MellinJackson.deriv_snorm_bound_of_infrastructure
TS45.MellinJackson.TriangleSplineDerivativeSnormInputsTarget
TS45.MellinJackson.triangleSplineDerivativeSnormInputsTarget
TS45.MellinJackson.TriangleSplineDerivativeSnormTarget
```

It proves that the elementary data needed for the future norm calculation are
available from TS43 and TS44, and it keeps the actual Lebesgue/snorm estimate
as an explicit local obligation.

TS46 proves the elementary support-measure input for that future norm
calculation:

```lean
TS46.MellinJackson.triangleSpline_support_volume_eq_two
TS46.MellinJackson.triangleSpline_support_volume_le_two
TS46.MellinJackson.TriangleSplineSupportMeasureInputs
TS46.MellinJackson.triangleSplineSupportMeasureInputs
TS46.MellinJackson.triangleSplineSupportMeasureTarget
```

It shows that the closed support interval `[-1, 1]` has Lebesgue measure
`ENNReal.ofReal 2`. It still does not prove the `snorm` bound, Sobolev
agreement, Plancherel, or Fourier-tail decay.

TS47 connects the TS43, TS44, and TS46 facts to the TS45 snorm infrastructure:

```lean
TS47.MellinJackson.BoundedSupportSnormLemma
TS47.MellinJackson.triangleSplineDeriv_complex_measurable
TS47.MellinJackson.triangleSplineDeriv_complex_norm_le_one
TS47.MellinJackson.triangleSplineDerivativeSnormInfrastructure
TS47.MellinJackson.triangleSplineDerivativeSnormTarget_of_boundedSupportLemma
```

It proves the complexified measurability and pointwise norm bound for the
derivative representative, then reduces the remaining `snorm <= 2` estimate to
a reusable bounded-support `snorm` lemma.

TS48 proves that reusable bounded-support `snorm` lemma:

```lean
TS48.MellinJackson.BoundedSupportSnormTarget
TS48.MellinJackson.boundedSupportSnormLemma
TS48.MellinJackson.boundedSupportSnormTarget
TS48.MellinJackson.triangleSplineDerivativeSnormTarget
```

It compares a supported, pointwise-bounded complex function with the indicator
of its support, invokes Mathlib's indicator-function `eLpNorm` estimate, and
closes the remaining `ENNReal` calculation by bounding `sqrt(2)` by `2`.
This turns the TS47 conditional bridge into a concrete discharge of the TS45
triangle-spline derivative `snorm <= 2` target.

TS49 isolates the Sobolev-agreement side of the triangle-spline route:

```lean
TS49.MellinJackson.TriangleSplineSobolevAgreementInfrastructure
TS49.MellinJackson.TriangleSplineSobolevAgreementTarget
TS49.MellinJackson.TriangleSplineSobolevAgreementTarget.of_infrastructure
```

It records the exact a.e. agreement needed between the abstract TS41 Sobolev
derivative representative and the explicit weak-derivative representative
`triangleSplineDeriv`. It does not prove that agreement, Plancherel, or any
Fourier-tail estimate.

TS50 assembles the triangle-spline tail route:

```lean
TS50.MellinJackson.TriangleSplineTailAssemblyInputs
TS50.MellinJackson.triangleSplineDeriv_snorm_bound
TS50.MellinJackson.triangleSplineTailInfrastructure_from_inputs
TS50.MellinJackson.TriangleSplineTailAssemblyTarget
TS50.MellinJackson.triangleSplineTailTarget_of_assembly
TS50.MellinJackson.mellinTailContract_from_triangleSplineAssembly
TS50.MellinJackson.mellinTailContractTarget_of_assemblyTarget
```

It uses the concrete TS48 derivative `snorm <= 2` bound and the TS49 Sobolev
agreement infrastructure to build the TS42 triangle-spline tail package
conditionally. The route to `Cm <= 1` is now wired, but still depends on
Sobolev agreement and the final Fourier-tail comparison.

TS51 isolates that final Fourier-tail comparison as an explicit package:

```lean
TS51.MellinJackson.triangleSplineComplex
TS51.MellinJackson.triangleSplineFourierTail
TS51.MellinJackson.TriangleSplineFourierTailComparisonInputs
TS51.MellinJackson.TriangleSplineFourierTailComparisonTarget
TS51.MellinJackson.triangleSpline_tail_snorm_le_one
TS51.MellinJackson.triangleSplineTailAssemblyInputs_from_fourierTailComparison
TS51.MellinJackson.mellinTailContractTarget_of_fourierTailComparisonTarget
```

It ties the comparison to both TS40 Fourier-tail infrastructure and TS49
Sobolev-agreement infrastructure. It does not prove Plancherel, Sobolev
agreement, or the concrete high-frequency estimate; those remain future
Mathlib-binding work.

TS52 prepares the Mathlib Fourier API binding layer:

```lean
TS52.MellinJackson.MathlibFourierAPIBinding
TS52.MellinJackson.MathlibFourierAPIBindingTarget
TS52.MellinJackson.MathlibFourierAPIBindingTarget.of_binding
TS52.MellinJackson.FourierAPINormalizationTarget_of_binding
TS52.MellinJackson.FourierAPINormalizationTarget_of_bindingTarget
```

It does not choose a concrete `fourierIntegral`, prove Plancherel, prove the
Fourier derivative rule, or discharge the high-frequency tail estimate. It
records the exact binding layer that must later connect the TS41 Fourier
normalization ledger to Mathlib's concrete theorem instances, with the
Plancherel constant transported into `ENNReal` via `ENNReal.ofReal`.

TS53 records the concrete Fourier symbols that compile in the current Mathlib
environment:

```lean
TS53.MellinJackson.realFourierTransformSymbol
TS53.MellinJackson.realFourierInvSymbol
TS53.MellinJackson.derivativeMultiplierCandidate
TS53.MellinJackson.realFourierTransformSymbol_real_eq_checked
TS53.MellinJackson.realFourierTransformSymbol_exp_kernel_checked
TS53.MellinJackson.realFourierTransformSymbol_deriv_rule
TS53.MellinJackson.FourierConcreteSymbolLedger
TS53.MellinJackson.fourierConcreteSymbolLedger
TS53.MellinJackson.FourierConcreteSymbolTarget
TS53.MellinJackson.fourierConcreteSymbolTarget
```

It checks that `Real.fourierIntegral`, `Real.fourierIntegralInv`, the
exponential kernel formula, and the real-line Fourier derivative rule are
available. It also records that a compatible Plancherel/L2 isometry symbol was
not located in this sprint, so TS52 remains uninstantiated.

TS54 turns that missing Plancherel/L2 symbol into a named local ledger and
contract:

```lean
TS54.MellinJackson.FourierPlancherelGapLedger
TS54.MellinJackson.fourierPlancherelGapLedger
TS54.MellinJackson.FourierPlancherelL2Contract
TS54.MellinJackson.FourierPlancherelL2Target
TS54.MellinJackson.FourierPlancherelL2Target.of_contract
TS54.MellinJackson.fourierPlancherelL2Contract_of_binding
TS54.MellinJackson.FourierPlancherelL2Target_of_binding
TS54.MellinJackson.FourierBindingWithPlancherel
TS54.MellinJackson.FourierBindingWithPlancherel.of_binding
```

It records that TS53 checked the forward transform, inverse transform, and
derivative-rule symbols, while leaving Plancherel as `notLocatedYet`. It also
states the exact `snorm` comparison needed to continue the concrete Mathlib
Fourier route.

TS55 decomposes the Sobolev-agreement side of the triangle-spline route:

```lean
TS55.MellinJackson.TriangleSplineSobolevAgreementLedger
TS55.MellinJackson.triangleSplineSobolevAgreementInfrastructure
TS55.MellinJackson.TriangleSplineSobolevAgreementLedgerTarget
TS55.MellinJackson.TriangleSplineSobolevAgreementLedgerTarget.of_ledger
TS55.MellinJackson.triangleSplineSobolevAgreementTarget_of_ledgerTarget
```

It does not prove the weak derivative identity. It records the branch,
boundary, and distributional sub-obligations that must eventually justify the
a.e. agreement between the TS41 Sobolev derivative slot and
`triangleSplineDeriv`.

TS56 proves the elementary affine formulae for the triangle spline:

```lean
TS56.MellinJackson.triangleSpline_eq_one_add_of_left
TS56.MellinJackson.triangleSpline_eq_one_sub_of_right
TS56.MellinJackson.triangleSpline_eq_zero_outside_Icc
TS56.MellinJackson.TriangleSplineBranchFormulae
TS56.MellinJackson.triangleSplineBranchFormulae
TS56.MellinJackson.TriangleSplineBranchFormulaeTarget
TS56.MellinJackson.triangleSplineBranchFormulaeTarget
```

It does not prove classical derivative, boundary, distributional, Plancherel,
or Fourier-tail statements. It gives the next Sobolev-side sprint a concrete
affine starting point on `[-1, 0]` and `[0, 1]`.

## Remaining Analytic Infrastructure

The final TS20 ledger names the remaining analytic obligations:

| Obligation | Role |
| --- | --- |
| `MellinFourierNormBridge` | logarithmic Mellin/Fourier norm bridge |
| `MellinFourierMeasureTransport` | a.e. transport between weighted, restricted, exp, and log measures |
| `MellinFourierMeasurabilityTransport` | strong measurability for the representative Mellin/Fourier operators |
| `MellinFourierAEEqTransport` | descent of the representative operators to `AEEqFun` |
| `MellinFourierLpIsometryInfrastructure` | `Memℒp`, norm, and linearity inputs for the future `Lp` isometry |
| `MellinFourierLpNormInputs` | `Memℒp` and `snorm` preservation inputs for the future `Lp` isometry |
| `MellinFourierLpLinearityInputs` | a.e. additivity and scalar-compatibility inputs for the future `Lp` isometry |
| `MellinFourierLpIsometry` | final `LinearIsometryEquiv` specification tied to `TsigmaFun`/`TsigmaInvFun` |
| `FourierTailInfrastructure` | Plancherel, derivative-control, and high-frequency tail estimate |
| `FourierAPINormalizationLedger` | concrete Fourier API and normalization choices for a future TS40 instance |
| `TriangleSplineTailInfrastructure` | triangle-spline derivative norm, Sobolev agreement, and Mellin-tail route |
| `TriangleSplineDerivativeSnormInfrastructure` | local triangle-spline derivative `snorm <= 2` estimate |
| `TriangleSplineSupportMeasureInputs` | Lebesgue measure bound for the triangle-spline support interval |
| `TriangleSplineSobolevAgreementInfrastructure` | agreement between the TS41 Sobolev derivative slot and `triangleSplineDeriv` |
| `TriangleSplineSobolevAgreementLedger` | decomposed branch, boundary, distributional, and Sobolev-slot obligations for the triangle spline |
| `TriangleSplineTailAssemblyInputs` | assembly inputs joining TS48 norm control, TS49 Sobolev agreement, and tail comparison |
| `TriangleSplineFourierTailComparisonInputs` | TS40/TS49-compatible high-frequency tail comparison for the triangle spline |
| `MathlibFourierAPIBinding` | concrete binding layer between TS41 Fourier ledger slots and future Mathlib Fourier theorem instances |
| `FourierConcreteSymbolLedger` | checked concrete Mathlib Fourier symbols and remaining Plancherel-symbol gap |
| `FourierPlancherelL2Contract` | compatible Plancherel/snorm theorem needed after the TS53 symbol probe |
| `DirichletCharacterBridge` | character orthogonality and bridge error |
| `LargeSieveInfrastructure` | local large-sieve estimate with `C <= 1` |
| `BrunTitchmarshLocalWindowBudget` | pointwise short-window prime count budget |
| `BrunTitchmarshShortInterval` | stronger threshold-form short-interval budget, currently `K = 20` |
| `BrunTitchmarshScaleBridge` | domination of the exact integer window-budget scale by a chosen closed-form scale |
| `BrunTitchmarshNatIntervalBound` | natural-interval prime-count Brun-Titchmarsh theorem |
| `SelbergSieveIntervalBound` | Selberg-sieve theorem producing an explicit local interval majorant |
| `SelbergMajorantBudgetComparison` | arithmetic comparison from Selberg majorant to TS22 BT budget |
| `ScaledLargeSieveInfrastructure` | large-sieve estimate targeting an explicit `ShortIntervalScale` |
| `ScaleToOTSAControl` | analytic cost of carrying a TS22 scale into OTSA |
| `ScaledOTSAAdmissible` | local numerical threshold for scaled OTSA constants |
| `PaddedScaleAnalyticInfrastructure` | TS25 package for the padded scale, interval BT, and OTSA admissibility |
| `OTSARationalCertificate` | rational upper-bound certificate for scaled OTSA admissibility |
| `OTSAConstantRegister` | labelled register for candidate rational OTSA constants |
| `LabelledOTSAConstantRegister` | typed-status register for smoke, candidate, and certified OTSA packages |
| `OTSAConstantProvenanceRegister` | provenance ledger for rational OTSA constant sources |
| `OTSACert_candidate_v1` | candidate-v1 rational OTSA admissibility package |
| `OTSAProvenance_candidate_v1` | candidate-v1 provenance ledger with remaining placeholders |
| `TraceMajorantContract` | conditional trace-contribution contract with target `Ct <= 1/2` |
| `OTSACert_candidate_v2` | trace-conditional candidate-v2 rational OTSA package |
| `MellinTailMajorantContract` | conditional Mellin-tail contract with target `Cm <= 1` |
| `ScaleTransferMajorantContract` | conditional scale-transfer contract with target `Cscale <= 2` |
| `OTSACert_candidate_v3` | final-majorants conditional rational OTSA package |
| `KernelSpectralControl` | OTSA spectral-kernel control |
| `TraceContributionControl` | OTSA trace/pole control |
| `MellinTailDecay` | OTSA Mellin-tail decay |
| `OTSACouplingHypothesis` | residual coupling inequality |

These are the objects that must be instantiated by genuine analytic proofs to
turn the relative architecture into an unconditional formal proof route.

## Build

The repository uses Lean 4.15.0 / Mathlib v4.15.0.

Typical build for the current sprint chain:

```powershell
lake build TS.Goldbach.Strong.TS16.CombinatorialDischarge `
  TS.Goldbach.Strong.TS17.MellinJacksonDischarge `
  TS.Goldbach.Strong.TS18.SecondMomentDischarge `
  TS.Goldbach.Strong.TS19.OTSAResidualDischarge `
  TS.Goldbach.Strong.TS21.SecondMomentBudgetDischarge `
  TS.Goldbach.Strong.TS22.BrunTitchmarshScaleDischarge
```

Build all TS15--TS56 targets:

```powershell
lake build TS.Goldbach.Strong.TS15.ShortIntervalSecondMoment `
  TS.Goldbach.Strong.TS15.ProblemE1ShortIntervals `
  TS.Goldbach.Strong.TS15.PCB_Q1_Discharge `
  TS.Goldbach.Strong.TS15.MellinJacksonFourier `
  TS.Goldbach.Strong.TS15.OTSAResidualDecomposition `
  TS.Goldbach.Strong.TS16.CombinatorialDischarge `
  TS.Goldbach.Strong.TS17.MellinJacksonDischarge `
  TS.Goldbach.Strong.TS18.SecondMomentDischarge `
  TS.Goldbach.Strong.TS19.OTSAResidualDischarge `
  TS.Goldbach.Strong.TS21.ShortIntervalBudget `
  TS.Goldbach.Strong.TS21.BrunTitchmarshShortInterval `
  TS.Goldbach.Strong.TS21.BrunTitchmarshEnergyDischarge `
  TS.Goldbach.Strong.TS21.ThresholdComputation `
  TS.Goldbach.Strong.TS21.SecondMomentBudgetDischarge `
  TS.Goldbach.Strong.TS22.EnergyScale `
  TS.Goldbach.Strong.TS22.BrunTitchmarshScaleDischarge `
  TS.Goldbach.Strong.TS22.ClosedFormScales `
  TS.Goldbach.Strong.TS22.BrunTitchmarshIntervalBridge `
  TS.Goldbach.Strong.TS22.ScaledLargeSieveDischarge `
  TS.Goldbach.Strong.TS23.OTSAScalePropagation `
  TS.Goldbach.Strong.TS24.ClosedFormScaleBridge `
  TS.Goldbach.Strong.TS25.PaddedScaleOTSAFeasibility `
  TS.Goldbach.Strong.TS26.OTSANumericalFeasibility `
  TS.Goldbach.Strong.TS27.OTSAConstantRegister `
  TS.Goldbach.Strong.TS28.OTSAConstantsCandidate `
  TS.Goldbach.Strong.TS29.OTSAConstantProvenance `
  TS.Goldbach.Strong.TS30.BrunTitchmarshSelbergRoadmap `
  TS.Goldbach.Strong.TS31.OTSAAsymptoticMajorants `
  TS.Goldbach.Strong.TS32.OTSATraceMajorantRoadmap `
  TS.Goldbach.Strong.TS33.OTSAFinalMajorantsRoadmap `
  TS.Goldbach.Strong.TS34.MellinFourierMeasureTransport `
  TS.Goldbach.Strong.TS35.MellinFourierAEEqTransport `
  TS.Goldbach.Strong.TS36.MellinFourierLpIsometryRoadmap `
  TS.Goldbach.Strong.TS37.MellinFourierLpNormInputs `
  TS.Goldbach.Strong.TS38.MellinFourierLpLinearityInputs `
  TS.Goldbach.Strong.TS39.MellinFourierLpIsometry `
  TS.Goldbach.Strong.TS40.FourierTailRoadmap `
  TS.Goldbach.Strong.TS41.FourierAPIProbe `
  TS.Goldbach.Strong.TS42.MellinTailSplineRoadmap `
  TS.Goldbach.Strong.TS43.TriangleSplinePointwise `
  TS.Goldbach.Strong.TS44.TriangleSplineMeasurabilitySupport `
  TS.Goldbach.Strong.TS45.TriangleSplineDerivativeSnorm `
  TS.Goldbach.Strong.TS46.TriangleSplineSupportMeasure `
  TS.Goldbach.Strong.TS47.TriangleSplineSnormDischarge `
  TS.Goldbach.Strong.TS48.BoundedSupportSnormLemma `
  TS.Goldbach.Strong.TS49.TriangleSplineSobolevAgreement `
  TS.Goldbach.Strong.TS50.TriangleSplineTailAssembly `
  TS.Goldbach.Strong.TS51.TriangleSplineFourierTailComparison `
  TS.Goldbach.Strong.TS52.FourierMathlibAPIBinding `
  TS.Goldbach.Strong.TS53.FourierConcreteSymbolsProbe `
  TS.Goldbach.Strong.TS54.FourierPlancherelGapLedger `
  TS.Goldbach.Strong.TS55.TriangleSplineSobolevAgreementLedger `
  TS.Goldbach.Strong.TS56.TriangleSplineBranchFormulae
```

## Audit

Audited scope:

```text
TS/Goldbach/Strong/TS15
TS/Goldbach/Strong/TS16
TS/Goldbach/Strong/TS17
TS/Goldbach/Strong/TS18
TS/Goldbach/Strong/TS19
TS/Goldbach/Strong/TS21
TS/Goldbach/Strong/TS22
TS/Goldbach/Strong/TS23
TS/Goldbach/Strong/TS24
TS/Goldbach/Strong/TS25
TS/Goldbach/Strong/TS26
TS/Goldbach/Strong/TS27
TS/Goldbach/Strong/TS28
TS/Goldbach/Strong/TS29
TS/Goldbach/Strong/TS30
TS/Goldbach/Strong/TS31
TS/Goldbach/Strong/TS32
TS/Goldbach/Strong/TS33
TS/Goldbach/Strong/TS34
TS/Goldbach/Strong/TS35
TS/Goldbach/Strong/TS36
TS/Goldbach/Strong/TS37
TS/Goldbach/Strong/TS38
TS/Goldbach/Strong/TS39
TS/Goldbach/Strong/TS40
TS/Goldbach/Strong/TS41
TS/Goldbach/Strong/TS42
TS/Goldbach/Strong/TS43
TS/Goldbach/Strong/TS44
TS/Goldbach/Strong/TS45
TS/Goldbach/Strong/TS46
TS/Goldbach/Strong/TS47
TS/Goldbach/Strong/TS48
TS/Goldbach/Strong/TS49
TS/Goldbach/Strong/TS50
TS/Goldbach/Strong/TS51
TS/Goldbach/Strong/TS52
TS/Goldbach/Strong/TS53
TS/Goldbach/Strong/TS54
TS/Goldbach/Strong/TS55
TS/Goldbach/Strong/TS56
```

Audit commands:

```powershell
rg -n "s[o]rry" TS\Goldbach\Strong\TS15 TS\Goldbach\Strong\TS16 TS\Goldbach\Strong\TS17 TS\Goldbach\Strong\TS18 TS\Goldbach\Strong\TS19 TS\Goldbach\Strong\TS21 TS\Goldbach\Strong\TS22 TS\Goldbach\Strong\TS23 TS\Goldbach\Strong\TS24 TS\Goldbach\Strong\TS25 TS\Goldbach\Strong\TS26 TS\Goldbach\Strong\TS27 TS\Goldbach\Strong\TS28 TS\Goldbach\Strong\TS29 TS\Goldbach\Strong\TS30 TS\Goldbach\Strong\TS31 TS\Goldbach\Strong\TS32 TS\Goldbach\Strong\TS33 TS\Goldbach\Strong\TS34 TS\Goldbach\Strong\TS35 TS\Goldbach\Strong\TS36 TS\Goldbach\Strong\TS37 TS\Goldbach\Strong\TS38 TS\Goldbach\Strong\TS39 TS\Goldbach\Strong\TS40 TS\Goldbach\Strong\TS41 TS\Goldbach\Strong\TS42 TS\Goldbach\Strong\TS43 TS\Goldbach\Strong\TS44 TS\Goldbach\Strong\TS45 TS\Goldbach\Strong\TS46 TS\Goldbach\Strong\TS47 TS\Goldbach\Strong\TS48 TS\Goldbach\Strong\TS49 TS\Goldbach\Strong\TS50 TS\Goldbach\Strong\TS51 TS\Goldbach\Strong\TS52 TS\Goldbach\Strong\TS53 TS\Goldbach\Strong\TS54 TS\Goldbach\Strong\TS55 TS\Goldbach\Strong\TS56
rg -n "a[x]iom" TS\Goldbach\Strong\TS15 TS\Goldbach\Strong\TS16 TS\Goldbach\Strong\TS17 TS\Goldbach\Strong\TS18 TS\Goldbach\Strong\TS19 TS\Goldbach\Strong\TS21 TS\Goldbach\Strong\TS22 TS\Goldbach\Strong\TS23 TS\Goldbach\Strong\TS24 TS\Goldbach\Strong\TS25 TS\Goldbach\Strong\TS26 TS\Goldbach\Strong\TS27 TS\Goldbach\Strong\TS28 TS\Goldbach\Strong\TS29 TS\Goldbach\Strong\TS30 TS\Goldbach\Strong\TS31 TS\Goldbach\Strong\TS32 TS\Goldbach\Strong\TS33 TS\Goldbach\Strong\TS34 TS\Goldbach\Strong\TS35 TS\Goldbach\Strong\TS36 TS\Goldbach\Strong\TS37 TS\Goldbach\Strong\TS38 TS\Goldbach\Strong\TS39 TS\Goldbach\Strong\TS40 TS\Goldbach\Strong\TS41 TS\Goldbach\Strong\TS42 TS\Goldbach\Strong\TS43 TS\Goldbach\Strong\TS44 TS\Goldbach\Strong\TS45 TS\Goldbach\Strong\TS46 TS\Goldbach\Strong\TS47 TS\Goldbach\Strong\TS48 TS\Goldbach\Strong\TS49 TS\Goldbach\Strong\TS50 TS\Goldbach\Strong\TS51 TS\Goldbach\Strong\TS52 TS\Goldbach\Strong\TS53 TS\Goldbach\Strong\TS54 TS\Goldbach\Strong\TS55 TS\Goldbach\Strong\TS56
```

Expected result: no matches.

## TS20 Manuscript

The synthesis document is available at:

```text
TS/Goldbach/Strong/TS20/TS20_Horizon_Goldbach_Synthesis.tex
```

It summarizes TS15--TS19 and records the final analytic infrastructure ledger.
It is written for XeLaTeX because it uses `fontspec`.

## Repository Note

The root project also contains older Horizon/Goldbach modules. Some older
areas may have their own independent audit status. The sprint chain documented
above is specifically the audited `TS/Goldbach/Strong/TS15`--`TS56` layer.
