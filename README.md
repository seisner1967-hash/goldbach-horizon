# Horizon Goldbach

Lean 4 formal specification programme for a conditional architecture around the
binary Goldbach conjecture.

This repository does **not** claim an unconditional proof of Goldbach. Its goal
is narrower and auditable: decompose the proof architecture into Lean-checked
modules, prove the finite/combinatorial layer, and expose the remaining
analytic work as named local infrastructure obligations.

## Current Focus: TS15--TS88

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
  TS57/
  TS58/
  TS59/
  TS60/
  TS61/
  TS62/
  TS63/
  TS64/
  TS65/
  TS66/
  TS67/
  TS68/
  TS69/
  TS70/
  TS71/
  TS72/
  TS73/
  TS74/
  TS75/
  TS76/
  TS77/
  TS78/
  TS79/
  TS80/
  TS81/
  TS82/
  TS83/
  TS84/
  TS85/
  TS86/
  TS87/
  TS88/
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
| TS57 | Triangle spline classical branch derivatives | `repo_committed` | proves classical derivatives on `(-1, 0)` and `(0, 1)` and agreement with `triangleSplineDeriv` |
| TS58 | Triangle spline boundary and exterior control | `repo_committed` | proves exterior derivative `0`, exterior agreement with `triangleSplineDeriv`, and nullity of the corner set |
| TS59 | Triangle spline off-corner classical derivative | `repo_committed` | proves the pointwise derivative agreement away from `{ -1, 0, 1 }` |
| TS60 | Triangle spline a.e. classical derivative | `repo_committed` | lifts TS59 through the null corner set to prove a.e. derivative agreement |
| TS61 | Triangle spline distributional derivative ledger | `repo_committed_relative` | records the weak-derivative identity contract and the TS60 a.e. input package |
| TS62 | Triangle spline test-function API probe | `repo_committed_relative` | binds the TS61 abstract test-function API to a concrete C1 compact-support package |
| TS63 | Triangle spline concrete distributional contract | `repo_committed_relative` | specializes the TS61 weak-derivative contract to the concrete TS62 test-function API |
| TS64 | Triangle spline IPP integrability inputs | `repo_committed_relative` | isolates the two Bochner-integrability inputs needed before proving the TS63 IPP identity |
| TS65 | Triangle spline IPP integrability discharge | `repo_committed` | proves the two TS64 Bochner-integrability inputs for the concrete TS62 test-function API |
| TS66 | Triangle spline IPP product support restriction | `repo_committed` | proves the two concrete IPP products vanish outside `[-1, 1]` |
| TS67 | Triangle spline IPP integral restriction | `repo_committed_relative` | fixes the integral-level restriction contract from global `volume` to `volume.restrict (Icc (-1) 1)` |
| TS68 | Triangle spline IPP integral restriction proof | `repo_committed` | proves the two TS67 integral-restriction equalities using TS66 support restriction |
| TS69 | Triangle spline IPP branch split | `repo_committed_relative` | fixes the branchwise split contract over `Icc (-1) 0` and `Ioc 0 1` |
| TS70 | Triangle spline IPP branch split proof | `repo_committed` | proves the TS69 branchwise split using disjoint restricted measures |
| TS71 | Triangle spline IPP right branch closed bridge | `repo_committed_relative` | fixes the bridge contract from `Ioc 0 1` to `Icc 0 1` |
| TS72 | Triangle spline IPP right branch closed bridge proof | `repo_committed` | proves the TS71 closed-right-branch bridge using the null endpoint |
| TS73 | Triangle spline IPP affine branch contract | `repo_committed_relative` | fixes the two local affine IPP identities on the closed branches |
| TS74 | Triangle spline IPP recombination from affine branches | `repo_committed_relative` | proves TS73 affine branch IPP is sufficient for the concrete TS63 contract |
| TS75 | Triangle spline IPP interval-integral bridge | `repo_committed_relative` | fixes the API bridge from restricted branch measures to directed interval integrals |
| TS76 | Triangle spline IPP interval-integral bridge proof | `repo_committed` | proves the TS75 bridge from restricted branch measures to directed interval integrals |
| TS77 | Triangle spline IPP affine branch proof | `repo_committed` | proves the two TS73 local affine integration-by-parts identities |
| TS78 | Triangle spline concrete distributional discharge | `repo_committed` | combines TS74 and TS77 to discharge the concrete TS63 weak-derivative contract |
| TS79 | Triangle spline distributional derivative discharge | `repo_committed` | lifts the concrete TS63 weak-derivative contract to the abstract TS61 distributional target |
| TS80 | Triangle spline Sobolev slot assembly | `repo_committed_relative` | packages TS60 and TS79, and isolates the exact TS41 Sobolev-slot agreement still needed for TS49/TS55 |
| TS81 | Triangle spline Sobolev slot API binding | `repo_committed_relative` | isolates the final TS41 API binding whose proof would close TS80, TS55, and TS49 |
| TS82 | Triangle spline Sobolev API reality probe | `repo_committed_relative` | records the current Mathlib Sobolev API gap and defines the recognition contract feeding TS81 |
| TS83 | Mellin-tail final API gap ledger | `repo_committed_relative` | packages the final Sobolev, Plancherel, and Fourier-tail API contracts needed for `Cm <= 1` |
| TS84 | Scale-transfer majorant roadmap | `repo_committed_relative` | opens the `Cscale <= 2` front and packages the final scale-transfer API contracts feeding TS33/TS25 |
| TS85 | Scale-transfer variance ledger | `repo_committed_relative` | decomposes the TS84 scale-transfer contract into a Gallagher-style variance-transfer obligation |
| TS86 | Grand-sieve variance roadmap | `repo_committed_relative` | decomposes the TS85 Gallagher contract into Farey-spacing and dual large-sieve variance obligations |
| TS87 | Farey spacing roadmap | `repo_committed_relative` | decomposes the TS86 Farey infrastructure into rational-point separation, covering, and counting contracts |
| TS88 | Farey separation proof | `repo_committed` | proves the classical `1 / (q q')` separation contract for TS87 Farey points |

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

TS57 proves the classical derivative facts on the two open affine branches:

```lean
TS57.MellinJackson.triangleSpline_hasDerivAt_left
TS57.MellinJackson.triangleSpline_hasDerivAt_right
TS57.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_left
TS57.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_right
TS57.MellinJackson.TriangleSplineClassicalBranchDerivatives
TS57.MellinJackson.triangleSplineClassicalBranchDerivatives
TS57.MellinJackson.TriangleSplineClassicalBranchDerivativesTarget
TS57.MellinJackson.triangleSplineClassicalBranchDerivativesTarget
```

It does not prove global a.e. differentiability, boundary/raccord control, the
distributional derivative identity, Sobolev-slot agreement, Plancherel, or
Fourier-tail estimates.

TS58 proves the exterior derivative and boundary-null control facts:

```lean
TS58.MellinJackson.triangleSpline_hasDerivAt_left_exterior
TS58.MellinJackson.triangleSpline_hasDerivAt_right_exterior
TS58.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_left_exterior
TS58.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_right_exterior
TS58.MellinJackson.triangleSplineCornerSet
TS58.MellinJackson.volume_triangleSplineCornerSet
TS58.MellinJackson.TriangleSplineBoundaryExteriorControl
TS58.MellinJackson.triangleSplineBoundaryExteriorControl
TS58.MellinJackson.TriangleSplineBoundaryExteriorControlTarget
TS58.MellinJackson.triangleSplineBoundaryExteriorControlTarget
```

It does not prove global a.e. differentiability or the distributional
derivative identity. It isolates the two exterior open regions and the
Lebesgue-null corner set `{ -1, 0, 1 }`.

TS59 proves the pointwise off-corner classical derivative bridge:

```lean
TS59.MellinJackson.ne_neg_one_of_not_corner
TS59.MellinJackson.ne_zero_of_not_corner
TS59.MellinJackson.ne_one_of_not_corner
TS59.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_of_not_corner
TS59.MellinJackson.TriangleSplineOffCornerClassicalDerivative
TS59.MellinJackson.triangleSplineOffCornerClassicalDerivative
TS59.MellinJackson.TriangleSplineOffCornerClassicalDerivativeTarget
TS59.MellinJackson.triangleSplineOffCornerClassicalDerivativeTarget
```

It does not prove the a.e. derivative statement. It prepares it by combining
the branch and exterior derivative facts into a single theorem on the
complement of `triangleSplineCornerSet`.

TS60 proves the a.e. classical derivative bridge:

```lean
TS60.MellinJackson.ae_not_mem_triangleSplineCornerSet
TS60.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_ae
TS60.MellinJackson.deriv_triangleSpline_eq_triangleSplineDeriv_ae
TS60.MellinJackson.TriangleSplineAEClassicalDerivative
TS60.MellinJackson.triangleSplineAEClassicalDerivative
TS60.MellinJackson.TriangleSplineAEClassicalDerivativeTarget
TS60.MellinJackson.triangleSplineAEClassicalDerivativeTarget
```

It does not prove the distributional derivative identity or Sobolev-slot
agreement. It lifts the off-corner derivative theorem through the null corner
set using `measure_zero_iff_ae_nmem`.

TS61 records the distributional derivative ledger:

```lean
TS61.MellinJackson.TriangleSplineTestFunctionAPI
TS61.MellinJackson.TriangleSplineDistributionalDerivativeContract
TS61.MellinJackson.TriangleSplineDistributionalDerivativeTarget
TS61.MellinJackson.TriangleSplineDistributionalDerivativeInputs
TS61.MellinJackson.triangleSplineDistributionalDerivativeInputs
TS61.MellinJackson.TriangleSplineDistributionalDerivativeInputsTarget
TS61.MellinJackson.triangleSplineDistributionalDerivativeInputsTarget
```

It does not prove the weak derivative identity. It fixes the test-function
interface and records the TS60 a.e. classical derivative bridge as an input for
the future integration-by-parts proof.

TS62 records the concrete test-function API probe:

```lean
TS62.MellinJackson.TriangleSplineConcreteTestFunction
TS62.MellinJackson.triangleSplineConcreteTestFunctionAPI
TS62.MellinJackson.TriangleSplineConcreteTestFunctionAPITarget
TS62.MellinJackson.triangleSplineConcreteTestFunctionAPITarget
```

It does not prove the distributional derivative identity or integration by
parts. It chooses a concrete C1 compact-support function package that can feed
the TS61 test-function interface.

TS63 specializes the distributional derivative contract to the concrete TS62
test-function API:

```lean
TS63.MellinJackson.TriangleSplineConcreteDistributionalContract
TS63.MellinJackson.distributionalContract_of_concrete
TS63.MellinJackson.TriangleSplineConcreteDistributionalContractTarget
TS63.MellinJackson.distributionalDerivativeTarget_of_concreteTarget
```

It does not prove the integration-by-parts identity. It states the exact
concrete weak-derivative identity for TS62 test functions and proves that this
concrete contract implies the abstract TS61 distributional target.

TS64 records the integration-by-parts integrability inputs:

```lean
TS64.MellinJackson.TriangleSplineIPPIntegrabilityInputs
TS64.MellinJackson.TriangleSplineIPPIntegrabilityTarget
```

It does not prove the IPP identity. It isolates the Bochner integrability of
the two products `triangleSpline * phi'` and `triangleSplineDeriv * phi`.

TS65 discharges the TS64 integrability package:

```lean
TS65.MellinJackson.triangleSpline_complex_measurable
TS65.MellinJackson.triangleSpline_complex_norm_le_two
TS65.MellinJackson.testFunction_integrable
TS65.MellinJackson.testFunction_deriv_integrable
TS65.MellinJackson.triangleSpline_mul_testFunctionDeriv_integrable
TS65.MellinJackson.triangleSplineDeriv_mul_testFunction_integrable
TS65.MellinJackson.triangleSplineIPPIntegrabilityInputs
TS65.MellinJackson.triangleSplineIPPIntegrabilityTarget
```

It still does not prove the IPP identity or the distributional derivative
identity. It removes the global product-integrability side conditions before
future branchwise integral splitting.

TS66 proves the pointwise support restriction for the two concrete IPP
products:

```lean
TS66.MellinJackson.left_ipp_product_zero_outside_Icc
TS66.MellinJackson.right_ipp_product_zero_outside_Icc
TS66.MellinJackson.TriangleSplineIPPProductSupportRestriction
TS66.MellinJackson.triangleSplineIPPProductSupportRestriction
TS66.MellinJackson.TriangleSplineIPPProductSupportRestrictionTarget
TS66.MellinJackson.triangleSplineIPPProductSupportRestrictionTarget
```

It does not restrict the global Bochner integrals to `[-1, 1]` and does not
prove the IPP identity. It prepares the next integral-restriction sprint by
showing both products vanish outside the triangle-spline support interval.

TS67 names the two concrete IPP integrands and records the exact
integral-restriction theorem shape:

```lean
TS67.MellinJackson.leftIPPIntegrand
TS67.MellinJackson.rightIPPIntegrand
TS67.MellinJackson.TriangleSplineIPPIntegralRestrictionInputs
TS67.MellinJackson.triangleSplineIPPIntegralRestrictionInputs
TS67.MellinJackson.TriangleSplineIPPIntegralRestriction
TS67.MellinJackson.TriangleSplineIPPIntegralRestrictionTarget
TS67.MellinJackson.triangleSplineIPPIntegralRestrictionInputsTarget
```

It does not prove the integral restriction. It records that the future theorem
must turn the TS65 integrability package and the TS66 pointwise support package
into equality between global `volume` integrals and
`volume.restrict (Icc (-1) 1)` integrals.

TS68 discharges the TS67 integral-restriction contract:

```lean
TS68.MellinJackson.left_global_eq_restrict
TS68.MellinJackson.right_global_eq_restrict
TS68.MellinJackson.triangleSplineIPPIntegralRestriction
TS68.MellinJackson.TriangleSplineIPPIntegralRestrictionProofTarget
TS68.MellinJackson.triangleSplineIPPIntegralRestrictionTarget
TS68.MellinJackson.triangleSplineIPPIntegralRestrictionProofTarget
```

It uses Mathlib's `setIntegral_eq_integral_of_forall_compl_eq_zero` together
with the TS66 pointwise support facts. It still does not split `[-1, 1]` into
branches and does not prove the concrete integration-by-parts identity.

TS69 records the branchwise split contract for the TS68-restricted integrals:

```lean
TS69.MellinJackson.leftBranchSet
TS69.MellinJackson.rightBranchSet
TS69.MellinJackson.leftBranchMeasure
TS69.MellinJackson.rightBranchMeasure
TS69.MellinJackson.TriangleSplineIPPBranchSplit
TS69.MellinJackson.TriangleSplineIPPBranchSplitInputs
TS69.MellinJackson.triangleSplineIPPBranchSplitInputs
TS69.MellinJackson.TriangleSplineIPPBranchSplitTarget
TS69.MellinJackson.triangleSplineIPPBranchSplitInputsTarget
```

It uses the disjoint branch pair `Icc (-1 : Real) 0` and `Ioc (0 : Real) 1`
to avoid double-counting the point `0`. It does not prove the branch split,
does not convert the right branch to a closed interval, and does not prove the
concrete integration-by-parts identity.

TS70 discharges the TS69 branchwise split contract:

```lean
TS70.MellinJackson.branch_union_eq_Icc
TS70.MellinJackson.disjoint_left_right_branch
TS70.MellinJackson.restrict_Icc_eq_left_add_right
TS70.MellinJackson.integral_branch_split
TS70.MellinJackson.left_integral_split
TS70.MellinJackson.right_integral_split
TS70.MellinJackson.triangleSplineIPPBranchSplit
TS70.MellinJackson.TriangleSplineIPPBranchSplitProofTarget
TS70.MellinJackson.triangleSplineIPPBranchSplitTarget
TS70.MellinJackson.triangleSplineIPPBranchSplitProofTarget
```

It proves the disjoint decomposition `[-1, 1] = [-1, 0] union (0, 1]`,
splits the restricted measure, and then splits both concrete IPP integrals
using TS65 integrability. It still does not convert `(0, 1]` to `[0, 1]` and
does not prove affine integration by parts.

TS71 records the closed-right-branch bridge contract:

```lean
TS71.MellinJackson.rightClosedBranchSet
TS71.MellinJackson.rightClosedBranchMeasure
TS71.MellinJackson.TriangleSplineIPPRightBranchClosedBridge
TS71.MellinJackson.TriangleSplineIPPRightBranchClosedBridgeInputs
TS71.MellinJackson.triangleSplineIPPRightBranchClosedBridgeInputs
TS71.MellinJackson.TriangleSplineIPPRightBranchClosedBridgeTarget
TS71.MellinJackson.triangleSplineIPPRightBranchClosedBridgeInputsTarget
```

It fixes the theorem shape saying that the right-branch integrals over
`Ioc (0 : Real) 1` may be replaced by integrals over `Icc (0 : Real) 1` for
the two concrete IPP integrands. It does not prove that bridge and does not
prove affine integration by parts.

TS72 discharges the TS71 closed-right-branch bridge:

```lean
TS72.MellinJackson.rightBranchMeasure_eq_rightClosedBranchMeasure
TS72.MellinJackson.integral_rightBranch_eq_rightClosedBranch
TS72.MellinJackson.left_rightBranch_eq_closed
TS72.MellinJackson.right_rightBranch_eq_closed
TS72.MellinJackson.triangleSplineIPPRightBranchClosedBridge
TS72.MellinJackson.TriangleSplineIPPRightBranchClosedBridgeProofTarget
TS72.MellinJackson.triangleSplineIPPRightBranchClosedBridgeTarget
TS72.MellinJackson.triangleSplineIPPRightBranchClosedBridgeProofTarget
```

It proves that the restricted measures on `Ioc (0 : Real) 1` and
`Icc (0 : Real) 1` coincide, then rewrites the two concrete IPP right-branch
integrals through that measure equality. It still does not prove affine
integration by parts.

TS73 records the local affine IPP contract:

```lean
TS73.MellinJackson.TriangleSplineIPPAffineBranchContract
TS73.MellinJackson.TriangleSplineIPPAffineBranchInputs
TS73.MellinJackson.triangleSplineIPPAffineBranchInputs
TS73.MellinJackson.TriangleSplineIPPAffineBranchContractTarget
TS73.MellinJackson.TriangleSplineIPPAffineBranchInputsTarget
TS73.MellinJackson.triangleSplineIPPAffineBranchInputsTarget
```

It fixes the exact left and right branch identities needed before
recombination. The left branch contributes `phi.toFun 0`; the right branch
contributes `- phi.toFun 0`. It does not prove either affine IPP identity.

TS74 proves the conditional recombination route from TS73 to TS63:

```lean
TS74.MellinJackson.concreteDistributionalContract_of_affineBranchContract
TS74.MellinJackson.TriangleSplineConcreteDistributionalFromAffineTarget
TS74.MellinJackson.triangleSplineConcreteDistributionalFromAffineTarget
TS74.MellinJackson.concreteDistributionalTarget_of_affineBranchTarget
```

It rewrites the global IPP integrals using TS68, TS70, and TS72, applies the
two local affine branch identities from TS73, cancels the boundary terms
`phi.toFun 0` and `- phi.toFun 0`, and reassembles the right-hand integral.
It does not prove the affine branch IPP identities themselves.

TS75 records the interval-integral API bridge needed before proving the affine
branch IPP identities:

```lean
TS75.MellinJackson.leftBranchIntervalIntegral
TS75.MellinJackson.rightClosedBranchIntervalIntegral
TS75.MellinJackson.TriangleSplineIPPIntervalIntegralBridge
TS75.MellinJackson.TriangleSplineIPPIntervalIntegralBridgeInputs
TS75.MellinJackson.triangleSplineIPPIntervalIntegralBridgeInputs
TS75.MellinJackson.TriangleSplineIPPIntervalIntegralBridgeTarget
TS75.MellinJackson.TriangleSplineIPPIntervalIntegralBridgeInputsTarget
TS75.MellinJackson.triangleSplineIPPIntervalIntegralBridgeInputsTarget
```

The TS73 affine branch contract is stated using restricted measures on the
closed branches. The one-dimensional calculus API in Mathlib is naturally
stated using directed interval integrals. TS75 fixes the exact conversion
facts needed between those two forms. It does not prove the conversion facts
and does not prove affine integration by parts.

TS76 discharges the TS75 interval-integral bridge:

```lean
TS76.MellinJackson.leftBranchMeasure_eq_leftIocMeasure
TS76.MellinJackson.integral_leftBranchMeasure_eq_interval
TS76.MellinJackson.integral_rightClosedBranchMeasure_eq_interval
TS76.MellinJackson.left_leftBranchMeasure_eq_interval
TS76.MellinJackson.right_leftBranchMeasure_eq_interval
TS76.MellinJackson.left_rightClosedBranchMeasure_eq_interval
TS76.MellinJackson.right_rightClosedBranchMeasure_eq_interval
TS76.MellinJackson.triangleSplineIPPIntervalIntegralBridge
TS76.MellinJackson.TriangleSplineIPPIntervalIntegralBridgeProofTarget
TS76.MellinJackson.triangleSplineIPPIntervalIntegralBridgeTarget
TS76.MellinJackson.triangleSplineIPPIntervalIntegralBridgeProofTarget
```

It uses `restrict_Ioc_eq_restrict_Icc` to remove endpoint singletons from the
closed-branch restricted measures, then `intervalIntegral.integral_of_le` to
match Mathlib's directed interval-integral form on `[-1, 0]` and `[0, 1]`.
It still does not prove affine integration by parts.

TS77 discharges the TS73 affine branch IPP contract:

```lean
TS77.MellinJackson.leftAffine
TS77.MellinJackson.rightAffine
TS77.MellinJackson.testFunction_hasDerivAt
TS77.MellinJackson.leftAffine_hasDerivAt
TS77.MellinJackson.rightAffine_hasDerivAt
TS77.MellinJackson.left_affine_interval_ipp
TS77.MellinJackson.right_affine_interval_ipp
TS77.MellinJackson.leftIPPIntegrand_eq_leftAffine_interval
TS77.MellinJackson.leftIPPIntegrand_eq_rightAffine_interval
TS77.MellinJackson.rightIPPIntegrand_eq_leftAffine_derivative_interval
TS77.MellinJackson.rightIPPIntegrand_eq_rightAffine_derivative_interval
TS77.MellinJackson.left_affine_ipp
TS77.MellinJackson.right_affine_ipp
TS77.MellinJackson.triangleSplineIPPAffineBranchContract
TS77.MellinJackson.TriangleSplineIPPAffineBranchProofTarget
TS77.MellinJackson.triangleSplineIPPAffineBranchContractTarget
TS77.MellinJackson.triangleSplineIPPAffineBranchProofTarget
```

It uses Mathlib's interval-integral integration-by-parts theorem on the affine
functions `1 + x` and `1 - x`, then transports the results back through TS56
branch formulae, TS43 pointwise derivative values away from null endpoints,
and the TS76 restricted-measure-to-interval-integral bridge. TS77 closes the
local affine IPP step, but does not itself perform the TS74 recombination into
the concrete TS63 distributional contract.

TS78 discharges the concrete TS63 distributional contract:

```lean
TS78.MellinJackson.triangleSplineConcreteDistributionalContract
TS78.MellinJackson.triangleSplineConcreteDistributionalContractTarget
TS78.MellinJackson.TriangleSplineConcreteDistributionalDischargeTarget
TS78.MellinJackson.triangleSplineConcreteDistributionalDischargeTarget
```

It mechanically applies the TS74 recombination theorem to the TS77 affine
branch IPP package. Thus the concrete weak-derivative identity against the
TS62 test-function API is now proved. TS78 does not yet lift this concrete
contract to the abstract TS61 distributional target or the TS49 Sobolev slot.

TS79 discharges the abstract TS61 distributional derivative target:

```lean
TS79.MellinJackson.triangleSplineDistributionalDerivativeContract
TS79.MellinJackson.triangleSplineDistributionalDerivativeTarget
TS79.MellinJackson.TriangleSplineDistributionalDerivativeDischargeTarget
TS79.MellinJackson.triangleSplineDistributionalDerivativeDischargeTarget
```

It applies the TS63 concrete-to-abstract bridge to the concrete TS78 contract.
Thus the weak-derivative identity is now available at the abstract TS61 ledger
level. TS79 does not yet prove the TS49 Sobolev-slot agreement or any
Plancherel/Fourier-tail estimate.

TS80 packages the TS60 a.e. classical derivative input and the TS79 abstract
distributional derivative input:

```lean
TS80.MellinJackson.TriangleSplineSobolevSlotAssemblyInputs
TS80.MellinJackson.triangleSplineSobolevSlotAssemblyInputs
TS80.MellinJackson.TriangleSplineSobolevSlotAssembly
TS80.MellinJackson.triangleSplineSobolevAgreementLedger
TS80.MellinJackson.triangleSplineSobolevAgreementInfrastructure
TS80.MellinJackson.triangleSplineSobolevSlotAssemblyInputsTarget
TS80.MellinJackson.triangleSplineSobolevAgreementLedgerTarget_of_slotAssemblyTarget
TS80.MellinJackson.triangleSplineSobolevAgreementTarget_of_slotAssemblyTarget
```

It isolates the exact remaining TS41 Sobolev derivative slot agreement and
proves that this single slot agreement is sufficient to discharge both the
TS55 ledger target and the TS49 Sobolev-agreement target. TS80 does not choose
a concrete Fourier/Sobolev API, prove Plancherel, or prove a Fourier-tail
estimate.

TS81 isolates the final API-level binding needed after TS80:

```lean
TS81.MellinJackson.TriangleSplineSobolevSlotAPIBinding
TS81.MellinJackson.triangleSplineSobolevSlotAssembly_of_apiBinding
TS81.MellinJackson.TriangleSplineSobolevSlotAPIBindingTarget
TS81.MellinJackson.triangleSplineSobolevSlotAssemblyTarget_of_apiBindingTarget
TS81.MellinJackson.triangleSplineSobolevAgreementLedgerTarget_of_apiBindingTarget
TS81.MellinJackson.triangleSplineSobolevAgreementTarget_of_apiBindingTarget
```

It states the exact condition required of the chosen TS41 ledger:
`api.sobolevDerivative 1 triangleSpline` must agree a.e. with
`triangleSplineDeriv`. Once this API binding is supplied, TS81 produces the
TS80 assembly target and then the TS55/TS49 Sobolev targets. TS81 does not
construct a concrete Mathlib Sobolev API or prove weak-derivative uniqueness.

TS82 records the current Sobolev/weak-derivative API probe:

```lean
TS82.MellinJackson.SobolevAPIProbeStatus
TS82.MellinJackson.TriangleSplineSobolevAPIRealityProbe
TS82.MellinJackson.triangleSplineSobolevAPIRealityProbe
TS82.MellinJackson.SobolevSlotRecognitionContract
TS82.MellinJackson.apiBinding_of_sobolevSlotRecognitionContract
TS82.MellinJackson.TriangleSplineSobolevAPIRealityProbeTarget
TS82.MellinJackson.SobolevSlotRecognitionContractTarget
TS82.MellinJackson.triangleSplineSobolevAPIRealityProbeTarget
TS82.MellinJackson.apiBindingTarget_of_recognitionContractTarget
TS82.MellinJackson.sobolevSlotAssemblyTarget_of_recognitionContractTarget
TS82.MellinJackson.sobolevAgreementLedgerTarget_of_recognitionContractTarget
TS82.MellinJackson.sobolevAgreementTarget_of_recognitionContractTarget
```

It records that the current local Mathlib probe locates Sobolev-inequality
material, but no ready-made weak-derivative/Sobolev representative API matching
the TS41 `sobolevDerivative` slot. It also defines the exact recognition
contract that will feed TS81, then TS80, then TS55/TS49 once a concrete API
proof is supplied.

TS83 records the final API-gap ledger for the Mellin-tail route:

```lean
TS83.MellinJackson.MellinTailFinalAPIGapLedger
TS83.MellinJackson.mellinTailFinalAPIGapLedger
TS83.MellinJackson.MellinTailFinalAPIContracts
TS83.MellinJackson.sobolevSlotAssembly_of_recognitionContract
TS83.MellinJackson.sobolevAgreementInfrastructure_of_recognitionContract
TS83.MellinJackson.triangleSplineFourierTailComparisonInputs_of_finalAPIContracts
TS83.MellinJackson.MellinTailFinalAPIGapLedgerTarget
TS83.MellinJackson.MellinTailFinalAPIContractsTarget
TS83.MellinJackson.mellinTailFinalAPIGapLedgerTarget
TS83.MellinJackson.sobolevSlotRecognitionContractTarget_of_finalAPIContractsTarget
TS83.MellinJackson.fourierPlancherelL2Target_of_finalAPIContractsTarget
TS83.MellinJackson.triangleSplineFourierTailComparisonTarget_of_finalAPIContractsTarget
TS83.MellinJackson.triangleSplineTailTarget_of_finalAPIContractsTarget
TS83.MellinJackson.mellinTailContractTarget_of_finalAPIContractsTarget
```

It proves that a compatible final package containing the TS82 Sobolev-slot
recognition contract, the TS54 Plancherel/L2 contract, and the TS51 Fourier-tail
comparison package yields the TS33 Mellin-tail majorant contract `Cm <= 1`.
TS83 does not prove those external API contracts; it makes the remaining
Mellin-tail dependencies explicit and mechanically connected.

TS84 opens the scale-transfer majorant front:

```lean
TS84.Goldbach.ScaleTransferMajorantRoadmap
TS84.Goldbach.scaleTransferMajorantRoadmap
TS84.Goldbach.ScaleTransferMajorantAPIContracts
TS84.Goldbach.scaleTransferMajorantContract_of_apiContracts
TS84.Goldbach.OTSAFinalMajorantAPIContracts
TS84.Goldbach.mellinTailMajorantContract_of_finalAPIContracts
TS84.Goldbach.scaleTransferMajorantContract_of_finalAPIContracts
TS84.Goldbach.OTSACert_candidate_v3_of_finalAPIContracts
TS84.Goldbach.OTSARegister_candidate_v3_of_finalAPIContracts
TS84.Goldbach.OTSAProvenance_candidate_v3_of_finalAPIContracts
TS84.Goldbach.scaledOTSAAdmissible_of_finalAPIContracts
TS84.Goldbach.PaddedScaleTransferFinalAPIContracts
TS84.Goldbach.paddedScaleAnalyticInfrastructure_of_finalAPIContracts
TS84.Goldbach.ScaleTransferMajorantRoadmapTarget
TS84.Goldbach.ScaleTransferMajorantAPIContractsTarget
TS84.Goldbach.OTSAFinalMajorantAPIContractsTarget
TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget
TS84.Goldbach.scaleTransferMajorantRoadmapTarget
TS84.Goldbach.scaleTransferMajorantContractTarget_of_apiContractsTarget
TS84.Goldbach.traceMajorantContractTarget_of_finalAPIContractsTarget
TS84.Goldbach.mellinTailFinalAPIContractsTarget_of_finalAPIContractsTarget
TS84.Goldbach.scaleTransferMajorantContractTarget_of_finalAPIContractsTarget
TS84.Goldbach.OTSACert_candidate_v3_target_of_finalAPIContractsTarget
TS84.Goldbach.OTSARegister_candidate_v3_target_of_finalAPIContractsTarget
TS84.Goldbach.OTSAProvenance_candidate_v3_target_of_finalAPIContractsTarget
TS84.Goldbach.scaledOTSAAdmissibleTarget_of_finalAPIContractsTarget
TS84.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_finalAPIContractsTarget
```

It does not prove a Gallagher/large-sieve scale-transfer theorem. It records
that the remaining `Cscale` work is to supply a padded TS23 scale control and a
compatible rational bound `Cscale <= 2`; once supplied, these contracts combine
with the TS32 trace contract and the TS83 Mellin-tail package to feed TS33 and
the TS25 padded-scale infrastructure.

TS85 decomposes the scale-transfer front one layer further:

```lean
TS85.Goldbach.ScaleTransferVarianceLedger
TS85.Goldbach.scaleTransferVarianceLedger
TS85.Goldbach.GallagherVarianceTransferContract
TS85.Goldbach.scaleToOTSAControl_of_gallagherVariance
TS85.Goldbach.PaddedGallagherVarianceTransferContract
TS85.Goldbach.scaleTransferMajorantAPIContracts_of_paddedGallagher
TS85.Goldbach.ScaleTransferVarianceLedgerTarget
TS85.Goldbach.GallagherVarianceTransferContractTarget
TS85.Goldbach.PaddedGallagherVarianceTransferContractTarget
TS85.Goldbach.scaleTransferVarianceLedgerTarget
TS85.Goldbach.scaleToOTSAControlTarget_of_gallagherVarianceTarget
TS85.Goldbach.scaleTransferMajorantAPIContractsTarget_of_paddedGallagherTarget
TS85.Goldbach.scaleTransferMajorantContractTarget_of_paddedGallagherTarget
TS85.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedGallagher
TS85.Goldbach.PaddedScaleTransferFinalAPIContractsTarget_of_BrunTitchmarsh_trace_mellin_paddedGallagher
TS85.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedGallagher
```

It does not prove Gallagher's variance estimate. It isolates the exact
Gallagher-style contract that produces the padded TS23 scale-to-OTSA control,
then proves that this contract feeds the TS84 final majorant package and the
TS25 padded-scale infrastructure.

TS86 opens the grand-sieve variance layer beneath TS85:

```lean
TS86.Goldbach.GrandSieveVarianceRoadmap
TS86.Goldbach.grandSieveVarianceRoadmap
TS86.Goldbach.FareySpacingInfrastructure
TS86.Goldbach.DualLargeSieveVarianceBound
TS86.Goldbach.GrandSieveVarianceInfrastructure
TS86.Goldbach.gallagherVarianceTransferContract_of_grandSieveVariance
TS86.Goldbach.PaddedGrandSieveVarianceInfrastructure
TS86.Goldbach.paddedGallagherVarianceTransferContract_of_grandSieveVariance
TS86.Goldbach.GrandSieveVarianceRoadmapTarget
TS86.Goldbach.FareySpacingInfrastructureTarget
TS86.Goldbach.DualLargeSieveVarianceBoundTarget
TS86.Goldbach.GrandSieveVarianceInfrastructureTarget
TS86.Goldbach.PaddedGrandSieveVarianceInfrastructureTarget
TS86.Goldbach.grandSieveVarianceRoadmapTarget
TS86.Goldbach.grandSieveVarianceInfrastructure_of_farey_dualLargeSieve
TS86.Goldbach.grandSieveVarianceInfrastructureTarget_of_farey_dualLargeSieveTargets
TS86.Goldbach.gallagherVarianceTransferContractTarget_of_grandSieveVarianceTarget
TS86.Goldbach.paddedGallagherVarianceTransferContractTarget_of_paddedGrandSieveTarget
TS86.Goldbach.scaleTransferMajorantAPIContractsTarget_of_paddedGrandSieveTarget
TS86.Goldbach.scaleTransferMajorantContractTarget_of_paddedGrandSieveTarget
TS86.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedGrandSieve
TS86.Goldbach.PaddedScaleTransferFinalAPIContractsTarget_of_BrunTitchmarsh_trace_mellin_paddedGrandSieve
TS86.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedGrandSieve
```

It does not prove the grand sieve or Farey-spacing estimates. It records that
Farey geometry plus a compatible dual large-sieve variance bound imply the
TS85 Gallagher contract, and hence the TS84/TS25 scale-transfer assembly.

TS87 opens the Farey-spacing layer beneath TS86:

```lean
TS87.Goldbach.FareyPoint
TS87.Goldbach.FareyPoint.value
TS87.Goldbach.FareyPoint.denBound
TS87.Goldbach.FareyPoint.valueDistinct
TS87.Goldbach.FareySeparationStatement
TS87.Goldbach.FareySeparationContract
TS87.Goldbach.FareyCoveringContract
TS87.Goldbach.FareyCountingContract
TS87.Goldbach.FareySpacingContract
TS87.Goldbach.FareySpacingRoadmap
TS87.Goldbach.fareySpacingInfrastructure_of_contract
TS87.Goldbach.FareySpacingRoadmapTarget
TS87.Goldbach.FareySeparationContractTarget
TS87.Goldbach.FareyCoveringContractTarget
TS87.Goldbach.FareyCountingContractTarget
TS87.Goldbach.FareySpacingContractTarget
TS87.Goldbach.fareySpacingRoadmapTarget
TS87.Goldbach.fareySpacingContractTarget_of_components
TS87.Goldbach.fareySpacingInfrastructureTarget_of_contractTarget
TS87.Goldbach.grandSieveVarianceInfrastructureTarget_of_fareyContract_dualLargeSieveTarget
TS87.Goldbach.paddedGrandSieveVarianceInfrastructureTarget_of_fareyContract_paddedDualLargeSieveTarget
TS87.Goldbach.paddedGallagherVarianceTransferContractTarget_of_fareyContract_paddedDualLargeSieveTarget
TS87.Goldbach.scaleTransferMajorantAPIContractsTarget_of_fareyContract_paddedDualLargeSieveTarget
TS87.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_farey_paddedDualLargeSieve
TS87.Goldbach.PaddedScaleTransferFinalAPIContractsTarget_of_BrunTitchmarsh_trace_mellin_farey_paddedDualLargeSieve
TS87.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_farey_paddedDualLargeSieve
```

It does not prove the Farey separation theorem, covering lemma, counting
lemma, or the dual large sieve. It records the rational-point API and the
local arithmetic contracts whose discharge would feed the TS86/TS85/TS84/TS25
scale-transfer assembly.

TS88 proves the Farey separation contract from TS87:

```lean
TS88.Goldbach.fareyCrossDiff
TS88.Goldbach.one_le_abs_int_cast
TS88.Goldbach.fareyCrossDiff_ne_zero_of_valueDistinct
TS88.Goldbach.farey_value_sub_eq_crossDiff_div
TS88.Goldbach.fareySeparationStatement
TS88.Goldbach.fareySeparationContract
TS88.Goldbach.fareySeparationContractTarget
TS88.Goldbach.FareySeparationProofTarget
TS88.Goldbach.fareySeparationProofTarget
TS88.Goldbach.fareySpacingContractTarget_of_covering_counting
TS88.Goldbach.fareySpacingInfrastructureTarget_of_covering_counting
TS88.Goldbach.paddedGrandSieveVarianceInfrastructureTarget_of_covering_counting_paddedDualLargeSieveTarget
TS88.Goldbach.scaleTransferMajorantAPIContractsTarget_of_covering_counting_paddedDualLargeSieveTarget
```

The proof is elementary: distinct real values force the integer
cross-difference `a*q' - a'*q` to be nonzero; a nonzero integer has real
absolute value at least `1`; division by the positive denominator product gives
the TS87 separation statement. TS88 does not prove Farey covering, Farey
counting, or the dual large sieve.

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
| `TriangleSplineSobolevSlotAssembly` | packages TS60 and TS79, leaving the exact TS41 `sobolevDerivative` slot agreement explicit |
| `TriangleSplineSobolevSlotAPIBinding` | final API-level proof that the selected TS41 `sobolevDerivative` recognizes `triangleSplineDeriv` |
| `SobolevSlotRecognitionContract` | concrete Sobolev/weak-derivative API proof feeding TS81 and closing the triangle-spline Sobolev slot |
| `MellinTailFinalAPIContracts` | compatible final package combining Sobolev recognition, Plancherel/L2, and Fourier-tail comparison for `Cm <= 1` |
| `ScaleTransferMajorantAPIContracts` | padded TS23 scale control plus compatible rational `Cscale <= 2` |
| `OTSAFinalMajorantAPIContracts` | final trace, Mellin-tail, and scale-transfer contracts feeding TS33 v3 |
| `PaddedScaleTransferFinalAPIContracts` | Brun-Titchmarsh input plus final majorants feeding TS25 padded-scale infrastructure |
| `GallagherVarianceTransferContract` | scale-level Gallagher/variance transfer contract feeding TS23 scale control |
| `PaddedGallagherVarianceTransferContract` | Gallagher transfer contract specialized to the TS24 padded scale |
| `FareySpacingInfrastructure` | rational-point spacing, covering, and counting geometry for the grand-sieve layer |
| `FareyPoint` | integer-numerator, positive-denominator rational point API for the Farey layer |
| `FareyCoveringContract` | covering geometry needed by the Gallagher/large-sieve transfer |
| `FareyCountingContract` | counting of selected rational points in Farey windows |
| `FareySpacingContract` | package combining Farey separation, covering, and counting contracts |
| `DualLargeSieveVarianceBound` | scale-level dual large-sieve variance estimate feeding Gallagher transfer |
| `GrandSieveVarianceInfrastructure` | Farey geometry plus dual large-sieve variance package feeding TS85 |
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

Build all TS15--TS88 targets:

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
  TS.Goldbach.Strong.TS56.TriangleSplineBranchFormulae `
  TS.Goldbach.Strong.TS57.TriangleSplineClassicalBranchDerivatives `
  TS.Goldbach.Strong.TS58.TriangleSplineBoundaryExteriorControl `
  TS.Goldbach.Strong.TS59.TriangleSplineOffCornerClassicalDerivative `
  TS.Goldbach.Strong.TS60.TriangleSplineAEClassicalDerivative `
  TS.Goldbach.Strong.TS61.TriangleSplineDistributionalDerivativeLedger `
  TS.Goldbach.Strong.TS62.TriangleSplineTestFunctionAPIProbe `
  TS.Goldbach.Strong.TS63.TriangleSplineConcreteDistributionalContract `
  TS.Goldbach.Strong.TS64.TriangleSplineIPPIntegrabilityInputs `
  TS.Goldbach.Strong.TS65.TriangleSplineIPPIntegrabilityDischarge `
  TS.Goldbach.Strong.TS66.TriangleSplineIPPProductSupportRestriction `
  TS.Goldbach.Strong.TS67.TriangleSplineIPPIntegralRestriction `
  TS.Goldbach.Strong.TS68.TriangleSplineIPPIntegralRestrictionProof `
  TS.Goldbach.Strong.TS69.TriangleSplineIPPBranchSplit `
  TS.Goldbach.Strong.TS70.TriangleSplineIPPBranchSplitProof `
  TS.Goldbach.Strong.TS71.TriangleSplineIPPRightBranchClosedBridge `
  TS.Goldbach.Strong.TS72.TriangleSplineIPPRightBranchClosedBridgeProof `
  TS.Goldbach.Strong.TS73.TriangleSplineIPPAffineBranchContract `
  TS.Goldbach.Strong.TS74.TriangleSplineIPPRecombinationFromAffine `
  TS.Goldbach.Strong.TS75.TriangleSplineIPPIntervalIntegralBridge `
  TS.Goldbach.Strong.TS76.TriangleSplineIPPIntervalIntegralBridgeProof `
  TS.Goldbach.Strong.TS77.TriangleSplineIPPAffineBranchProof `
  TS.Goldbach.Strong.TS78.TriangleSplineConcreteDistributionalDischarge `
  TS.Goldbach.Strong.TS79.TriangleSplineDistributionalDerivativeDischarge `
  TS.Goldbach.Strong.TS80.TriangleSplineSobolevSlotAssembly `
  TS.Goldbach.Strong.TS81.TriangleSplineSobolevSlotAPIBinding `
  TS.Goldbach.Strong.TS82.TriangleSplineSobolevAPIRealityProbe `
  TS.Goldbach.Strong.TS83.MellinTailFinalAPIGapLedger `
  TS.Goldbach.Strong.TS84.ScaleTransferMajorantRoadmap `
  TS.Goldbach.Strong.TS85.ScaleTransferVarianceLedger `
  TS.Goldbach.Strong.TS86.GrandSieveVarianceRoadmap `
  TS.Goldbach.Strong.TS87.FareySpacingRoadmap `
  TS.Goldbach.Strong.TS88.FareySeparationProof
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
TS/Goldbach/Strong/TS57
TS/Goldbach/Strong/TS58
TS/Goldbach/Strong/TS59
TS/Goldbach/Strong/TS60
TS/Goldbach/Strong/TS61
TS/Goldbach/Strong/TS62
TS/Goldbach/Strong/TS63
TS/Goldbach/Strong/TS64
TS/Goldbach/Strong/TS65
TS/Goldbach/Strong/TS66
TS/Goldbach/Strong/TS67
TS/Goldbach/Strong/TS68
TS/Goldbach/Strong/TS69
TS/Goldbach/Strong/TS70
TS/Goldbach/Strong/TS71
TS/Goldbach/Strong/TS72
TS/Goldbach/Strong/TS73
TS/Goldbach/Strong/TS74
TS/Goldbach/Strong/TS75
TS/Goldbach/Strong/TS76
TS/Goldbach/Strong/TS77
TS/Goldbach/Strong/TS78
TS/Goldbach/Strong/TS79
TS/Goldbach/Strong/TS80
TS/Goldbach/Strong/TS81
TS/Goldbach/Strong/TS82
TS/Goldbach/Strong/TS83
TS/Goldbach/Strong/TS84
TS/Goldbach/Strong/TS85
TS/Goldbach/Strong/TS86
TS/Goldbach/Strong/TS87
TS/Goldbach/Strong/TS88
```

Audit commands:

```powershell
rg -n "s[o]rry" TS\Goldbach\Strong\TS15 TS\Goldbach\Strong\TS16 TS\Goldbach\Strong\TS17 TS\Goldbach\Strong\TS18 TS\Goldbach\Strong\TS19 TS\Goldbach\Strong\TS21 TS\Goldbach\Strong\TS22 TS\Goldbach\Strong\TS23 TS\Goldbach\Strong\TS24 TS\Goldbach\Strong\TS25 TS\Goldbach\Strong\TS26 TS\Goldbach\Strong\TS27 TS\Goldbach\Strong\TS28 TS\Goldbach\Strong\TS29 TS\Goldbach\Strong\TS30 TS\Goldbach\Strong\TS31 TS\Goldbach\Strong\TS32 TS\Goldbach\Strong\TS33 TS\Goldbach\Strong\TS34 TS\Goldbach\Strong\TS35 TS\Goldbach\Strong\TS36 TS\Goldbach\Strong\TS37 TS\Goldbach\Strong\TS38 TS\Goldbach\Strong\TS39 TS\Goldbach\Strong\TS40 TS\Goldbach\Strong\TS41 TS\Goldbach\Strong\TS42 TS\Goldbach\Strong\TS43 TS\Goldbach\Strong\TS44 TS\Goldbach\Strong\TS45 TS\Goldbach\Strong\TS46 TS\Goldbach\Strong\TS47 TS\Goldbach\Strong\TS48 TS\Goldbach\Strong\TS49 TS\Goldbach\Strong\TS50 TS\Goldbach\Strong\TS51 TS\Goldbach\Strong\TS52 TS\Goldbach\Strong\TS53 TS\Goldbach\Strong\TS54 TS\Goldbach\Strong\TS55 TS\Goldbach\Strong\TS56 TS\Goldbach\Strong\TS57 TS\Goldbach\Strong\TS58 TS\Goldbach\Strong\TS59 TS\Goldbach\Strong\TS60 TS\Goldbach\Strong\TS61 TS\Goldbach\Strong\TS62 TS\Goldbach\Strong\TS63 TS\Goldbach\Strong\TS64 TS\Goldbach\Strong\TS65 TS\Goldbach\Strong\TS66 TS\Goldbach\Strong\TS67 TS\Goldbach\Strong\TS68 TS\Goldbach\Strong\TS69 TS\Goldbach\Strong\TS70 TS\Goldbach\Strong\TS71 TS\Goldbach\Strong\TS72 TS\Goldbach\Strong\TS73 TS\Goldbach\Strong\TS74 TS\Goldbach\Strong\TS75 TS\Goldbach\Strong\TS76 TS\Goldbach\Strong\TS77 TS\Goldbach\Strong\TS78 TS\Goldbach\Strong\TS79 TS\Goldbach\Strong\TS80 TS\Goldbach\Strong\TS81 TS\Goldbach\Strong\TS82 TS\Goldbach\Strong\TS83 TS\Goldbach\Strong\TS84 TS\Goldbach\Strong\TS85 TS\Goldbach\Strong\TS86 TS\Goldbach\Strong\TS87 TS\Goldbach\Strong\TS88
rg -n "a[x]iom" TS\Goldbach\Strong\TS15 TS\Goldbach\Strong\TS16 TS\Goldbach\Strong\TS17 TS\Goldbach\Strong\TS18 TS\Goldbach\Strong\TS19 TS\Goldbach\Strong\TS21 TS\Goldbach\Strong\TS22 TS\Goldbach\Strong\TS23 TS\Goldbach\Strong\TS24 TS\Goldbach\Strong\TS25 TS\Goldbach\Strong\TS26 TS\Goldbach\Strong\TS27 TS\Goldbach\Strong\TS28 TS\Goldbach\Strong\TS29 TS\Goldbach\Strong\TS30 TS\Goldbach\Strong\TS31 TS\Goldbach\Strong\TS32 TS\Goldbach\Strong\TS33 TS\Goldbach\Strong\TS34 TS\Goldbach\Strong\TS35 TS\Goldbach\Strong\TS36 TS\Goldbach\Strong\TS37 TS\Goldbach\Strong\TS38 TS\Goldbach\Strong\TS39 TS\Goldbach\Strong\TS40 TS\Goldbach\Strong\TS41 TS\Goldbach\Strong\TS42 TS\Goldbach\Strong\TS43 TS\Goldbach\Strong\TS44 TS\Goldbach\Strong\TS45 TS\Goldbach\Strong\TS46 TS\Goldbach\Strong\TS47 TS\Goldbach\Strong\TS48 TS\Goldbach\Strong\TS49 TS\Goldbach\Strong\TS50 TS\Goldbach\Strong\TS51 TS\Goldbach\Strong\TS52 TS\Goldbach\Strong\TS53 TS\Goldbach\Strong\TS54 TS\Goldbach\Strong\TS55 TS\Goldbach\Strong\TS56 TS\Goldbach\Strong\TS57 TS\Goldbach\Strong\TS58 TS\Goldbach\Strong\TS59 TS\Goldbach\Strong\TS60 TS\Goldbach\Strong\TS61 TS\Goldbach\Strong\TS62 TS\Goldbach\Strong\TS63 TS\Goldbach\Strong\TS64 TS\Goldbach\Strong\TS65 TS\Goldbach\Strong\TS66 TS\Goldbach\Strong\TS67 TS\Goldbach\Strong\TS68 TS\Goldbach\Strong\TS69 TS\Goldbach\Strong\TS70 TS\Goldbach\Strong\TS71 TS\Goldbach\Strong\TS72 TS\Goldbach\Strong\TS73 TS\Goldbach\Strong\TS74 TS\Goldbach\Strong\TS75 TS\Goldbach\Strong\TS76 TS\Goldbach\Strong\TS77 TS\Goldbach\Strong\TS78 TS\Goldbach\Strong\TS79 TS\Goldbach\Strong\TS80 TS\Goldbach\Strong\TS81 TS\Goldbach\Strong\TS82 TS\Goldbach\Strong\TS83 TS\Goldbach\Strong\TS84 TS\Goldbach\Strong\TS85 TS\Goldbach\Strong\TS86 TS\Goldbach\Strong\TS87 TS\Goldbach\Strong\TS88
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
above is specifically the audited `TS/Goldbach/Strong/TS15`--`TS88` layer.
