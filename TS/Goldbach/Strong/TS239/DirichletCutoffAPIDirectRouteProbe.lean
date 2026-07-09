import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TS.Goldbach.Strong.TS238.AbelToCutoffBridgeFrontier

/-!
# TS239 - Dirichlet Cutoff API and Direct Route Probe

TS238 isolates the Abel-to-cutoff bridge as the remaining Tauberian input.
This sprint records a targeted direct-cutoff API probe against the locked
Mathlib revision used by the repository.

The current locked Mathlib does not expose `Real.sinc` or a ready-made
Dirichlet cutoff theorem in the probed modules.  TS239 therefore does not
claim the cutoff value.  It instead creates a local normalized sinc surrogate,
proves that it agrees with the repository Dirichlet kernel away from zero, and
proves that its interval integrals agree with the TS228 partial integrals.
-/

namespace TS239
namespace Goldbach

open Filter MeasureTheory
open scoped Topology

/-- Bounded audit outcome for the TS239 direct-cutoff API probe. -/
inductive DirichletCutoffAPIProbeOutcome where
  | directCutoffSymbolLocated
  | noDirectCutoffSymbolLocatedInProbedModules
  | normalizedSincCompatibilityBindingEstablished
  deriving DecidableEq, Repr

/-- Mathlib modules and repository modules inspected by the TS239 probe. -/
def dirichletCutoffProbedModules : List String :=
  [ "Mathlib.Analysis.SpecialFunctions.Integrals",
    "Mathlib.Analysis.SpecialFunctions.ImproperIntegrals",
    "Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic",
    "Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds",
    "Mathlib.MeasureTheory.Integral.IntegralEqImproper",
    "Mathlib.MeasureTheory.Integral.IntervalIntegral",
    "Mathlib.Analysis.Fourier.Inversion",
    "TS.Goldbach.Strong.TS215.DirichletSineIntegralAPIProbe",
    "TS.Goldbach.Strong.TS216.DirichletUnitFrequencyValueProbe",
    "TS.Goldbach.Strong.TS228.DirichletProductCutoffPartialIntegralBridge" ]

/-- Search terms used for the bounded API probe. -/
def dirichletCutoffSearchTerms : List String :=
  [ "Real.sinc",
    "sinc",
    "sin_div",
    "sineIntegral",
    "Dirichlet",
    "tendsto_integral",
    "integral_sinc",
    "integral_sin_div",
    "atTop" ]

/--
Local normalized sinc surrogate.  It matches the usual continuous convention
at zero, while the repository's historical Dirichlet kernel is `sin x / x`
with Lean's field division value `0 / 0 = 0`.
-/
noncomputable def normalizedSinc (x : Real) : Real :=
  if x = 0 then 1 else Real.sin x / x

/-- The future/direct cutoff target for the local normalized sinc surrogate. -/
def NormalizedSincCutoffAtTopStatement : Prop :=
  Tendsto
    (fun T : Real =>
      intervalIntegral normalizedSinc 0 T volume)
    atTop
    (nhds (Real.pi / 2))

/-- The direct one-sided cutoff target, definitionally identical to TS228. -/
def DirectDirichletCutoffAtTopStatement : Prop :=
  TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement

/--
Fallback quantitative target for a direct cutoff route.  It is not proved in
TS239; it records the next natural tail estimate if no direct API theorem is
available.
-/
def DirichletTailBoundStatement : Prop :=
  forall T U : Real,
    0 < T ->
    T <= U ->
      |TS228.Goldbach.dirichletUnitPartialIntegral U -
        TS228.Goldbach.dirichletUnitPartialIntegral T| <= 2 / T

/-- Away from zero, the repository unit kernel is the local normalized sinc. -/
theorem sineDirichletKernel_one_eq_normalizedSinc_of_ne_zero
    {x : Real}
    (hx : x = 0 -> False) :
    TS213.Goldbach.sineDirichletKernel 1 x =
      normalizedSinc x := by
  by_cases h0 : x = 0
  exact False.elim (hx h0)
  simp [TS213.Goldbach.sineDirichletKernel, normalizedSinc, h0]

/--
The TS228 partial integral is unchanged if the repository kernel is replaced by
the normalized sinc surrogate.  The two functions differ at most at `{0}`.
-/
theorem dirichletUnitPartialIntegral_eq_normalizedSincIntegral
    (T : Real) :
    TS228.Goldbach.dirichletUnitPartialIntegral T =
      intervalIntegral normalizedSinc 0 T volume := by
  unfold TS228.Goldbach.dirichletUnitPartialIntegral
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards
    [compl_mem_ae_iff.2 (by simp : volume ({0} : Set Real) = 0)]
    with x hx _hxI
  have hx0 : x = 0 -> False := by
    simpa [Set.mem_compl_iff] using hx
  exact sineDirichletKernel_one_eq_normalizedSinc_of_ne_zero (x := x) hx0

/--
Any future direct theorem for the local normalized sinc surrogate immediately
supplies the TS228 one-sided cutoff target.
-/
theorem dirichletUnitPartialIntegralAtTop_of_normalizedSinc
    (h : NormalizedSincCutoffAtTopStatement) :
    TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement := by
  unfold NormalizedSincCutoffAtTopStatement at h
  unfold TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement
  exact h.congr'
    (Eventually.of_forall fun T =>
      (dirichletUnitPartialIntegral_eq_normalizedSincIntegral T).symm)

/--
Any future direct proof of the one-sided cutoff target supplies TS228 directly.
This is intentionally just the identity bridge.
-/
theorem dirichletUnitPartialIntegralAtTop_of_directCutoff
    (h : DirectDirichletCutoffAtTopStatement) :
    TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement := by
  simpa [DirectDirichletCutoffAtTopStatement] using h

/--
Any future normalized-sinc cutoff theorem activates the product cutoff unit
value through the already proved TS228 bridge.
-/
theorem dirichletProductCutoffUnitValue_of_normalizedSinc
    (h : NormalizedSincCutoffAtTopStatement) :
    TS227.Goldbach.DirichletProductCutoffUnitValueStatement :=
  TS228.Goldbach.dirichletProductCutoffUnitValue_of_partialIntegralAtTop
    (dirichletUnitPartialIntegralAtTop_of_normalizedSinc h)

/--
Any future normalized-sinc cutoff theorem activates the TS219
third-derivative cutoff value through the already proved TS225--TS228 route.
-/
theorem cosSquareThirdDerivativeCutoffValue_of_normalizedSinc
    (h : NormalizedSincCutoffAtTopStatement) :
    TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement :=
  TS227.Goldbach.cosSquareThirdDerivativeCutoffValue_of_unitDirichlet
    (dirichletProductCutoffUnitValue_of_normalizedSinc h)

/-- Ledger for the TS239 direct-cutoff API probe. -/
structure DirichletCutoffAPIDirectRouteProbeLedger where
  ts238_frontier :
    TS238.Goldbach.AbelToCutoffBridgeFrontierLedger

  probe_outcome :
    DirichletCutoffAPIProbeOutcome

  probed_modules :
    List String

  search_terms :
    List String

  normalized_sinc_cutoff_statement : Prop
  normalized_sinc_cutoff_statement_eq :
    normalized_sinc_cutoff_statement =
      NormalizedSincCutoffAtTopStatement

  direct_cutoff_statement : Prop
  direct_cutoff_statement_eq :
    direct_cutoff_statement =
      TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement

  repository_kernel_to_normalized_sinc_bridge_proved :
    forall T : Real,
      TS228.Goldbach.dirichletUnitPartialIntegral T =
        intervalIntegral normalizedSinc 0 T volume

  normalized_sinc_cutoff_supplies_ts228 :
    NormalizedSincCutoffAtTopStatement ->
      TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement

  normalized_sinc_cutoff_supplies_ts227 :
    NormalizedSincCutoffAtTopStatement ->
      TS227.Goldbach.DirichletProductCutoffUnitValueStatement

  normalized_sinc_cutoff_supplies_ts219 :
    NormalizedSincCutoffAtTopStatement ->
      TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement

  mathlib_real_sinc_symbol_not_located_in_locked_mathlib : True
  direct_cutoff_symbol_not_located_in_probed_modules : True
  direct_cutoff_value_not_proved : True
  dirichlet_tail_bound_not_proved : True
  abel_to_cutoff_bridge_not_proved : True
  cos_square_integral_value_not_proved : True
  canonical_sinc_fourth_value_not_proved : True
  plancherel_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS239 probe ledger. -/
noncomputable def dirichletCutoffAPIDirectRouteProbeLedger :
    DirichletCutoffAPIDirectRouteProbeLedger where
  ts238_frontier :=
    TS238.Goldbach.abelToCutoffBridgeFrontierLedger
  probe_outcome :=
    DirichletCutoffAPIProbeOutcome.noDirectCutoffSymbolLocatedInProbedModules
  probed_modules :=
    dirichletCutoffProbedModules
  search_terms :=
    dirichletCutoffSearchTerms
  normalized_sinc_cutoff_statement :=
    NormalizedSincCutoffAtTopStatement
  normalized_sinc_cutoff_statement_eq := rfl
  direct_cutoff_statement :=
    TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement
  direct_cutoff_statement_eq := rfl
  repository_kernel_to_normalized_sinc_bridge_proved :=
    dirichletUnitPartialIntegral_eq_normalizedSincIntegral
  normalized_sinc_cutoff_supplies_ts228 :=
    dirichletUnitPartialIntegralAtTop_of_normalizedSinc
  normalized_sinc_cutoff_supplies_ts227 :=
    dirichletProductCutoffUnitValue_of_normalizedSinc
  normalized_sinc_cutoff_supplies_ts219 :=
    cosSquareThirdDerivativeCutoffValue_of_normalizedSinc
  mathlib_real_sinc_symbol_not_located_in_locked_mathlib := True.intro
  direct_cutoff_symbol_not_located_in_probed_modules := True.intro
  direct_cutoff_value_not_proved := True.intro
  dirichlet_tail_bound_not_proved := True.intro
  abel_to_cutoff_bridge_not_proved := True.intro
  cos_square_integral_value_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS239. -/
def DirichletCutoffAPIDirectRouteProbeTarget : Prop :=
  Nonempty DirichletCutoffAPIDirectRouteProbeLedger

/--
TS239 target: the direct cutoff API probe is recorded, the local normalized
sinc compatibility bridge is proved, and the remaining cutoff obligations stay
explicit.
-/
theorem dirichletCutoffAPIDirectRouteProbeTarget :
    DirichletCutoffAPIDirectRouteProbeTarget :=
  Nonempty.intro dirichletCutoffAPIDirectRouteProbeLedger

end Goldbach
end TS239
