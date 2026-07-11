import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic
import TS.Goldbach.Strong.TS260.RiemannZetaVanishingOrderRealization

/-!
# TS261 - Riemann Zeta Vanishing Order Conjugation Reduction

TS260 reduced conjugation of abstract multiplicities to conjugation of
Mathlib's canonical analytic order for `riemannZeta`.

This sprint proves the generic order-transport mechanism.  It transports both
the locally-zero branch and every finite local factorization through the
double conjugation `z |-> star (f (star z))`.

Two analytic inputs remain explicit: double conjugation preserves analyticity,
and the Riemann zeta function satisfies Schwarz reflection.  Given those
inputs, TS261 discharges the TS260 order-conjugation statement and routes all
TS259 and TS258 finite-reality consequences.

No inhabitant of either analytic input is constructed here.
-/

namespace TS261
namespace Goldbach

/-- Double conjugation of a complex-valued complex function. -/
noncomputable def conjugatedFunction
    (f : Complex -> Complex) :
    Complex -> Complex :=
  fun z => star (f (star z))

/-- Analyticity of a function is preserved by double conjugation. -/
def ConjugatedFunctionAnalyticityStatement : Prop :=
  forall (f : Complex -> Complex) (z : Complex),
    AnalyticAt Complex f z ->
      AnalyticAt Complex (conjugatedFunction f) (star z)

/-- Schwarz reflection for the Riemann zeta function. -/
def RiemannZetaSchwarzReflectionStatement : Prop :=
  forall z : Complex,
    riemannZeta (star z) = star (riemannZeta z)

/-- The two remaining analytic inputs for the zeta order reduction. -/
structure RiemannZetaVanishingOrderConjugationInputContract where
  conjugated_function_analyticity :
    ConjugatedFunctionAnalyticityStatement

  riemann_zeta_schwarz_reflection :
    RiemannZetaSchwarzReflectionStatement

/-- Evaluation at a conjugate point exposes the conjugated value. -/
theorem conjugatedFunction_apply_star
    (f : Complex -> Complex)
    (z : Complex) :
    conjugatedFunction f (star z) = star (f z) := by
  simp [conjugatedFunction]

/-- Applying double conjugation twice recovers the original function. -/
theorem conjugatedFunction_involutive
    (f : Complex -> Complex) :
    conjugatedFunction (conjugatedFunction f) = f := by
  funext z
  simp [conjugatedFunction]

/-- Pull an eventual property back through complex conjugation. -/
theorem eventually_precomp_star
    {p : Complex -> Prop}
    {z : Complex}
    (h : Filter.Eventually p (nhds z)) :
    Filter.Eventually (fun w => p (star w)) (nhds (star z)) := by
  have hTendsto :
      Filter.Tendsto (star : Complex -> Complex)
        (nhds (star z)) (nhds z) := by
    simpa using (tendsto_star (star z))
  exact hTendsto.eventually h

/-- Non-vanishing at the center survives double conjugation. -/
theorem conjugatedFunction_ne_zero_at_star
    {g : Complex -> Complex}
    {z : Complex}
    (hNonzero : Not (g z = 0)) :
    Not (conjugatedFunction g (star z) = 0) := by
  intro hZero
  apply hNonzero
  have hStar := congrArg star hZero
  simpa [conjugatedFunction] using hStar

/-- Local vanishing is transported through double conjugation. -/
theorem conjugatedFunction_eventuallyEq_zero
    {f : Complex -> Complex}
    {z : Complex}
    (hZero :
      Filter.Eventually (fun w => f w = 0) (nhds z)) :
    Filter.Eventually
      (fun w => conjugatedFunction f w = 0)
      (nhds (star z)) := by
  have hPulled := eventually_precomp_star hZero
  filter_upwards [hPulled] with w hw
  unfold conjugatedFunction
  rw [hw]
  simp

/-- A local factorization is transported with the same natural exponent. -/
theorem conjugatedFunction_factorization_eventually
    {f g : Complex -> Complex}
    {z : Complex}
    {n : Nat}
    (hFactor :
      Filter.Eventually
        (fun w => f w = (w - z) ^ n * g w)
        (nhds z)) :
    Filter.Eventually
      (fun w =>
        conjugatedFunction f w =
          (w - star z) ^ n * conjugatedFunction g w)
      (nhds (star z)) := by
  have hPulled := eventually_precomp_star hFactor
  filter_upwards [hPulled] with w hw
  have hStar := congrArg star hw
  simpa [conjugatedFunction] using hStar

/-- Analytic order is independent of the proof after function equality. -/
theorem analyticAt_order_eq_of_function_eq
    {f g : Complex -> Complex}
    {z : Complex}
    (hfg : f = g)
    (hf : AnalyticAt Complex f z)
    (hg : AnalyticAt Complex g z) :
    hf.order = hg.order := by
  subst g
  rfl

/-- Double conjugation preserves analytic order once analyticity is supplied. -/
theorem conjugatedFunction_order_eq
    (hAnalytic : ConjugatedFunctionAnalyticityStatement)
    {f : Complex -> Complex}
    {z : Complex}
    (hf : AnalyticAt Complex f z) :
    (hAnalytic f z hf).order = hf.order := by
  by_cases hTop : hf.order = Top.top
  case pos =>
    have hLocallyZero :
        Filter.Eventually (fun w => f w = 0) (nhds z) :=
      (AnalyticAt.order_eq_top_iff hf).mp hTop
    have hConjugatedTop :
        (hAnalytic f z hf).order = Top.top :=
      (AnalyticAt.order_eq_top_iff (hAnalytic f z hf)).mpr
        (conjugatedFunction_eventuallyEq_zero hLocallyZero)
    exact hConjugatedTop.trans hTop.symm
  case neg =>
    have hExists :
        Exists fun n : Nat => (n : ENat) = hf.order :=
      ENat.ne_top_iff_exists.mp hTop
    let n : Nat := Classical.choose hExists
    have hn : (n : ENat) = hf.order := Classical.choose_spec hExists
    have hFactorExists :=
      (AnalyticAt.order_eq_nat_iff hf n).mp hn.symm
    let g : Complex -> Complex := Classical.choose hFactorExists
    have hgSpec := Classical.choose_spec hFactorExists
    have hgAnalytic : AnalyticAt Complex g z := hgSpec.1
    have hgNonzero : Not (g z = 0) := hgSpec.2.1
    have hgFactor :
        Filter.Eventually
          (fun w => f w = (w - z) ^ n * g w)
          (nhds z) := by
      simpa [smul_eq_mul] using hgSpec.2.2
    have hConjugatedOrder :
        (hAnalytic f z hf).order = (n : ENat) :=
      (AnalyticAt.order_eq_nat_iff (hAnalytic f z hf) n).mpr
        (Exists.intro
          (conjugatedFunction g)
          (And.intro
            (hAnalytic g z hgAnalytic)
            (And.intro
              (conjugatedFunction_ne_zero_at_star hgNonzero)
              (by
                have hTransported :=
                  conjugatedFunction_factorization_eventually hgFactor
                simpa [smul_eq_mul] using hTransported))))
    exact hConjugatedOrder.trans hn

/-- Schwarz reflection identifies the double conjugate of zeta with zeta. -/
theorem conjugatedRiemannZeta_eq
    (hSchwarz : RiemannZetaSchwarzReflectionStatement) :
    conjugatedFunction riemannZeta = riemannZeta := by
  funext z
  unfold conjugatedFunction
  rw [hSchwarz z]
  simp

/-- The two analytic inputs discharge the exact TS260 conjugation target. -/
theorem riemannZetaVanishingOrderConjugation_of_inputs
    (inputs : RiemannZetaVanishingOrderConjugationInputContract)
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract) :
    TS260.Goldbach.RiemannZetaVanishingOrderConjugationStatement C := by
  intro rho hZero
  unfold TS260.Goldbach.riemannZetaVanishingOrderAtZero
  let hf := TS260.Goldbach.riemannZeta_analyticAt_zeroSet C rho hZero
  let hStarZero := C.conjugate_closed rho hZero
  let hActual :=
    TS260.Goldbach.riemannZeta_analyticAt_zeroSet C (star rho) hStarZero
  let hConjugated :=
    inputs.conjugated_function_analyticity riemannZeta rho hf
  have hOrderConjugated : hConjugated.order = hf.order :=
    conjugatedFunction_order_eq
      inputs.conjugated_function_analyticity hf
  have hFunctionEq : conjugatedFunction riemannZeta = riemannZeta :=
    conjugatedRiemannZeta_eq inputs.riemann_zeta_schwarz_reflection
  have hOrderFunctionEq : hConjugated.order = hActual.order :=
    analyticAt_order_eq_of_function_eq
      hFunctionEq hConjugated hActual
  exact hOrderFunctionEq.symm.trans hOrderConjugated

/-- A realization and TS261 inputs give the TS258 multiplicity premise. -/
theorem multiplicityConjugation_of_realization_and_inputs
    (inputs : RiemannZetaVanishingOrderConjugationInputContract)
    (R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract) :
    TS258.Goldbach.ZeroMultiplicityConjugationInvariantStatement R.base :=
  TS260.Goldbach.multiplicityConjugation_of_realization R
    (riemannZetaVanishingOrderConjugation_of_inputs inputs R.base)

/-- A realization and TS261 inputs build the TS259 extension. -/
noncomputable def ts259Extension_of_realization_and_inputs
    (inputs : RiemannZetaVanishingOrderConjugationInputContract)
    (R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract) :
    TS259.Goldbach.RiemannZetaZeroFamilyMultiplicityConjugationContract :=
  TS260.Goldbach.ts259Extension_of_realization R
    (riemannZetaVanishingOrderConjugation_of_inputs inputs R.base)

/-- TS261 inputs route a realization to finite-sum reality. -/
theorem realizedTruncation_zeroSumReality_of_inputs
    (inputs : RiemannZetaVanishingOrderConjugationInputContract)
    (R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract)
    (truncation :
      TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationTruncationData R) :
    TS256.Goldbach.TruncatedZeroSumRealityStatement
      R.base truncation TS257.Goldbach.triangleSplineZeroSpectralSummand :=
  TS260.Goldbach.realizedTruncation_zeroSumReality R
    (riemannZetaVanishingOrderConjugation_of_inputs inputs R.base)
    truncation

/-- TS261 inputs route a realization to lossless real projection. -/
theorem realizedTruncation_realProjectionLossless_of_inputs
    (inputs : RiemannZetaVanishingOrderConjugationInputContract)
    (R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract)
    (truncation :
      TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationTruncationData R)
    (X : Nat) :
    ((TS257.Goldbach.triangleSplineZeroContributionFunction
      R.base truncation X : Real) : Complex) =
      TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
        R.base truncation X :=
  TS260.Goldbach.realizedTruncation_realProjectionLossless R
    (riemannZetaVanishingOrderConjugation_of_inputs inputs R.base)
    truncation X

/-- TS261 inputs route a realization to exact absolute-value transport. -/
theorem realizedTruncation_realAbs_eq_complexAbs_of_inputs
    (inputs : RiemannZetaVanishingOrderConjugationInputContract)
    (R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract)
    (truncation :
      TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationTruncationData R)
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          R.base truncation X) =
      Complex.abs
        (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
          R.base truncation X) :=
  TS260.Goldbach.realizedTruncation_realAbs_eq_complexAbs R
    (riemannZetaVanishingOrderConjugation_of_inputs inputs R.base)
    truncation X

/-- Ledger recording the complete order-conjugation reduction. -/
structure RiemannZetaVanishingOrderConjugationReductionLedger where
  ts260_vanishing_order :
    TS260.Goldbach.RiemannZetaVanishingOrderRealizationLedger

  generic_order_transport :
    forall hAnalytic : ConjugatedFunctionAnalyticityStatement,
      forall
        {f : Complex -> Complex}
        {z : Complex}
        (hf : AnalyticAt Complex f z),
        (hAnalytic f z hf).order = hf.order

  zeta_order_conjugation_from_inputs :
    forall C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract,
      RiemannZetaVanishingOrderConjugationInputContract ->
        TS260.Goldbach.RiemannZetaVanishingOrderConjugationStatement C

  realization_supplies_zero_sum_reality :
    forall R : TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationContract,
      RiemannZetaVanishingOrderConjugationInputContract ->
        forall truncation :
            TS260.Goldbach.RiemannZetaZeroMultiplicityRealizationTruncationData R,
          TS256.Goldbach.TruncatedZeroSumRealityStatement
            R.base truncation TS257.Goldbach.triangleSplineZeroSpectralSummand

  analytic_inputs_not_constructed : True
  concrete_realization_not_constructed : True
  explicit_formula_identity_not_proved : True
  zero_contribution_bound_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS261 ledger. -/
noncomputable def riemannZetaVanishingOrderConjugationReductionLedger :
    RiemannZetaVanishingOrderConjugationReductionLedger where
  ts260_vanishing_order :=
    TS260.Goldbach.riemannZetaVanishingOrderRealizationLedger
  generic_order_transport := conjugatedFunction_order_eq
  zeta_order_conjugation_from_inputs := fun C inputs =>
    riemannZetaVanishingOrderConjugation_of_inputs inputs C
  realization_supplies_zero_sum_reality := fun R inputs truncation =>
    realizedTruncation_zeroSumReality_of_inputs inputs R truncation
  analytic_inputs_not_constructed := True.intro
  concrete_realization_not_constructed := True.intro
  explicit_formula_identity_not_proved := True.intro
  zero_contribution_bound_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS261. -/
def RiemannZetaVanishingOrderConjugationReductionTarget : Prop :=
  Nonempty RiemannZetaVanishingOrderConjugationReductionLedger

/-- TS261 target: the order-conjugation reduction is assembled. -/
theorem riemannZetaVanishingOrderConjugationReductionTarget :
    RiemannZetaVanishingOrderConjugationReductionTarget :=
  Nonempty.intro riemannZetaVanishingOrderConjugationReductionLedger

end Goldbach
end TS261
