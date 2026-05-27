import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.ENNReal.Real
import TS.Goldbach.Strong.TS17.MellinFourierWeightedMeasure

namespace TS17
namespace MellinJackson

open MeasureTheory Set Filter

/-- The Mellin density used for `muWeighted` is measurable. -/
theorem measurable_mellinWeight (sigma : Real) :
    Measurable (mellinWeight sigma) := by
  unfold mellinWeight
  exact Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const

/-- The weighted Mellin measure is supported on the positive half-line. -/
theorem ae_pos_muWeighted (sigma : Real) :
    ∀ᵐ x ∂muWeighted sigma, 0 < x := by
  rw [muWeighted, ae_withDensity_iff (measurable_mellinWeight sigma)]
  filter_upwards with x hx
  by_contra hpos
  have hzero : mellinWeight sigma x = 0 := mellinWeight_of_nonpos hpos
  exact hx hzero

/-- The Mellin density is nonzero on the positive half-line. -/
theorem mellinWeight_ne_zero_of_pos {sigma x : Real} (hx : 0 < x) :
    mellinWeight sigma x ≠ 0 := by
  rw [mellinWeight_of_pos hx]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hx _))

/-- The Mellin density is nonzero along the exponential parametrisation. -/
theorem mellinWeight_exp_ne_zero (sigma u : Real) :
    mellinWeight sigma (Real.exp u) ≠ 0 :=
  mellinWeight_ne_zero_of_pos (Real.exp_pos u)

/--
On the support of `muWeighted`, the density condition in `ae_withDensity_iff`
can be discharged by positivity.
-/
theorem ae_muWeighted_of_forall_pos
    {sigma : Real} {p : Real -> Prop}
    (hp : ∀ x : Real, 0 < x -> p x) :
    ∀ᵐ x ∂muWeighted sigma, p x := by
  filter_upwards [ae_pos_muWeighted sigma] with x hx
  exact hp x hx

/-- The inverse-after-forward representative identity holds almost everywhere. -/
theorem ae_TsigmaInvFun_TsigmaFun
    (sigma : Real) (W : Real -> Complex) :
    ∀ᵐ x ∂muWeighted sigma,
      TsigmaInvFun sigma (TsigmaFun sigma W) x = W x := by
  filter_upwards [ae_pos_muWeighted sigma] with x hx
  exact TsigmaInvFun_TsigmaFun_of_pos sigma W hx

/-- The forward-after-inverse representative identity holds everywhere, hence a.e. -/
theorem ae_TsigmaFun_TsigmaInvFun
    (sigma : Real) (V : Real -> Complex) :
    ∀ᵐ u ∂(volume : Measure Real),
      TsigmaFun sigma (TsigmaInvFun sigma V) u = V u := by
  exact ae_of_all _ fun u => congrFun (TsigmaFun_TsigmaInvFun sigma V) u

/--
Local infrastructure needed to descend the representative operators to
`AEEqFun`.

The previous lemmas prove the support and inverse identities. The remaining
quotient-specific issue is transport of a.e. equality through `exp`/`log`,
together with the corresponding a.e. strong measurability facts.
-/
structure MellinFourierAEEqTransport (sigma : Real) where
  tsigma_aestronglyMeasurable :
    ∀ W : Real -> Complex,
      AEStronglyMeasurable W (muWeighted sigma) ->
        AEStronglyMeasurable (TsigmaFun sigma W) volume
  tsigma_congr :
    ∀ {W Z : Real -> Complex},
      W =ᵐ[muWeighted sigma] Z ->
        TsigmaFun sigma W =ᵐ[volume] TsigmaFun sigma Z
  inv_aestronglyMeasurable :
    ∀ V : Real -> Complex,
      AEStronglyMeasurable V volume ->
        AEStronglyMeasurable (TsigmaInvFun sigma V) (muWeighted sigma)
  inv_congr :
    ∀ {V U : Real -> Complex},
      V =ᵐ[volume] U ->
        TsigmaInvFun sigma V =ᵐ[muWeighted sigma] TsigmaInvFun sigma U

/-- Descent of `TsigmaFun` to almost-everywhere equivalence classes. -/
noncomputable def TsigmaAEEqFun
    {sigma : Real} (H : MellinFourierAEEqTransport sigma) :
    AEEqFun Real Complex (muWeighted sigma) ->
      AEEqFun Real Complex volume := fun F =>
  Quotient.liftOn' F
    (fun W : { W : Real -> Complex // AEStronglyMeasurable W (muWeighted sigma) } =>
      AEEqFun.mk (TsigmaFun sigma W.1) (H.tsigma_aestronglyMeasurable W.1 W.2))
    (fun W Z hWZ => by
      exact AEEqFun.mk_eq_mk.mpr (H.tsigma_congr hWZ))

/-- Descent of `TsigmaInvFun` to almost-everywhere equivalence classes. -/
noncomputable def TsigmaInvAEEqFun
    {sigma : Real} (H : MellinFourierAEEqTransport sigma) :
    AEEqFun Real Complex volume ->
      AEEqFun Real Complex (muWeighted sigma) := fun F =>
  Quotient.liftOn' F
    (fun V : { V : Real -> Complex // AEStronglyMeasurable V volume } =>
      AEEqFun.mk (TsigmaInvFun sigma V.1) (H.inv_aestronglyMeasurable V.1 V.2))
    (fun V U hVU => by
      exact AEEqFun.mk_eq_mk.mpr (H.inv_congr hVU))

/-- The descended inverse is a left inverse on `AEEqFun`. -/
theorem TsigmaInvAEEqFun_left
    {sigma : Real} (H : MellinFourierAEEqTransport sigma)
    (F : AEEqFun Real Complex (muWeighted sigma)) :
    TsigmaInvAEEqFun H (TsigmaAEEqFun H F) = F := by
  refine AEEqFun.induction_on F ?_
  intro W hW
  exact AEEqFun.mk_eq_mk.mpr (ae_TsigmaInvFun_TsigmaFun sigma W)

/-- The descended inverse is a right inverse on `AEEqFun`. -/
theorem TsigmaInvAEEqFun_right
    {sigma : Real} (H : MellinFourierAEEqTransport sigma)
    (F : AEEqFun Real Complex volume) :
    TsigmaAEEqFun H (TsigmaInvAEEqFun H F) = F := by
  refine AEEqFun.induction_on F ?_
  intro V hV
  exact AEEqFun.mk_eq_mk.mpr (ae_TsigmaFun_TsigmaInvFun sigma V)

end MellinJackson
end TS17
