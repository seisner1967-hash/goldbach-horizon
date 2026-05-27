import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
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

end MellinJackson
end TS17
