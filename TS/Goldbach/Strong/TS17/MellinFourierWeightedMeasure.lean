import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import TS.Goldbach.Strong.TS17.MellinFourierChangeOfVariables

namespace TS17
namespace MellinJackson

open MeasureTheory Set

/--
Mellin weight on the real line.

It is `x^(2*sigma-1)` on `(0, infinity)` and zero elsewhere, encoded as an
`ENNReal` density for `Measure.withDensity`.
-/
noncomputable def mellinWeight (sigma : Real) (x : Real) : ENNReal :=
  if 0 < x then ENNReal.ofReal (x ^ (2 * sigma - 1)) else 0

/-- The weighted Mellin measure on the full real line. -/
noncomputable def muWeighted (sigma : Real) : Measure Real :=
  volume.withDensity (mellinWeight sigma)

/-- The same weighted measure, written as a density over the positive half-line. -/
noncomputable def muWeightedPositive (sigma : Real) : Measure Real :=
  (volume.restrict (Ioi 0)).withDensity fun x => ENNReal.ofReal (x ^ (2 * sigma - 1))

/-- The logarithmic Mellin/Fourier pullback on representative functions. -/
noncomputable def TsigmaFun (sigma : Real) (W : Real -> Complex) (u : Real) : Complex :=
  W (Real.exp u) * (Real.exp (sigma * u) : Complex)

/-- The pointwise inverse candidate for the logarithmic Mellin/Fourier pullback. -/
noncomputable def TsigmaInvFun (sigma : Real) (V : Real -> Complex) (x : Real) : Complex :=
  if 0 < x then
    V (Real.log x) * (Real.exp (-(sigma * Real.log x)) : Complex)
  else
    0

@[simp]
theorem mellinWeight_of_pos {sigma x : Real} (hx : 0 < x) :
    mellinWeight sigma x = ENNReal.ofReal (x ^ (2 * sigma - 1)) := by
  simp [mellinWeight, hx]

@[simp]
theorem mellinWeight_of_nonpos {sigma x : Real} (hx : ¬ 0 < x) :
    mellinWeight sigma x = 0 := by
  simp [mellinWeight, hx]

@[simp]
theorem TsigmaFun_add (sigma : Real) (W Z : Real -> Complex) :
    TsigmaFun sigma (fun x => W x + Z x) =
      fun u => TsigmaFun sigma W u + TsigmaFun sigma Z u := by
  funext u
  simp [TsigmaFun, add_mul]

@[simp]
theorem TsigmaFun_smul (sigma : Real) (c : Complex) (W : Real -> Complex) :
    TsigmaFun sigma (c • W) = c • TsigmaFun sigma W := by
  funext u
  simp [TsigmaFun, mul_assoc]

@[simp]
theorem TsigmaInvFun_exp (sigma : Real) (V : Real -> Complex) (u : Real) :
    TsigmaInvFun sigma V (Real.exp u) =
      V u * (Real.exp (-(sigma * u)) : Complex) := by
  simp [TsigmaInvFun, Real.exp_pos, Real.log_exp]

/-- Right inverse identity on representative functions. -/
theorem TsigmaFun_TsigmaInvFun (sigma : Real) (V : Real -> Complex) :
    TsigmaFun sigma (TsigmaInvFun sigma V) = V := by
  funext u
  simp [TsigmaFun, TsigmaInvFun, Real.exp_pos, Real.log_exp, mul_assoc,
    <- Complex.ofReal_mul, <- Real.exp_add]
  have hcancel :
      Complex.exp (-((sigma * u : Real) : Complex)) *
          Complex.exp ((sigma * u : Real) : Complex) = 1 := by
    rw [<- Complex.exp_add]
    simp
  rw [hcancel, mul_one]

/-- Left inverse identity on the positive half-line. -/
theorem TsigmaInvFun_TsigmaFun_of_pos
    (sigma : Real) (W : Real -> Complex) {x : Real} (hx : 0 < x) :
    TsigmaInvFun sigma (TsigmaFun sigma W) x = W x := by
  simp [TsigmaInvFun, TsigmaFun, hx, Real.exp_log hx, mul_assoc,
    <- Complex.ofReal_mul, <- Real.exp_add]
  have hcancel :
      Complex.exp (((sigma * Real.log x : Real) : Complex)) *
          Complex.exp (-((sigma * Real.log x : Real) : Complex)) = 1 := by
    rw [<- Complex.exp_add]
    simp
  rw [hcancel, mul_one]

/-- Weighted square-norm kernel on the Mellin side. -/
noncomputable def weightedNormKernel
    (sigma : Real) (W : Real -> Complex) (x : Real) : Real :=
  ‖W x‖ ^ 2 * x ^ (2 * sigma - 1)

/-- Square-norm kernel after applying `TsigmaFun`. -/
noncomputable def TsigmaNormKernel
    (sigma : Real) (W : Real -> Complex) (u : Real) : Real :=
  ‖TsigmaFun sigma W u‖ ^ 2

/-- Pointwise square-norm identity for the pullback factor. -/
theorem TsigmaNormKernel_eq
    (sigma : Real) (W : Real -> Complex) (u : Real) :
    TsigmaNormKernel sigma W u =
      ‖W (Real.exp u)‖ ^ 2 * Real.exp (2 * sigma * u) := by
  simp [TsigmaNormKernel, TsigmaFun, norm_mul, Real.norm_eq_abs,
    Complex.norm_eq_abs, Complex.abs_exp, abs_of_pos (Real.exp_pos _),
    sq, <- Real.exp_add]
  have hexp :
      Real.exp (sigma * u) * Real.exp (sigma * u) =
        Real.exp (2 * sigma * u) := by
    rw [<- Real.exp_add]
    ring_nf
  rw [<- hexp]
  ring

/--
Pointwise form of the Mellin density cancellation under `x = exp u`.

This is the algebraic identity used after `integral_Ioi_eq_integral_exp_smul`.
-/
theorem exp_smul_weightedNormKernel_eq_TsigmaNormKernel
    (sigma : Real) (W : Real -> Complex) (u : Real) :
    (Real.exp u) • weightedNormKernel sigma W (Real.exp u) =
      TsigmaNormKernel sigma W u := by
  rw [TsigmaNormKernel_eq, weightedNormKernel]
  simp [<- Real.exp_mul]
  have hexp :
      Real.exp u * Real.exp (u * (2 * sigma - 1)) =
        Real.exp (2 * sigma * u) := by
    rw [<- Real.exp_add]
    congr 1
    ring
  rw [<- hexp]
  ring

/--
Pre-quotient L2 norm-square identity on representative functions, written as
a Bochner integral over real-valued square-norm kernels.
-/
theorem integral_weightedNormKernel_eq_integral_TsigmaNormKernel
    (sigma : Real) (W : Real -> Complex) :
    (∫ x in Ioi (0 : Real), weightedNormKernel sigma W x) =
      ∫ u : Real, TsigmaNormKernel sigma W u := by
  rw [integral_Ioi_eq_integral_exp_smul (weightedNormKernel sigma W)]
  apply integral_congr_ae
  filter_upwards with u
  exact exp_smul_weightedNormKernel_eq_TsigmaNormKernel sigma W u

end MellinJackson
end TS17
