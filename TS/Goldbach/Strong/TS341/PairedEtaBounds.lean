import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Tactic

namespace TS341.Goldbach

noncomputable section

open Complex Set intervalIntegral

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# TS341: paired eta bounds

The raw alternating series is only conditionally convergent in the critical
strip, so it cannot be represented directly by `tsum`. Pairing consecutive
terms produces an absolutely convergent series on `0 < re s`.
-/

/-- One paired eta term. -/
noncomputable def complexEtaPair (n : Nat) (s : Complex) : Complex :=
  (((2 * n + 1 : Nat) : Complex) ^ (-s)) -
    (((2 * n + 2 : Nat) : Complex) ^ (-s))

private theorem complexEtaPair_eq_integral (n : Nat) {s : Complex}
    (hs : Not (s = 0)) :
    complexEtaPair n s =
      s * intervalIntegral
        (fun x : Real => (x : Complex) ^ (-s - 1))
        (2 * n + 1 : Real) (2 * n + 2 : Real) MeasureTheory.volume := by
  have hInterval :
      Not (Membership.mem (Set.uIcc (2 * n + 1 : Real) (2 * n + 2 : Real))
        (0 : Real)) := by
    rw [uIcc_of_le (by norm_num)]
    intro h0
    have hPos : (0 : Real) < 2 * n + 1 := by positivity
    exact (not_lt_of_ge h0.1) hPos
  have hExponent : Not (-s - 1 = (-1 : Complex)) := by
    intro h
    apply hs
    linear_combination -h
  rw [integral_cpow (Or.inr (And.intro hExponent hInterval))]
  unfold complexEtaPair
  push_cast
  have hsNeg : Not (-s = 0) := neg_ne_zero.mpr hs
  field_simp
  ring

/-- Uniform bound for one paired term on a local right-half-plane slice. -/
theorem norm_complexEtaPair_le
    (n : Nat) {s : Complex} {delta M : Real}
    (hdelta : 0 < delta)
    (hsRe : delta <= s.re)
    (hsNorm : norm s <= M) :
    norm (complexEtaPair n s) <=
      M * (2 * n + 1 : Real) ^ (-delta - 1) := by
  have hs : Not (s = 0) := by
    intro h
    rw [h] at hsRe
    norm_num at hsRe
    linarith
  rw [complexEtaPair_eq_integral n hs, norm_mul]
  have hIntegral :
      norm (intervalIntegral
        (fun x : Real => (x : Complex) ^ (-s - 1))
        (2 * n + 1 : Real) (2 * n + 2 : Real) MeasureTheory.volume) <=
        (2 * n + 1 : Real) ^ (-delta - 1) := by
    calc
      norm (intervalIntegral
          (fun x : Real => (x : Complex) ^ (-s - 1))
          (2 * n + 1 : Real) (2 * n + 2 : Real) MeasureTheory.volume)
          <= (2 * n + 1 : Real) ^ (-delta - 1) *
              norm ((2 * n + 2 : Real) - (2 * n + 1 : Real)) := by
            apply norm_integral_le_of_norm_le_const
            intro x hx
            rw [uIoc_of_le (by norm_num)] at hx
            have haPos : (0 : Real) < 2 * n + 1 := by positivity
            have hxPos : 0 < x := lt_trans haPos hx.1
            rw [Complex.norm_eq_abs,
              Complex.abs_cpow_eq_rpow_re_of_pos hxPos]
            have hxOne : 1 <= x := by
              have hn : (0 : Real) <= n := by positivity
              have haOne : (1 : Real) <= 2 * n + 1 := by linarith
              exact haOne.trans hx.1.le
            calc
              x ^ (-s - 1).re
                  = x ^ (-s.re - 1) := by simp
              _ <= x ^ (-delta - 1) :=
                Real.rpow_le_rpow_of_exponent_le hxOne (by linarith)
              _ <= (2 * n + 1 : Real) ^ (-delta - 1) := by
                apply Real.rpow_le_rpow_of_exponent_nonpos
                next => positivity
                next => exact hx.1.le
                next => linarith
      _ = (2 * n + 1 : Real) ^ (-delta - 1) := by
        norm_num
  have hM : 0 <= M := (norm_nonneg s).trans hsNorm
  exact mul_le_mul hsNorm hIntegral (norm_nonneg _) hM

private theorem summable_odd_rpow {delta : Real} (hdelta : 0 < delta) :
    Summable (fun n : Nat =>
      (2 * n + 1 : Real) ^ (-delta - 1)) := by
  have hPower : -delta - 1 < (-1 : Real) := by linarith
  have hBase : Summable (fun n : Nat => (n : Real) ^ (-delta - 1)) :=
    Real.summable_nat_rpow.mpr hPower
  have hShift : Summable (fun n : Nat =>
      ((n + 1 : Nat) : Real) ^ (-delta - 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr hBase
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hShift
  apply Real.rpow_le_rpow_of_exponent_nonpos
  next => positivity
  next =>
    push_cast
    have hn : (0 : Real) <= (n : Real) := by positivity
    nlinarith
  next => linarith

/-- The paired eta series is absolutely summable at every point of the open
right half-plane. -/
theorem complexEtaPair_summable {s : Complex} (hs : 0 < s.re) :
    Summable (fun n : Nat => complexEtaPair n s) := by
  have hMajor := (summable_odd_rpow hs).mul_left (norm s)
  refine hMajor.of_norm_bounded
    (fun n : Nat => norm s * (2 * n + 1 : Real) ^ (-s.re - 1)) ?_
  intro n
  exact norm_complexEtaPair_le n hs le_rfl le_rfl

/-- Complex eta represented by the absolutely convergent paired series. -/
noncomputable def complexEta (s : Complex) : Complex :=
  tsum (fun n : Nat => complexEtaPair n s)

private theorem complexEtaPair_differentiable (n : Nat) :
    Differentiable Complex (complexEtaPair n) := by
  unfold complexEtaPair
  fun_prop

/-- The paired eta function is complex differentiable at every point of the
open right half-plane. -/
theorem complexEta_differentiableAt {s : Complex} (hs : 0 < s.re) :
    DifferentiableAt Complex complexEta s := by
  let delta : Real := s.re / 2
  let M : Real := norm s + 1
  let U : Set Complex := Set.inter {w | delta < w.re} (Metric.ball 0 M)
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hUOpen : IsOpen U := by
    apply IsOpen.inter
    next => exact (continuous_re.isOpen_preimage _ isOpen_Ioi)
    next => exact Metric.isOpen_ball
  have hsU : Membership.mem U s := by
    constructor
    next => dsimp [delta]; linarith
    next => simp [Metric.mem_ball, M]
  have hMajor := (summable_odd_rpow hdelta).mul_left M
  have hDiffOn : DifferentiableOn Complex complexEta U := by
    unfold complexEta
    apply differentiableOn_tsum_of_summable_norm hMajor
    next =>
      intro n
      exact (complexEtaPair_differentiable n).differentiableOn
    next => exact hUOpen
    next =>
      intro n w hw
      apply norm_complexEtaPair_le n hdelta hw.1.le
      have hwNorm : norm w < M := by
        simpa [Metric.mem_ball] using hw.2
      exact hwNorm.le
  exact hDiffOn.differentiableAt (hUOpen.mem_nhds hsU)

/-- The paired eta function is analytic on `re s > 0`. -/
theorem complexEta_analyticOnNhd :
    AnalyticOnNhd Complex complexEta {s : Complex | 0 < s.re} := by
  apply DifferentiableOn.analyticOnNhd
  next =>
    intro s hs
    exact (complexEta_differentiableAt hs).differentiableWithinAt
  next => exact continuous_re.isOpen_preimage _ isOpen_Ioi

end

end TS341.Goldbach
