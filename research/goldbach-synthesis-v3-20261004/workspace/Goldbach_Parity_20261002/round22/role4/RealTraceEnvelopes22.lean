import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/- Source preparation. These explicit envelopes and pointwise prerequisites
   do not certify the sums of zeros, the full trace identity, or its truncation. -/

noncomputable section

open Set

namespace GoldbachContinuous22

def spectralRate : ℝ := Real.pi / 4

def heatError (Y T : ℝ) : ℝ :=
  4 * Y * Real.exp (-spectralRate * T) *
    (T * Real.log T + (Real.log T + 1) / spectralRate + 1 / (spectralRate ^ 2 * T))

def primeError (Y X : ℝ) : ℝ :=
  Real.exp (-X / Y) * ((X + Y) * Real.log X + Y + 2 * Y ^ 2 / X)

def dualError (Y Q : ℝ) : ℝ := (Real.log Q + 1) / (Y * Q)

def archError (Y R : ℝ) : ℝ :=
  (4 / 3 : ℝ) * (Real.exp (-R / Y) + 1 / (2 * Y * R ^ 2) + 2 / (Y * R))

theorem spectralRate_pos : 0 < spectralRate := by
  unfold spectralRate
  exact div_pos Real.pi_pos (by norm_num)

theorem heatError_nonneg {Y T : ℝ} (hY : 1 ≤ Y) (hT : 10 ≤ T) :
    0 ≤ heatError Y T := by
  have hY0 : 0 ≤ Y := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have ha := spectralRate_pos
  unfold heatError
  positivity

theorem primeError_nonneg {Y X : ℝ} (hY : 1 ≤ Y) (hX : 3 ≤ X) :
    0 ≤ primeError Y X := by
  have hY0 : 0 ≤ Y := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  unfold primeError
  positivity

theorem dualError_nonneg {Y Q : ℝ} (hY : 1 ≤ Y) (hQ : 3 ≤ Q) :
    0 ≤ dualError Y Q := by
  have hY0 : 0 ≤ Y := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  unfold dualError
  positivity

theorem archError_nonneg {Y R : ℝ} (hY : 1 ≤ Y) (hR : 2 ≤ R) :
    0 ≤ archError Y R := by
  have hY0 : 0 ≤ Y := by linarith
  have hR0 : 0 ≤ R := by linarith
  unfold archError
  positivity

/-- Joint continuity of the displayed spectral envelope on its genuine domain. -/
theorem heatError_continuousAt {Y T : ℝ} (hT : 0 < T) :
    ContinuousAt (fun p : ℝ × ℝ => heatError p.1 p.2) (Y, T) := by
  have ha := spectralRate_pos
  unfold heatError
  fun_prop (disch := positivity)

theorem primeError_continuousAt {Y X : ℝ} (hY : 0 < Y) (hX : 0 < X) :
    ContinuousAt (fun p : ℝ × ℝ => primeError p.1 p.2) (Y, X) := by
  unfold primeError
  fun_prop (disch := positivity)

theorem dualError_continuousAt {Y Q : ℝ} (hY : 0 < Y) (hQ : 0 < Q) :
    ContinuousAt (fun p : ℝ × ℝ => dualError p.1 p.2) (Y, Q) := by
  unfold dualError
  fun_prop (disch := positivity)

theorem archError_continuousAt {Y R : ℝ} (hY : 0 < Y) (hR : 0 < R) :
    ContinuousAt (fun p : ℝ × ℝ => archError p.1 p.2) (Y, R) := by
  unfold archError
  fun_prop (disch := positivity)

/-- Concavity bound used to integrate the actual prime-side tail. -/
theorem log_tangent_upper {X x : ℝ} (hX : 0 < X) (hx : 0 < x) :
    Real.log x ≤ Real.log X + (x - X) / X := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hX)
  rw [Real.log_div hx.ne' hX.ne'] at h
  have hid : x / X - 1 = (x - X) / X := by
    field_simp [hX.ne']
    ring
  rw [hid] at h
  linarith

/-- Second-order upper bound for t log t, with its actual constant 1/(2T). -/
theorem tlog_taylor_upper {T t : ℝ} (hT : 0 < T) (htt : T ≤ t) :
    t * Real.log t ≤ T * Real.log T + (Real.log T + 1) * (t - T) +
      (t - T) ^ 2 / (2 * T) := by
  let g : ℝ → ℝ := fun x => T * Real.log T + (Real.log T + 1) * (x - T) +
    (x - T) ^ 2 / (2 * T) - x * Real.log x
  have hderiv : ∀ x : ℝ, 0 < x →
      HasDerivAt g (Real.log T + (x - T) / T - Real.log x) x := by
    intro x hx
    have hlin := ((hasDerivAt_id x).sub_const T).const_mul (Real.log T + 1)
    have hsquare := (((hasDerivAt_id x).sub_const T).pow 2).div_const (2 * T)
    have hlog := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne')
    have hd := (((hasDerivAt_const x (T * Real.log T)).add hlin).add hsquare).sub hlog
    convert hd using 1
    · dsimp [g]
    · field_simp [hT.ne', hx.ne']
      ring
  have hcont : ContinuousOn g (Ici T) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx0 : 0 < x := hT.trans_le hx
    dsimp [g]
    fun_prop (disch := positivity)
  have hmono : MonotoneOn g (Ici T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici T) hcont
      (f' := fun x => Real.log T + (x - T) / T - Real.log x)
    · intro x hx
      have hxT : T < x := by simpa only [interior_Ici, mem_Ioi] using hx
      exact (hderiv x (hT.trans hxT)).hasDerivWithinAt
    · intro x hx
      have hxT : T < x := by simpa only [interior_Ici, mem_Ioi] using hx
      linarith [log_tangent_upper hT (hT.trans hxT)]
  have hineq := hmono (show T ∈ Ici T by simp) (show t ∈ Ici T from htt) htt
  dsimp [g] at hineq
  nlinarith

/-- The same tangent estimate under the nonnegative prime-tail density. -/
theorem prime_integrand_le_tangent {Y X x : ℝ}
    (hY : 0 < Y) (hX : 0 < X) (hx : 0 < x) :
    (x / Y) * Real.log x * Real.exp (-x / Y) ≤
      (x / Y) * (Real.log X + (x - X) / X) * Real.exp (-x / Y) := by
  have hlog := log_tangent_upper hX hx
  have hxy : 0 ≤ x / Y := (div_pos hx hY).le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlog hxy) (Real.exp_pos _).le

/-- Uniform denominator control for the actual archimedean integral. -/
theorem arch_denominator_pos {x : ℝ} (hx : 2 ≤ x) : 0 < x - 1 / x := by
  have hx0 : 0 < x := by linarith
  have hsmall : 1 / x ≤ x / 4 := by
    apply (div_le_iff₀ hx0).mpr
    nlinarith
  linarith

theorem arch_denominator_inv_le {x : ℝ} (hx : 2 ≤ x) :
    1 / (x - 1 / x) ≤ 4 / (3 * x) := by
  have hx0 : 0 < x := by linarith
  have hsmall : 1 / x ≤ x / 4 := by
    apply (div_le_iff₀ hx0).mpr
    nlinarith
  apply (div_le_div_iff₀ (arch_denominator_pos hx) (by positivity : 0 < 3 * x)).mpr
  nlinarith

def realTest (Y x : ℝ) : ℝ := (x / Y) * Real.exp (-x / Y)

theorem realTest_one_le {Y : ℝ} (hY : 0 < Y) : realTest Y 1 ≤ 1 / Y := by
  have hexp : Real.exp (-1 / Y) ≤ 1 := Real.exp_le_one_iff.mpr (by positivity)
  unfold realTest
  exact (mul_le_mul_of_nonneg_left hexp (by positivity)).trans_eq (mul_one _)

end GoldbachContinuous22

#print axioms GoldbachContinuous22.spectralRate
#print axioms GoldbachContinuous22.heatError
#print axioms GoldbachContinuous22.primeError
#print axioms GoldbachContinuous22.dualError
#print axioms GoldbachContinuous22.archError
#print axioms GoldbachContinuous22.spectralRate_pos
#print axioms GoldbachContinuous22.heatError_nonneg
#print axioms GoldbachContinuous22.primeError_nonneg
#print axioms GoldbachContinuous22.dualError_nonneg
#print axioms GoldbachContinuous22.archError_nonneg
#print axioms GoldbachContinuous22.heatError_continuousAt
#print axioms GoldbachContinuous22.primeError_continuousAt
#print axioms GoldbachContinuous22.dualError_continuousAt
#print axioms GoldbachContinuous22.archError_continuousAt
#print axioms GoldbachContinuous22.log_tangent_upper
#print axioms GoldbachContinuous22.tlog_taylor_upper
#print axioms GoldbachContinuous22.prime_integrand_le_tangent
#print axioms GoldbachContinuous22.arch_denominator_pos
#print axioms GoldbachContinuous22.arch_denominator_inv_le
#print axioms GoldbachContinuous22.realTest
#print axioms GoldbachContinuous22.realTest_one_le
