import ZetaEulerDirect22
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/- SOURCE_ONLY. The logarithm of the genuine analytic Euler product is
   differentiated with a constructed locally uniform, summable p-series bound.
   The conclusion concerns riemannZeta, not an abstract function. Identifying
   the prime quotient sum with the direct prime-power Lambda series is a
   subsequent obligation, never a premise of this module. -/

noncomputable section

open Complex Set Filter
open scoped Topology

namespace GoldbachContinuous22

def contourPrimeLog (p : Nat.Primes) (s : ℂ) : ℂ :=
  -Complex.log (1 - (p : ℂ) ^ (-s))

def contourPrimeLogDerivative (p : Nat.Primes) (s : ℂ) : ℂ :=
  -((p : ℂ) ^ (-s) * Complex.log (p : ℂ)) / (1 - (p : ℂ) ^ (-s))

def contourEulerLog (s : ℂ) : ℂ := ∑' p : Nat.Primes, contourPrimeLog p s

theorem contourPrime_cpow_norm (p : Nat.Primes) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  change ‖((p : ℕ) : ℂ) ^ (-s)‖ = _
  rw [← Complex.ofReal_natCast, Complex.norm_eq_abs,
    Complex.abs_cpow_eq_rpow_re_of_pos hp, Complex.neg_re]

theorem contourPrime_cpow_norm_le_half (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have hp1 : (1 : ℝ) ≤ p := by linarith
  rw [contourPrime_cpow_norm]
  calc
    (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = 1 / (p : ℝ) := by rw [Real.rpow_neg_one]; rfl
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2

theorem contourPrime_factor_mem_slitPlane (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    1 - (p : ℂ) ^ (-s) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hr : ((p : ℂ) ^ (-s)).re ≤ ‖(p : ℂ) ^ (-s)‖ := by
    simpa only [Complex.norm_eq_abs] using
      (le_abs_self _).trans (Complex.abs_re_le_abs ((p : ℂ) ^ (-s)))
  have hn := contourPrime_cpow_norm_le_half p hs
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem hasDerivAt_contourPrimeLog (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (contourPrimeLog p) (contourPrimeLogDerivative p s) s := by
  have hp : (p : ℂ) ≠ 0 := by
    exact_mod_cast p.property.ne_zero
  have hpow := (hasDerivAt_id s).neg.const_cpow (c := (p : ℂ)) (Or.inl hp)
  have h := ((hpow.const_sub (1 : ℂ)).clog
    (contourPrime_factor_mem_slitPlane p hs)).neg
  convert h using 1 <;> dsimp [contourPrimeLog, contourPrimeLogDerivative] <;> ring

theorem contourPrimeLog_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => contourPrimeLog p s) := by
  have h := (contourZetaSummand_norm_summable hs).of_norm.clog_one_sub.neg.subtype
    {p : ℕ | p.Prime}
  simpa only [contourZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    contourPrimeLog] using h

theorem contour_log_le_rpow_div {x delta : ℝ} (hx : 0 < x) (hdelta : 0 < delta) :
    Real.log x ≤ x ^ delta / delta := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx delta)
  rw [Real.log_rpow hx delta] at h
  apply (le_div_iff₀ hdelta).mpr
  nlinarith

theorem contourPrimeLogDerivative_local_bound (p : Nat.Primes) {s : ℂ} {kappa : ℝ}
    (hkappa : 1 < kappa) (hs : kappa ≤ s.re) :
    ‖contourPrimeLogDerivative p s‖ ≤
      2 * Real.log (p : ℝ) * (p : ℝ) ^ (-kappa) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hp0 : 0 < (p : ℝ) := by linarith
  have hs1 : 1 < s.re := hkappa.trans_le hs
  have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hlog : ‖Complex.log (p : ℂ)‖ = Real.log (p : ℝ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hp0.le,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
  have hden : 1 / 2 ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
    simp only [norm_one] at h
    have hn := contourPrime_cpow_norm_le_half p hs1
    linarith
  have hpow : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-kappa) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  rw [contourPrimeLogDerivative, norm_div, norm_neg, norm_mul,
    contourPrime_cpow_norm, hlog]
  calc
    ((p : ℝ) ^ (-s.re) * Real.log (p : ℝ)) / ‖1 - (p : ℂ) ^ (-s)‖ ≤
        ((p : ℝ) ^ (-s.re) * Real.log (p : ℝ)) / (1 / 2) :=
      div_le_div_of_nonneg_left
        (mul_nonneg (Real.rpow_nonneg hp0.le _) hlog0) (by norm_num) hden
    _ = 2 * Real.log (p : ℝ) * (p : ℝ) ^ (-s.re) := by ring
    _ ≤ 2 * Real.log (p : ℝ) * (p : ℝ) ^ (-kappa) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) hlog0)

/-- A closed p-series majorant, not a summability assumption supplied to the final theorem. -/
theorem contourPrimeLogDerivative_pseries_bound (p : Nat.Primes) {s : ℂ} {kappa : ℝ}
    (hkappa : 1 < kappa) (hs : kappa ≤ s.re) :
    ‖contourPrimeLogDerivative p s‖ ≤
      (2 / ((kappa - 1) / 2)) * (p : ℝ) ^ (-((kappa + 1) / 2)) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hdelta : 0 < (kappa - 1) / 2 := by linarith
  have hlog := contour_log_le_rpow_div hp0 hdelta
  calc
    _ ≤ 2 * Real.log (p : ℝ) * (p : ℝ) ^ (-kappa) :=
      contourPrimeLogDerivative_local_bound p hkappa hs
    _ ≤ 2 * ((p : ℝ) ^ ((kappa - 1) / 2) / ((kappa - 1) / 2)) *
        (p : ℝ) ^ (-kappa) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by norm_num))
        (Real.rpow_nonneg hp0.le _)
    _ = (2 / ((kappa - 1) / 2)) * (p : ℝ) ^ (-((kappa + 1) / 2)) := by
      calc
        _ = (2 / ((kappa - 1) / 2)) *
            ((p : ℝ) ^ ((kappa - 1) / 2) * (p : ℝ) ^ (-kappa)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hp0]
          congr 2
          ring

theorem contourPrimeLogDerivative_majorant_summable {kappa : ℝ} (hkappa : 1 < kappa) :
    Summable (fun p : Nat.Primes =>
      (2 / ((kappa - 1) / 2)) * (p : ℝ) ^ (-((kappa + 1) / 2))) := by
  have hn : Summable (fun n : ℕ => (n : ℝ) ^ (-((kappa + 1) / 2))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact (hn.subtype {p : ℕ | p.Prime}).mul_left (2 / ((kappa - 1) / 2))

theorem hasDerivAt_contourEulerLog {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt contourEulerLog (∑' p : Nat.Primes, contourPrimeLogDerivative p s) s := by
  let kappa : ℝ := (1 + s.re) / 2
  let domain : Set ℂ := {z | kappa < z.re}
  have hkappa : 1 < kappa := by dsimp [kappa]; linarith
  have hsdom : s ∈ domain := by dsimp [domain, kappa]; linarith
  have hopen : IsOpen domain := isOpen_lt continuous_const Complex.continuous_re
  have hconv : Convex ℝ domain := by
    simpa only [domain] using (convex_Ioi kappa).linear_preimage Complex.reLm
  exact hasDerivAt_tsum_of_isPreconnected
    (contourPrimeLogDerivative_majorant_summable hkappa) hopen hconv.isPreconnected
    (fun p z hz => hasDerivAt_contourPrimeLog p (hkappa.trans hz))
    (fun p z hz => contourPrimeLogDerivative_pseries_bound p hkappa hz.le)
    hsdom (contourPrimeLog_summable hs) hsdom

/-- Exact analytic prime quotient form of the logarithmic derivative of genuine zeta. -/
theorem contourZeta_logDeriv_prime_quotient {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZeta s / riemannZeta s =
      ∑' p : Nat.Primes, contourPrimeLogDerivative p s := by
  have hd := (hasDerivAt_contourEulerLog hs).cexp
  have heq : riemannZeta =ᶠ[𝓝 s] (fun z : ℂ => Complex.exp (contourEulerLog z)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
      with z hz
    exact (contourZeta_euler_exp_log hz).symm
  have hdζ := hd.congr_of_eventuallyEq heq
  have hval : Complex.exp (contourEulerLog s) = riemannZeta s := contourZeta_euler_exp_log hs
  rw [hdζ.deriv, hval]
  exact mul_div_cancel_left₀ _ (contourZeta_ne_zero_on_right hs)

end GoldbachContinuous22

#print axioms GoldbachContinuous22.contourPrimeLog
#print axioms GoldbachContinuous22.contourPrimeLogDerivative
#print axioms GoldbachContinuous22.contourEulerLog
#print axioms GoldbachContinuous22.contourPrime_cpow_norm
#print axioms GoldbachContinuous22.contourPrime_cpow_norm_le_half
#print axioms GoldbachContinuous22.contourPrime_factor_mem_slitPlane
#print axioms GoldbachContinuous22.hasDerivAt_contourPrimeLog
#print axioms GoldbachContinuous22.contourPrimeLog_summable
#print axioms GoldbachContinuous22.contour_log_le_rpow_div
#print axioms GoldbachContinuous22.contourPrimeLogDerivative_local_bound
#print axioms GoldbachContinuous22.contourPrimeLogDerivative_pseries_bound
#print axioms GoldbachContinuous22.contourPrimeLogDerivative_majorant_summable
#print axioms GoldbachContinuous22.hasDerivAt_contourEulerLog
#print axioms GoldbachContinuous22.contourZeta_logDeriv_prime_quotient
