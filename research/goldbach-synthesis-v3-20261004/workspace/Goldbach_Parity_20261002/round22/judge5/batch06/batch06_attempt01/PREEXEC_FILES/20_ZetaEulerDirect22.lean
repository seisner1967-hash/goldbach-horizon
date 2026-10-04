import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.RiemannZeta

/- SOURCE_ONLY: direct analytic Euler logarithm for genuine riemannZeta.
   The selected route is norm convergence -> generic Euler product -> exponential
   of the prime logarithms -> nonvanishing. It does not use the cached Dirichlet
   convolution identity for vonMangoldt, or invert zeta by any arithmetic series.
   Differentiation of the prime sum remains a separate obligation. -/

noncomputable section

open Complex
open scoped Topology

namespace GoldbachContinuous22

def contourZetaSummandHom (s : ℂ) (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := (n : ℂ) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simpa only [Nat.cast_mul, Complex.ofReal_natCast] using
      Complex.mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg (-s)

theorem contourZetaSummand_norm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖contourZetaSummandHom s (Complex.ne_zero_of_one_lt_re hs) n‖) := by
  simp only [contourZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  convert Real.summable_nat_rpow_inv.mpr hs with n
  rw [← Complex.ofReal_natCast, Complex.norm_eq_abs,
    Complex.abs_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n)
      (Complex.re_neg_ne_zero_of_one_lt_re hs),
    Complex.neg_re, Real.rpow_neg (Nat.cast_nonneg n)]

theorem contourZetaSummand_tsum {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, contourZetaSummandHom s (Complex.ne_zero_of_one_lt_re hs) n) =
      riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  simp only [contourZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    Complex.cpow_neg, one_div]

theorem contourZeta_euler_exp_log {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))) =
      riemannZeta s := by
  have h := EulerProduct.exp_tsum_primes_log_eq_tsum
    (contourZetaSummand_norm_summable hs)
  exact h.trans (contourZetaSummand_tsum hs)

theorem contourZeta_ne_zero_on_right {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ≠ 0 := by
  rw [← contourZeta_euler_exp_log hs]
  exact Complex.exp_ne_zero _

end GoldbachContinuous22

#print axioms GoldbachContinuous22.contourZetaSummandHom
#print axioms GoldbachContinuous22.contourZetaSummand_norm_summable
#print axioms GoldbachContinuous22.contourZetaSummand_tsum
#print axioms GoldbachContinuous22.contourZeta_euler_exp_log
#print axioms GoldbachContinuous22.contourZeta_ne_zero_on_right
