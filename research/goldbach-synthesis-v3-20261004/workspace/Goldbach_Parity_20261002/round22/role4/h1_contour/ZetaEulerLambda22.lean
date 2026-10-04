import ZetaEulerDerivative22
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/- SOURCE_ONLY. The coefficients below are defined directly by prime powers.
   The analytic Euler derivative is reindexed using the canonical bijection
   (p,k) ↦ p^(k+1). Absolute convergence is constructed by an explicit p-series
   bound. No divisor-sum inversion or cached von Mangoldt convolution is used.
   This is a genuine right-half-plane logarithmic derivative, not the trace
   formula or its additive Goldbach consequence. -/

noncomputable section
open Complex Set Filter
open scoped Topology

namespace GoldbachContinuous22

def contourLambdaWeight (n : ℕ) : ℝ := by
  classical
  exact if IsPrimePow n then Real.log (Nat.minFac n) else 0

def contourLambdaTerm (n : ℕ) (s : ℂ) : ℂ :=
  (contourLambdaWeight n : ℂ) * (n : ℂ) ^ (-s)

theorem contourLambdaWeight_nonneg (n : ℕ) : 0 ≤ contourLambdaWeight n := by
  classical
  unfold contourLambdaWeight
  split_ifs
  · exact Real.log_nonneg (by exact_mod_cast Nat.minFac_pos n)
  · exact le_rfl

theorem contourLambdaWeight_le_log {n : ℕ} (hn : 0 < n) :
    contourLambdaWeight n ≤ Real.log (n : ℝ) := by
  classical
  unfold contourLambdaWeight
  split_ifs
  · exact Real.log_le_log (by exact_mod_cast Nat.minFac_pos n)
      (by exact_mod_cast Nat.minFac_le hn)
  · exact Real.log_nonneg (by exact_mod_cast hn)

theorem contourLambdaWeight_prime_pow (p : Nat.Primes) (k : ℕ) :
    contourLambdaWeight ((p : ℕ) ^ (k + 1)) = Real.log (p : ℝ) := by
  classical
  have hpp : IsPrimePow ((p : ℕ) ^ (k + 1)) :=
    p.property.isPrimePow.pow (Nat.succ_ne_zero k)
  simp only [contourLambdaWeight, if_pos hpp,
    p.property.pow_minFac (Nat.succ_ne_zero k)]

theorem contourNat_pow_cpow (n k : ℕ) (s : ℂ) :
    ((n ^ k : ℕ) : ℂ) ^ (-s) = ((n : ℂ) ^ (-s)) ^ k := by
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul]

theorem contourLambdaTerm_prime_pow (p : Nat.Primes) (k : ℕ) (s : ℂ) :
    contourLambdaTerm ((p : ℕ) ^ (k + 1)) s =
      Complex.log (p : ℂ) * ((p : ℂ) ^ (-s)) ^ (k + 1) := by
  rw [contourLambdaTerm, contourLambdaWeight_prime_pow, contourNat_pow_cpow]
  congr 1
  exact Complex.natCast_log

/-- Constructed absolute-convergence majorant on the entire natural-number
    coefficient series. Its constants depend only on the half-plane margin. -/
theorem contourLambdaTerm_pseries_bound {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    ‖contourLambdaTerm n s‖ ≤
      (1 / ((s.re - 1) / 2)) * (n : ℝ) ^ (-((s.re + 1) / 2)) := by
  classical
  have hdelta : 0 < (s.re - 1) / 2 := by linarith
  by_cases hnpp : IsPrimePow n
  · have hn : 0 < n := hnpp.pos
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    have hlog := contour_log_le_rpow_div hn0 hdelta
    have hpow : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
      rw [← Complex.ofReal_natCast, Complex.norm_eq_abs,
        Complex.abs_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
    rw [contourLambdaTerm, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (contourLambdaWeight_nonneg n), hpow]
    calc
      contourLambdaWeight n * (n : ℝ) ^ (-s.re) ≤
          Real.log (n : ℝ) * (n : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (contourLambdaWeight_le_log hn)
          (Real.rpow_nonneg hn0.le _)
      _ ≤ ((n : ℝ) ^ ((s.re - 1) / 2) / ((s.re - 1) / 2)) *
          (n : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hn0.le _)
      _ = (1 / ((s.re - 1) / 2)) * (n : ℝ) ^ (-((s.re + 1) / 2)) := by
        calc
          _ = (1 / ((s.re - 1) / 2)) *
              ((n : ℝ) ^ ((s.re - 1) / 2) * (n : ℝ) ^ (-s.re)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hn0]
            congr 2
            ring
  · simp only [contourLambdaTerm, contourLambdaWeight, if_neg hnpp,
      Complex.ofReal_zero, zero_mul, norm_zero]
    exact mul_nonneg (one_div_nonneg.mpr hdelta.le)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem contourLambdaTerm_norm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ‖contourLambdaTerm n s‖) := by
  have hn : Summable (fun n : ℕ => (n : ℝ) ^ (-((s.re + 1) / 2))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hmajorant := hn.mul_left (1 / ((s.re - 1) / 2))
  refine Summable.of_norm_bounded _ hmajorant fun n => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact contourLambdaTerm_pseries_bound hs n

theorem contourLambdaTerm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => contourLambdaTerm n s) :=
  (contourLambdaTerm_norm_summable hs).of_norm

theorem contourPrimeGeometric_hasSum (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => Complex.log (p : ℂ) *
      ((p : ℂ) ^ (-s)) ^ (k + 1))
      (Complex.log (p : ℂ) * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s))) := by
  have hnorm : ‖(p : ℂ) ^ (-s)‖ < 1 :=
    (contourPrime_cpow_norm_le_half p hs).trans_lt (by norm_num)
  have h := (hasSum_geometric_of_norm_lt_one hnorm).mul_left
    (Complex.log (p : ℂ) * (p : ℂ) ^ (-s))
  convert h using 1 <;> simp only [div_eq_mul_inv] <;>
    first | (funext k; rw [pow_succ]; ring) | ring

theorem contourLambdaTerm_prime_product_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun pk : Nat.Primes × ℕ =>
      Complex.log (pk.1 : ℂ) * ((pk.1 : ℂ) ^ (-s)) ^ (pk.2 + 1)) := by
  have hsub := (contourLambdaTerm_summable hs).subtype {n : ℕ | IsPrimePow n}
  have h := Nat.Primes.prodNatEquiv.summable_iff.mpr hsub
  refine h.congr fun pk => ?_
  change contourLambdaTerm ((pk.1 : ℕ) ^ (pk.2 + 1)) s = _
  exact contourLambdaTerm_prime_pow pk.1 pk.2 s

/-- Exact regrouping of the actual Lambda Dirichlet series. Absolute convergence
    above pays the product-to-iterated-sum step; the prime-power bijection pays
    the coefficients and their multiplicities. -/
theorem contourLambda_tsum_prime_geometric {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, contourLambdaTerm n s) =
      ∑' p : Nat.Primes, ∑' k : ℕ,
        Complex.log (p : ℂ) * ((p : ℂ) ^ (-s)) ^ (k + 1) := by
  classical
  have hsupp : Function.support (fun n : ℕ => contourLambdaTerm n s) ⊆
      {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra hnpp
    exact hn (by simp [contourLambdaTerm, contourLambdaWeight, hnpp])
  calc
    (∑' n : ℕ, contourLambdaTerm n s) =
        ∑' n : {n : ℕ // IsPrimePow n}, contourLambdaTerm n s :=
      (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' pk : Nat.Primes × ℕ,
        contourLambdaTerm (Nat.Primes.prodNatEquiv pk) s :=
      (Nat.Primes.prodNatEquiv.tsum_eq
        (fun n : {n : ℕ // IsPrimePow n} => contourLambdaTerm n s)).symm
    _ = ∑' pk : Nat.Primes × ℕ,
        Complex.log (pk.1 : ℂ) * ((pk.1 : ℂ) ^ (-s)) ^ (pk.2 + 1) := by
      apply tsum_congr
      intro pk
      exact contourLambdaTerm_prime_pow pk.1 pk.2 s
    _ = _ := tsum_prod (contourLambdaTerm_prime_product_summable hs)

/-- Genuine zeta, genuine directly defined prime-power weights, and a proved
    domain/convergence condition. No abstract trace or free Lambda premise. -/
theorem contourZeta_logDeriv_direct_Lambda {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZeta s / riemannZeta s =
      -(∑' n : ℕ, (contourLambdaWeight n : ℂ) * (n : ℂ) ^ (-s)) := by
  rw [contourZeta_logDeriv_prime_quotient hs]
  calc
    (∑' p : Nat.Primes, contourPrimeLogDerivative p s) =
        ∑' p : Nat.Primes, -(∑' k : ℕ,
          Complex.log (p : ℂ) * ((p : ℂ) ^ (-s)) ^ (k + 1)) := by
      apply tsum_congr
      intro p
      rw [(contourPrimeGeometric_hasSum p hs).tsum_eq]
      unfold contourPrimeLogDerivative
      ring
    _ = -(∑' p : Nat.Primes, ∑' k : ℕ,
        Complex.log (p : ℂ) * ((p : ℂ) ^ (-s)) ^ (k + 1)) := tsum_neg
    _ = _ := by
      rw [← contourLambda_tsum_prime_geometric hs]
      rfl

end GoldbachContinuous22

#print axioms GoldbachContinuous22.contourLambdaWeight
#print axioms GoldbachContinuous22.contourLambdaTerm
#print axioms GoldbachContinuous22.contourLambdaWeight_nonneg
#print axioms GoldbachContinuous22.contourLambdaWeight_le_log
#print axioms GoldbachContinuous22.contourLambdaWeight_prime_pow
#print axioms GoldbachContinuous22.contourNat_pow_cpow
#print axioms GoldbachContinuous22.contourLambdaTerm_prime_pow
#print axioms GoldbachContinuous22.contourLambdaTerm_pseries_bound
#print axioms GoldbachContinuous22.contourLambdaTerm_norm_summable
#print axioms GoldbachContinuous22.contourLambdaTerm_summable
#print axioms GoldbachContinuous22.contourPrimeGeometric_hasSum
#print axioms GoldbachContinuous22.contourLambdaTerm_prime_product_summable
#print axioms GoldbachContinuous22.contourLambda_tsum_prime_geometric
#print axioms GoldbachContinuous22.contourZeta_logDeriv_direct_Lambda
