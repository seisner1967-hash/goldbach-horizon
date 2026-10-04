import PositiveTailComparisons22
import Mathlib.Algebra.IsPrimePow

/- Direct prime-power weight, exactly the unbundled formula of von Mangoldt.
   Its inequalities below come directly from minFac≤n, without importing a
   divisor-sum identity or any inversion argument. Source only. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace GoldbachContinuous22

def tracePrimeWeight (n : ℕ) : ℝ := by
  classical
  exact if IsPrimePow n then Real.log (Nat.minFac n) else 0

theorem tracePrimeWeight_nonneg (n : ℕ) : 0 ≤ tracePrimeWeight n := by
  classical
  unfold tracePrimeWeight
  split_ifs
  · exact Real.log_nonneg (by exact_mod_cast Nat.minFac_pos n)
  · exact le_rfl

theorem tracePrimeWeight_le_log {n : ℕ} (hn : 0 < n) :
    tracePrimeWeight n ≤ Real.log (n : ℝ) := by
  classical
  unfold tracePrimeWeight
  split_ifs
  · exact Real.log_le_log (by exact_mod_cast Nat.minFac_pos n)
      (by exact_mod_cast Nat.minFac_le hn)
  · exact Real.log_nonneg (by exact_mod_cast hn)

def primeTraceTerm (Y : ℝ) (n : ℕ) : ℝ := tracePrimeWeight n * realTest Y n

def dualTraceTerm (Y : ℝ) (n : ℕ) : ℝ :=
  (tracePrimeWeight n / (Y * (n : ℝ) ^ 2)) * Real.exp (-(1 / (Y * (n : ℝ))))

theorem primeTraceTerm_nonneg {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    0 ≤ primeTraceTerm Y n :=
  mul_nonneg (tracePrimeWeight_nonneg n) (realTest_nonneg hY (Nat.cast_nonneg n))

theorem primeTraceTerm_le_density {Y : ℝ} (hY : 0 < Y) {n : ℕ} (hn : 0 < n) :
    primeTraceTerm Y n ≤ primeDensity Y n := by
  have hw := tracePrimeWeight_le_log hn
  have hp := realTest_nonneg hY (Nat.cast_nonneg n)
  calc
    primeTraceTerm Y n ≤ Real.log (n : ℝ) * realTest Y n :=
      mul_le_mul_of_nonneg_right hw hp
    _ = primeDensity Y n := by
      unfold primeDensity realTest
      ring

theorem dualTraceTerm_nonneg {Y : ℝ} (hY : 0 < Y) (n : ℕ) :
    0 ≤ dualTraceTerm Y n := by
  have hw := tracePrimeWeight_nonneg n
  unfold dualTraceTerm
  positivity

theorem dualTraceTerm_le_density {Y : ℝ} (hY : 0 < Y) {n : ℕ} (hn : 0 < n) :
    dualTraceTerm Y n ≤ dualDensity Y n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hw := tracePrimeWeight_le_log hn
  have hexp : Real.exp (-(1 / (Y * (n : ℝ)))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by positivity)
  have hdiv := div_le_div_of_nonneg_right hw (by positivity : 0 ≤ Y * (n : ℝ) ^ 2)
  calc
    dualTraceTerm Y n ≤ (Real.log (n : ℝ) / (Y * (n : ℝ) ^ 2)) * 1 :=
      mul_le_mul hdiv hexp (Real.exp_pos _).le (by positivity)
    _ = dualDensity Y n := by unfold dualDensity; rw [mul_one]

/-- The actual prime-power trace tail beyond an integer cutoff satisfies H4. -/
theorem primeTrace_tail {Y : ℝ} (hY : 0 < Y) {X : ℕ} (hX : 3 ≤ X)
    (hXY : 3 * Y ≤ (X : ℝ)) :
    Summable (fun n : ℕ => primeTraceTerm Y (X + n + 1)) ∧
      (∑' n : ℕ, primeTraceTerm Y (X + n + 1)) ≤ primeError Y X := by
  have hXR : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  obtain ⟨hs, hb⟩ := primeDensity_sample_tail hY hXR hXY
  have hdom : ∀ n : ℕ, primeTraceTerm Y (X + n + 1) ≤
      primeDensity Y ((X : ℝ) + (n + 1 : ℕ)) := by
    intro n
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      primeTraceTerm_le_density hY (show 0 < X + n + 1 by omega)
  have hactual : Summable (fun n : ℕ => primeTraceTerm Y (X + n + 1)) := by
    apply hs.of_norm_bounded _
    intro n
    rw [Real.norm_of_nonneg (primeTraceTerm_nonneg hY _)]
    exact hdom n
  exact ⟨hactual, (tsum_le_tsum hdom hactual hs).trans hb⟩

/-- The actual dual prime-power trace tail beyond an integer cutoff satisfies H5. -/
theorem dualTrace_tail {Y : ℝ} (hY : 0 < Y) {Q : ℕ} (hQ : 3 ≤ Q) :
    Summable (fun n : ℕ => dualTraceTerm Y (Q + n + 1)) ∧
      (∑' n : ℕ, dualTraceTerm Y (Q + n + 1)) ≤ dualError Y Q := by
  have hQR : (3 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  obtain ⟨hs, hb⟩ := dualDensity_sample_tail hY hQR
  have hdom : ∀ n : ℕ, dualTraceTerm Y (Q + n + 1) ≤
      dualDensity Y ((Q : ℝ) + (n + 1 : ℕ)) := by
    intro n
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      dualTraceTerm_le_density hY (show 0 < Q + n + 1 by omega)
  have hactual : Summable (fun n : ℕ => dualTraceTerm Y (Q + n + 1)) := by
    apply hs.of_norm_bounded _
    intro n
    rw [Real.norm_of_nonneg (dualTraceTerm_nonneg hY _)]
    exact hdom n
  exact ⟨hactual, (tsum_le_tsum hdom hactual hs).trans hb⟩

end GoldbachContinuous22

#print axioms GoldbachContinuous22.tracePrimeWeight
#print axioms GoldbachContinuous22.tracePrimeWeight_nonneg
#print axioms GoldbachContinuous22.tracePrimeWeight_le_log
#print axioms GoldbachContinuous22.primeTraceTerm
#print axioms GoldbachContinuous22.dualTraceTerm
#print axioms GoldbachContinuous22.primeTraceTerm_nonneg
#print axioms GoldbachContinuous22.primeTraceTerm_le_density
#print axioms GoldbachContinuous22.dualTraceTerm_nonneg
#print axioms GoldbachContinuous22.dualTraceTerm_le_density
#print axioms GoldbachContinuous22.primeTrace_tail
#print axioms GoldbachContinuous22.dualTrace_tail
