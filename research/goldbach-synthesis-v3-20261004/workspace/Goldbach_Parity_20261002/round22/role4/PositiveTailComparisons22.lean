import DualLogTail22
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Topology.Algebra.InfiniteSum.Real

/- Positive cell comparison for the continuous trace contract; source only.
   No sieve, divisor inversion, bilinear decomposition, or progression remainder. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace GoldbachContinuous22

theorem integrableOn_Ioi_translate (f : ℝ → ℝ) (X : ℝ) :
    IntegrableOn (fun u : ℝ => f (X + u)) (Ioi 0) ↔ IntegrableOn f (Ioi X) := by
  have A : MeasurableEmbedding (fun u : ℝ => u + X) :=
    (Homeomorph.addRight X).isClosedEmbedding.measurableEmbedding
  have hpre : (fun u : ℝ => u + X) ⁻¹' Ioi X = Ioi 0 := by
    ext u
    change X < u + X ↔ 0 < u
    constructor <;> intro h <;> linarith
  have h := A.integrableOn_map_iff (f := f) (μ := volume) (s := Ioi X)
  rw [map_add_right_eq_self, hpre] at h
  simpa only [Function.comp_def, add_comm] using h.symm

theorem integral_Ioi_translate (f : ℝ → ℝ) (X : ℝ) :
    (∫ u : ℝ in Ioi 0, f (X + u)) = ∫ x : ℝ in Ioi X, f x := by
  have A : MeasurableEmbedding (fun u : ℝ => u + X) :=
    (Homeomorph.addRight X).isClosedEmbedding.measurableEmbedding
  have hpre : (fun u : ℝ => u + X) ⁻¹' Ioi X = Ioi 0 := by
    ext u
    change X < u + X ↔ 0 < u
    constructor <;> intro h <;> linarith
  have h := A.setIntegral_map f (Ioi X) (μ := volume)
  rw [map_add_right_eq_self, hpre] at h
  simpa only [add_comm] using h.symm

/-- A concrete positive cell comparison, including summability at infinity. -/
theorem positive_tail_sum_le_integral {f : ℝ → ℝ} {X : ℝ}
    (hf : AntitoneOn f (Ici X)) (hpos : ∀ x ∈ Ici X, 0 ≤ f x)
    (hint : IntegrableOn f (Ioi X)) :
    Summable (fun n : ℕ => f (X + (n + 1 : ℕ))) ∧
      (∑' n : ℕ, f (X + (n + 1 : ℕ))) ≤ ∫ x : ℝ in Ioi X, f x := by
  have hseq : ∀ n : ℕ, 0 ≤ f (X + (n + 1 : ℕ)) := by
    intro n
    apply hpos
    change X ≤ X + (n + 1 : ℕ)
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hpartial : ∀ M : ℕ,
      (∑ n ∈ Finset.range M, f (X + (n + 1 : ℕ))) ≤ ∫ x : ℝ in Ioi X, f x := by
    intro M
    have hc := (hf.mono (show Icc X (X + M) ⊆ Ici X from fun x hx => hx.1)).sum_le_integral
    calc
      (∑ n ∈ Finset.range M, f (X + (n + 1 : ℕ))) ≤ ∫ x in X..X + M, f x := hc
      _ = ∫ x in Ioc X (X + M), f x :=
        intervalIntegral.integral_of_le (le_add_of_nonneg_right (Nat.cast_nonneg M))
      _ ≤ ∫ x in Ioi X, f x := by
        apply setIntegral_mono_set hint
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact hpos x hx.le
        · exact Eventually.of_forall (fun x hx => hx.1)
  exact ⟨summable_of_sum_range_le hseq hpartial, Real.tsum_le_of_sum_range_le hseq hpartial⟩

def primeDensity (Y x : ℝ) : ℝ := (x / Y) * Real.log x * Real.exp (-x / Y)

theorem log_ge_half {x : ℝ} (hx : 3 ≤ x) : (1 / 2 : ℝ) ≤ Real.log x := by
  have hx0 : 0 < x := by linarith
  have hsmall : 1 / x ≤ (1 / 3 : ℝ) := by
    apply (div_le_div_iff₀ hx0 (by norm_num : 0 < (3 : ℝ))).mpr
    linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hx0
  rw [← one_div] at hlog
  linarith

theorem primeDensity_hasDerivAt {Y x : ℝ} (hY : 0 < Y) (hx : 0 < x) :
    HasDerivAt (primeDensity Y)
      (Real.exp (-x / Y) / Y * (Real.log x + 1 - (x / Y) * Real.log x)) x := by
  have hl := ((hasDerivAt_id x).div_const Y).mul (Real.hasDerivAt_log hx.ne')
  have he := (((hasDerivAt_id x).neg).div_const Y).exp
  have hd := hl.mul he
  convert hd using 1
  · rfl
  · field_simp [hY.ne', hx.ne']
    ring

theorem primeDensity_antitoneOn {Y X : ℝ} (hY : 0 < Y) (hX : 3 ≤ X)
    (hXY : 3 * Y ≤ X) : AntitoneOn (primeDensity Y) (Ici X) := by
  have hcont : ContinuousOn (primeDensity Y) (Ici X) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx0 : 0 < x := by linarith [hx]
    unfold primeDensity
    fun_prop (disch := positivity)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici X) hcont
    (f' := fun x => Real.exp (-x / Y) / Y * (Real.log x + 1 - (x / Y) * Real.log x))
  · intro x hx
    have hxX : X < x := by simpa only [interior_Ici, mem_Ioi] using hx
    exact (primeDensity_hasDerivAt hY (by linarith)).hasDerivWithinAt
  · intro x hx
    have hxX : X < x := by simpa only [interior_Ici, mem_Ioi] using hx
    have hx3 : 3 ≤ x := by linarith
    have hlog := log_ge_half hx3
    have hlog0 : 0 ≤ Real.log x := by linarith
    have hxy : (3 : ℝ) ≤ x / Y := (le_div_iff₀ hY).mpr (by linarith)
    have hp := mul_le_mul_of_nonneg_right hxy hlog0
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    linarith

theorem primeDensity_integrable_and_integral_bound {Y X : ℝ}
    (hY : 0 < Y) (hX : 1 ≤ X) :
    IntegrableOn (primeDensity Y) (Ioi X) ∧
      (∫ x : ℝ in Ioi X, primeDensity Y x) ≤ primeError Y X := by
  obtain ⟨hf, hb⟩ := prime_kernel_integrable_and_bound hY hX
  refine ⟨(integrableOn_Ioi_translate (primeDensity Y) X).mp hf, ?_⟩
  rw [← integral_Ioi_translate (primeDensity Y) X]
  exact hb

/-- Closed discrete sample tail of the analytic prime density. -/
theorem primeDensity_sample_tail {Y X : ℝ} (hY : 0 < Y) (hX : 3 ≤ X)
    (hXY : 3 * Y ≤ X) :
    Summable (fun n : ℕ => primeDensity Y (X + (n + 1 : ℕ))) ∧
      (∑' n : ℕ, primeDensity Y (X + (n + 1 : ℕ))) ≤ primeError Y X := by
  obtain ⟨hf, hb⟩ := primeDensity_integrable_and_integral_bound hY (by linarith)
  have hpos : ∀ x ∈ Ici X, 0 ≤ primeDensity Y x := by
    intro x hx
    have hx1 : 1 ≤ x := by linarith [hx]
    have hl := Real.log_nonneg hx1
    unfold primeDensity
    positivity
  obtain ⟨hs, hsbound⟩ := positive_tail_sum_le_integral
    (primeDensity_antitoneOn hY hX hXY) hpos hf
  exact ⟨hs, hsbound.trans hb⟩

def dualDensity (Y x : ℝ) : ℝ := Real.log x / (Y * x ^ 2)

theorem dualDensity_hasDerivAt {Y x : ℝ} (hY : 0 < Y) (hx : 0 < x) :
    HasDerivAt (dualDensity Y) ((1 - 2 * Real.log x) / (Y * x ^ 3)) x := by
  have hd := (Real.hasDerivAt_log hx.ne').div
    (((hasDerivAt_id x).pow 2).const_mul Y) (by positivity : Y * x ^ 2 ≠ 0)
  convert hd using 1
  · rfl
  · field_simp [hY.ne', hx.ne']
    ring

theorem dualDensity_antitoneOn {Y Q : ℝ} (hY : 0 < Y) (hQ : 3 ≤ Q) :
    AntitoneOn (dualDensity Y) (Ici Q) := by
  have hcont : ContinuousOn (dualDensity Y) (Ici Q) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hx0 : 0 < x := by linarith [hx]
    unfold dualDensity
    fun_prop (disch := positivity)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici Q) hcont
    (f' := fun x => (1 - 2 * Real.log x) / (Y * x ^ 3))
  · intro x hx
    have hxQ : Q < x := by simpa only [interior_Ici, mem_Ioi] using hx
    exact (dualDensity_hasDerivAt hY (by linarith)).hasDerivWithinAt
  · intro x hx
    have hxQ : Q < x := by simpa only [interior_Ici, mem_Ioi] using hx
    have hx3 : 3 ≤ x := by linarith
    have hlog := log_ge_half hx3
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

/-- Exact H5 sample-tail inequality for the logarithmic density. -/
theorem dualDensity_sample_tail {Y Q : ℝ} (hY : 0 < Y) (hQ : 3 ≤ Q) :
    Summable (fun n : ℕ => dualDensity Y (Q + (n + 1 : ℕ))) ∧
      (∑' n : ℕ, dualDensity Y (Q + (n + 1 : ℕ))) ≤ dualError Y Q := by
  obtain ⟨hf, heq⟩ := integral_dual_density hY (by linarith : 1 ≤ Q)
  have hpos : ∀ x ∈ Ici Q, 0 ≤ dualDensity Y x := by
    intro x hx
    have hx1 : 1 ≤ x := by linarith [hx]
    have hl := Real.log_nonneg hx1
    unfold dualDensity
    positivity
  obtain ⟨hs, hb⟩ := positive_tail_sum_le_integral (dualDensity_antitoneOn hY hQ) hpos hf
  exact ⟨hs, hb.trans_eq heq⟩

end GoldbachContinuous22

#print axioms GoldbachContinuous22.integrableOn_Ioi_translate
#print axioms GoldbachContinuous22.integral_Ioi_translate
#print axioms GoldbachContinuous22.positive_tail_sum_le_integral
#print axioms GoldbachContinuous22.primeDensity
#print axioms GoldbachContinuous22.log_ge_half
#print axioms GoldbachContinuous22.primeDensity_hasDerivAt
#print axioms GoldbachContinuous22.primeDensity_antitoneOn
#print axioms GoldbachContinuous22.primeDensity_integrable_and_integral_bound
#print axioms GoldbachContinuous22.primeDensity_sample_tail
#print axioms GoldbachContinuous22.dualDensity
#print axioms GoldbachContinuous22.dualDensity_hasDerivAt
#print axioms GoldbachContinuous22.dualDensity_antitoneOn
#print axioms GoldbachContinuous22.dualDensity_sample_tail
