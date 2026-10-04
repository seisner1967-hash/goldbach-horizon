import ArchimedeanTail22
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/- Source-only removal of the genuine endpoint singularity at x=1. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def archNumerator (Y x : ℝ) : ℝ :=
  realTest Y x + realTest Y (1 / x) / x - 2 * realTest Y 1 / x

def archDenominator (x : ℝ) : ℝ := x - 1 / x

theorem realTest_hasDerivAt {Y : ℝ} (hY : 0 < Y) (x : ℝ) :
    HasDerivAt (realTest Y) ((1 / Y) * (1 - x / Y) * Real.exp (-x / Y)) x := by
  have hlin := (hasDerivAt_id x).div_const Y
  have he := (((hasDerivAt_id x).neg).div_const Y).exp
  have hd := hlin.mul he
  convert hd using 1
  · rfl
  · field_simp [hY.ne']
    ring

theorem archNumerator_one (Y : ℝ) : archNumerator Y 1 = 0 := by
  unfold archNumerator
  norm_num only [div_one, one_div_one]
  ring

theorem archDenominator_one : archDenominator 1 = 0 := by
  unfold archDenominator
  norm_num

theorem archNumerator_hasDerivAt_one {Y : ℝ} (hY : 0 < Y) :
    HasDerivAt (archNumerator Y) (realTest Y 1) 1 := by
  have hi : HasDerivAt (fun x : ℝ => 1 / x) (-1) 1 := by
    simpa only [one_div, id_eq, one_pow, div_one] using
      (hasDerivAt_id (1 : ℝ)).inv (by norm_num : (1 : ℝ) ≠ 0)
  have hf := realTest_hasDerivAt hY (1 : ℝ)
  have hcomp := hf.comp_of_eq hi (by norm_num : (1 : ℝ) = 1 / 1)
  have hquot := hcomp.div (hasDerivAt_id (1 : ℝ)) (by norm_num : (1 : ℝ) ≠ 0)
  have hconst := (hasDerivAt_const (1 : ℝ) (2 * realTest Y 1)).div
    (hasDerivAt_id (1 : ℝ)) (by norm_num : (1 : ℝ) ≠ 0)
  have hd := (hf.add hquot).sub hconst
  convert hd using 1
  · rfl
  · simp only [Function.comp_def, div_one, mul_one, one_pow]
    ring

theorem archDenominator_hasDerivAt_one : HasDerivAt archDenominator 2 1 := by
  have hi : HasDerivAt (fun x : ℝ => 1 / x) (-1) 1 := by
    simpa only [one_div, id_eq, one_pow, div_one] using
      (hasDerivAt_id (1 : ℝ)).inv (by norm_num : (1 : ℝ) ≠ 0)
  convert (hasDerivAt_id (1 : ℝ)).sub hi using 1 <;> norm_num [archDenominator]

/-- The exact removable limit, obtained from derivatives of numerator and denominator. -/
theorem arch_endpoint_tendsto {Y : ℝ} (hY : 0 < Y) :
    Tendsto (archIntegrand Y) (𝓝[≠] (1 : ℝ)) (𝓝 (realTest Y 1 / 2)) := by
  have hn := hasDerivAt_iff_tendsto_slope.mp (archNumerator_hasDerivAt_one hY)
  have hd := hasDerivAt_iff_tendsto_slope.mp archDenominator_hasDerivAt_one
  have hquot := hn.div hd (by norm_num : (2 : ℝ) ≠ 0)
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx1 : x ≠ (1 : ℝ) := by
    simpa only [mem_compl_iff, mem_singleton_iff] using hx
  simp only [slope_def_field, archNumerator_one, archDenominator_one, sub_zero]
  rw [div_div_div_cancel_right₀ (sub_ne_zero.mpr hx1)]
  rfl

def archContinuous (Y : ℝ) : ℝ → ℝ := by
  classical
  exact Function.update (archIntegrand Y) 1 (realTest Y 1 / 2)

theorem archContinuous_one (Y : ℝ) : archContinuous Y 1 = realTest Y 1 / 2 := by
  classical
  unfold archContinuous
  exact Function.update_self _ _ _

theorem archContinuous_eq {Y x : ℝ} (hx : x ≠ 1) :
    archContinuous Y x = archIntegrand Y x := by
  classical
  unfold archContinuous
  exact Function.update_of_ne hx _ _

theorem archContinuous_continuousAt_one {Y : ℝ} (hY : 0 < Y) :
    ContinuousAt (archContinuous Y) 1 := by
  classical
  unfold archContinuous
  exact continuousAt_update_same.mpr (arch_endpoint_tendsto hY)

theorem archContinuous_continuousOn {Y : ℝ} (hY : 0 < Y) :
    ContinuousOn (archContinuous Y) (Ici 1) := by
  classical
  intro x hx
  by_cases hx1 : x = 1
  · subst x
    exact (archContinuous_continuousAt_one hY).continuousWithinAt
  · have hxgt : 1 < x := lt_of_le_of_ne hx (Ne.symm hx1)
    have hx0 : 0 < x := by linarith
    have hi : 1 / x < 1 := (div_lt_iff₀ hx0).mpr (by linarith)
    have hd : 0 < x - 1 / x := by linarith
    have hc : ContinuousAt (archIntegrand Y) x := by
      unfold archIntegrand realTest
      fun_prop (disch := positivity)
    unfold archContinuous
    exact ((continuousAt_update_of_ne hx1).mpr hc).continuousWithinAt

/-- The entire improper archimedean integral is defined by a genuine integrable function. -/
theorem archIntegrand_integrableOn {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (archIntegrand Y) (Ioi 1) := by
  have hc : ContinuousOn (archContinuous Y) (Icc (1 : ℝ) 2) :=
    (archContinuous_continuousOn hY).mono (fun x hx => hx.1)
  have hcompact : IntegrableOn (archContinuous Y) (Icc (1 : ℝ) 2) :=
    hc.integrableOn_compact isCompact_Icc
  have hbounded : IntegrableOn (archIntegrand Y) (Ioc (1 : ℝ) 2) := by
    apply (hcompact.mono_set Ioc_subset_Icc_self).congr_fun _ measurableSet_Ioc
    intro x hx
    exact archContinuous_eq (ne_of_gt hx.1)
  have htail := (arch_tail_integrable_and_bound hY (show (2 : ℝ) ≤ 2 from le_rfl)).1
  have hunion : Ioc (1 : ℝ) 2 ∪ Ioi 2 = Ioi 1 := by
    ext x
    change (1 < x ∧ x ≤ 2) ∨ 2 < x ↔ 1 < x
    constructor
    · intro h
      rcases h with h | h
      · exact h.1
      · linarith
    · intro h
      by_cases hx : x ≤ 2
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (lt_of_not_ge hx)
  rw [← hunion]
  exact hbounded.union htail

end GoldbachContinuous22

#print axioms GoldbachContinuous22.archNumerator
#print axioms GoldbachContinuous22.archDenominator
#print axioms GoldbachContinuous22.realTest_hasDerivAt
#print axioms GoldbachContinuous22.archNumerator_one
#print axioms GoldbachContinuous22.archDenominator_one
#print axioms GoldbachContinuous22.archNumerator_hasDerivAt_one
#print axioms GoldbachContinuous22.archDenominator_hasDerivAt_one
#print axioms GoldbachContinuous22.arch_endpoint_tendsto
#print axioms GoldbachContinuous22.archContinuous
#print axioms GoldbachContinuous22.archContinuous_one
#print axioms GoldbachContinuous22.archContinuous_eq
#print axioms GoldbachContinuous22.archContinuous_continuousAt_one
#print axioms GoldbachContinuous22.archContinuous_continuousOn
#print axioms GoldbachContinuous22.archIntegrand_integrableOn
