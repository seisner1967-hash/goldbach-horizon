import Mathlib.NumberTheory.VonMangoldt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Tactic

/-! SOURCE ONLY. The actual von Mangoldt heat trace is used throughout.
Only its direct prime-power definition and nonnegativity are used from the
arithmetic-function API. The geometric bounds below are derived, not supplied
as assumptions. No sieve, arithmetic bilinear estimate, Mobius identity,
Vaughan decomposition or progression remainder is used. This module bounds
the continuous correlation projection error only. Fourier orthogonality, a
uniform zeta/spectral evaluator, prime-power removal and D_N remain separate.
No compilation or numerical execution has been performed for this source. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def projectionHeatRatio (a : ℝ) : ℝ := Real.exp (-a)

def projectionAmplitude (a : ℝ) : ℝ :=
  projectionHeatRatio a / (1 - projectionHeatRatio a) ^ 2

def projectionTailEnvelope (a : ℝ) (M : ℕ) : ℝ :=
  projectionHeatRatio a ^ (M + 1) *
    (((M + 1 : ℕ) : ℝ) / (1 - projectionHeatRatio a) + projectionAmplitude a)

def projectionHeatTerm (a theta : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) * (projectionHeatRatio a : ℂ) ^ n *
    Complex.exp ((((n : ℝ) * theta : ℝ) : ℂ) * Complex.I)

def projectionHeatTrace (a theta : ℝ) : ℂ := ∑' n : ℕ, projectionHeatTerm a theta n

def projectionHeatPartial (a theta : ℝ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (M + 1), projectionHeatTerm a theta n

def projectionHeatTail (a theta : ℝ) (M : ℕ) : ℂ :=
  ∑' k : ℕ, projectionHeatTerm a theta (k + (M + 1))

def projectionCorrelation (a theta : ℝ) : ℂ :=
  projectionHeatTrace a theta * star (projectionHeatTrace a (-theta))

def projectionPartialCorrelation (a theta : ℝ) (M : ℕ) : ℂ :=
  projectionHeatPartial a theta M * star (projectionHeatPartial a (-theta) M)

def projectionCharacter (N : ℕ) (theta : ℝ) : ℂ :=
  Complex.exp (((-(N : ℝ) * theta : ℝ) : ℂ) * Complex.I)

def thermalContinuousProjection (a : ℝ) (N : ℕ) : ℂ :=
  ((Real.exp (a * (N : ℝ)) / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ theta : ℝ in (0)..(2 * Real.pi),
      projectionCorrelation a theta * projectionCharacter N theta

def thermalPartialProjection (a : ℝ) (N M : ℕ) : ℂ :=
  ((Real.exp (a * (N : ℝ)) / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ theta : ℝ in (0)..(2 * Real.pi),
      projectionPartialCorrelation a theta M * projectionCharacter N theta

def projectionErrorEnvelope (a : ℝ) (N M : ℕ) : ℝ :=
  2 * Real.exp (a * (N : ℝ)) * projectionAmplitude a * projectionTailEnvelope a M

theorem projectionHeatRatio_pos (a : ℝ) : 0 < projectionHeatRatio a := Real.exp_pos _

theorem projectionHeatRatio_lt_one {a : ℝ} (ha : 0 < a) : projectionHeatRatio a < 1 := by
  exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha)

theorem norm_projectionHeatRatio_lt_one {a : ℝ} (ha : 0 < a) :
    ‖projectionHeatRatio a‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (projectionHeatRatio_pos a)]
  exact projectionHeatRatio_lt_one ha

/-- Direct prime-power bound, without an arithmetic inversion formula. -/
theorem projection_vonMangoldt_le_nat (n : ℕ) :
    ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  rw [ArithmeticFunction.vonMangoldt_apply]
  split_ifs
  · have hp : 0 < (Nat.minFac n : ℝ) := by exact_mod_cast Nat.minFac_pos n
    have hlog := Real.log_le_sub_one_of_pos hp
    have hfac : (Nat.minFac n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.minFac_le hn0
    linarith
  · positivity

theorem norm_projectionHeatTerm (a theta : ℝ) (n : ℕ) :
    ‖projectionHeatTerm a theta n‖ =
      ArithmeticFunction.vonMangoldt n * projectionHeatRatio a ^ n := by
  simp only [projectionHeatTerm, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
    abs_of_pos (projectionHeatRatio_pos a), Complex.norm_exp_ofReal_mul_I, mul_one]

theorem norm_projectionHeatTerm_le (a theta : ℝ) (n : ℕ) :
    ‖projectionHeatTerm a theta n‖ ≤ (n : ℝ) * projectionHeatRatio a ^ n := by
  rw [norm_projectionHeatTerm]
  exact mul_le_mul_of_nonneg_right (projection_vonMangoldt_le_nat n)
    (pow_nonneg (projectionHeatRatio_pos a).le _)

theorem hasSum_projection_majorant {a : ℝ} (ha : 0 < a) :
    HasSum (fun n : ℕ => (n : ℝ) * projectionHeatRatio a ^ n) (projectionAmplitude a) :=
  hasSum_coe_mul_geometric_of_norm_lt_one (norm_projectionHeatRatio_lt_one ha)

/-- The full shifted geometric first moment equals B(a,M), including M+1. -/
theorem hasSum_projection_tail_majorant {a : ℝ} (ha : 0 < a) (M : ℕ) :
    HasSum (fun k : ℕ => ((k + (M + 1) : ℕ) : ℝ) *
      projectionHeatRatio a ^ (k + (M + 1))) (projectionTailEnvelope a M) := by
  have hN := hasSum_projection_majorant ha
  have hG := hasSum_geometric_of_norm_lt_one (norm_projectionHeatRatio_lt_one ha)
  have h := (hN.add (hG.mul_left ((M + 1 : ℕ) : ℝ))).mul_right
    (projectionHeatRatio a ^ (M + 1))
  convert h using 1
  · funext k
    simp only [Nat.cast_add, pow_add]
    ring
  · unfold projectionTailEnvelope projectionAmplitude
    simp only [div_eq_mul_inv]
    ring

theorem summable_norm_projectionHeatTerm {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    Summable (fun n : ℕ => ‖projectionHeatTerm a theta n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_projectionHeatTerm_le a theta) (hasSum_projection_majorant ha).summable

theorem summable_projectionHeatTerm {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    Summable (projectionHeatTerm a theta) := (summable_norm_projectionHeatTerm ha theta).of_norm

theorem summable_norm_projectionHeatTail {a : ℝ} (ha : 0 < a) (theta : ℝ) (M : ℕ) :
    Summable (fun k : ℕ => ‖projectionHeatTerm a theta (k + (M + 1))‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => norm_projectionHeatTerm_le a theta (k + (M + 1)))
    (hasSum_projection_tail_majorant ha M).summable

theorem norm_projectionHeatTrace_le {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    ‖projectionHeatTrace a theta‖ ≤ projectionAmplitude a := by
  have hn := summable_norm_projectionHeatTerm ha theta
  have hmaj := hasSum_projection_majorant ha
  exact (norm_tsum_le_tsum_norm hn).trans
    ((tsum_le_tsum (norm_projectionHeatTerm_le a theta) hn hmaj.summable).trans_eq hmaj.tsum_eq)

theorem norm_projectionHeatTail_le {a : ℝ} (ha : 0 < a) (theta : ℝ) (M : ℕ) :
    ‖projectionHeatTail a theta M‖ ≤ projectionTailEnvelope a M := by
  have hn := summable_norm_projectionHeatTail ha theta M
  have hmaj := hasSum_projection_tail_majorant ha M
  exact (norm_tsum_le_tsum_norm hn).trans
    ((tsum_le_tsum (fun k => norm_projectionHeatTerm_le a theta (k + (M + 1)))
      hn hmaj.summable).trans_eq hmaj.tsum_eq)

theorem projectionHeatPartial_add_tail {a : ℝ} (ha : 0 < a) (theta : ℝ) (M : ℕ) :
    projectionHeatPartial a theta M + projectionHeatTail a theta M =
      projectionHeatTrace a theta :=
  sum_add_tsum_nat_add (M + 1) (summable_projectionHeatTerm ha theta)

theorem norm_projectionHeatTrace_sub_partial_le {a : ℝ} (ha : 0 < a)
    (theta : ℝ) (M : ℕ) :
    ‖projectionHeatTrace a theta - projectionHeatPartial a theta M‖ ≤
      projectionTailEnvelope a M := by
  rw [← projectionHeatPartial_add_tail ha theta M, add_sub_cancel_left]
  exact norm_projectionHeatTail_le ha theta M

theorem norm_projectionHeatPartial_le {a : ℝ} (ha : 0 < a) (theta : ℝ) (M : ℕ) :
    ‖projectionHeatPartial a theta M‖ ≤ projectionAmplitude a := by
  have hmaj := hasSum_projection_majorant ha
  calc
    ‖projectionHeatPartial a theta M‖ ≤
        ∑ n ∈ Finset.range (M + 1), ‖projectionHeatTerm a theta n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (M + 1), (n : ℝ) * projectionHeatRatio a ^ n := by
      exact Finset.sum_le_sum (fun n hn => norm_projectionHeatTerm_le a theta n)
    _ ≤ projectionAmplitude a :=
      sum_le_hasSum (Finset.range (M + 1)) (fun n hn =>
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (projectionHeatRatio_pos a).le _)) hmaj

theorem projectionAmplitude_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ projectionAmplitude a := by
  unfold projectionAmplitude projectionHeatRatio
  positivity

theorem projectionTailEnvelope_nonneg {a : ℝ} (ha : 0 < a) (M : ℕ) :
    0 ≤ projectionTailEnvelope a M := by
  have hd : 0 < 1 - projectionHeatRatio a := sub_pos.mpr (projectionHeatRatio_lt_one ha)
  have hA := projectionAmplitude_nonneg ha
  have hr := projectionHeatRatio_pos a
  unfold projectionTailEnvelope
  positivity

theorem norm_projectionCorrelation_sub_partial_le {a : ℝ} (ha : 0 < a)
    (theta : ℝ) (M : ℕ) :
    ‖projectionCorrelation a theta - projectionPartialCorrelation a theta M‖ ≤
      2 * projectionAmplitude a * projectionTailEnvelope a M := by
  have hA := projectionAmplitude_nonneg ha
  have hB := projectionTailEnvelope_nonneg ha M
  have hid : projectionCorrelation a theta - projectionPartialCorrelation a theta M =
      (projectionHeatTrace a theta - projectionHeatPartial a theta M) *
        star (projectionHeatTrace a (-theta)) +
      projectionHeatPartial a theta M *
        star (projectionHeatTrace a (-theta) - projectionHeatPartial a (-theta) M) := by
    unfold projectionCorrelation projectionPartialCorrelation
    rw [star_sub]
    ring
  rw [hid]
  calc
    _ ≤ ‖(projectionHeatTrace a theta - projectionHeatPartial a theta M) *
        star (projectionHeatTrace a (-theta))‖ +
      ‖projectionHeatPartial a theta M *
        star (projectionHeatTrace a (-theta) - projectionHeatPartial a (-theta) M)‖ :=
      norm_add_le _ _
    _ ≤ projectionTailEnvelope a M * projectionAmplitude a +
        projectionAmplitude a * projectionTailEnvelope a M := by
      simp only [norm_mul, Complex.star_def, RCLike.norm_conj]
      exact add_le_add
        (mul_le_mul (norm_projectionHeatTrace_sub_partial_le ha theta M)
          (norm_projectionHeatTrace_le ha (-theta)) (norm_nonneg _) hB)
        (mul_le_mul (norm_projectionHeatPartial_le ha theta M)
          (norm_projectionHeatTrace_sub_partial_le ha (-theta) M) (norm_nonneg _) hA)
    _ = _ := by ring

theorem projectionHeatTrace_continuous {a : ℝ} (ha : 0 < a) :
    Continuous (projectionHeatTrace a) := by
  apply continuous_tsum
  · intro n
    unfold projectionHeatTerm
    fun_prop
  · exact (hasSum_projection_majorant ha).summable
  · intro n theta
    exact norm_projectionHeatTerm_le a theta n

theorem projectionHeatPartial_continuous (a : ℝ) (M : ℕ) :
    Continuous (fun theta : ℝ => projectionHeatPartial a theta M) := by
  unfold projectionHeatPartial projectionHeatTerm
  fun_prop

theorem projectionCorrelation_continuous {a : ℝ} (ha : 0 < a) :
    Continuous (projectionCorrelation a) := by
  have h := projectionHeatTrace_continuous ha
  exact h.mul ((h.comp continuous_id.neg).star)

theorem projectionPartialCorrelation_continuous (a : ℝ) (M : ℕ) :
    Continuous (fun theta : ℝ => projectionPartialCorrelation a theta M) := by
  have h := projectionHeatPartial_continuous a M
  exact h.mul ((h.comp continuous_id.neg).star)

theorem norm_projectionCharacter (N : ℕ) (theta : ℝ) : ‖projectionCharacter N theta‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- Genuine error between two integrals of the actual continuous traces.
    This is not the Fourier coefficient theorem or a bound for D_N. -/
theorem thermalContinuousProjection_error_le {a : ℝ} (ha : 0 < a) (N M : ℕ) :
    ‖thermalContinuousProjection a N - thermalPartialProjection a N M‖ ≤
      projectionErrorEnvelope a N M := by
  have hchar : Continuous (projectionCharacter N) := by
    unfold projectionCharacter
    fun_prop
  have hi := ((projectionCorrelation_continuous ha).mul hchar).intervalIntegrable
    (0 : ℝ) (2 * Real.pi)
  have hf := ((projectionPartialCorrelation_continuous a M).mul hchar).intervalIntegrable
    (0 : ℝ) (2 * Real.pi)
  have hbound : ∀ theta : ℝ,
      ‖(projectionCorrelation a theta - projectionPartialCorrelation a theta M) *
        projectionCharacter N theta‖ ≤ 2 * projectionAmplitude a * projectionTailEnvelope a M := by
    intro theta
    rw [norm_mul, norm_projectionCharacter, mul_one]
    exact norm_projectionCorrelation_sub_partial_le ha theta M
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi) (fun theta ht => hbound theta)
  have hc : 0 < Real.exp (a * (N : ℝ)) / (2 * Real.pi) := by positivity
  unfold thermalContinuousProjection thermalPartialProjection
  rw [← mul_sub, ← intervalIntegral.integral_sub hi hf]
  simp_rw [← sub_mul]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  calc
    _ ≤ (Real.exp (a * (N : ℝ)) / (2 * Real.pi)) *
        ((2 * projectionAmplitude a * projectionTailEnvelope a M) * |2 * Real.pi - 0|) :=
      mul_le_mul_of_nonneg_left hb hc.le
    _ = projectionErrorEnvelope a N M := by
      rw [sub_zero, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      unfold projectionErrorEnvelope
      field_simp [Real.pi_ne_zero] <;> ring

theorem projectionErrorEnvelope_nonneg {a : ℝ} (ha : 0 < a) (N M : ℕ) :
    0 ≤ projectionErrorEnvelope a N M := by
  have hA := projectionAmplitude_nonneg ha
  have hB := projectionTailEnvelope_nonneg ha M
  unfold projectionErrorEnvelope
  positivity

theorem projectionAmplitude_continuousOn : ContinuousOn projectionAmplitude (Ioi (0 : ℝ)) := by
  intro a ha
  have hd : 0 < 1 - Real.exp (-a) := sub_pos.mpr (projectionHeatRatio_lt_one ha)
  apply ContinuousAt.continuousWithinAt
  unfold projectionAmplitude projectionHeatRatio
  fun_prop (disch := positivity)

theorem projectionTailEnvelope_continuousOn (M : ℕ) :
    ContinuousOn (fun a : ℝ => projectionTailEnvelope a M) (Ioi (0 : ℝ)) := by
  intro a ha
  have hd : 0 < 1 - Real.exp (-a) := sub_pos.mpr (projectionHeatRatio_lt_one ha)
  apply ContinuousAt.continuousWithinAt
  unfold projectionTailEnvelope projectionAmplitude projectionHeatRatio
  fun_prop (disch := positivity)

theorem projectionErrorEnvelope_continuousOn (N M : ℕ) :
    ContinuousOn (fun a : ℝ => projectionErrorEnvelope a N M) (Ioi (0 : ℝ)) := by
  have he : Continuous (fun a : ℝ => Real.exp (a * (N : ℝ))) := by fun_prop
  exact ((continuousOn_const.mul he.continuousOn).mul
    projectionAmplitude_continuousOn).mul (projectionTailEnvelope_continuousOn M)

end GoldbachContinuous22

#print axioms GoldbachContinuous22.projectionHeatRatio
#print axioms GoldbachContinuous22.projectionAmplitude
#print axioms GoldbachContinuous22.projectionTailEnvelope
#print axioms GoldbachContinuous22.projectionHeatTerm
#print axioms GoldbachContinuous22.projectionHeatTrace
#print axioms GoldbachContinuous22.projectionHeatPartial
#print axioms GoldbachContinuous22.projectionHeatTail
#print axioms GoldbachContinuous22.projectionCorrelation
#print axioms GoldbachContinuous22.projectionPartialCorrelation
#print axioms GoldbachContinuous22.projectionCharacter
#print axioms GoldbachContinuous22.thermalContinuousProjection
#print axioms GoldbachContinuous22.thermalPartialProjection
#print axioms GoldbachContinuous22.projectionErrorEnvelope
#print axioms GoldbachContinuous22.projectionHeatRatio_pos
#print axioms GoldbachContinuous22.projectionHeatRatio_lt_one
#print axioms GoldbachContinuous22.norm_projectionHeatRatio_lt_one
#print axioms GoldbachContinuous22.projection_vonMangoldt_le_nat
#print axioms GoldbachContinuous22.norm_projectionHeatTerm
#print axioms GoldbachContinuous22.norm_projectionHeatTerm_le
#print axioms GoldbachContinuous22.hasSum_projection_majorant
#print axioms GoldbachContinuous22.hasSum_projection_tail_majorant
#print axioms GoldbachContinuous22.summable_norm_projectionHeatTerm
#print axioms GoldbachContinuous22.summable_projectionHeatTerm
#print axioms GoldbachContinuous22.summable_norm_projectionHeatTail
#print axioms GoldbachContinuous22.norm_projectionHeatTrace_le
#print axioms GoldbachContinuous22.norm_projectionHeatTail_le
#print axioms GoldbachContinuous22.projectionHeatPartial_add_tail
#print axioms GoldbachContinuous22.norm_projectionHeatTrace_sub_partial_le
#print axioms GoldbachContinuous22.norm_projectionHeatPartial_le
#print axioms GoldbachContinuous22.projectionAmplitude_nonneg
#print axioms GoldbachContinuous22.projectionTailEnvelope_nonneg
#print axioms GoldbachContinuous22.norm_projectionCorrelation_sub_partial_le
#print axioms GoldbachContinuous22.projectionHeatTrace_continuous
#print axioms GoldbachContinuous22.projectionHeatPartial_continuous
#print axioms GoldbachContinuous22.projectionCorrelation_continuous
#print axioms GoldbachContinuous22.projectionPartialCorrelation_continuous
#print axioms GoldbachContinuous22.norm_projectionCharacter
#print axioms GoldbachContinuous22.thermalContinuousProjection_error_le
#print axioms GoldbachContinuous22.projectionErrorEnvelope_nonneg
#print axioms GoldbachContinuous22.projectionAmplitude_continuousOn
#print axioms GoldbachContinuous22.projectionTailEnvelope_continuousOn
#print axioms GoldbachContinuous22.projectionErrorEnvelope_continuousOn
