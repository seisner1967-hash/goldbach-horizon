import ZetaEulerLambda22
import ZetaReflection22
import Mathlib.Analysis.Complex.RemovableSingularity

/- SOURCE_ONLY. A is the actual zeta with its simple pole removed, using the
   proven residue1. Its value at1 and analyticity are derived, not supplied
   as an abstract entire-function hypothesis. Its logarithmic derivatives
   retain the actual rational pole term needed for C3/C4. -/

noncomputable section
open Complex Set Filter
open scoped Topology

namespace GoldbachContinuous22

def contourZetaA : ℂ → ℂ := by
  classical
  exact Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1

theorem contourZetaA_one : contourZetaA 1 = 1 := by
  classical
  simp [contourZetaA]

theorem contourZetaA_eq_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    contourZetaA s = (s - 1) * riemannZeta s := by
  classical
  simp only [contourZetaA, Function.update_of_ne hs]

theorem contourZetaA_continuousAt_one : ContinuousAt contourZetaA 1 := by
  classical
  exact continuousAt_update_same.mpr riemannZeta_residue_one

theorem hasDerivAt_contourZetaA_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    HasDerivAt contourZetaA
      (riemannZeta s + (s - 1) * deriv riemannZeta s) s := by
  have hprod := ((hasDerivAt_id s).sub_const (1 : ℂ)).mul
    (differentiableAt_riemannZeta hs).hasDerivAt
  have heq : contourZetaA =ᶠ[𝓝 s] (fun z : ℂ => (z - 1) * riemannZeta z) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact contourZetaA_eq_of_ne_one hz
  simpa only [one_mul] using hprod.congr_of_eventuallyEq heq

/-- The pole removal uses the real zeta residue and the actual punctured
    differentiability. No hEntire or hResidue premise is introduced. -/
theorem contourZetaA_analyticAt_one : AnalyticAt ℂ contourZetaA 1 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    _ contourZetaA_continuousAt_one
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (hasDerivAt_contourZetaA_of_ne_one hs).differentiableAt

theorem contourZetaA_differentiable : Differentiable ℂ contourZetaA := by
  intro s
  by_cases hs : s = 1
  · subst s
    exact contourZetaA_analyticAt_one.differentiableAt
  · exact (hasDerivAt_contourZetaA_of_ne_one hs).differentiableAt

theorem contourZetaA_analyticAt (s : ℂ) : AnalyticAt ℂ contourZetaA s :=
  contourZetaA_differentiable.analyticAt s

theorem contourZetaA_ne_zero_on_right {s : ℂ} (hs : 1 < s.re) :
    contourZetaA s ≠ 0 := by
  have hs1 : s ≠ 1 := by
    intro heq
    simp only [heq, Complex.one_re, lt_self_iff_false] at hs
  rw [contourZetaA_eq_of_ne_one hs1]
  exact mul_ne_zero (sub_ne_zero.mpr hs1) (contourZeta_ne_zero_on_right hs)

theorem contourZetaA_ne_zero_in_left_strip {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 0) : contourZetaA s ≠ 0 := by
  have hs : s ≠ 1 := by
    intro heq
    simp only [heq, Complex.one_re] at hs1
    linarith
  rw [contourZetaA_eq_of_ne_one hs]
  exact mul_ne_zero (sub_ne_zero.mpr hs)
    (contourZeta_ne_zero_in_left_strip hs0 hs1)

theorem contourZetaA_logDeriv_of_ne_one {s : ℂ} (hs : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    deriv contourZetaA s / contourZetaA s =
      1 / (s - 1) + deriv riemannZeta s / riemannZeta s := by
  rw [(hasDerivAt_contourZetaA_of_ne_one hs).deriv, contourZetaA_eq_of_ne_one hs]
  field_simp [sub_ne_zero.mpr hs, hζ]
  ring

/-- The actual A logarithmic derivative on the right half-plane. -/
theorem contourZetaA_logDeriv_right {s : ℂ} (hs : 1 < s.re) :
    deriv contourZetaA s / contourZetaA s =
      1 / (s - 1) - ∑' n : ℕ, (contourLambdaWeight n : ℂ) * (n : ℂ) ^ (-s) := by
  have hs1 : s ≠ 1 := by
    intro heq
    simp only [heq, Complex.one_re, lt_self_iff_false] at hs
  rw [contourZetaA_logDeriv_of_ne_one hs1 (contourZeta_ne_zero_on_right hs),
    contourZeta_logDeriv_direct_Lambda hs, add_neg_eq_sub]

/-- The reflected actual A logarithmic derivative. All nonvanishing statements
    are derived from the domain, not imported as a trace conclusion. -/
theorem contourZetaA_logDeriv_left {s : ℂ}
    (hs0 : -1 < s.re) (hs1 : s.re < 0) :
    deriv contourZetaA s / contourZetaA s =
      1 / (s - 1) + deriv contourChi s / contourChi s +
        ∑' n : ℕ, (contourLambdaWeight n : ℂ) * (n : ℂ) ^ (-(1 - s)) := by
  have hs : s ≠ 1 := by
    intro heq
    simp only [heq, Complex.one_re] at hs1
    linarith
  have hr : 1 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  rw [contourZetaA_logDeriv_of_ne_one hs (contourZeta_ne_zero_in_left_strip hs0 hs1),
    contourZeta_logDeriv_reflection hs0 hs1, contourZeta_logDeriv_direct_Lambda hr]
  ring

end GoldbachContinuous22

#print axioms GoldbachContinuous22.contourZetaA
#print axioms GoldbachContinuous22.contourZetaA_one
#print axioms GoldbachContinuous22.contourZetaA_eq_of_ne_one
#print axioms GoldbachContinuous22.contourZetaA_continuousAt_one
#print axioms GoldbachContinuous22.hasDerivAt_contourZetaA_of_ne_one
#print axioms GoldbachContinuous22.contourZetaA_analyticAt_one
#print axioms GoldbachContinuous22.contourZetaA_differentiable
#print axioms GoldbachContinuous22.contourZetaA_analyticAt
#print axioms GoldbachContinuous22.contourZetaA_ne_zero_on_right
#print axioms GoldbachContinuous22.contourZetaA_ne_zero_in_left_strip
#print axioms GoldbachContinuous22.contourZetaA_logDeriv_of_ne_one
#print axioms GoldbachContinuous22.contourZetaA_logDeriv_right
#print axioms GoldbachContinuous22.contourZetaA_logDeriv_left
