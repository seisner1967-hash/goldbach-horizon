import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# TS282 - ASCII bridge for the regularized completed zeta API

The locked Mathlib declarations use the Unicode subscript-zero character.
This file contains the only unavoidable uses of that character and gives the
API stable ASCII names for the rest of TS282.
-/

noncomputable section

namespace TS282
namespace Goldbach

/-- ASCII alias for Mathlib's entire regularized completed zeta function. -/
noncomputable def completedRiemannZetaZero (s : Complex) : Complex :=
  completedRiemannZeta₀ s

theorem differentiable_completedRiemannZetaZero :
    Differentiable Complex completedRiemannZetaZero := by
  exact differentiable_completedZeta₀

theorem completedRiemannZetaZero_one_sub (s : Complex) :
    completedRiemannZetaZero (1 - s) = completedRiemannZetaZero s := by
  exact completedRiemannZeta₀_one_sub s

theorem completedRiemannZeta_eq_zero_regularization (s : Complex) :
    completedRiemannZeta s =
      completedRiemannZetaZero s - 1 / s - 1 / (1 - s) := by
  exact completedRiemannZeta_eq s

/-- ASCII alias for the reciprocal real archimedean Gamma factor. -/
noncomputable def completedRiemannZetaGammaInv (s : Complex) : Complex :=
  (Complex.Gammaℝ s)⁻¹

theorem differentiable_completedRiemannZetaGammaInv :
    Differentiable Complex completedRiemannZetaGammaInv := by
  exact Complex.differentiable_Gammaℝ_inv

theorem completedRiemannZetaGammaInv_ne_zero_of_re_pos
    {s : Complex}
    (hs : 0 < s.re) :
    Not (completedRiemannZetaGammaInv s = 0) := by
  unfold completedRiemannZetaGammaInv
  exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hs)

/-- The reciprocal archimedean Gamma factor is nonzero off the real axis. -/
theorem completedRiemannZetaGammaInv_ne_zero_of_im_ne_zero
    {s : Complex}
    (hs : Not (s.im = 0)) :
    Not (completedRiemannZetaGammaInv s = 0) := by
  unfold completedRiemannZetaGammaInv
  apply inv_ne_zero
  intro hGamma
  rw [Complex.Gammaℝ_eq_zero_iff] at hGamma
  obtain ⟨n, hn⟩ := hGamma
  apply hs
  rw [hn]
  simp

theorem riemannZeta_eq_completed_mul_gammaInv
    {s : Complex}
    (hs : Not (s = 0)) :
    riemannZeta s =
      completedRiemannZeta s * completedRiemannZetaGammaInv s := by
  rw [riemannZeta_def_of_ne_zero hs]
  rfl

end Goldbach
end TS282
