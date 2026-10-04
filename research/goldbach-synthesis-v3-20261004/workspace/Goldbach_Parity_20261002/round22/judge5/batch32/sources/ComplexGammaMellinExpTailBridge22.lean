import ComplexGammaMellinHolomorphy22
import ComplexGammaMellinTail22

/-! SOURCE ONLY / PENDING_TAIL_DEPENDENCY. Tail28 failed elaboration;
its separate SOURCE revision02 awaits an independent compiler verdict.
This exact bridge uses the actual
Mellin inversion27; it never assumes the exponential/integral identity.
No execution is authorized by this source file or its imports. -/

noncomputable section
namespace GoldbachComplexGammaMellin22

theorem complex_exp_sub_truncated_eq_tail {w : ℂ} (hw : 0 < w.re)
    {H : ℝ} (hH : 0 ≤ H) :
    Complex.exp (-w) - complexGammaTruncated w H = complexGammaTail w H := by
  rw [← complexGammaInverse_eq_exp hw]
  exact complexGammaInverse_sub_truncated_eq_tail hw hH

theorem complex_exp_truncation_error_le {w : ℂ} (hw : 0 < w.re)
    {H : ℝ} (hH : 0 ≤ H) :
    ‖Complex.exp (-w) - complexGammaTruncated w H‖ ≤ complexGammaTailRadius w H := by
  rw [← complexGammaInverse_eq_exp hw]
  exact complexGammaInverse_truncation_error_le hw hH

end GoldbachComplexGammaMellin22

#print axioms GoldbachComplexGammaMellin22.complex_exp_sub_truncated_eq_tail
#print axioms GoldbachComplexGammaMellin22.complex_exp_truncation_error_le
