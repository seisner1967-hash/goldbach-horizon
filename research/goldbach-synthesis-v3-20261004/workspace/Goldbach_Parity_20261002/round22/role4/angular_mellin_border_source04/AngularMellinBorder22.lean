import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! SOURCE ONLY, not elaborated or compiled by the author.
The principal complex power stays off its cut because the real part of its
base is a > 0. All derivative and integrability charges below are constructed.
The character has equal endpoint values; the complex power is not assumed
periodic. The border vanishes for q=0 and is nonzero for q=1 and N>0.
This finite-interval identity gives no global spectral cancellation or D_N bound.
-/

noncomputable section

open MeasureTheory

namespace GoldbachAngularMellinBorder22

def angularBase (a theta : ℝ) : ℂ := (a : ℂ) - Complex.I * (theta : ℂ)

def angularPower (a : ℝ) (q : ℂ) (theta : ℝ) : ℂ :=
  angularBase a theta ^ (-q)

def angularCharacter (N : ℕ) (theta : ℝ) : ℂ :=
  Complex.exp (-(N : ℂ) * Complex.I * (theta : ℂ))

def angularIntegrand (a : ℝ) (N : ℕ) (q : ℂ) (theta : ℝ) : ℂ :=
  angularPower a q theta * angularCharacter N theta

def angularDerivative (a : ℝ) (N : ℕ) (q : ℂ) (theta : ℝ) : ℂ :=
  Complex.I * q * angularIntegrand a N (q + 1) theta -
    Complex.I * (N : ℂ) * angularIntegrand a N q theta

def angularNormalizer : ℂ := (2 * (Real.pi : ℂ))⁻¹

def angularJ (a : ℝ) (N : ℕ) (q : ℂ) : ℂ :=
  angularNormalizer * ∫ theta in (-Real.pi)..Real.pi, angularIntegrand a N q theta

def angularBorder (a : ℝ) (N : ℕ) (q : ℂ) : ℂ :=
  Complex.I * angularNormalizer * (-1 : ℂ) ^ N *
    (angularPower a q Real.pi - angularPower a q (-Real.pi)) / (N : ℂ)

theorem angularBase_re (a theta : ℝ) : (angularBase a theta).re = a := by
  simp [angularBase, Complex.mul_re]

theorem angularBase_mem_slitPlane {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    angularBase a theta ∈ Complex.slitPlane := by
  exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa [angularBase_re] using ha))

theorem angularBase_ne_zero {a : ℝ} (ha : 0 < a) (theta : ℝ) :
    angularBase a theta ≠ 0 :=
  Complex.slitPlane_ne_zero (angularBase_mem_slitPlane ha theta)

theorem angularPower_hasDerivAt {a : ℝ} (ha : 0 < a) (q : ℂ) (theta : ℝ) :
    HasDerivAt (angularPower a q)
      (Complex.I * q * angularPower a (q + 1) theta) theta := by
  have hb : HasDerivAt (fun z : ℂ => (a : ℂ) - Complex.I * z)
      (-Complex.I) (theta : ℂ) := by
    simpa only [mul_one] using
      ((hasDerivAt_id (theta : ℂ)).const_mul Complex.I).const_sub (a : ℂ)
  have hp := hb.cpow_const (c := -q) (angularBase_mem_slitPlane ha theta)
  have he : -q - 1 = -(q + 1) := by ring
  rw [he] at hp
  simpa only [angularPower, angularBase, neg_mul, mul_neg, neg_neg,
    mul_comm, mul_left_comm, mul_assoc] using hp.comp_ofReal

theorem angularCharacter_hasDerivAt (N : ℕ) (theta : ℝ) :
    HasDerivAt (angularCharacter N)
      ((-(N : ℂ) * Complex.I) * angularCharacter N theta) theta := by
  have hb : HasDerivAt (fun z : ℂ => -(N : ℂ) * Complex.I * z)
      (-(N : ℂ) * Complex.I) (theta : ℂ) := by
    simpa only [mul_one] using
      (hasDerivAt_id (theta : ℂ)).const_mul (-(N : ℂ) * Complex.I)
  change HasDerivAt
    (fun t : ℝ => Complex.exp (-(N : ℂ) * Complex.I * (t : ℂ)))
    ((-(N : ℂ) * Complex.I) * Complex.exp (-(N : ℂ) * Complex.I * (theta : ℂ))) theta
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hb.cexp.comp_ofReal

theorem angularIntegrand_hasDerivAt {a : ℝ} (ha : 0 < a) (N : ℕ) (q : ℂ)
    (theta : ℝ) : HasDerivAt (angularIntegrand a N q)
      (angularDerivative a N q theta) theta := by
  change HasDerivAt (fun t => angularPower a q t * angularCharacter N t) _ theta
  convert (angularPower_hasDerivAt ha q theta).mul
    (angularCharacter_hasDerivAt N theta) using 1 <;>
    dsimp only [angularDerivative, angularIntegrand] <;> ring

theorem angularPower_continuous {a : ℝ} (ha : 0 < a) (q : ℂ) :
    Continuous (angularPower a q) :=
  continuous_iff_continuousAt.mpr fun theta =>
    (angularPower_hasDerivAt ha q theta).continuousAt

theorem angularCharacter_continuous (N : ℕ) : Continuous (angularCharacter N) :=
  continuous_iff_continuousAt.mpr fun theta =>
    (angularCharacter_hasDerivAt N theta).continuousAt

theorem angularIntegrand_continuous {a : ℝ} (ha : 0 < a) (N : ℕ) (q : ℂ) :
    Continuous (angularIntegrand a N q) :=
  (angularPower_continuous ha q).mul (angularCharacter_continuous N)

theorem angularDerivative_continuous {a : ℝ} (ha : 0 < a) (N : ℕ) (q : ℂ) :
    Continuous (angularDerivative a N q) :=
  (continuous_const.mul (angularIntegrand_continuous ha N (q + 1))).sub
    (continuous_const.mul (angularIntegrand_continuous ha N q))

theorem angularIntegrand_intervalIntegrable {a : ℝ} (ha : 0 < a) (N : ℕ) (q : ℂ) :
    IntervalIntegrable (angularIntegrand a N q) volume (-Real.pi) Real.pi :=
  (angularIntegrand_continuous ha N q).intervalIntegrable (-Real.pi) Real.pi

theorem angularDerivative_intervalIntegrable {a : ℝ} (ha : 0 < a) (N : ℕ) (q : ℂ) :
    IntervalIntegrable (angularDerivative a N q) volume (-Real.pi) Real.pi :=
  (angularDerivative_continuous ha N q).intervalIntegrable (-Real.pi) Real.pi

theorem angularCharacter_pi (N : ℕ) : angularCharacter N Real.pi = (-1 : ℂ) ^ N := by
  have he : -(N : ℂ) * Complex.I * (Real.pi : ℂ) =
      (N : ℂ) * (-((Real.pi : ℂ) * Complex.I)) := by ring
  rw [angularCharacter, he, Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem angularCharacter_neg_pi (N : ℕ) :
    angularCharacter N (-Real.pi) = (-1 : ℂ) ^ N := by
  have he : -(N : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ) =
      (N : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    rw [Complex.ofReal_neg]
    ring
  rw [angularCharacter, he, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

theorem angularIntegral_derivative_eq {a : ℝ} (ha : 0 < a) (N : ℕ) (q : ℂ) :
    (∫ theta in (-Real.pi)..Real.pi, angularDerivative a N q theta) =
      (-1 : ℂ) ^ N * (angularPower a q Real.pi - angularPower a q (-Real.pi)) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun theta _ => angularIntegrand_hasDerivAt ha N q theta)
    (angularDerivative_intervalIntegrable ha N q)
  rw [angularIntegrand, angularIntegrand, angularCharacter_pi, angularCharacter_neg_pi] at h
  calc
    _ = angularPower a q Real.pi * (-1 : ℂ) ^ N -
        angularPower a q (-Real.pi) * (-1 : ℂ) ^ N := h
    _ = _ := by ring

theorem angularJ_balance {a : ℝ} (ha : 0 < a) (N : ℕ) (q : ℂ) :
    Complex.I * q * angularJ a N (q + 1) -
      Complex.I * (N : ℂ) * angularJ a N q =
      angularNormalizer * (-1 : ℂ) ^ N *
        (angularPower a q Real.pi - angularPower a q (-Real.pi)) := by
  have hnext := (angularIntegrand_intervalIntegrable ha N (q + 1)).const_mul (Complex.I * q)
  have hthis := (angularIntegrand_intervalIntegrable ha N q).const_mul (Complex.I * (N : ℂ))
  have hlin : (∫ theta in (-Real.pi)..Real.pi, angularDerivative a N q theta) =
      Complex.I * q * (∫ theta in (-Real.pi)..Real.pi, angularIntegrand a N (q + 1) theta) -
      Complex.I * (N : ℂ) * (∫ theta in (-Real.pi)..Real.pi, angularIntegrand a N q theta) := by
    unfold angularDerivative
    rw [intervalIntegral.integral_sub hnext hthis,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have h := congrArg (fun z : ℂ => angularNormalizer * z)
    (angularIntegral_derivative_eq ha N q)
  rw [hlin] at h
  dsimp only [angularJ]
  calc
    _ = angularNormalizer *
        (Complex.I * q * (∫ theta in (-Real.pi)..Real.pi, angularIntegrand a N (q + 1) theta) -
        Complex.I * (N : ℂ) * (∫ theta in (-Real.pi)..Real.pi, angularIntegrand a N q theta)) := by ring
    _ = _ := by simpa only [mul_assoc] using h

theorem angularJ_recurrence {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 0 < N) (q : ℂ) :
    angularJ a N q = angularBorder a N q + (q / (N : ℂ)) * angularJ a N (q + 1) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have h := congrArg (fun z : ℂ => Complex.I * z) (angularJ_balance ha N q)
  change Complex.I * (Complex.I * q * angularJ a N (q + 1) -
      Complex.I * (N : ℂ) * angularJ a N q) =
    Complex.I * (angularNormalizer * (-1 : ℂ) ^ N *
      (angularPower a q Real.pi - angularPower a q (-Real.pi))) at h
  have he : Complex.I * (Complex.I * q * angularJ a N (q + 1) -
      Complex.I * (N : ℂ) * angularJ a N q) =
      (N : ℂ) * angularJ a N q - q * angularJ a N (q + 1) := by
    calc
      _ = (Complex.I * Complex.I) *
          (q * angularJ a N (q + 1) - (N : ℂ) * angularJ a N q) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [he] at h
  calc
    angularJ a N q =
        (Complex.I * (angularNormalizer * (-1 : ℂ) ^ N *
          (angularPower a q Real.pi - angularPower a q (-Real.pi))) +
          q * angularJ a N (q + 1)) / (N : ℂ) := by
      apply (eq_div_iff hN0).mpr
      rw [mul_comm (angularJ a N q)]
      exact (sub_eq_iff_eq_add).mp h
    _ = _ := by dsimp only [angularBorder]; simp only [div_eq_mul_inv]; ring

theorem angularBorder_explicit (a : ℝ) (N : ℕ) (q : ℂ) :
    angularBorder a N q = Complex.I * (-1 : ℂ) ^ N *
      (((a : ℂ) - Complex.I * (Real.pi : ℂ)) ^ (-q) -
        ((a : ℂ) + Complex.I * (Real.pi : ℂ)) ^ (-q)) /
          (2 * (Real.pi : ℂ) * (N : ℂ)) := by
  dsimp only [angularBorder, angularNormalizer, angularPower, angularBase]
  simp only [Complex.ofReal_neg, mul_neg, sub_neg_eq_add, div_eq_mul_inv, mul_inv_rev]
  ring

theorem angularBorder_zero (a : ℝ) (N : ℕ) : angularBorder a N (0 : ℂ) = 0 := by
  simp [angularBorder, angularPower]

theorem angularQuadratic_ne_zero (a : ℝ) :
    (a : ℂ) ^ 2 + (Real.pi : ℂ) ^ 2 ≠ 0 := by
  have hp : 0 < a ^ 2 + Real.pi ^ 2 := by positivity
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt hp)

theorem angularBorder_one {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 0 < N) :
    angularBorder a N (1 : ℂ) =
      -(-1 : ℂ) ^ N / ((N : ℂ) * ((a : ℂ) ^ 2 + (Real.pi : ℂ) ^ 2)) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hm := angularBase_ne_zero ha Real.pi
  have hp' := angularBase_ne_zero ha (-Real.pi)
  have hden := angularQuadratic_ne_zero a
  rw [angularBorder_explicit]
  simp only [Complex.cpow_neg_one]
  dsimp only [angularBase] at hm hp'
  simp only [Complex.ofReal_neg, mul_neg, sub_neg_eq_add] at hp'
  field_simp [hN0, hp, hm, hp', hden] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem angularBorder_one_ne_zero {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 0 < N) :
    angularBorder a N (1 : ℂ) ≠ 0 := by
  rw [angularBorder_one ha hN]
  exact div_ne_zero
    (neg_ne_zero.mpr (pow_ne_zero N (by norm_num : (-1 : ℂ) ≠ 0)))
    (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)) (angularQuadratic_ne_zero a))

end GoldbachAngularMellinBorder22

#print axioms GoldbachAngularMellinBorder22.angularBase
#print axioms GoldbachAngularMellinBorder22.angularPower
#print axioms GoldbachAngularMellinBorder22.angularCharacter
#print axioms GoldbachAngularMellinBorder22.angularIntegrand
#print axioms GoldbachAngularMellinBorder22.angularDerivative
#print axioms GoldbachAngularMellinBorder22.angularNormalizer
#print axioms GoldbachAngularMellinBorder22.angularJ
#print axioms GoldbachAngularMellinBorder22.angularBorder
#print axioms GoldbachAngularMellinBorder22.angularBase_re
#print axioms GoldbachAngularMellinBorder22.angularBase_mem_slitPlane
#print axioms GoldbachAngularMellinBorder22.angularBase_ne_zero
#print axioms GoldbachAngularMellinBorder22.angularPower_hasDerivAt
#print axioms GoldbachAngularMellinBorder22.angularCharacter_hasDerivAt
#print axioms GoldbachAngularMellinBorder22.angularIntegrand_hasDerivAt
#print axioms GoldbachAngularMellinBorder22.angularPower_continuous
#print axioms GoldbachAngularMellinBorder22.angularCharacter_continuous
#print axioms GoldbachAngularMellinBorder22.angularIntegrand_continuous
#print axioms GoldbachAngularMellinBorder22.angularDerivative_continuous
#print axioms GoldbachAngularMellinBorder22.angularIntegrand_intervalIntegrable
#print axioms GoldbachAngularMellinBorder22.angularDerivative_intervalIntegrable
#print axioms GoldbachAngularMellinBorder22.angularCharacter_pi
#print axioms GoldbachAngularMellinBorder22.angularCharacter_neg_pi
#print axioms GoldbachAngularMellinBorder22.angularIntegral_derivative_eq
#print axioms GoldbachAngularMellinBorder22.angularJ_balance
#print axioms GoldbachAngularMellinBorder22.angularJ_recurrence
#print axioms GoldbachAngularMellinBorder22.angularBorder_explicit
#print axioms GoldbachAngularMellinBorder22.angularBorder_zero
#print axioms GoldbachAngularMellinBorder22.angularQuadratic_ne_zero
#print axioms GoldbachAngularMellinBorder22.angularBorder_one
#print axioms GoldbachAngularMellinBorder22.angularBorder_one_ne_zero
