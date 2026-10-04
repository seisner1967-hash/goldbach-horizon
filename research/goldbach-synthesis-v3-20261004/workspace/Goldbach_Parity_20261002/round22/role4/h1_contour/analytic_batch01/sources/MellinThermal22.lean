import GammaPrerequisites22
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.MellinInversion

/- SOURCE_ONLY: forward Mellin identity for the actual fixed thermal test.
   Convergence is constructed from Euler's Gamma integral, then transported
   by a positive real dilation. No inversion or contour identity is assumed.
   No execution, numerical validation, or H1 conclusion is claimed here. -/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace GoldbachContinuous22

def thermalUnitTest (x : ℝ) : ℂ :=
  (x : ℂ) * (Real.exp (-x) : ℂ)

def thermalTest (Y x : ℝ) : ℂ :=
  thermalUnitTest (Y⁻¹ * x)

def thermalDualTest (Y x : ℝ) : ℂ :=
  (x : ℂ) ^ (-1 : ℂ) * thermalTest Y x⁻¹

theorem thermalTest_eq_real (Y x : ℝ) :
    thermalTest Y x = ((x / Y) * Real.exp (-(x / Y)) : ℝ) := by
  unfold thermalTest thermalUnitTest
  rw [show Y⁻¹ * x = x / Y by rw [div_eq_mul_inv, mul_comm]]
  exact (Complex.ofReal_mul _ _).symm

theorem thermalTest_continuous (Y : ℝ) : Continuous (thermalTest Y) := by
  unfold thermalTest thermalUnitTest
  fun_prop

theorem thermalUnitTest_mellin_convergent {s : ℂ} (hs : -1 < s.re) :
    MellinConvergent thermalUnitTest s := by
  have hs1 : 0 < (s + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hbase : MellinConvergent (fun x : ℝ => (Real.exp (-x) : ℂ)) (s + 1) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm] using
      Complex.GammaIntegral_convergent hs1
  simpa only [thermalUnitTest, Complex.cpow_one, smul_eq_mul] using
    (MellinConvergent.cpow_smul (f := fun x : ℝ => (Real.exp (-x) : ℂ))
      (s := s) (a := (1 : ℂ))).mpr hbase

theorem mellin_thermalUnitTest {s : ℂ} (hs : -1 < s.re) :
    mellin thermalUnitTest s = Complex.Gamma (s + 1) := by
  have hs1 : 0 < (s + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  calc
    _ = mellin (fun x : ℝ => (Real.exp (-x) : ℂ)) (s + 1) := by
      simpa only [thermalUnitTest, Complex.cpow_one, smul_eq_mul] using
        mellin_cpow_smul (fun x : ℝ => (Real.exp (-x) : ℂ)) s (1 : ℂ)
    _ = Complex.GammaIntegral (s + 1) :=
      (congrFun Complex.GammaIntegral_eq_mellin (s + 1)).symm
    _ = Complex.Gamma (s + 1) := (Complex.Gamma_eq_integral hs1).symm

theorem thermalTest_mellin_convergent {Y : ℝ} {s : ℂ}
    (hY : 0 < Y) (hs : -1 < s.re) : MellinConvergent (thermalTest Y) s := by
  exact (MellinConvergent.comp_mul_left (f := thermalUnitTest) (s := s)
    (inv_pos.mpr hY)).mpr (thermalUnitTest_mellin_convergent hs)

theorem mellin_thermalTest {Y : ℝ} {s : ℂ} (hY : 0 < Y) (hs : -1 < s.re) :
    mellin (thermalTest Y) s = (Y : ℂ) ^ s * Complex.Gamma (s + 1) := by
  have harg : (Y : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hY.le]
    exact Real.pi_ne_zero.symm
  change mellin (fun x : ℝ => thermalUnitTest (Y⁻¹ * x)) s = _
  rw [mellin_comp_mul_left thermalUnitTest s (inv_pos.mpr hY),
    mellin_thermalUnitTest hs, smul_eq_mul, Complex.ofReal_inv,
    Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, neg_neg]

/-- Both the exact identity and its absolute convergence are paid. -/
theorem hasMellin_thermalTest {Y : ℝ} {s : ℂ} (hY : 0 < Y) (hs : -1 < s.re) :
    HasMellin (thermalTest Y) s ((Y : ℂ) ^ s * Complex.Gamma (s + 1)) :=
  ⟨thermalTest_mellin_convergent hY hs, mellin_thermalTest hY hs⟩

theorem thermalDualTest_mellin_convergent {Y : ℝ} {s : ℂ}
    (hY : 0 < Y) (hs : s.re < 2) : MellinConvergent (thermalDualTest Y) s := by
  have hs' : -1 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hexponent : (s + (-1 : ℂ)) / ((-1 : ℝ) : ℂ) = 1 - s := by
    push_cast
    ring
  have hcomp : MellinConvergent (fun x : ℝ => thermalTest Y x⁻¹) (s + (-1 : ℂ)) := by
    have hc := (MellinConvergent.comp_rpow (f := thermalTest Y)
      (s := s + (-1 : ℂ)) (a := (-1 : ℝ)) (by norm_num)).mpr
      (hexponent.symm ▸ thermalTest_mellin_convergent hY hs')
    simpa only [Real.rpow_neg_one] using hc
  exact (MellinConvergent.cpow_smul (f := fun x : ℝ => thermalTest Y x⁻¹)
    (s := s) (a := (-1 : ℂ))).mpr hcomp

theorem mellin_thermalDualTest {Y : ℝ} {s : ℂ} (hY : 0 < Y) (hs : s.re < 2) :
    mellin (thermalDualTest Y) s =
      (Y : ℂ) ^ (1 - s) * Complex.Gamma (2 - s) := by
  have hs' : -1 < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  calc
    _ = mellin (fun x : ℝ => thermalTest Y x⁻¹) (s + (-1 : ℂ)) := by
      simpa only [thermalDualTest, smul_eq_mul] using
        mellin_cpow_smul (fun x : ℝ => thermalTest Y x⁻¹) s (-1 : ℂ)
    _ = mellin (thermalTest Y) (1 - s) := by
      rw [mellin_comp_inv]
      congr 1
      ring
    _ = (Y : ℂ) ^ (1 - s) * Complex.Gamma (2 - s) := by
      rw [mellin_thermalTest hY hs']
      congr 2
      ring

end GoldbachContinuous22

#print axioms GoldbachContinuous22.thermalUnitTest
#print axioms GoldbachContinuous22.thermalTest
#print axioms GoldbachContinuous22.thermalDualTest
#print axioms GoldbachContinuous22.thermalTest_eq_real
#print axioms GoldbachContinuous22.thermalTest_continuous
#print axioms GoldbachContinuous22.thermalUnitTest_mellin_convergent
#print axioms GoldbachContinuous22.mellin_thermalUnitTest
#print axioms GoldbachContinuous22.thermalTest_mellin_convergent
#print axioms GoldbachContinuous22.mellin_thermalTest
#print axioms GoldbachContinuous22.hasMellin_thermalTest
#print axioms GoldbachContinuous22.thermalDualTest_mellin_convergent
#print axioms GoldbachContinuous22.mellin_thermalDualTest
