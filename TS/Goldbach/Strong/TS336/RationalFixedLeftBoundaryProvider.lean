import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic
import TS.Goldbach.Strong.TS307.FixedLeftArchimedeanLogarithmicRate
import TS.Goldbach.Strong.TS314.FiniteQuadraticSpectralMomentGoodScale
import TS.Goldbach.Strong.TS335.RationalExceptionalResidueProvider

/-!
# TS336: rational fixed-left boundary provider

This module supplies explicit rational caps for the two scalar masses isolated
by TS305 and transports the resulting fixed-left boundary estimate uniformly
over a dyadic window.  It contains no zero data, empirical payload, trace-budget
assembly, or half-budget claim.
-/

namespace TS336
namespace Goldbach

noncomputable section

open Complex Filter MeasureTheory Set

set_option maxHeartbeats 1000000

/-! ## Reflected von Mangoldt mass -/

private theorem integral_one_to_one_add_rpow_le_two
    (k : Nat) :
    (∫ x : Real in (1 : Real)..1 + k, x ^ (-(3 : Real) / 2)) <= 2 := by
  have hle : (1 : Real) <= 1 + k := by
    exact le_add_of_nonneg_right (Nat.cast_nonneg k)
  have hz : (0 : Real) ∉ Set.uIcc (1 : Real) (1 + k) := by
    rw [Set.uIcc_of_le hle]
    simp
  rw [integral_rpow (Or.inr ⟨by norm_num, hz⟩)]
  have hnonneg : 0 <= (1 + (k : Real)) ^ (-(1 : Real) / 2) :=
    Real.rpow_nonneg (by positivity) _
  norm_num
  nlinarith

private theorem sum_range_nat_add_one_rpow_le_three
    (N : Nat) :
    (∑ n ∈ Finset.range N,
      (((n + 1 : Nat) : Real) ^ (-(3 : Real) / 2))) <= 3 := by
  cases N with
  | zero => simp
  | succ k =>
      rw [Finset.sum_range_succ']
      have hAnti :
          AntitoneOn (fun x : Real => x ^ (-(3 : Real) / 2))
            (Set.Icc (1 : Real) (1 + k)) := by
        exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono
          (fun x hx => by
            have : (0 : Real) < x := lt_of_lt_of_le zero_lt_one hx.1
            exact this)
      have hTail := hAnti.sum_le_integral (x₀ := (1 : Real)) (a := k)
      have hTail' :
          (∑ x ∈ Finset.range k,
            (((x + 1 + 1 : Nat) : Real) ^ (-(3 : Real) / 2))) <=
            ∫ x : Real in (1 : Real)..1 + k, x ^ (-(3 : Real) / 2) := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
          add_left_comm] using hTail
      have hIntegral := integral_one_to_one_add_rpow_le_two k
      norm_num at hTail' ⊢
      nlinarith

private theorem tsum_nat_add_one_rpow_le_three :
    (∑' n : Nat,
      (((n + 1 : Nat) : Real) ^ (-(3 : Real) / 2))) <= 3 := by
  apply tsum_le_of_sum_le'
  · norm_num
  intro s
  let N := if h : s.Nonempty then s.max' h + 1 else 0
  have hsSubset : s ⊆ Finset.range N := by
    intro n hn
    by_cases h : s.Nonempty
    · simp only [N, dif_pos h, Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.le_max' s n hn)
    · exact (h ⟨n, hn⟩).elim
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsSubset
    (fun _ _ _ => Real.rpow_nonneg (by positivity) _)).trans
      (sum_range_nat_add_one_rpow_le_three N)

private theorem tsum_nat_rpow_le_three :
    (∑' n : Nat, ((n : Real) ^ (-(3 : Real) / 2))) <= 3 := by
  have hSummable : Summable (fun n : Nat => (n : Real) ^ (-(3 : Real) / 2)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  rw [tsum_eq_zero_add hSummable]
  norm_num
  simpa only [Nat.cast_add, Nat.cast_one,
    show (-(3 : Real) / 2) = -(3 / 2 : Real) by ring] using
      tsum_nat_add_one_rpow_le_three

theorem fixedLeftReflectedVonMangoldtMass_le_six :
    TS305.Goldbach.fixedLeftReflectedVonMangoldtMass <= 6 := by
  unfold TS305.Goldbach.fixedLeftReflectedVonMangoldtMass
  calc
    (∑' n : Nat,
        norm (LSeries.term TS298.Goldbach.vM
          ((5 / 2 : Real) : Complex) n)) <=
        ∑' n : Nat, 2 * ((n : Real) ^ (-(3 : Real) / 2)) := by
      apply tsum_le_tsum
      · intro n
        rcases n with _ | n
        · simp [LSeries.term]
        rw [LSeries.norm_term_eq]
        simp only [TS298.Goldbach.vM, norm_real, Real.norm_eq_abs,
          _root_.abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        simp only [Nat.succ_ne_zero, if_false]
        have hVM := ArithmeticFunction.vonMangoldt_le_log (n := n + 1)
        have hLog := Real.log_le_self
          (show 0 <= (((n + 1 : Nat) : Real)) by positivity)
        have hLinear :
            ArithmeticFunction.vonMangoldt (n + 1) <=
              2 * (((n + 1 : Nat) : Real)) := by
          nlinarith
        have hPowPos :
            0 < (((n + 1 : Nat) : Real) ^ (5 / 2 : Real)) :=
          Real.rpow_pos_of_pos (by positivity) _
        rw [show ((((5 / 2 : Real) : Complex)).re) = (5 / 2 : Real) by
          norm_num]
        rw [div_le_iff₀ hPowPos]
        have hRewrite :
            2 * (((n + 1 : Nat) : Real) ^ (-(3 : Real) / 2)) *
                (((n + 1 : Nat) : Real) ^ (5 / 2 : Real)) =
              2 * (((n + 1 : Nat) : Real)) := by
          calc
            _ = 2 *
                ((((n + 1 : Nat) : Real) ^ (-(3 : Real) / 2)) *
                  (((n + 1 : Nat) : Real) ^ (5 / 2 : Real))) := by ring
            _ = 2 * (((n + 1 : Nat) : Real) ^
                ((-(3 : Real) / 2) + 5 / 2)) := by
              rw [Real.rpow_add (Nat.cast_pos.mpr (Nat.succ_pos n))]
            _ = _ := by norm_num
        rw [hRewrite]
        exact hLinear
      · exact TS305.Goldbach.fixedLeftReflectedVonMangoldtMass_summable
      · exact
          (Real.summable_nat_rpow.mpr
            (by norm_num : (-(3 : Real) / 2) < -1)).mul_left 2
    _ = 2 * (∑' n : Nat, ((n : Real) ^ (-(3 : Real) / 2))) := by
      rw [tsum_mul_left]
    _ <= 6 := by
      nlinarith [tsum_nat_rpow_le_three]

/-! ## Logarithmic kernel mass -/

private theorem integral_japanese_three_quarters_le_six :
    (∫ t : Real, (1 + |t| ^ 2) ^ (-(3 : Real) / 4)) <= 6 := by
  let f : Real -> Real := fun t => (1 + t ^ 2) ^ (-(3 : Real) / 4)
  have hf : Integrable f := by
    have h := integrable_rpow_neg_one_add_norm_sq
      (E := Real) (μ := volume) (r := (3 / 2 : Real)) (by norm_num)
    simpa only [f, Real.norm_eq_abs, _root_.sq_abs,
      show (-(3 / 2 : Real) / 2) = (-(3 : Real) / 4) by ring] using h
  have hNear : IntegrableOn f (Ioc (0 : Real) 1) := hf.integrableOn
  have hFar : IntegrableOn f (Ioi (1 : Real)) := hf.integrableOn
  have hNearConst : IntegrableOn (fun _ : Real => (1 : Real)) (Ioc 0 1) :=
    integrableOn_const.2 (Or.inr measure_Ioc_lt_top)
  have hFarPower :
      IntegrableOn (fun t : Real => t ^ (-(3 : Real) / 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have hNearLe :
      (∫ t : Real in Ioc 0 1, f t) <= 1 := by
    calc
      (∫ t : Real in Ioc 0 1, f t) <=
          ∫ _t : Real in Ioc 0 1, (1 : Real) := by
        exact setIntegral_mono_on hNear hNearConst measurableSet_Ioc
          (fun t ht => by
            unfold f
            exact Real.rpow_le_one_of_one_le_of_nonpos
              (by nlinarith [sq_nonneg t]) (by norm_num))
      _ = 1 := by norm_num [MeasureTheory.setIntegral_const, Real.volume_Ioc]
  have hFarLe :
      (∫ t : Real in Ioi 1, f t) <= 2 := by
    calc
      (∫ t : Real in Ioi 1, f t) <=
          ∫ t : Real in Ioi 1, t ^ (-(3 : Real) / 2) := by
        exact setIntegral_mono_on hFar hFarPower measurableSet_Ioi
          (fun t ht => by
            have htPos : 0 < t := lt_trans zero_lt_one ht
            unfold f
            calc
              (1 + t ^ 2) ^ (-(3 : Real) / 4) <=
                  (t ^ 2) ^ (-(3 : Real) / 4) :=
                Real.rpow_le_rpow_of_exponent_nonpos
                  (sq_pos_of_pos htPos) (by linarith) (by norm_num)
              _ = t ^ (-(3 : Real) / 2) := by
                rw [<- Real.rpow_natCast, <- Real.rpow_mul htPos.le]
                norm_num)
      _ = 2 := by
        rw [integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
        norm_num
  have hHalf : (∫ t : Real in Ioi 0, f t) <= 3 := by
    calc
      (∫ t : Real in Ioi 0, f t) =
          (∫ t : Real in Ioc 0 1, f t) +
            ∫ t : Real in Ioi 1, f t := by
        rw [<- setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
          hNear hFar, Ioc_union_Ioi_eq_Ioi (by norm_num)]
      _ <= 3 := by linarith
  calc
    (∫ t : Real, (1 + |t| ^ 2) ^ (-(3 : Real) / 4)) =
        2 * ∫ t : Real in Ioi 0, f t := by
      simpa only [f] using (integral_comp_abs (f := f))
    _ <= 6 := by nlinarith

theorem fixedLeftLogKernelMass_le_forty :
    TS305.Goldbach.fixedLeftLogKernelMass <= 40 := by
  have hJapanese : Integrable
      (fun t : Real => (1 + |t| ^ 2) ^ (-(3 : Real) / 4)) := by
    have h := integrable_rpow_neg_one_add_norm_sq
      (E := Real) (μ := volume) (r := (3 / 2 : Real)) (by norm_num)
    simpa only [Real.norm_eq_abs,
      show (-(3 / 2 : Real) / 2) = (-(3 : Real) / 4) by ring] using h
  unfold TS305.Goldbach.fixedLeftLogKernelMass
  calc
    (∫ t : Real,
        TS305.Goldbach.fixedLeftLogWeight t / (1 + t ^ 2)) <=
        ∫ t : Real, 5 * (1 + |t| ^ 2) ^ (-(3 : Real) / 4) := by
      exact integral_mono TS305.Goldbach.fixedLeftLogKernel_integrable
        (hJapanese.const_mul 5)
        (fun t => TS305.Goldbach.fixedLeftLogWeight_div_one_add_sq_le_japanese t)
    _ = 5 * (∫ t : Real, (1 + |t| ^ 2) ^ (-(3 : Real) / 4)) := by
      rw [MeasureTheory.integral_mul_left]
    _ <= 40 := by
      nlinarith [integral_japanese_three_quarters_le_six]

/-! ## Rational assembly -/

theorem fixedLeftArchimedeanConstant_le_twelve :
    TS307.Goldbach.fixedLeftArchimedeanConstant <= 12 := by
  have hLogCast :
      Complex.log (2 * (Real.pi : Complex)) =
        (Real.log (2 * Real.pi) : Complex) := by
    calc
      Complex.log (2 * (Real.pi : Complex)) =
          Complex.log ((2 * Real.pi : Real) : Complex) := by
            congr 1
            norm_num
      _ = (Real.log (2 * Real.pi) : Complex) :=
        (Complex.ofReal_log (by positivity : 0 <= 2 * Real.pi)).symm
  unfold TS307.Goldbach.fixedLeftArchimedeanConstant
  rw [hLogCast, Complex.norm_real, Real.norm_eq_abs,
    _root_.abs_of_nonneg TS335.Goldbach.real_log_two_pi_nonnegative]
  nlinarith [TS335.Goldbach.real_log_two_pi_lt_three, Real.pi_le_four]

theorem fixedLeftLogDerivativeConstant_le_eighteen :
    TS307.Goldbach.fixedLeftLogDerivativeBoundData.constant <= 18 := by
  change
    TS307.Goldbach.fixedLeftArchimedeanConstant +
      TS305.Goldbach.fixedLeftReflectedVonMangoldtMass <= 18
  linarith [fixedLeftArchimedeanConstant_le_twelve,
    fixedLeftReflectedVonMangoldtMass_le_six]

theorem fixedLeftBoundaryLimit_norm_le_1440_mul_scale
    (x : Nat) :
    norm (TS305.Goldbach.fixedLeftBoundaryLimit x) <=
      1440 * TS305.Goldbach.fixedLeftScale x := by
  calc
    norm (TS305.Goldbach.fixedLeftBoundaryLimit x) <=
        TS305.Goldbach.fixedLeftUniformBound
          x TS307.Goldbach.fixedLeftLogDerivativeBoundData :=
      TS307.Goldbach.fixedLeftBoundaryLimit_norm_le x
    _ <= 1440 * TS305.Goldbach.fixedLeftScale x := by
      unfold TS305.Goldbach.fixedLeftUniformBound
      have hScale := TS305.Goldbach.fixedLeftScale_nonnegative x
      have hMass := TS305.Goldbach.fixedLeftLogKernelMass_nonnegative
      have hConstant :=
        TS307.Goldbach.fixedLeftLogDerivativeBoundData.constant_nonnegative
      calc
        2 * TS307.Goldbach.fixedLeftLogDerivativeBoundData.constant *
              TS305.Goldbach.fixedLeftScale x *
            TS305.Goldbach.fixedLeftLogKernelMass <=
            2 * 18 * TS305.Goldbach.fixedLeftScale x * 40 := by
          gcongr
          · exact fixedLeftLogDerivativeConstant_le_eighteen
          · exact fixedLeftLogKernelMass_le_forty
        _ = 1440 * TS305.Goldbach.fixedLeftScale x := by ring

theorem fixedLeftScale_le_inv
    (x : Nat)
    (hx : 1 <= x) :
    TS305.Goldbach.fixedLeftScale x <= 1 / (x : Real) := by
  unfold TS305.Goldbach.fixedLeftScale
  rw [one_div, <- Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx) (by norm_num)

theorem fixedLeftBoundaryLimit_norm_le_1440_mul_rpow
    (x : Nat) :
    norm (TS305.Goldbach.fixedLeftBoundaryLimit x) <=
      1440 * ((x : Real) ^ (-(3 : Real) / 2)) := by
  simpa [TS305.Goldbach.fixedLeftScale] using
    fixedLeftBoundaryLimit_norm_le_1440_mul_scale x

theorem fixedLeftBoundaryLimit_norm_le_1440_div
    (x : Nat)
    (hx : 1 <= x) :
    norm (TS305.Goldbach.fixedLeftBoundaryLimit x) <=
      1440 / (x : Real) := by
  calc
    norm (TS305.Goldbach.fixedLeftBoundaryLimit x) <=
        1440 * TS305.Goldbach.fixedLeftScale x :=
      fixedLeftBoundaryLimit_norm_le_1440_mul_scale x
    _ <= 1440 * (1 / (x : Real)) := by
      exact mul_le_mul_of_nonneg_left (fixedLeftScale_le_inv x hx) (by norm_num)
    _ = 1440 / (x : Real) := by ring

theorem fixedLeftBoundaryLimit_norm_le_1440_div_on_dyadicWindow
    (X x : Nat)
    (hX : 0 < X)
    (hxWindow : Membership.mem (TS314.Goldbach.dyadicWindow X) x) :
    norm (TS305.Goldbach.fixedLeftBoundaryLimit x) <=
      1440 / (X : Real) := by
  have hxOne := TS314.Goldbach.one_le_of_mem_dyadicWindow hX hxWindow
  have hxX : (X : Real) <= (x : Real) := by
    exact_mod_cast (TS314.Goldbach.mem_dyadicWindow_iff.mp hxWindow).1
  have hXReal : 0 < (X : Real) := by exact_mod_cast hX
  have hInv : (1 : Real) / (x : Real) <= 1 / (X : Real) :=
    one_div_le_one_div_of_le hXReal hxX
  calc
    norm (TS305.Goldbach.fixedLeftBoundaryLimit x) <=
        1440 / (x : Real) := fixedLeftBoundaryLimit_norm_le_1440_div x hxOne
    _ <= 1440 / (X : Real) := by
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hInv (by norm_num : (0 : Real) <= 1440)

/-- A reusable rational upper bound for the full fixed-left boundary. -/
structure RationalFixedLeftBoundaryBound (x : Nat) where
  majorant : Rat
  majorant_nonnegative : 0 <= majorant
  boundary_le :
    norm (TS305.Goldbach.fixedLeftBoundaryLimit x) <= (majorant : Real)

/-- The closed rational certificate `1440 / x`. -/
noncomputable def rationalFixedLeftBoundaryBound
    (x : Nat)
    (hx : 0 < x) :
    RationalFixedLeftBoundaryBound x where
  majorant := 1440 / (x : Rat)
  majorant_nonnegative := div_nonneg (by norm_num) (by positivity)
  boundary_le := by
    calc
      norm (TS305.Goldbach.fixedLeftBoundaryLimit x) <=
          1440 / (x : Real) :=
        fixedLeftBoundaryLimit_norm_le_1440_div x hx
      _ = ((1440 / (x : Rat) : Rat) : Real) := by simp

end

end Goldbach
end TS336
