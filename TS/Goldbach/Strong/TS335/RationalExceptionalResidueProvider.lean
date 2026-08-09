import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic
import TS.Goldbach.Strong.TS306.ExceptionalResidueInventory
import TS.Goldbach.Strong.TS314.FiniteQuadraticSpectralMomentGoodScale
import TS.Goldbach.Strong.TS332.ShiftedInfiniteZeroTailProvider

namespace TS335
namespace Goldbach

noncomputable section

open Complex Filter

/-!
# TS335: rational exceptional-residue provider

This module supplies explicit rational caps for the two symbolic logarithmic
derivatives in the TS306 exceptional residue inventory.  It proves the value
at zero through a removable-singularity regularization of the completed zeta
function and controls the value at minus one by reflection to the absolutely
convergent von Mangoldt series at two.

No zero table, empirical payload, trace-budget assembly, or left-boundary
estimate is introduced here.
-/

local notation "gammaE" => Real.eulerMascheroniConstant
local notation "gammaC" => (Real.eulerMascheroniConstant : Complex)

/-! ## Reflection correction at minus one -/

theorem zetaLeftReflectionCorrection_two_eq :
    TS305.Goldbach.zetaLeftReflectionCorrection 2 =
      (((1 : Real) - gammaE - Real.log (2 * Real.pi) : Real) : Complex) := by
  let b : Complex := ((2 * Real.pi : Real) : Complex)
  have hb : Not (b = 0) := by
    dsimp [b]
    exact_mod_cast mul_ne_zero (by norm_num : Not ((2 : Real) = 0)) Real.pi_ne_zero
  have hPow :
      HasDerivAt (fun s : Complex => b ^ (-s))
        (b ^ (-(2 : Complex)) * Complex.log b * (-1)) 2 := by
    simpa using
      ((hasDerivAt_id (2 : Complex)).neg.const_cpow (c := b) (Or.inl hb))
  have hGamma :
      HasDerivAt Complex.Gamma
        (((1 : Nat).factorial : Complex) *
          ((-(gammaE : Real) + harmonic 1 : Real) : Complex)) 2 := by
    convert Complex.hasDerivAt_Gamma_nat 1 using 1 <;> norm_num
  have hInner :
      HasDerivAt (fun s : Complex => (Real.pi : Complex) * s / 2)
        ((Real.pi : Complex) / 2) 2 := by
    convert ((hasDerivAt_id (2 : Complex)).const_mul
      (Real.pi : Complex)).div_const 2 using 1 <;> ring
  have hCos :
      HasDerivAt
        (fun s : Complex => Complex.cos ((Real.pi : Complex) * s / 2))
        (-Complex.sin ((Real.pi : Complex) * 2 / 2) *
          ((Real.pi : Complex) / 2)) 2 := by
    exact (Complex.hasDerivAt_cos _).comp 2 hInner
  have hFactor :
      HasDerivAt TS305.Goldbach.zetaLeftReflectionFactor
        (((0 * b ^ (-(2 : Complex)) +
            2 * (b ^ (-(2 : Complex)) * Complex.log b * (-1))) *
              Complex.Gamma 2 +
            (2 * b ^ (-(2 : Complex))) *
              (((1 : Nat).factorial : Complex) *
                ((-(gammaE : Real) + harmonic 1 : Real) : Complex))) *
              Complex.cos ((Real.pi : Complex) * 2 / 2) +
          ((2 * b ^ (-(2 : Complex))) * Complex.Gamma 2) *
            (-Complex.sin ((Real.pi : Complex) * 2 / 2) *
              ((Real.pi : Complex) / 2))) 2 := by
    simpa [TS305.Goldbach.zetaLeftReflectionFactor, b] using
      ((((hasDerivAt_const (x := (2 : Complex)) (c := (2 : Complex))).mul
        hPow).mul hGamma).mul hCos)
  have hFactorNe :
      Not (TS305.Goldbach.zetaLeftReflectionFactor 2 = 0) := by
    have hFE := TS305.Goldbach.riemannZeta_one_sub_eq_reflectionFactor_mul
      (s := (2 : Complex)) (by norm_num)
    intro hZero
    apply TS306.Goldbach.riemannZeta_neg_one_ne_zero
    convert hFE.trans (by rw [hZero, zero_mul]) using 1 <;> norm_num
  unfold TS305.Goldbach.zetaLeftReflectionCorrection logDeriv
  change
    deriv TS305.Goldbach.zetaLeftReflectionFactor 2 /
      TS305.Goldbach.zetaLeftReflectionFactor 2 = _
  rw [div_eq_iff hFactorNe, hFactor.deriv]
  simp [TS305.Goldbach.zetaLeftReflectionFactor, b,
    Complex.ofReal_log (by positivity : 0 <= 2 * Real.pi),
    Complex.Gamma_nat_eq_factorial]
  ring

theorem neg_riemannZeta_logDerivative_neg_one_eq_reflection_two :
    -deriv riemannZeta (-1) / riemannZeta (-1) =
      TS305.Goldbach.zetaLeftReflectionCorrection 2 -
        LSeries TS298.Goldbach.vM 2 := by
  let u : Complex := 2
  have hu : 1 < u.re := by
    norm_num [u]
  have huLeft : 1 - u = (-1 : Complex) := by
    norm_num [u]
  have hFactor :
      Not (TS305.Goldbach.zetaLeftReflectionFactor u = 0) := by
    have hFE := TS305.Goldbach.riemannZeta_one_sub_eq_reflectionFactor_mul
      (s := u) hu
    intro hFactor
    apply TS306.Goldbach.riemannZeta_neg_one_ne_zero
    rw [← huLeft, hFE, hFactor, zero_mul]
  have hRight : Not (riemannZeta u = 0) :=
    riemannZeta_ne_zero_of_one_lt_re hu
  have hFactorDiff :
      DifferentiableAt Complex TS305.Goldbach.zetaLeftReflectionFactor u :=
    TS305.Goldbach.zetaLeftReflectionFactor_differentiableAt hu
  have hRightDiff : DifferentiableAt Complex riemannZeta u := by
    exact differentiableAt_riemannZeta (by norm_num [u])
  have hLeftDiff : DifferentiableAt Complex riemannZeta (1 - u) := by
    exact differentiableAt_riemannZeta (by norm_num [u])
  have hOneSubDiff :
      DifferentiableAt Complex (fun z : Complex => 1 - z) u :=
    (differentiableAt_const (1 : Complex)).sub differentiableAt_id
  have hEventually :
      Filter.EventuallyEq (nhds u)
        (fun z : Complex => riemannZeta (1 - z))
        (fun z => TS305.Goldbach.zetaLeftReflectionFactor z * riemannZeta z) := by
    filter_upwards [
      (isOpen_lt continuous_const continuous_re).mem_nhds hu] with z hz
    exact TS305.Goldbach.riemannZeta_one_sub_eq_reflectionFactor_mul hz
  have hDeriv := Filter.EventuallyEq.deriv_eq hEventually
  have hPoint := hEventually.eq_of_nhds
  have hProduct := logDeriv_mul u hFactor hRight hFactorDiff hRightDiff
  have hLogReflection :
      logDeriv (fun z : Complex => riemannZeta (1 - z)) u =
        TS305.Goldbach.zetaLeftReflectionCorrection u +
          logDeriv riemannZeta u := by
    unfold TS305.Goldbach.zetaLeftReflectionCorrection logDeriv
    change
      deriv (fun z : Complex => riemannZeta (1 - z)) u /
          riemannZeta (1 - u) =
        deriv TS305.Goldbach.zetaLeftReflectionFactor u /
            TS305.Goldbach.zetaLeftReflectionFactor u +
          deriv riemannZeta u / riemannZeta u
    rw [hDeriv, hPoint]
    exact hProduct
  have hComp := logDeriv_comp hLeftDiff hOneSubDiff
  have hComp' :
      logDeriv (fun z : Complex => riemannZeta (1 - z)) u =
        -logDeriv riemannZeta (1 - u) := by
    rw [deriv_const_sub, deriv_id''] at hComp
    simpa [Function.comp_def] using hComp
  have hDirichlet :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hu
  have hDirichlet' :
      LSeries TS298.Goldbach.vM u = -logDeriv riemannZeta u := by
    change
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) u =
        -logDeriv riemannZeta u
    simpa [logDeriv, neg_div] using hDirichlet
  have hFinal :
      -deriv riemannZeta (1 - u) / riemannZeta (1 - u) =
        TS305.Goldbach.zetaLeftReflectionCorrection u -
          LSeries TS298.Goldbach.vM u := by
    rw [neg_div]
    change
      -logDeriv riemannZeta (1 - u) =
        TS305.Goldbach.zetaLeftReflectionCorrection u -
          LSeries TS298.Goldbach.vM u
    rw [← hComp', hLogReflection, hDirichlet']
    ring
  convert hFinal using 1 <;> norm_num [u]

/-! ## A rational bound for the reflected von Mangoldt series -/

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

theorem norm_LSeries_vonMangoldt_two_le_six :
    norm (LSeries TS298.Goldbach.vM (2 : Complex)) <= 6 := by
  have hSummable :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := (2 : Complex)) (by norm_num)
  calc
    norm (LSeries TS298.Goldbach.vM (2 : Complex)) <=
        ∑' n : Nat, norm (LSeries.term TS298.Goldbach.vM (2 : Complex) n) :=
      norm_tsum_le_tsum_norm hSummable.norm
    _ <= ∑' n : Nat, 2 * ((n : Real) ^ (-(3 : Real) / 2)) := by
      apply tsum_le_tsum
      · intro n
        rcases n with _ | n
        · simp [LSeries.term]
        rw [LSeries.norm_term_eq]
        simp only [TS298.Goldbach.vM, norm_real, Real.norm_eq_abs,
          _root_.abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        simp only [Nat.succ_ne_zero, if_false]
        have hLog := Real.log_natCast_le_rpow_div (n + 1)
          (by norm_num : (0 : Real) < 1 / 2)
        have hVM := ArithmeticFunction.vonMangoldt_le_log (n := n + 1)
        have hLog' :
            Real.log ((n + 1 : Nat) : Real) <=
              2 * (((n + 1 : Nat) : Real) ^ (1 / 2 : Real)) := by
          norm_num [div_eq_mul_inv] at hLog
          convert hLog using 1 <;> norm_num [Nat.cast_add] <;> ring
        have hPowPos : 0 < ((n + 1 : Nat) : Real) ^ (2 : Real) :=
          Real.rpow_pos_of_pos (by positivity) _
        rw [show ((2 : Complex).re) = (2 : Real) by norm_num]
        rw [div_le_iff₀ hPowPos]
        have hRewrite :
            2 * (((n + 1 : Nat) : Real) ^ (-(3 : Real) / 2)) *
                (((n + 1 : Nat) : Real) ^ (2 : Real)) =
              2 * (((n + 1 : Nat) : Real) ^ (1 / 2 : Real)) := by
          calc
            _ = 2 *
                ((((n + 1 : Nat) : Real) ^ (-(3 : Real) / 2)) *
                  (((n + 1 : Nat) : Real) ^ (2 : Real))) := by ring
            _ = 2 * (((n + 1 : Nat) : Real) ^
                ((-(3 : Real) / 2) + 2)) := by
              rw [Real.rpow_add (Nat.cast_pos.mpr (Nat.succ_pos n))]
            _ = _ := by congr 2 <;> ring
        rw [hRewrite]
        exact hVM.trans hLog'
      · exact hSummable.norm
      · exact
          (Real.summable_nat_rpow.mpr
            (by norm_num : (-(3 : Real) / 2) < -1)).mul_left 2
    _ = 2 * (∑' n : Nat, ((n : Real) ^ (-(3 : Real) / 2))) := by
      rw [tsum_mul_left]
    _ <= 6 := by
      nlinarith [tsum_nat_rpow_le_three]

/-! ## Closed cap at minus one -/

theorem real_log_two_pi_nonnegative :
    0 <= Real.log (2 * Real.pi) := by
  apply Real.log_nonneg
  nlinarith [Real.pi_gt_three]

theorem real_log_two_pi_lt_three :
    Real.log (2 * Real.pi) < 3 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  exact lt_trans (by nlinarith [Real.pi_lt_four])
    TS332.Goldbach.twenty_lt_exp_three

theorem norm_zetaLeftReflectionCorrection_two_le_three :
    norm (TS305.Goldbach.zetaLeftReflectionCorrection 2) <= 3 := by
  rw [zetaLeftReflectionCorrection_two_eq]
  rw [Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · nlinarith [Real.eulerMascheroniConstant_lt_two_thirds,
      real_log_two_pi_lt_three]
  · nlinarith [Real.one_half_lt_eulerMascheroniConstant,
      real_log_two_pi_nonnegative]

theorem exceptionalNegOneQuotient_norm_le_nine :
    norm (deriv riemannZeta (-1) / riemannZeta (-1)) <= (9 : Real) := by
  rw [← norm_neg]
  rw [← neg_div]
  rw [neg_riemannZeta_logDerivative_neg_one_eq_reflection_two]
  exact (norm_sub_le _ _).trans (by
    nlinarith [norm_zetaLeftReflectionCorrection_two_le_three,
      norm_LSeries_vonMangoldt_two_le_six])

/-! ## Removable singularity and the exact derivative at zero -/

lemma GammaR_two : Gammaℝ (2 : Complex) = 1 / (Real.pi : Complex) := by
  rw [Gammaℝ_def]
  norm_num [Complex.Gamma_one, cpow_neg_one]

lemma hasDerivAt_GammaR_two :
    HasDerivAt Gammaℝ
      (-(gammaC + Complex.log (Real.pi : Complex)) /
        (2 * (Real.pi : Complex))) 2 := by
  let f : Complex -> Complex := fun s => (Real.pi : Complex) ^ (-s / 2)
  let g : Complex -> Complex := fun s => Complex.Gamma (s / 2)
  have hf : HasDerivAt f
      (-Complex.log (Real.pi : Complex) /
        (2 * (Real.pi : Complex))) 2 := by
    have h := ((hasDerivAt_neg (2 : Complex)).div_const 2).const_cpow
      (c := (Real.pi : Complex)) (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
    refine h.congr_deriv ?_
    dsimp [f]
    norm_num [cpow_neg_one]
    field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring_nf <;> simp
  have hg : HasDerivAt g (-gammaC / 2) 2 := by
    have hGamma : HasDerivAt Complex.Gamma (-gammaC) ((2 : Complex) / 2) := by
      simpa using Complex.hasDerivAt_Gamma_one
    have hInner : HasDerivAt (fun s : Complex => s / 2) (1 / 2) 2 :=
      (hasDerivAt_id (2 : Complex)).div_const 2
    have h := hGamma.comp (h := fun s : Complex => s / 2) 2 hInner
    have h' : HasDerivAt (Complex.Gamma ∘ fun s : Complex => s / 2)
        (-gammaC / 2) 2 := h.congr_deriv (by ring)
    simpa only [g, Function.comp_apply] using h'
  refine (hf.mul hg).congr_deriv ?_
  dsimp [f, g]
  norm_num [Complex.Gamma_one, cpow_neg_one]
  field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

lemma hasDerivAt_invGammaR_two :
    HasDerivAt (fun s : Complex => (Gammaℝ s)⁻¹)
      ((Real.pi : Complex) *
        (gammaC + Complex.log (Real.pi : Complex)) / 2) 2 := by
  have h := hasDerivAt_GammaR_two.inv (GammaR_two.trans_ne (by
    exact one_div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)))
  refine h.congr_deriv ?_
  rw [GammaR_two]
  field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

noncomputable def shiftedGammaInvFactor (s : Complex) : Complex :=
  (2 * (Real.pi : Complex))⁻¹ * (Gammaℝ (s + 2))⁻¹

noncomputable def regularizedZetaNumerator (s : Complex) : Complex :=
  s * completedRiemannZeta₀ s - 1 / (1 - s)

noncomputable def regularizedZetaAtZero (s : Complex) : Complex :=
  regularizedZetaNumerator s * shiftedGammaInvFactor s

lemma completedRiemannZeta0_zero :
    completedRiemannZeta₀ 0 =
      (gammaC - Complex.log (4 * (Real.pi : Complex))) / 2 + 1 := by
  calc
    completedRiemannZeta₀ 0 = completedRiemannZeta₀ 1 := by
      simpa using (completedRiemannZeta₀_one_sub 0).symm
    _ = (gammaC - Complex.log (4 * (Real.pi : Complex))) / 2 + 1 :=
      completedRiemannZeta₀_one

lemma shiftedGammaInvFactor_zero : shiftedGammaInvFactor 0 = 1 / 2 := by
  rw [shiftedGammaInvFactor, zero_add, GammaR_two]
  field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

lemma hasDerivAt_shiftedGammaInvFactor_zero :
    HasDerivAt shiftedGammaInvFactor
      ((gammaC + Complex.log (Real.pi : Complex)) / 4) 0 := by
  have hInner : HasDerivAt (fun s : Complex => s + 2) 1 0 := by
    simpa using (hasDerivAt_id (0 : Complex)).add_const 2
  have hOuter : HasDerivAt (fun s : Complex => (Gammaℝ s)⁻¹)
      ((Real.pi : Complex) *
        (gammaC + Complex.log (Real.pi : Complex)) / 2) ((0 : Complex) + 2) := by
    simpa using hasDerivAt_invGammaR_two
  have hComp := hOuter.comp (h := fun s : Complex => s + 2) 0 hInner
  have hMul := hComp.const_mul (2 * (Real.pi : Complex))⁻¹
  refine hMul.congr_deriv ?_
  field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring

lemma regularizedZetaNumerator_zero : regularizedZetaNumerator 0 = -1 := by
  simp [regularizedZetaNumerator]

lemma hasDerivAt_regularizedZetaNumerator_zero :
    HasDerivAt regularizedZetaNumerator
      ((gammaC - Complex.log (4 * (Real.pi : Complex))) / 2) 0 := by
  have hCompleted : HasDerivAt completedRiemannZeta₀
      (deriv completedRiemannZeta₀ 0) 0 :=
    differentiable_completedZeta₀.differentiableAt.hasDerivAt
  have hProd := (hasDerivAt_id (0 : Complex)).mul hCompleted
  have hOneSub : HasDerivAt (fun s : Complex => 1 - s) (-1) 0 := by
    simpa using (hasDerivAt_const (0 : Complex) 1).sub (hasDerivAt_id 0)
  have hInv := hOneSub.inv (by norm_num : (1 - (0 : Complex)) ≠ 0)
  have hNumerator := hProd.sub hInv
  have hNumerator' : HasDerivAt
      (fun s : Complex => s * completedRiemannZeta₀ s - (1 - s)⁻¹)
      ((gammaC - Complex.log (4 * (Real.pi : Complex))) / 2) 0 := by
    refine hNumerator.congr_deriv ?_
    rw [completedRiemannZeta0_zero]
    norm_num
  change HasDerivAt
    (fun s : Complex => s * completedRiemannZeta₀ s - 1 / (1 - s)) _ _
  simpa only [one_div] using hNumerator'

lemma hasDerivAt_regularizedZetaAtZero_zero :
    HasDerivAt regularizedZetaAtZero
      (((gammaC - Complex.log (4 * (Real.pi : Complex))) / 2) * (1 / 2) -
        (gammaC + Complex.log (Real.pi : Complex)) / 4) 0 := by
  have h := hasDerivAt_regularizedZetaNumerator_zero.mul
    hasDerivAt_shiftedGammaInvFactor_zero
  refine h.congr_deriv ?_
  rw [regularizedZetaNumerator_zero, shiftedGammaInvFactor_zero]
  ring

lemma invGammaR_eq_mul_shiftedGammaInvFactor
    {s : Complex} (hs : s ≠ 0) :
    (Gammaℝ s)⁻¹ = s * shiftedGammaInvFactor s := by
  rw [shiftedGammaInvFactor, Gammaℝ_add_two hs]
  field_simp [hs, ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, one_mul,
    mul_comm (Gammaℝ s)⁻¹ s⁻¹, ← mul_assoc,
    mul_inv_cancel₀ hs, one_mul]

lemma riemannZeta_eq_regularizedZetaAtZero
    {s : Complex} (hs : s ≠ 0) (hsOne : s ≠ 1) :
    riemannZeta s = regularizedZetaAtZero s := by
  rw [riemannZeta_def_of_ne_zero hs, div_eq_mul_inv,
    invGammaR_eq_mul_shiftedGammaInvFactor hs,
    completedRiemannZeta_eq]
  unfold regularizedZetaAtZero regularizedZetaNumerator
  have hOneSub : (1 : Complex) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hsOne)
  field_simp [hs, hOneSub]
  ring

lemma regularizedZetaAtZero_zero : regularizedZetaAtZero 0 = -1 / 2 := by
  rw [regularizedZetaAtZero, regularizedZetaNumerator_zero,
    shiftedGammaInvFactor_zero]
  ring

lemma riemannZeta_eventuallyEq_regularizedZetaAtZero :
    riemannZeta =ᶠ[nhds (0 : Complex)] regularizedZetaAtZero := by
  have hZeroOne : (0 : Complex) ≠ 1 := by norm_num
  filter_upwards [isOpen_compl_singleton.mem_nhds hZeroOne] with s hsOne
  rcases eq_or_ne s 0 with rfl | hs
  · rw [riemannZeta_zero, regularizedZetaAtZero_zero]
  · exact riemannZeta_eq_regularizedZetaAtZero hs hsOne

lemma real_log_four_pi_add_log_pi :
    Real.log (4 * Real.pi) + Real.log Real.pi =
      2 * Real.log (2 * Real.pi) := by
  have hTwo : (2 : Real) ≠ 0 := by norm_num
  have hPi : Real.pi ≠ 0 := Real.pi_ne_zero
  calc
    Real.log (4 * Real.pi) + Real.log Real.pi =
        Real.log (2 * (2 * Real.pi)) + Real.log Real.pi := by
          congr 2
          ring
    _ = (Real.log 2 + Real.log (2 * Real.pi)) + Real.log Real.pi := by
          rw [Real.log_mul hTwo (mul_ne_zero hTwo hPi)]
    _ = 2 * Real.log (2 * Real.pi) := by
          rw [Real.log_mul hTwo hPi]
          ring

lemma complex_log_four_pi_add_log_pi :
    Complex.log (4 * (Real.pi : Complex)) +
        Complex.log (Real.pi : Complex) =
      2 * Complex.log (2 * (Real.pi : Complex)) := by
  have h := congrArg (fun x : Real => (x : Complex))
    real_log_four_pi_add_log_pi
  norm_num only [Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ofNat] at h
  rw [Complex.ofReal_log (by positivity : 0 <= 4 * Real.pi),
    Complex.ofReal_log Real.pi_pos.le,
    Complex.ofReal_log (by positivity : 0 <= 2 * Real.pi)] at h
  simpa [mul_comm] using h

lemma hasDerivAt_riemannZeta_zero_exact :
    HasDerivAt riemannZeta
      (-Complex.log (2 * (Real.pi : Complex)) / 2) 0 := by
  have hRegularized : HasDerivAt regularizedZetaAtZero
      (-Complex.log (2 * (Real.pi : Complex)) / 2) 0 := by
    refine hasDerivAt_regularizedZetaAtZero_zero.congr_deriv ?_
    have hLog := complex_log_four_pi_add_log_pi
    calc
      ((gammaC - Complex.log (4 * (Real.pi : Complex))) / 2) * (1 / 2) -
          (gammaC + Complex.log (Real.pi : Complex)) / 4 =
          -(Complex.log (4 * (Real.pi : Complex)) +
            Complex.log (Real.pi : Complex)) / 4 := by ring
      _ = -(2 * Complex.log (2 * (Real.pi : Complex))) / 4 := by rw [hLog]
      _ = -Complex.log (2 * (Real.pi : Complex)) / 2 := by ring
  exact hRegularized.congr_of_eventuallyEq
    riemannZeta_eventuallyEq_regularizedZetaAtZero

lemma deriv_riemannZeta_zero_exact :
    deriv riemannZeta 0 =
      -Complex.log (2 * (Real.pi : Complex)) / 2 :=
  hasDerivAt_riemannZeta_zero_exact.deriv

lemma neg_zeta_logDerivative_zero_exact :
    -deriv riemannZeta 0 / riemannZeta 0 =
      -Complex.log (2 * (Real.pi : Complex)) := by
  rw [deriv_riemannZeta_zero_exact, riemannZeta_zero]
  ring

theorem exceptionalZeroQuotient_norm_le_three :
    norm (-deriv riemannZeta 0 / riemannZeta 0) <= (3 : Real) := by
  rw [neg_zeta_logDerivative_zero_exact, norm_neg]
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
  rw [hLogCast,
    Complex.norm_real, Real.norm_eq_abs,
    _root_.abs_of_nonneg real_log_two_pi_nonnegative]
  exact real_log_two_pi_lt_three.le

/-! ## Abstract and concrete rational providers -/

theorem concreteExceptionalResidueBound_le_of_caps
    (x : Nat)
    (hx : 0 < x)
    {C0 C1 : Real}
    (h0 : norm (-deriv riemannZeta 0 / riemannZeta 0) <= C0)
    (h1 : norm (deriv riemannZeta (-1) / riemannZeta (-1)) <= C1) :
    TS306.Goldbach.concreteExceptionalResidueBound x <=
      C0 + C1 / (x : Real) := by
  have hxReal : 0 < (x : Real) := by exact_mod_cast hx
  have hScale : norm (1 / (x : Complex)) = 1 / (x : Real) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  unfold TS306.Goldbach.concreteExceptionalResidueBound
  rw [norm_mul, hScale]
  have hScaled :=
    mul_le_mul_of_nonneg_left h1 (one_div_nonneg.mpr (le_of_lt hxReal))
  have hScaled' :
      1 / (x : Real) *
          norm (deriv riemannZeta (-1) / riemannZeta (-1)) <=
        C1 / (x : Real) := by
    simpa [div_eq_mul_inv, mul_comm] using hScaled
  exact add_le_add h0 hScaled'

theorem concreteExceptionalResidueBound_le_on_dyadicWindow_of_caps
    (X x : Nat)
    (hX : 0 < X)
    (hxWindow : Membership.mem (TS314.Goldbach.dyadicWindow X) x)
    {C0 C1 : Real}
    (h0 : norm (-deriv riemannZeta 0 / riemannZeta 0) <= C0)
    (h1 : norm (deriv riemannZeta (-1) / riemannZeta (-1)) <= C1)
    (hC1 : 0 <= C1) :
    TS306.Goldbach.concreteExceptionalResidueBound x <=
      C0 + C1 / (X : Real) := by
  have hx : 0 < x :=
    lt_of_lt_of_le hX (TS314.Goldbach.mem_dyadicWindow_iff.mp hxWindow).1
  have hxX : (X : Real) <= (x : Real) := by
    exact_mod_cast (TS314.Goldbach.mem_dyadicWindow_iff.mp hxWindow).1
  have hXReal : 0 < (X : Real) := by exact_mod_cast hX
  have hInv : (1 : Real) / (x : Real) <= 1 / (X : Real) := by
    exact one_div_le_one_div_of_le hXReal hxX
  have hDiv : C1 / (x : Real) <= C1 / (X : Real) := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hInv hC1
  exact (concreteExceptionalResidueBound_le_of_caps x hx h0 h1).trans
    (add_le_add_left hDiv C0)

/-- A reusable rational upper bound for the TS306 exceptional contribution. -/
structure RationalExceptionalResidueBound (x : Nat) where
  majorant : Rat
  majorant_nonnegative : 0 <= majorant
  residue_le :
    TS306.Goldbach.concreteExceptionalResidueBound x <= (majorant : Real)

/-- Construct a rational exceptional-residue certificate from rational caps
on the two logarithmic derivatives. -/
noncomputable def RationalExceptionalResidueBound.ofCaps
    (x : Nat)
    (hx : 0 < x)
    (C0 C1 : Rat)
    (hC0 : 0 <= C0)
    (hC1 : 0 <= C1)
    (h0 : norm (-deriv riemannZeta 0 / riemannZeta 0) <= (C0 : Real))
    (h1 : norm (deriv riemannZeta (-1) / riemannZeta (-1)) <= (C1 : Real)) :
    RationalExceptionalResidueBound x where
  majorant := C0 + C1 / (x : Rat)
  majorant_nonnegative :=
    add_nonneg hC0 (div_nonneg hC1 (by positivity))
  residue_le := by
    calc
      TS306.Goldbach.concreteExceptionalResidueBound x <=
          (C0 : Real) + (C1 : Real) / (x : Real) :=
        concreteExceptionalResidueBound_le_of_caps x hx h0 h1
      _ = ((C0 + C1 / (x : Rat) : Rat) : Real) := by norm_cast

theorem concreteExceptionalResidueBound_le_three_add_nine_div
    (x : Nat)
    (hx : 0 < x) :
    TS306.Goldbach.concreteExceptionalResidueBound x <=
      (3 : Real) + 9 / (x : Real) :=
  concreteExceptionalResidueBound_le_of_caps x hx
    exceptionalZeroQuotient_norm_le_three
    exceptionalNegOneQuotient_norm_le_nine

theorem concreteExceptionalResidueBound_le_three_add_nine_div_on_dyadicWindow
    (X x : Nat)
    (hX : 0 < X)
    (hxWindow : Membership.mem (TS314.Goldbach.dyadicWindow X) x) :
    TS306.Goldbach.concreteExceptionalResidueBound x <=
      (3 : Real) + 9 / (X : Real) :=
  concreteExceptionalResidueBound_le_on_dyadicWindow_of_caps X x hX hxWindow
    exceptionalZeroQuotient_norm_le_three
    exceptionalNegOneQuotient_norm_le_nine (by norm_num)

/-- The closed rational certificate `3 + 9/x`. -/
noncomputable def rationalExceptionalResidueBound
    (x : Nat)
    (hx : 0 < x) :
    RationalExceptionalResidueBound x :=
  RationalExceptionalResidueBound.ofCaps x hx 3 9
    (by norm_num) (by norm_num)
    exceptionalZeroQuotient_norm_le_three
    exceptionalNegOneQuotient_norm_le_nine

end

end Goldbach
end TS335
