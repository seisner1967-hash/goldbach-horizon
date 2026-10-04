import PhysicalLogVariation21
import Mathlib.NumberTheory.AbelSummation

namespace GoldbachRound21.PhysicalAP

open scoped BigOperators
open Finset MeasureTheory
open GoldbachRound18.SeparatedTypeII
open GoldbachRound20.SwitchedComposite
open GoldbachRound20.Friable.SourceGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 12000000

def ordinaryWeightedAP (N t nu L U : ℕ) : ℝ :=
  ∑ q ∈ Icc L U, physicalLogWeight N t (q : ℝ) * ordinaryPrimeCoefficient N t nu q

def unmaskedAPMass (N t nu L U : ℕ) : ℝ :=
  ∑ q ∈ Icc L U,
    if q.Prime ∧ Nat.ModEq nu (t * q) N
    then Real.log ((N - t * q : ℕ) : ℝ) else 0

def retiredAPMass (N t nu L U : ℕ) : ℝ :=
  ∑ q ∈ Icc L U,
    if q.Prime ∧ q ∣ N ∧ Nat.ModEq nu (t * q) N
    then Real.log ((N - t * q : ℕ) : ℝ) else 0

theorem primeUnitAPMass_retirement (N t nu L U : ℕ) :
    primeUnitAPMass N t nu L U = unmaskedAPMass N t nu L U - retiredAPMass N t nu L U := by
  unfold primeUnitAPMass unmaskedAPMass retiredAPMass
  rw [sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro q hq
  by_cases hp : q.Prime
  · by_cases hd : q ∣ N
    · have hu : ¬ Nat.Coprime q N := (hp.coprime_iff_not_dvd).not.mpr (by simpa using hd)
      by_cases hc : Nat.ModEq nu (t * q) N <;> simp [hp, hd, hu, hc]
    · have hu : Nat.Coprime q N := hp.coprime_iff_not_dvd.mpr hd
      by_cases hc : Nat.ModEq nu (t * q) N <;> simp [hp, hd, hu, hc]
  · simp [hp]

theorem ordinaryWeightedAP_eq_unmasked {N t nu L U : ℕ}
    (hL : 2 ≤ L) (hU : 1 < (N : ℝ) - (t : ℝ) * U) :
    ordinaryWeightedAP N t nu L U = unmaskedAPMass N t nu L U := by
  unfold ordinaryWeightedAP unmaskedAPMass ordinaryPrimeCoefficient
  apply sum_congr rfl
  intro q hq
  have hql : L ≤ q := (mem_Icc.mp hq).1
  have hqu : q ≤ U := (mem_Icc.mp hq).2
  have hq1 : 1 < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hqU : (q : ℝ) ≤ U := by exact_mod_cast hqu
  have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg _
  have htqN : t * q ≤ N := by
    have hr : (t : ℝ) * q ≤ N := by nlinarith
    exact_mod_cast hr
  have hcast : ((N - t * q : ℕ) : ℝ) = (N : ℝ) - (t : ℝ) * q := by
    rw [Nat.cast_sub htqN, Nat.cast_mul]
  by_cases hc : q.Prime ∧ Nat.ModEq nu (t * q) N
  · rw [if_pos hc, if_pos hc, hcast]
    unfold physicalLogWeight
    exact div_mul_cancel₀ _ (Real.log_pos hq1).ne'
  · simp [hc]

theorem weightedAP_abel_identity {N t nu L U : ℕ}
    (hnu : 0 < nu) (hLU : L ≤ U) (hL : 2 < L)
    (hU : 1 < (N : ℝ) - (t : ℝ) * U) :
    ordinaryWeightedAP N t nu L U -
      (∫ y in ((L : ℝ) - 1)..(U : ℝ), physicalLogWeight N t y) / (Nat.totient nu : ℝ) =
        physicalLogWeight N t U * ordinaryAPError N t nu U -
          physicalLogWeight N t ((L : ℝ) - 1) * ordinaryAPError N t nu ((L : ℝ) - 1) -
            ∫ y in ((L : ℝ) - 1)..(U : ℝ),
              deriv (physicalLogWeight N t) y * ordinaryAPError N t nu y := by
  let A : ℝ := (L : ℝ) - 1
  let f := physicalLogWeight N t
  let phi : ℝ := Nat.totient nu
  have hA : 1 < A := by
    have hc : (2 : ℝ) < L := by exact_mod_cast hL
    dsimp [A]; linarith
  have hA0 : 0 ≤ A := (zero_lt_one.trans hA).le
  have hAU : A ≤ (U : ℝ) := by
    have hcast : (L : ℝ) ≤ U := by exact_mod_cast hLU
    dsimp [A]; linarith
  have hdiff : ∀ y ∈ Set.Icc A (U : ℝ), DifferentiableAt ℝ f y := by
    intro y hy
    obtain ⟨hy1, hj1⟩ := physicalLogWeight_range_guards hA hU hy
    exact (physicalLogWeight_hasDerivAt hy1 hj1).differentiableAt
  have hdint := physicalLogWeight_deriv_integrableOn hA hU
  have hab := sum_mul_eq_sub_sub_integral_mul (ordinaryPrimeCoefficient N t nu)
    hA0 hAU hdiff hdint
  have hAfloor : ⌊A⌋₊ = L - 1 := by
    have he : A = ((L - 1 : ℕ) : ℝ) := by
      dsimp [A]; rw [Nat.cast_sub (by omega)]; norm_num
    rw [he, Nat.floor_natCast]
  have hinterval : Ioc (L - 1) U = Icc L U := by
    ext q
    simp only [mem_Ioc, mem_Icc]
    omega
  rw [hAfloor, Nat.floor_natCast, hinterval] at hab
  have hAbel : ordinaryWeightedAP N t nu L U =
      f U * ordinaryPrimeTheta N t nu U - f A * ordinaryPrimeTheta N t nu (L - 1) -
        ∫ y in A..(U : ℝ), deriv f y * ordinaryPrimeTheta N t nu ⌊y⌋₊ := by
    simpa only [ordinaryWeightedAP, ordinaryPrimeTheta, f,
      intervalIntegral.integral_of_le hAU] using hab
  have hfc : ContinuousOn f (Set.uIcc A (U : ℝ)) := by
    rw [Set.uIcc_of_le hAU]
    exact physicalLogWeight_continuousOn hA hU
  have hlin : ContinuousOn (fun y : ℝ => y / phi) (Set.uIcc A (U : ℝ)) :=
    (continuous_id.div_const phi).continuousOn
  have hfd : IntervalIntegrable (deriv f) volume A (U : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAU).mpr hdint
  have hlind : IntervalIntegrable (fun _ : ℝ => 1 / phi) volume A (U : ℝ) :=
    intervalIntegrable_const
  have hmodel := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hfc hlin
    (fun y hy => (hdiff y (by
      simp only [min_eq_left hAU, max_eq_right hAU, Set.mem_Ioo] at hy
      exact ⟨hy.1.le, hy.2.le⟩)).hasDerivAt)
    (fun y _ => (hasDerivAt_id y).div_const phi) hfd hlind
  have hmodel' :
      (∫ y in A..(U : ℝ), f y) / phi = f U * ((U : ℝ) / phi) -
        f A * (A / phi) - ∫ y in A..(U : ℝ), deriv f y * (y / phi) := by
    simpa only [div_eq_mul_inv, one_mul, intervalIntegral.integral_mul_const] using hmodel
  have herrorIntegral :
      (∫ y in A..(U : ℝ), deriv f y * ordinaryPrimeTheta N t nu ⌊y⌋₊) -
        (∫ y in A..(U : ℝ), deriv f y * (y / phi)) =
          ∫ y in A..(U : ℝ), deriv f y * ordinaryAPError N t nu y := by
    have hlinint := hfd.mul_continuousOn hlin
    have hthetaint : IntervalIntegrable
        (fun y => deriv f y * ordinaryPrimeTheta N t nu ⌊y⌋₊) volume A (U : ℝ) := by
      have hi := error_mul_integrableOn hnu hA0 hdint
      have hie : IntervalIntegrable (fun y => deriv f y * ordinaryAPError N t nu y)
          volume A (U : ℝ) := by
        simpa [mul_comm] using (intervalIntegrable_iff_integrableOn_Icc_of_le hAU).mpr hi
      have hs := hie.add hlinint
      convert hs using 1
      ext y; unfold ordinaryAPError; dsimp [phi]; ring
    rw [← intervalIntegral.integral_sub hthetaint hlinint]
    apply intervalIntegral.integral_congr
    intro y _
    unfold ordinaryAPError
    dsimp [phi]
    ring
  change ordinaryWeightedAP N t nu L U - (∫ y in A..(U : ℝ), f y) / phi = _
  unfold ordinaryAPError
  rw [Nat.floor_natCast, hAfloor]
  rw [hAbel, hmodel']
  rw [← herrorIntegral]
  ring

theorem weightedAP_error_bound {N t nu L U : ℕ}
    (hnu : 0 < nu) (hLU : L ≤ U) (hL : 2 < L)
    (hU : 1 < (N : ℝ) - (t : ℝ) * U) :
    |ordinaryWeightedAP N t nu L U -
      (∫ y in ((L : ℝ) - 1)..(U : ℝ), physicalLogWeight N t y) / (Nat.totient nu : ℝ)| ≤
        2 * physicalLogWeight N t ((L : ℝ) - 1) * physicalAPEnvelope N t nu U := by
  let A : ℝ := (L : ℝ) - 1
  let E := physicalAPEnvelope N t nu U
  let f := physicalLogWeight N t
  have hA : 1 < A := by
    have hc : (2 : ℝ) < L := by exact_mod_cast hL
    dsimp [A]; linarith
  have hAU : A ≤ (U : ℝ) := by
    dsimp [A]; have hc : (L : ℝ) ≤ U := by exact_mod_cast hLU; linarith
  have hA0 : 0 ≤ A := (zero_lt_one.trans hA).le
  have hmemA : A ∈ Set.Icc A (U : ℝ) := ⟨le_rfl, hAU⟩
  have hmemU : (U : ℝ) ∈ Set.Icc A (U : ℝ) := ⟨hAU, le_rfl⟩
  obtain ⟨_, hjA⟩ := physicalLogWeight_range_guards hA hU hmemA
  have hfA : 0 ≤ f A := physicalLogWeight_nonneg hA hjA
  have hfU : 0 ≤ f U := physicalLogWeight_nonneg (hA.trans_le hAU) hU
  have heA : |ordinaryAPError N t nu A| ≤ E := ordinaryAPError_le_envelope hnu hA0 hAU
  have heU : |ordinaryAPError N t nu U| ≤ E := ordinaryAPError_le_envelope hnu (Nat.cast_nonneg _) le_rfl
  have hint := physicalLogWeight_deriv_integrableOn hA hU
  have hfd : IntervalIntegrable (deriv f) volume A (U : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAU).mpr hint
  have hi : IntervalIntegrable (fun y => deriv f y * ordinaryAPError N t nu y)
      volume A (U : ℝ) := by
    simpa [mul_comm] using (intervalIntegrable_iff_integrableOn_Icc_of_le hAU).mpr
      (error_mul_integrableOn hnu hA0 hint)
  have hig : IntervalIntegrable (fun y => |deriv f y| * E) volume A (U : ℝ) :=
    hfd.abs.mul_const E
  have hibound : |∫ y in A..(U : ℝ), deriv f y * ordinaryAPError N t nu y| ≤
      (f A - f U) * E := by
    calc
      _ ≤ ∫ y in A..(U : ℝ), |deriv f y * ordinaryAPError N t nu y| :=
        intervalIntegral.abs_integral_le_integral_abs hAU
      _ ≤ ∫ y in A..(U : ℝ), |deriv f y| * E := by
        apply intervalIntegral.integral_mono_on hAU hi.abs hig
        intro y hy
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (ordinaryAPError_le_envelope hnu (hA0.trans hy.1) hy.2) (abs_nonneg _)
      _ = (f A - f U) * E := by
        rw [intervalIntegral.integral_mul_const, physicalLogWeight_variation hAU hA hU]
  rw [weightedAP_abel_identity hnu hLU hL hU]
  change |f U * ordinaryAPError N t nu U - f A * ordinaryAPError N t nu A -
    ∫ y in A..(U : ℝ), deriv f y * ordinaryAPError N t nu y| ≤ _
  calc
    _ ≤ |f U * ordinaryAPError N t nu U| + |f A * ordinaryAPError N t nu A| +
        |∫ y in A..(U : ℝ), deriv f y * ordinaryAPError N t nu y| := by
      exact (abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)
    _ ≤ f U * E + f A * E + (f A - f U) * E := by
      rw [abs_mul, abs_of_nonneg hfU, abs_mul, abs_of_nonneg hfA]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left heU hfU)
        (mul_le_mul_of_nonneg_left heA hfA)) hibound
    _ = 2 * f A * E := by ring

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound21.PhysicalAP.ordinaryWeightedAP
#print axioms GoldbachRound21.PhysicalAP.unmaskedAPMass
#print axioms GoldbachRound21.PhysicalAP.retiredAPMass
#print axioms GoldbachRound21.PhysicalAP.primeUnitAPMass_retirement
#print axioms GoldbachRound21.PhysicalAP.ordinaryWeightedAP_eq_unmasked
#print axioms GoldbachRound21.PhysicalAP.weightedAP_abel_identity
#print axioms GoldbachRound21.PhysicalAP.weightedAP_error_bound

end
end GoldbachRound21.PhysicalAP
