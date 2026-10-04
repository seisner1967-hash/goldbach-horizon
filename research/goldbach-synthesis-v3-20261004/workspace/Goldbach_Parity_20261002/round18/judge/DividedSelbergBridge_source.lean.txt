import DividedRootCounts
import FourFormCollisionLoss

/-! Constructed weights and a quantitative finite truncation on the new actual
divided forms. The only analytic input below is the independent prime-log sum;
Mertens, totient, interval CRT errors, D10 and D11 are not asserted here. -/
namespace GoldbachRound18.DoubleExtraction
open Finset
open GoldbachRound17
noncomputable section

def switchG (N e q z : ℕ) : ℝ :=
  Selberg.G (Selberg.primeSupport z) z (dividedDensity · N e q)
def switchWeight (N e q z : ℕ) : Finset ℕ → ℝ :=
  Selberg.weight (Selberg.primeSupport z) z (dividedDensity · N e q)
def switchRemainder (J : Finset ℕ) (N e q : ℕ) (d : Finset ℕ) : ℝ :=
  Selberg.remainder J (fun x => dividedForm N e q x) (dividedDensity · N e q) d
def switchH (N e q : ℕ) (p : ℕ) : ℝ := dividedDensity p N e q / (1 - dividedDensity p N e q)
def switchEuler (N e q y : ℕ) : ℝ := ∏ p ∈ Selberg.primeSupport y, (1 + switchH N e q p)
def switchCollisionLoss (N e q y : ℕ) : ℝ :=
  ∏ p ∈ Selberg.primeSupport y,
    if p ∣ actualDelta N e q then (FourFormCollisionLoss.primeBase p)^3 else 1

variable {N e q y z : ℕ}

theorem switch_density_properties (h : Cell N q)
    (hns : ∀ p ∈ Selberg.primeSupport z, dividedRho p N e q < p) :
    ∀ p ∈ Selberg.primeSupport z, 0 < dividedDensity p N e q ∧ dividedDensity p N e q < 1 := by
  intro p hp
  letI : Fact p.Prime := ⟨(Selberg.mem_primeSupport.mp hp).1⟩
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hr : 0 < (dividedRho p N e q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) (rho_lower h))
  exact ⟨div_pos hr hp0, (div_lt_one hp0).mpr (by exact_mod_cast hns p hp)⟩

theorem switch_principal_identity (h : Cell N q) (hz : 1 ≤ z)
    (hns : ∀ p ∈ Selberg.primeSupport z, dividedRho p N e q < p) :
    Selberg.principal (Selberg.primeSupport z) (dividedDensity · N e q) (switchWeight N e q z) =
      1 / switchG N e q z :=
  Selberg.principal_optimum hz (switch_density_properties h hns)

theorem switch_finite_upper_bound (J : Finset ℕ) (h : Cell N q) (hz : 1 ≤ z)
    (hns : ∀ p ∈ Selberg.primeSupport z, dividedRho p N e q < p) :
    ((dividedRoughCell J (Selberg.primeSupport z) N e q).card : ℝ) ≤
      (J.card : ℝ) / switchG N e q z +
        ∑ d ∈ Selberg.support (Selberg.primeSupport z) z,
        ∑ t ∈ Selberg.support (Selberg.primeSupport z) z, |switchRemainder J N e q (d ∪ t)| := by
  classical
  have heq : dividedRoughCell J (Selberg.primeSupport z) N e q =
      J.filter (fun x => Selberg.rough (Selberg.primeSupport z) (fun x => dividedForm N e q x) x) := by
    ext x
    simp [dividedRoughCell, Selberg.rough]
  rw [heq]
  exact Selberg.finite_support_upper_bound (P := Selberg.primeSupport z) (J := J) (z := z)
    (F := fun x => dividedForm N e q x) (g := (dividedDensity · N e q)) hz
    (fun p hp => le_trans (by norm_num) (Selberg.mem_primeSupport.mp hp).1.two_le)
    (switch_density_properties h hns)

theorem switch_sieve_dichotomy (J : Finset ℕ) (h : Cell N q) (hz : 1 ≤ z) :
    dividedRoughCell J (Selberg.primeSupport z) N e q = ∅ ∨
      (0 < switchG N e q z ∧
      Selberg.principal (Selberg.primeSupport z) (dividedDensity · N e q) (switchWeight N e q z) =
        1 / switchG N e q z ∧ switchWeight N e q z ∅ = 1 ∧
      (∀ d ⊆ Selberg.primeSupport z, |switchWeight N e q z d| ≤ 1) ∧
      ((dividedRoughCell J (Selberg.primeSupport z) N e q).card : ℝ) ≤
        (J.card : ℝ) / switchG N e q z +
          ∑ d ∈ Selberg.support (Selberg.primeSupport z) z,
          ∑ t ∈ Selberg.support (Selberg.primeSupport z) z, |switchRemainder J N e q (d ∪ t)|) := by
  by_cases hs : ∃ p ∈ Selberg.primeSupport z, dividedRho p N e q = p
  · obtain ⟨p, hp, hs⟩ := hs
    letI : Fact p.Prime := ⟨(Selberg.mem_primeSupport.mp hp).1⟩
    exact Or.inl (saturation_roughCell_empty J _ hp hs)
  · have hns : ∀ p ∈ Selberg.primeSupport z, dividedRho p N e q < p := by
      intro p hp
      letI : Fact p.Prime := ⟨(Selberg.mem_primeSupport.mp hp).1⟩
      exact lt_of_le_of_ne rho_le_modulus (fun heq => hs ⟨p, hp, heq⟩)
    have hg := switch_density_properties h hns
    exact Or.inr ⟨Selberg.G_pos hz hg, switch_principal_identity h hz hns,
      Selberg.weight_empty hz hg, fun d hd => Selberg.weight_abs_le_one hz
        (fun p hp => le_trans (by norm_num) (Selberg.mem_primeSupport.mp hp).1.two_le) hg hd,
      switch_finite_upper_bound J h hz hns⟩

theorem switchH_nonneg (h : Cell N q)
    (hns : ∀ p ∈ Selberg.primeSupport y, dividedRho p N e q < p) :
    ∀ p ∈ Selberg.primeSupport y, 0 ≤ switchH N e q p := by
  intro p hp
  obtain ⟨hg0, hg1⟩ := switch_density_properties h hns p hp
  exact (div_pos hg0 (sub_pos.mpr hg1)).le

theorem switchH_ratio (h : Cell N q)
    (hns : ∀ p ∈ Selberg.primeSupport y, dividedRho p N e q < p)
    {p : ℕ} (hp : p ∈ Selberg.primeSupport y) :
    switchH N e q p / (1 + switchH N e q p) = dividedDensity p N e q := by
  obtain ⟨_, hg1⟩ := switch_density_properties h hns p hp
  have hn := (sub_pos.mpr hg1).ne'
  unfold switchH
  field_simp

theorem switch_weighted_moment (h : Cell N q)
    (hns : ∀ p ∈ Selberg.primeSupport y, dividedRho p N e q < p) :
    (∑ s ∈ (Selberg.primeSupport y).powerset,
      PowersetMoment.subsetWeight (switchH N e q) s * PowersetMoment.subsetLog s) =
      switchEuler N e q y *
        (∑ p ∈ Selberg.primeSupport y, dividedDensity p N e q * Real.log p) := by
  dsimp only [PowersetMoment.subsetLog]
  rw [PowersetMoment.weighted_moment _ _ _ (switchH_nonneg h hns)]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [switchH_ratio h hns hp]

theorem switch_density_log_sum_le_four (h : Cell N q) (hg : TargetGuards N e q) :
    (∑ p ∈ Selberg.primeSupport y, dividedDensity p N e q * Real.log p) ≤
      4 * (∑ p ∈ Selberg.primeSupport y, Real.log p / p) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  letI : Fact p.Prime := ⟨(Selberg.mem_primeSupport.mp hp).1⟩
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hr : (dividedRho p N e q : ℝ) ≤ 4 := by exact_mod_cast rho_le_four h hg
  have hd : dividedDensity p N e q ≤ 4 / (p : ℝ) := div_le_div_of_nonneg_right hr hp0.le
  have hm := mul_le_mul_of_nonneg_right hd (Real.log_natCast_nonneg p)
  dsimp only [dividedDensity] at *
  convert hm using 1; ring

theorem switchG_half_euler_of_log_moment (h : Cell N q)
    (hyz : y ≤ z) (hz : 0 < (z : ℝ)) (hlogz : 0 < Real.log z)
    (hns : ∀ p ∈ Selberg.primeSupport z, dividedRho p N e q < p)
    (hm : (∑ p ∈ Selberg.primeSupport y, dividedDensity p N e q * Real.log p) ≤ Real.log z / 2) :
    switchEuler N e q y / 2 ≤ switchG N e q z := by
  have hsub := FourFormTruncation.primeSupport_mono hyz
  have hny : ∀ p ∈ Selberg.primeSupport y, dividedRho p N e q < p :=
    fun p hp => hns p (hsub hp)
  have hE : 0 ≤ switchEuler N e q y := by
    exact Finset.prod_nonneg fun p hp => by linarith [switchH_nonneg h hny p hp]
  have hmoment :
      (∑ s ∈ (Selberg.primeSupport y).powerset,
        PowersetMoment.subsetWeight (switchH N e q) s * PowersetMoment.subsetLog s) ≤
      Real.log z / 2 * (∑ s ∈ (Selberg.primeSupport y).powerset,
        PowersetMoment.subsetWeight (switchH N e q) s) := by
    rw [switch_weighted_moment h hny, PowersetMoment.total_weight]
    change switchEuler N e q y * _ ≤ Real.log z / 2 * switchEuler N e q y
    nlinarith
  have hc := PowersetMoment.cutoff_markov (Selberg.primeSupport y) (switchH N e q) z
    (switchH_nonneg h hny) (fun p hp => (Selberg.mem_primeSupport.mp hp).1.pos)
    hz hlogz hmoment
  rw [PowersetMoment.total_weight] at hc
  change switchEuler N e q y / 2 ≤
    Selberg.G (Selberg.primeSupport y) z (dividedDensity · N e q) at hc
  exact hc.trans (FourFormTruncation.G_mono_support hsub (switch_density_properties h hns))

theorem switchG_half_euler_of_prime_log_sum (h : Cell N q) (hg : TargetGuards N e q)
    (hyz : y ≤ z) (hz : 0 < (z : ℝ))
    (hns : ∀ p ∈ Selberg.primeSupport z, dividedRho p N e q < p)
    (hlogz : 32 ≤ Real.log z) (hlogy : 32 * Real.log y ≤ Real.log z)
    (hprime : (∑ p ∈ Selberg.primeSupport y, Real.log p / p) ≤ 2 + 2 * Real.log y) :
    switchEuler N e q y / 2 ≤ switchG N e q z := by
  have hm := switch_density_log_sum_le_four (y := y) h hg
  have hl : (∑ p ∈ Selberg.primeSupport y, dividedDensity p N e q * Real.log p) ≤
      Real.log z / 2 := by nlinarith
  exact switchG_half_euler_of_log_moment h hyz hz (by linarith) hns hl

theorem switchEuler_factor (h : Cell N q)
    (hns : ∀ p ∈ Selberg.primeSupport y, dividedRho p N e q < p)
    {p : ℕ} (hp : p ∈ Selberg.primeSupport y) :
    1 + switchH N e q p = 1 / (1 - dividedDensity p N e q) := by
  obtain ⟨_, hg1⟩ := switch_density_properties h hns p hp
  have hn := (sub_pos.mpr hg1).ne'
  unfold switchH
  field_simp

theorem switch_collision_factor_le (h : Cell N q) (hg : TargetGuards N e q)
    (hns : ∀ p ∈ Selberg.primeSupport y, dividedRho p N e q < p)
    {p : ℕ} (hp : p ∈ Selberg.primeSupport y) :
    (1 / FourFormCollisionLoss.primeBase p)^4 *
      (if p ∣ actualDelta N e q then (FourFormCollisionLoss.primeBase p)^3 else 1) ≤
        1 + switchH N e q p := by
  have hpp := (Selberg.mem_primeSupport.mp hp).1
  letI : Fact p.Prime := ⟨hpp⟩
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hpp.pos
  have hb := FourFormCollisionLoss.primeBase_positive hpp
  obtain ⟨_, hg1⟩ := switch_density_properties h hns p hp
  rw [switchEuler_factor h hns hp]
  by_cases hd : p ∣ actualDelta N e q
  · rw [if_pos hd]
    have hr : (1 : ℝ) ≤ dividedRho p N e q := by exact_mod_cast rho_lower h
    have hdens : 1 / (p : ℝ) ≤ dividedDensity p N e q := div_le_div_of_nonneg_right hr hp0.le
    have heq : (1 / FourFormCollisionLoss.primeBase p)^4 *
        (FourFormCollisionLoss.primeBase p)^3 = 1 / FourFormCollisionLoss.primeBase p := by
      field_simp
      ring
    rw [heq]
    exact one_div_le_one_div_of_le (sub_pos.mpr hg1)
      (by dsimp [FourFormCollisionLoss.primeBase]; linarith)
  · rw [if_neg hd, mul_one]
    have hr4 := rho_eq_four_of_not_dvd_actualDelta (l := p) h hg hd
    have hg4 : dividedDensity p N e q = 4 / (p : ℝ) := by simp [dividedDensity, hr4]
    have ht : -(2 : ℝ) ≤ -(1 / (p : ℝ)) := by
      have hl : 1 / (p : ℝ) < 1 := (div_lt_one hp0).mpr (by exact_mod_cast hpp.one_lt)
      linarith
    have hbern := one_add_mul_le_pow ht 4
    have hbd : 1 - dividedDensity p N e q ≤ (FourFormCollisionLoss.primeBase p)^4 := by
      rw [hg4]
      dsimp [FourFormCollisionLoss.primeBase]
      convert hbern using 1; ring
    simpa only [one_div_pow] using one_div_le_one_div_of_le (sub_pos.mpr hg1) hbd

theorem switchEuler_collision_loss (h : Cell N q) (hg : TargetGuards N e q)
    (hns : ∀ p ∈ Selberg.primeSupport y, dividedRho p N e q < p) :
    (FourFormCollisionLoss.mertensEuler y)^4 * switchCollisionLoss N e q y ≤
      switchEuler N e q y := by
  unfold FourFormCollisionLoss.mertensEuler switchCollisionLoss switchEuler
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    apply mul_nonneg (pow_nonneg (one_div_nonneg.mpr
      (FourFormCollisionLoss.primeBase_positive (Selberg.mem_primeSupport.mp hp).1).le) 4)
    split_ifs
    · exact pow_nonneg (FourFormCollisionLoss.primeBase_positive (Selberg.mem_primeSupport.mp hp).1).le 3
    · norm_num
  · intro p hp
    exact switch_collision_factor_le h hg hns hp

theorem switchG_collision_loss_half (h : Cell N q) (hg : TargetGuards N e q)
    (hyz : y ≤ z) (hz : 0 < (z : ℝ))
    (hns : ∀ p ∈ Selberg.primeSupport z, dividedRho p N e q < p)
    (hlogz : 32 ≤ Real.log z) (hlogy : 32 * Real.log y ≤ Real.log z)
    (hprime : (∑ p ∈ Selberg.primeSupport y, Real.log p / p) ≤ 2 + 2 * Real.log y) :
    (FourFormCollisionLoss.mertensEuler y)^4 * switchCollisionLoss N e q y / 2 ≤ switchG N e q z := by
  have hsub := FourFormTruncation.primeSupport_mono hyz
  have hny : ∀ p ∈ Selberg.primeSupport y, dividedRho p N e q < p := fun p hp => hns p (hsub hp)
  have he := switchEuler_collision_loss h hg hny
  have hG := switchG_half_euler_of_prime_log_sum h hg hyz hz hns hlogz hlogy hprime
  linarith

#print axioms switchG
#print axioms switchWeight
#print axioms switchRemainder
#print axioms switchH
#print axioms switchEuler
#print axioms switchCollisionLoss
#print axioms switch_density_properties
#print axioms switch_principal_identity
#print axioms switch_finite_upper_bound
#print axioms switch_sieve_dichotomy
#print axioms switchH_nonneg
#print axioms switchH_ratio
#print axioms switch_weighted_moment
#print axioms switch_density_log_sum_le_four
#print axioms switchG_half_euler_of_log_moment
#print axioms switchG_half_euler_of_prime_log_sum
#print axioms switchEuler_factor
#print axioms switch_collision_factor_le
#print axioms switchEuler_collision_loss
#print axioms switchG_collision_loss_half

end
end GoldbachRound18.DoubleExtraction
