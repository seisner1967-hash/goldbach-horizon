import RankCalibrationFace
import SeparatedTypeIICount

/-!
The new rank references are defined on their actual finite support. Every price
is retained. The real prime and raw von Mangoldt measures are distinct.
The normalized support variation is proved without any hypothesis that the
price or Gamma is small. Historical interval-count lemmas are imported only.
-/
namespace GoldbachRound19.RankCalibration

open scoped BigOperators
open Finset
open GoldbachRound18.SeparatedTypeII
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000

def normalizedReference (A : ℕ) (U : Finset ℕ) (b : ℕ) : ℝ :=
  (A : ℝ) / U.card * if b ∈ U then 1 else 0

def referenceMass (A : ℕ) (U : Finset ℕ) (f : ℕ → ℝ) : ℝ :=
  (A : ℝ) / U.card * ∑ b ∈ U, f b

def centeredMass (F : Parameters) (I U : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  (∑ b ∈ I, beta F b * w (candidate F b)) -
    referenceMass (structureCount F I) U (fun b => w (candidate F b))

def supportPrice (F : Parameters) (I U V : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  referenceMass (structureCount F I) V (fun b => w (candidate F b)) -
    referenceMass (structureCount F I) U (fun b => w (candidate F b))

def cofactorWeight (F : Parameters) (S : ℝ) : ℝ := Real.log (F.c : ℝ) + S

def aggregateGamma {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (F : ι → Parameters) (I U : ι → Finset ℕ) (S : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, cofactorWeight (F d) S * centeredMass (F d) (I d) (U d) w

def aggregatePrice {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (F : ι → Parameters) (I U V : ι → Finset ℕ) (S : ℝ) (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, cofactorWeight (F d) S * supportPrice (F d) (I d) (U d) (V d) w

theorem normalized_reference_zero_mass (U : Finset ℕ) (b : ℕ) :
    normalizedReference 0 U b = 0 := by simp [normalizedReference]

theorem reference_mass_zero (U : Finset ℕ) (f : ℕ → ℝ) :
    referenceMass 0 U f = 0 := by simp [referenceMass]

theorem reference_mass_empty (A : ℕ) (f : ℕ → ℝ) :
    referenceMass A ∅ f = 0 := by simp [referenceMass]

theorem reference_mass_sum (A : ℕ) (I U : Finset ℕ) (f : ℕ → ℝ)
    (hU : U ⊆ I) :
    ∑ b ∈ I, normalizedReference A U b * f b = referenceMass A U f := by
  unfold normalizedReference referenceMass
  rw [mul_sum]
  rw [← sum_subset hU]
  · apply sum_congr rfl
    intro b hb
    simp [hb]
  · intro b hbI hbU
    simp [hbU]

theorem old_reference_is_normalized (F : Parameters) (I : Finset ℕ) (H b : ℕ) :
    reference F I H b = normalizedReference (structureCount F I) (units I H) b := rfl

theorem old_weighted_profile_is_centered_mass (F : Parameters) (I : Finset ℕ)
    (H : ℕ) (w : ℕ → ℝ) :
    weightedProfile F I H w = centeredMass F I (units I H) w := by
  unfold weightedProfile centeredMass centered
  simp_rw [sub_mul]
  rw [sum_sub_distrib]
  rw [show (∑ b ∈ I, reference F I H b * w (candidate F b)) =
      referenceMass (structureCount F I) (units I H) (fun b => w (candidate F b)) from
    by simpa only [old_reference_is_normalized] using
      reference_mass_sum (structureCount F I) I (units I H)
        (fun b => w (candidate F b)) (filter_subset _ _)]

theorem centered_mass_calibration (F : Parameters) (I U V : Finset ℕ)
    (w : ℕ → ℝ) :
    centeredMass F I U w = centeredMass F I V w + supportPrice F I U V w := by
  unfold centeredMass supportPrice
  ring

theorem support_price_two_steps (F : Parameters) (I U₀ U V : Finset ℕ)
    (w : ℕ → ℝ) :
    supportPrice F I U₀ V w = supportPrice F I U₀ U w + supportPrice F I U V w := by
  unfold supportPrice
  ring

theorem weighted_rank_price_decomposition {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (F : ι → Parameters) (I U₀ U V : ι → Finset ℕ)
    (S : ℝ) (w : ℕ → ℝ) :
    aggregateGamma D F I U₀ S w = aggregateGamma D F I V S w +
      aggregatePrice D F I U₀ U S w + aggregatePrice D F I U V S w := by
  unfold aggregateGamma aggregatePrice
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  rw [centered_mass_calibration (F d) (I d) (U₀ d) (V d) w,
    support_price_two_steps (F d) (I d) (U₀ d) (U d) (V d) w]
  ring

theorem theta_weighted_rank_price_decomposition {ι : Type*} [DecidableEq ι]
    (N : ℕ) (D : Finset ι) (F : ι → Parameters) (I U₀ U V : ι → Finset ℕ) (S : ℝ) :
    aggregateGamma D F I U₀ S (theta N) = aggregateGamma D F I V S (theta N) +
      aggregatePrice D F I U₀ U S (theta N) + aggregatePrice D F I U V S (theta N) :=
  weighted_rank_price_decomposition D F I U₀ U V S (theta N)

theorem raw_weighted_rank_price_decomposition {ι : Type*} [DecidableEq ι]
    (N : ℕ) (D : Finset ι) (F : ι → Parameters) (I U₀ U V : ι → Finset ℕ) (S : ℝ) :
    aggregateGamma D F I U₀ S (rawLambda N) = aggregateGamma D F I V S (rawLambda N) +
      aggregatePrice D F I U₀ U S (rawLambda N) +
      aggregatePrice D F I U V S (rawLambda N) :=
  weighted_rank_price_decomposition D F I U₀ U V S (rawLambda N)

theorem support_price_raw_theta_difference (F : Parameters) (I U V : Finset ℕ) :
    supportPrice F I U V (rawLambda F.N) = supportPrice F I U V (theta F.N) +
      supportPrice F I U V (fun j => rawLambda F.N j - theta F.N j) := by
  unfold supportPrice referenceMass
  simp_rw [sum_sub_distrib]
  ring

theorem aggregate_price_raw_theta_difference {ι : Type*} [DecidableEq ι]
    (N : ℕ) (D : Finset ι) (F : ι → Parameters) (I U V : ι → Finset ℕ) (S : ℝ) :
    aggregatePrice D F I U V S (rawLambda N) =
      aggregatePrice D F I U V S (theta N) +
      aggregatePrice D F I U V S (fun j => rawLambda N j - theta N j) := by
  unfold aggregatePrice supportPrice referenceMass
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  simp_rw [sum_sub_distrib]
  ring

theorem rank_reference_empty_branch (F : Parameters) (I U₀ V : Finset ℕ)
    (hA : structureCount F I ≤ V.card) (hV : V.card = 0) (w : ℕ → ℝ) :
    structureCount F I = 0 ∧ supportPrice F I U₀ V w = 0 := by
  have he : structureCount F I = 0 := by omega
  exact ⟨he, by simp [supportPrice, referenceMass, he]⟩

theorem normalized_rank_price_cross_mean (A : ℕ) (U V : Finset ℕ) (f : ℕ → ℝ)
    (hU : U.card ≠ 0) (hV : V.card ≠ 0) :
    referenceMass A V f - referenceMass A U f =
      (A : ℝ) * ((U.card : ℝ) * (∑ b ∈ V, f b) -
        (V.card : ℝ) * (∑ b ∈ U, f b)) / ((U.card : ℝ) * V.card) := by
  unfold referenceMass
  have hu : (U.card : ℝ) ≠ 0 := by exact_mod_cast hU
  have hv : (V.card : ℝ) ≠ 0 := by exact_mod_cast hV
  field_simp
  ring

theorem normalized_reference_change_bound (A : ℕ) (U V : Finset ℕ) (f : ℕ → ℝ)
    (hVU : V ⊆ U) (hA : A ≤ V.card) {u : ℝ} (_hu : 0 ≤ u)
    (hf : ∀ b ∈ U, 0 ≤ f b ∧ f b ≤ u) :
    |referenceMass A V f - referenceMass A U f| ≤
      u * (A : ℝ) * ((U \ V).card : ℝ) / U.card := by
  by_cases hv0 : V.card = 0
  · have ha0 : A = 0 := by omega
    simp [referenceMass, ha0]
  have hv : 0 < (V.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hv0
  have hu0 : U.card ≠ 0 := by
    have hc := card_le_card hVU
    omega
  have huc : 0 < (U.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hu0
  have hA0 : 0 ≤ (A : ℝ) := by positivity
  have hsumV0 : 0 ≤ ∑ b ∈ V, f b := sum_nonneg fun b hb => (hf b (hVU hb)).1
  have hsumV : (∑ b ∈ V, f b) ≤ (V.card : ℝ) * u := by
    calc
      _ ≤ ∑ b ∈ V, u := sum_le_sum fun b hb => (hf b (hVU hb)).2
      _ = _ := by simp [mul_comm]
  have hsumL0 : 0 ≤ ∑ b ∈ U \ V, f b :=
    sum_nonneg fun b hb => (hf b (mem_sdiff.mp hb).1).1
  have hsumL : (∑ b ∈ U \ V, f b) ≤ ((U \ V).card : ℝ) * u := by
    calc
      _ ≤ ∑ b ∈ U \ V, u := sum_le_sum fun b hb => (hf b (mem_sdiff.mp hb).1).2
      _ = _ := by simp [mul_comm]
  have hcard : ((U \ V).card : ℝ) + (V.card : ℝ) = U.card := by
    exact_mod_cast card_sdiff_add_card_eq_card hVU
  have hsum : (∑ b ∈ U \ V, f b) + (∑ b ∈ V, f b) = ∑ b ∈ U, f b :=
    sum_sdiff hVU
  have he : referenceMass A V f - referenceMass A U f =
      (A : ℝ) * (((U \ V).card : ℝ) * (∑ b ∈ V, f b) -
        (V.card : ℝ) * (∑ b ∈ U \ V, f b)) / ((V.card : ℝ) * U.card) := by
    unfold referenceMass
    rw [← hsum, ← hcard]
    field_simp
    ring
  have hvu : 0 < (V.card : ℝ) * U.card := mul_pos hv huc
  have hl : 0 ≤ ((U \ V).card : ℝ) := by positivity
  have hboundL : (V.card : ℝ) * (∑ b ∈ U \ V, f b) ≤
      u * (V.card : ℝ) * ((U \ V).card : ℝ) := by nlinarith
  have hboundV : ((U \ V).card : ℝ) * (∑ b ∈ V, f b) ≤
      u * (V.card : ℝ) * ((U \ V).card : ℝ) := by nlinarith
  have hnum : |((U \ V).card : ℝ) * (∑ b ∈ V, f b) -
      (V.card : ℝ) * (∑ b ∈ U \ V, f b)| ≤
      u * (V.card : ℝ) * ((U \ V).card : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hl hsumV0, mul_nonneg (le_of_lt hv) hsumL0]
  rw [he, abs_div, abs_mul, abs_of_nonneg hA0, abs_of_pos hvu]
  calc
    _ ≤ (A : ℝ) * (u * (V.card : ℝ) * ((U \ V).card : ℝ)) /
        ((V.card : ℝ) * U.card) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hA0) (le_of_lt hvu)
    _ = _ := by field_simp; ring

theorem normalized_reference_change_bound_card (A : ℕ) (U V : Finset ℕ)
    (f : ℕ → ℝ) (hVU : V ⊆ U) (hA : A ≤ V.card) {u : ℝ} (hu : 0 ≤ u)
    (hf : ∀ b ∈ U, 0 ≤ f b ∧ f b ≤ u) :
    |referenceMass A V f - referenceMass A U f| ≤ u * ((U \ V).card : ℝ) := by
  have hs := normalized_reference_change_bound A U V f hVU hA hu hf
  by_cases hu0 : U.card = 0
  · have hv0 : V.card = 0 := by have := card_le_card hVU; omega
    have ha0 : A = 0 := by omega
    simp [referenceMass, ha0]
    exact mul_nonneg hu (by positivity)
  have huc : 0 < (U.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hu0
  have hac : (A : ℝ) ≤ U.card := by exact_mod_cast le_trans hA (card_le_card hVU)
  have hl : 0 ≤ ((U \ V).card : ℝ) := by positivity
  apply le_trans hs
  apply (div_le_iff₀ huc).mpr
  nlinarith [mul_nonneg hu hl]

theorem theta_nonnegative (N j : ℕ) : 0 ≤ theta N j := by
  unfold theta
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ j from le_trans (by omega) h.1.two_le))
  · exact le_rfl

theorem raw_nonnegative (N j : ℕ) : 0 ≤ rawLambda N j := by
  unfold rawLambda
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

theorem theta_candidate_bound (F : Parameters) {N : ℕ} (hN : F.N = N)
    (hNp : 1 ≤ N) (b : ℕ) : 0 ≤ theta N (candidate F b) ∧
      theta N (candidate F b) ≤ Real.log (N : ℝ) := by
  refine ⟨theta_nonnegative N _, ?_⟩
  unfold theta
  split_ifs with h
  · apply Real.log_le_log
    · exact_mod_cast h.1.pos
    · exact_mod_cast (show candidate F b ≤ N by simp [candidate, hN])
  · exact Real.log_nonneg (by exact_mod_cast hNp)

theorem reference_nonnegative (A : ℕ) (U : Finset ℕ) (b : ℕ) :
    0 ≤ normalizedReference A U b := by
  unfold normalizedReference
  split_ifs <;> positivity

theorem canonical_profile_on_rank_face_nonpositive (F : Parameters) (I U : Finset ℕ)
    {b : ℕ} (ha : 529 ≤ F.a) (hd : 1771 ∣ conductor F * b) :
    beta F b - normalizedReference (structureCount F I) U b ≤ 0 := by
  rw [fixed_rank_face_beta_zero F ha hd]
  have := reference_nonnegative (structureCount F I) U b
  linarith

theorem rank_face_prime_summand_nonpositive (F : Parameters) (I U : Finset ℕ)
    {b : ℕ} (ha : 529 ≤ F.a) (hd : 1771 ∣ conductor F * b) :
    (beta F b - normalizedReference (structureCount F I) U b) *
      theta F.N (candidate F b) ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg
    (canonical_profile_on_rank_face_nonpositive F I U ha hd)
    (theta_nonnegative _ _)

theorem rank_face_raw_summand_nonpositive (F : Parameters) (I U : Finset ℕ)
    {b : ℕ} (ha : 529 ≤ F.a) (hd : 1771 ∣ conductor F * b) :
    (beta F b - normalizedReference (structureCount F I) U b) *
      rawLambda F.N (candidate F b) ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg
    (canonical_profile_on_rank_face_nonpositive F I U ha hd)
    (raw_nonnegative _ _)

end
end GoldbachRound19.RankCalibration

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound19.RankCalibration.normalizedReference
#print axioms GoldbachRound19.RankCalibration.referenceMass
#print axioms GoldbachRound19.RankCalibration.centeredMass
#print axioms GoldbachRound19.RankCalibration.supportPrice
#print axioms GoldbachRound19.RankCalibration.cofactorWeight
#print axioms GoldbachRound19.RankCalibration.aggregateGamma
#print axioms GoldbachRound19.RankCalibration.aggregatePrice
#print axioms GoldbachRound19.RankCalibration.normalized_reference_zero_mass
#print axioms GoldbachRound19.RankCalibration.reference_mass_zero
#print axioms GoldbachRound19.RankCalibration.reference_mass_empty
#print axioms GoldbachRound19.RankCalibration.reference_mass_sum
#print axioms GoldbachRound19.RankCalibration.old_reference_is_normalized
#print axioms GoldbachRound19.RankCalibration.old_weighted_profile_is_centered_mass
#print axioms GoldbachRound19.RankCalibration.centered_mass_calibration
#print axioms GoldbachRound19.RankCalibration.support_price_two_steps
#print axioms GoldbachRound19.RankCalibration.weighted_rank_price_decomposition
#print axioms GoldbachRound19.RankCalibration.theta_weighted_rank_price_decomposition
#print axioms GoldbachRound19.RankCalibration.raw_weighted_rank_price_decomposition
#print axioms GoldbachRound19.RankCalibration.support_price_raw_theta_difference
#print axioms GoldbachRound19.RankCalibration.aggregate_price_raw_theta_difference
#print axioms GoldbachRound19.RankCalibration.rank_reference_empty_branch
#print axioms GoldbachRound19.RankCalibration.normalized_rank_price_cross_mean
#print axioms GoldbachRound19.RankCalibration.normalized_reference_change_bound
#print axioms GoldbachRound19.RankCalibration.normalized_reference_change_bound_card
#print axioms GoldbachRound19.RankCalibration.theta_nonnegative
#print axioms GoldbachRound19.RankCalibration.raw_nonnegative
#print axioms GoldbachRound19.RankCalibration.theta_candidate_bound
#print axioms GoldbachRound19.RankCalibration.reference_nonnegative
#print axioms GoldbachRound19.RankCalibration.canonical_profile_on_rank_face_nonpositive
#print axioms GoldbachRound19.RankCalibration.rank_face_prime_summand_nonpositive
#print axioms GoldbachRound19.RankCalibration.rank_face_raw_summand_nonpositive
