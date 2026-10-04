import SeparatedTypeII

/-!
Round19 / node13.11. The rank face is excluded from every actual canonical
PhysicalWitness18. No primality of the candidate N-d*b is assumed. The
remaining modulus is a quotient by the actual gcd, including overlaps with d.
This file is an auxiliary arithmetic ingredient, not a parity victory.
-/
namespace GoldbachRound19.RankCalibration

open scoped BigOperators
open Finset
open GoldbachRound18.SeparatedTypeII
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000

def rankProduct (p₁ p₂ p₃ : ℕ) : ℕ := p₁ * p₂ * p₃

def remainingModulus (P d : ℕ) : ℕ := P / Nat.gcd P d

theorem prime_dvd_conductor {F : Parameters} {p : ℕ}
    (hc : F.c.Prime) (hr : F.r.Prime) (hp : p.Prime)
    (h : p ∣ conductor F) : p = F.c ∨ p = F.r := by
  rcases hp.dvd_mul.mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp hc).mp h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp hr).mp h)

theorem three_distinct_primes_not_dvd_conductor {F : Parameters}
    {p₁ p₂ p₃ : ℕ} (hc : F.c.Prime) (hr : F.r.Prime)
    (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h₃ : p₃.Prime)
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) :
    ¬ rankProduct p₁ p₂ p₃ ∣ conductor F := by
  intro h
  have hd₁ : p₁ ∣ conductor F :=
    dvd_trans (by unfold rankProduct; exact dvd_mul_of_dvd_left (dvd_mul_right p₁ p₂) p₃) h
  have hd₂ : p₂ ∣ conductor F :=
    dvd_trans (by unfold rankProduct; exact dvd_mul_of_dvd_left (dvd_mul_left p₂ p₁) p₃) h
  have hd₃ : p₃ ∣ conductor F :=
    dvd_trans (by unfold rankProduct; exact dvd_mul_left p₃ (p₁ * p₂)) h
  rcases prime_dvd_conductor hc hr h₁ hd₁ with e₁ | e₁ <;>
    rcases prime_dvd_conductor hc hr h₂ hd₂ with e₂ | e₂ <;>
    rcases prime_dvd_conductor hc hr h₃ hd₃ with e₃ | e₃ <;> omega

theorem small_prime_in_physical_image_is_conductor {F : Parameters}
    {b p : ℕ} (hb : physicalMask F b) (hp : p.Prime)
    (hs : p * p ≤ F.a) (hd : p ∣ conductor F * b) :
    p = F.c ∨ p = F.r := by
  rcases hb with ⟨t⟩
  have hn : ¬ p ∣ b := by
    intro hpb
    have hz := omitted_mask_zero F hp hs hpb
    have ho : beta F b = 1 := by simp [beta, show physicalMask F b from ⟨t⟩]
    linarith
  exact prime_dvd_conductor t.c_prime t.r_prime hp ((hp.dvd_mul.mp hd).resolve_right hn)

theorem three_small_primes_face_excludes_physicalMask (F : Parameters)
    {b p₁ p₂ p₃ : ℕ} (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h₃ : p₃.Prime)
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃)
    (hs₁ : p₁ * p₁ ≤ F.a) (hs₂ : p₂ * p₂ ≤ F.a) (hs₃ : p₃ * p₃ ≤ F.a)
    (hd : rankProduct p₁ p₂ p₃ ∣ conductor F * b) :
    ¬ physicalMask F b := by
  intro hb
  have hd₁ : p₁ ∣ conductor F * b :=
    dvd_trans (by unfold rankProduct; exact dvd_mul_of_dvd_left (dvd_mul_right p₁ p₂) p₃) hd
  have hd₂ : p₂ ∣ conductor F * b :=
    dvd_trans (by unfold rankProduct; exact dvd_mul_of_dvd_left (dvd_mul_left p₂ p₁) p₃) hd
  have hd₃ : p₃ ∣ conductor F * b :=
    dvd_trans (by unfold rankProduct; exact dvd_mul_left p₃ (p₁ * p₂)) hd
  rcases small_prime_in_physical_image_is_conductor hb h₁ hs₁ hd₁ with e₁ | e₁ <;>
    rcases small_prime_in_physical_image_is_conductor hb h₂ hs₂ hd₂ with e₂ | e₂ <;>
    rcases small_prime_in_physical_image_is_conductor hb h₃ hs₃ hd₃ with e₃ | e₃ <;> omega

theorem three_small_primes_face_beta_zero (F : Parameters)
    {b p₁ p₂ p₃ : ℕ} (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h₃ : p₃.Prime)
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃)
    (hs₁ : p₁ * p₁ ≤ F.a) (hs₂ : p₂ * p₂ ≤ F.a) (hs₃ : p₃ * p₃ ≤ F.a)
    (hd : rankProduct p₁ p₂ p₃ ∣ conductor F * b) : beta F b = 0 := by
  simp [beta, three_small_primes_face_excludes_physicalMask F h₁ h₂ h₃
    h₁₂ h₁₃ h₂₃ hs₁ hs₂ hs₃ hd]

theorem remaining_modulus_mul_gcd (P d : ℕ) :
    remainingModulus P d * Nat.gcd P d = P := by
  exact Nat.div_mul_cancel (Nat.gcd_dvd_left P d)

theorem remaining_modulus_dvd (P d : ℕ) : remainingModulus P d ∣ P :=
  ⟨Nat.gcd P d, (remaining_modulus_mul_gcd P d).symm⟩

theorem remaining_modulus_coprime {P d : ℕ} (hs : Squarefree P) (hd : d ≠ 0) :
    Nat.Coprime (remainingModulus P d) d :=
  Nat.coprime_div_gcd_of_squarefree hs hd

theorem remaining_face_modulus_iff {P d b : ℕ} (hs : Squarefree P) (hd : d ≠ 0) :
    P ∣ d * b ↔ remainingModulus P d ∣ b := by
  constructor
  · intro h
    have hq : remainingModulus P d ∣ d * b := dvd_trans (remaining_modulus_dvd P d) h
    exact (remaining_modulus_coprime hs hd).dvd_mul_left.mp hq
  · intro h
    obtain ⟨z, hz⟩ := Nat.gcd_dvd_right P d
    obtain ⟨t, ht⟩ := h
    refine ⟨z * t, ?_⟩
    calc
      d * b = (Nat.gcd P d * z) * (remainingModulus P d * t) := congrArg₂ (· * ·) hz ht
      _ = (remainingModulus P d * Nat.gcd P d) * (z * t) := by ring
      _ = P * (z * t) := by rw [remaining_modulus_mul_gcd P d]

theorem remaining_modulus_gt_one {P d : ℕ} (hp : 0 < P) (hn : ¬ P ∣ d) :
    1 < remainingModulus P d := by
  have hpos : 0 < remainingModulus P d := Nat.div_gcd_pos_of_pos_left d hp
  by_contra hh
  have he : remainingModulus P d = 1 := by omega
  have hpq := remaining_modulus_mul_gcd P d
  rw [he, one_mul] at hpq
  exact hn (hpq ▸ Nat.gcd_dvd_right P d)

theorem remaining_modulus_unit {P d N h : ℕ} (hs : Squarefree P) (hd : d ≠ 0)
    (hunit : Nat.Coprime P (N * h)) :
    Nat.Coprime (remainingModulus P d) (N * d * h) := by
  have hu : Nat.Coprime (remainingModulus P d) (N * h) :=
    hunit.coprime_dvd_left (remaining_modulus_dvd P d)
  have hqd := remaining_modulus_coprime hs hd
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hu.mul_right hqd

theorem canonical_remaining_modulus_gt_one (F : Parameters) {p₁ p₂ p₃ : ℕ}
    (hc : F.c.Prime) (hr : F.r.Prime)
    (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h₃ : p₃.Prime)
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) :
    1 < remainingModulus (rankProduct p₁ p₂ p₃) (conductor F) := by
  apply remaining_modulus_gt_one
  · exact Nat.mul_pos (Nat.mul_pos h₁.pos h₂.pos) h₃.pos
  · exact three_distinct_primes_not_dvd_conductor hc hr h₁ h₂ h₃ h₁₂ h₁₃ h₂₃

def rankUnits (F : Parameters) (I : Finset ℕ) (H P : ℕ) : Finset ℕ :=
  (units I H).filter fun b => ¬ P ∣ conductor F * b

theorem rank_units_modulus (F : Parameters) (I : Finset ℕ) {H P : ℕ}
    (hs : Squarefree P) (hd : conductor F ≠ 0) :
    rankUnits F I H P =
      (units I H).filter fun b => ¬ remainingModulus P (conductor F) ∣ b := by
  ext b
  simp [rankUnits, remaining_face_modulus_iff hs hd]

theorem rank_support (F : Parameters) (I : Finset ℕ) {h p₁ p₂ p₃ : ℕ}
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ h → p * p ≤ F.a)
    (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h₃ : p₃.Prime)
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃)
    (hs₁ : p₁ * p₁ ≤ F.a) (hs₂ : p₂ * p₂ ≤ F.a) (hs₃ : p₃ * p₃ ≤ F.a) :
    I.filter (physicalMask F) ⊆
      rankUnits F I (F.N * conductor F * h) (rankProduct p₁ p₂ p₃) := by
  intro b hb
  obtain ⟨hbI, hbM⟩ := mem_filter.mp hb
  apply mem_filter.mpr
  refine ⟨mem_filter.mpr ⟨hbI, mask_unit_reference F hbM hsmall⟩, ?_⟩
  intro hd
  exact three_small_primes_face_excludes_physicalMask F h₁ h₂ h₃
    h₁₂ h₁₃ h₂₃ hs₁ hs₂ hs₃ hd hbM

theorem rank_structure_le_card (F : Parameters) (I : Finset ℕ) {h p₁ p₂ p₃ : ℕ}
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ h → p * p ≤ F.a)
    (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h₃ : p₃.Prime)
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃)
    (hs₁ : p₁ * p₁ ≤ F.a) (hs₂ : p₂ * p₂ ≤ F.a) (hs₃ : p₃ * p₃ ≤ F.a) :
    structureCount F I ≤
      (rankUnits F I (F.N * conductor F * h) (rankProduct p₁ p₂ p₃)).card :=
  card_le_card (rank_support F I hsmall h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hs₁ hs₂ hs₃)

theorem rank_empty_implies_structure_zero (F : Parameters) (I : Finset ℕ)
    {h p₁ p₂ p₃ : ℕ}
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ h → p * p ≤ F.a)
    (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h₃ : p₃.Prime)
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃)
    (hs₁ : p₁ * p₁ ≤ F.a) (hs₂ : p₂ * p₂ ≤ F.a) (hs₃ : p₃ * p₃ ≤ F.a)
    (he : (rankUnits F I (F.N * conductor F * h) (rankProduct p₁ p₂ p₃)).card = 0) :
    structureCount F I = 0 := by
  have hb := rank_structure_le_card F I hsmall h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hs₁ hs₂ hs₃
  omega

theorem fixed_rank_product : rankProduct 7 11 23 = 1771 := by norm_num [rankProduct]

theorem fixed_rank_squarefree : Squarefree (1771 : ℕ) := by
  have h7 : Nat.Prime 7 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have h23 : Nat.Prime 23 := by norm_num
  have h77 : Squarefree (7 * 11 : ℕ) :=
    (Nat.squarefree_mul (by norm_num : Nat.Coprime 7 11)).mpr
      ⟨h7.prime.squarefree, h11.prime.squarefree⟩
  have hP : Squarefree ((7 * 11) * 23 : ℕ) :=
    (Nat.squarefree_mul (by norm_num : Nat.Coprime (7 * 11) 23)).mpr
      ⟨h77, h23.prime.squarefree⟩
  norm_num at hP
  exact hP

theorem fixed_rank_face_beta_zero (F : Parameters) {b : ℕ} (ha : 529 ≤ F.a)
    (hd : 1771 ∣ conductor F * b) : beta F b = 0 := by
  exact three_small_primes_face_beta_zero F
    (by norm_num : Nat.Prime 7) (by norm_num : Nat.Prime 11) (by norm_num : Nat.Prime 23)
    (by norm_num) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) (by simpa [rankProduct] using hd)

end
end GoldbachRound19.RankCalibration

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound19.RankCalibration.rankProduct
#print axioms GoldbachRound19.RankCalibration.remainingModulus
#print axioms GoldbachRound19.RankCalibration.prime_dvd_conductor
#print axioms GoldbachRound19.RankCalibration.three_distinct_primes_not_dvd_conductor
#print axioms GoldbachRound19.RankCalibration.small_prime_in_physical_image_is_conductor
#print axioms GoldbachRound19.RankCalibration.three_small_primes_face_excludes_physicalMask
#print axioms GoldbachRound19.RankCalibration.three_small_primes_face_beta_zero
#print axioms GoldbachRound19.RankCalibration.remaining_modulus_mul_gcd
#print axioms GoldbachRound19.RankCalibration.remaining_modulus_dvd
#print axioms GoldbachRound19.RankCalibration.remaining_modulus_coprime
#print axioms GoldbachRound19.RankCalibration.remaining_face_modulus_iff
#print axioms GoldbachRound19.RankCalibration.remaining_modulus_gt_one
#print axioms GoldbachRound19.RankCalibration.remaining_modulus_unit
#print axioms GoldbachRound19.RankCalibration.canonical_remaining_modulus_gt_one
#print axioms GoldbachRound19.RankCalibration.rankUnits
#print axioms GoldbachRound19.RankCalibration.rank_units_modulus
#print axioms GoldbachRound19.RankCalibration.rank_support
#print axioms GoldbachRound19.RankCalibration.rank_structure_le_card
#print axioms GoldbachRound19.RankCalibration.rank_empty_implies_structure_zero
#print axioms GoldbachRound19.RankCalibration.fixed_rank_product
#print axioms GoldbachRound19.RankCalibration.fixed_rank_squarefree
#print axioms GoldbachRound19.RankCalibration.fixed_rank_face_beta_zero
