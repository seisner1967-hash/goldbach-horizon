import Mathlib
import EulerAnchor

/-! Actual canonical witnesses for the selected double-semiprime cell.
The quotient primality and source-window inequalities are selection guards;
no prime incidence, density, capacity or sieve denominator is assumed. -/
namespace GoldbachRound18.DoubleExtraction

noncomputable section

def anchor (N : ℕ) : ℕ := GoldbachRound16.Anchor.leastMissingOddPrime N
def resource1 (N q : ℕ) : ℕ := N - q
def resource0 (N q : ℕ) : ℕ := N - anchor N * q
def witness1 (N q : ℕ) : ℕ := (resource1 N q).minFac
def witness0 (N q : ℕ) : ℕ := (resource0 N q).minFac
def quotient1 (N q : ℕ) : ℕ := resource1 N q / witness1 N q
def quotient0 (N q : ℕ) : ℕ := resource0 N q / witness0 N q
def modulus (N q : ℕ) : ℕ := witness1 N q * witness0 N q
def representative (N q : ℕ) : ℕ := q % modulus N q
def progressionIndex (N q : ℕ) : ℕ := q / modulus N q

structure Cell (N q : ℕ) : Prop where
  N_ne_zero : N ≠ 0
  N_even : Even N
  q_prime : q.Prime
  q_unit : q.Coprime N
  anchor_lt_q : anchor N < q
  anchor_mul_q_lt : anchor N * q < N
  resource1_two : 2 ≤ resource1 N q
  resource0_two : 2 ≤ resource0 N q
  quotient1_prime : (quotient1 N q).Prime
  quotient0_prime : (quotient0 N q).Prime
  witness1_lt_quotient : witness1 N q < quotient1 N q
  witness0_lt_quotient : witness0 N q < quotient0 N q

variable {N q : ℕ}

theorem anchor_spec (h : Cell N q) :
    (anchor N).Prime ∧ anchor N ≠ 2 ∧ ¬ anchor N ∣ N ∧
      ∀ l, l.Prime → l < anchor N → l ∣ N := by
  exact GoldbachRound16.Anchor.leastMissingOddPrime_spec h.N_ne_zero h.N_even

theorem anchor_three (h : Cell N q) : 3 ≤ anchor N := by
  obtain ⟨hp, h2, _, _⟩ := anchor_spec h
  have := hp.two_le
  omega

theorem anchor_unit (h : Cell N q) : (anchor N).Coprime N := by
  obtain ⟨hp, _, hn, _⟩ := anchor_spec h
  exact hp.coprime_iff_not_dvd.mpr hn

theorem q_lt_N (h : Cell N q) : q < N := by
  have hp := anchor_three h
  nlinarith [h.anchor_mul_q_lt]

theorem resource1_unit (h : Cell N q) : (resource1 N q).Coprime N := by
  exact (Nat.coprime_self_sub_left (q_lt_N h).le).mpr h.q_unit

theorem resource0_unit (h : Cell N q) : (resource0 N q).Coprime N := by
  exact (Nat.coprime_self_sub_left h.anchor_mul_q_lt.le).mpr
    (Nat.coprime_mul_iff_left.mpr ⟨anchor_unit h, h.q_unit⟩)

theorem witness1_prime (h : Cell N q) : (witness1 N q).Prime := by
  exact Nat.minFac_prime (by have := h.resource1_two; omega)

theorem witness0_prime (h : Cell N q) : (witness0 N q).Prime := by
  exact Nat.minFac_prime (by have := h.resource0_two; omega)

theorem witness1_dvd : witness1 N q ∣ resource1 N q := Nat.minFac_dvd _
theorem witness0_dvd : witness0 N q ∣ resource0 N q := Nat.minFac_dvd _

theorem witness1_unit (h : Cell N q) : (witness1 N q).Coprime N := by
  exact Nat.Coprime.of_dvd_left witness1_dvd (resource1_unit h)

theorem witness0_unit (h : Cell N q) : (witness0 N q).Coprime N := by
  exact Nat.Coprime.of_dvd_left witness0_dvd (resource0_unit h)

theorem witness1_ge_anchor (h : Cell N q) : anchor N ≤ witness1 N q := by
  by_contra hc
  have hd := (anchor_spec h).2.2.2 _ (witness1_prime h) (by omega)
  exact ((witness1_prime h).coprime_iff_not_dvd.mp (witness1_unit h)) hd

theorem witness0_ge_anchor (h : Cell N q) : anchor N ≤ witness0 N q := by
  by_contra hc
  have hd := (anchor_spec h).2.2.2 _ (witness0_prime h) (by omega)
  exact ((witness0_prime h).coprime_iff_not_dvd.mp (witness0_unit h)) hd

theorem resource1_factorization :
    witness1 N q * quotient1 N q = resource1 N q := by
  exact Nat.mul_div_cancel' witness1_dvd

theorem resource0_factorization :
    witness0 N q * quotient0 N q = resource0 N q := by
  exact Nat.mul_div_cancel' witness0_dvd

theorem q_mod_witness1 (h : Cell N q) :
    q ≡ N [MOD witness1 N q] := by
  exact (Nat.modEq_iff_dvd' (q_lt_N h).le).mpr witness1_dvd

theorem anchor_q_mod_witness0 (h : Cell N q) :
    anchor N * q ≡ N [MOD witness0 N q] := by
  exact (Nat.modEq_iff_dvd' h.anchor_mul_q_lt.le).mpr witness0_dvd

theorem witness0_ne_anchor (h : Cell N q) : witness0 N q ≠ anchor N := by
  intro heq
  have hd0 : anchor N ∣ N - anchor N * q := by
    simpa only [resource0, heq] using (witness0_dvd (N := N) (q := q))
  have hd : anchor N ∣ N := by
    have hadd := dvd_add hd0 (dvd_mul_right (anchor N) q)
    simpa only [Nat.sub_add_cancel h.anchor_mul_q_lt.le] using hadd
  exact (anchor_spec h).2.2.1 hd

theorem witnesses_distinct (h : Cell N q) : witness1 N q ≠ witness0 N q := by
  intro heq
  have hfirst := q_mod_witness1 h
  have hsecond : anchor N * q ≡ N [MOD witness1 N q] := by
    simpa only [← heq] using anchor_q_mod_witness0 h
  have hcong : N ≡ anchor N * N [MOD witness1 N q] :=
    hsecond.symm.trans (hfirst.mul_left (anchor N))
  have hle : N ≤ anchor N * N := by nlinarith [anchor_three h]
  have hd : witness1 N q ∣ (anchor N - 1) * N := by
    have ht := (Nat.modEq_iff_dvd' hle).mp hcong
    simpa only [Nat.sub_mul, one_mul] using ht
  have hd' := (witness1_unit h).dvd_of_dvd_mul_right hd
  have hpos : 0 < anchor N - 1 := by have := anchor_three h; omega
  have hle' := Nat.le_of_dvd hpos hd'
  have hge := witness1_ge_anchor h
  omega

theorem witnesses_coprime (h : Cell N q) :
    (witness1 N q).Coprime (witness0 N q) :=
  (Nat.coprime_primes (witness1_prime h) (witness0_prime h)).mpr
    (witnesses_distinct h)

theorem prime_unit_ge_anchor (h : Cell N q) {l : ℕ} (hl : l.Prime)
    (hlN : l.Coprime N) : anchor N ≤ l := by
  by_contra hc
  exact (hl.coprime_iff_not_dvd.mp hlN)
    ((anchor_spec h).2.2.2 l hl (by omega))

theorem resources_coprime (h : Cell N q) :
    (resource1 N q).Coprime (resource0 N q) := by
  apply Nat.coprime_of_dvd
  intro l hl hl1 hl0
  have hlN := Nat.Coprime.of_dvd_left hl1 (resource1_unit h)
  have hge := prime_unit_ge_anchor h hl hlN
  have hm1 : q ≡ N [MOD l] :=
    (Nat.modEq_iff_dvd' (q_lt_N h).le).mpr hl1
  have hm0 : anchor N * q ≡ N [MOD l] :=
    (Nat.modEq_iff_dvd' h.anchor_mul_q_lt.le).mpr hl0
  have hm : N ≡ anchor N * N [MOD l] :=
    hm0.symm.trans (hm1.mul_left (anchor N))
  have hle : N ≤ anchor N * N := by nlinarith [anchor_three h]
  have hd : l ∣ (anchor N - 1) * N := by
    have ht := (Nat.modEq_iff_dvd' hle).mp hm
    simpa only [Nat.sub_mul, one_mul] using ht
  have hd' := hlN.dvd_of_dvd_mul_right hd
  have hpos : 0 < anchor N - 1 := by have := anchor_three h; omega
  have := Nat.le_of_dvd hpos hd'
  omega

theorem anchor_resource0_coprime (h : Cell N q) :
    (anchor N).Coprime (resource0 N q) := by
  apply (anchor_spec h).1.coprime_iff_not_dvd.mpr
  intro hd
  have hadd := dvd_add hd (dvd_mul_right (anchor N) q)
  have hn : anchor N ∣ N := by
    simpa only [resource0, Nat.sub_add_cancel h.anchor_mul_q_lt.le] using hadd
  exact (anchor_spec h).2.2.1 hn

theorem anchor_witness0_coprime (h : Cell N q) :
    (anchor N).Coprime (witness0 N q) :=
  (Nat.coprime_primes (anchor_spec h).1 (witness0_prime h)).mpr
    (witness0_ne_anchor h).symm

theorem modulus_pos (h : Cell N q) : 0 < modulus N q :=
  Nat.mul_pos (witness1_prime h).pos (witness0_prime h).pos

theorem representative_lt (h : Cell N q) : representative N q < modulus N q :=
  Nat.mod_lt _ (modulus_pos h)

theorem representative_le : representative N q ≤ q := Nat.mod_le _ _

theorem progression_identity :
    q = representative N q + modulus N q * progressionIndex N q := by
  exact (Nat.mod_add_div _ _).symm

theorem representative_mod_witness1 (h : Cell N q) :
    representative N q ≡ N [MOD witness1 N q] := by
  exact ((Nat.mod_modEq q (modulus N q)).of_dvd
    (dvd_mul_right (witness1 N q) (witness0 N q))).trans (q_mod_witness1 h)

theorem representative_anchor_mod_witness0 (h : Cell N q) :
    anchor N * representative N q ≡ N [MOD witness0 N q] := by
  exact (((Nat.mod_modEq q (modulus N q)).of_dvd
    (dvd_mul_left (witness0 N q) (witness1 N q))).mul_left (anchor N)).trans
      (anchor_q_mod_witness0 h)

theorem representative_is_actual_CRT (h : Cell N q) :
    representative N q =
      (Nat.chineseRemainder (witnesses_coprime h) N q : ℕ) := by
  have hAq : representative N q ≡ q [MOD witness0 N q] :=
    (Nat.mod_modEq q (modulus N q)).of_dvd
      (dvd_mul_left (witness0 N q) (witness1 N q))
  have hcong := Nat.chineseRemainder_modEq_unique (witnesses_coprime h)
    (representative_mod_witness1 h) hAq
  exact hcong.eq_of_lt_of_lt (representative_lt h)
    (Nat.chineseRemainder_lt_mul (witnesses_coprime h) N q
      (witness1_prime h).ne_zero (witness0_prime h).ne_zero)

theorem representative_unique_linear_CRT (h : Cell N q) {B : ℕ}
    (hB : B < modulus N q) (h1 : B ≡ N [MOD witness1 N q])
    (h0 : anchor N * B ≡ N [MOD witness0 N q]) : B = representative N q := by
  have hm1 := h1.trans (representative_mod_witness1 h).symm
  have hm0p := h0.trans (representative_anchor_mod_witness0 h).symm
  have hm0 := Nat.ModEq.cancel_left_of_coprime (anchor_witness0_coprime h).symm hm0p
  have hm := (Nat.modEq_and_modEq_iff_modEq_mul (witnesses_coprime h)).mp ⟨hm1, hm0⟩
  exact hm.eq_of_lt_of_lt hB (representative_lt h)

theorem distinct_prime_product_not_primePow {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) : ¬ IsPrimePow (p * r) := by
  intro hpow
  obtain ⟨s, k, hs, _, hsk⟩ := (isPrimePow_nat_iff _).mp hpow
  have hps : p ∣ s ^ k := by rw [hsk]; exact dvd_mul_right p r
  have hrs : r ∣ s ^ k := by rw [hsk]; exact dvd_mul_left r p
  exact hne ((Nat.prime_eq_prime_of_dvd_pow hp hs hps).trans
    (Nat.prime_eq_prime_of_dvd_pow hr hs hrs).symm)

theorem anchor_q_rawLambda_zero (h : Cell N q) :
    ArithmeticFunction.vonMangoldt (anchor N * q) = 0 := by
  exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    (distinct_prime_product_not_primePow (anchor_spec h).1 h.q_prime
      (ne_of_lt h.anchor_lt_q))

theorem reciprocal_axis1_prime (h : Cell N q) : (N - resource1 N q).Prime := by
  simpa only [resource1, Nat.sub_sub_self (q_lt_N h).le] using h.q_prime

theorem reciprocal_axis0_rawLambda_zero (h : Cell N q) :
    ArithmeticFunction.vonMangoldt (N - resource0 N q) = 0 := by
  simpa only [resource0, Nat.sub_sub_self h.anchor_mul_q_lt.le] using
    anchor_q_rawLambda_zero h

theorem reciprocal_axis0_theta_zero (h : Cell N q) :
    GoldbachRound11.theta N (N - resource0 N q) = 0 := by
  have hnp : ¬ (anchor N * q).Prime := by
    intro hp
    exact distinct_prime_product_not_primePow (anchor_spec h).1 h.q_prime
      (ne_of_lt h.anchor_lt_q) hp.isPrimePow
  simp only [resource0, Nat.sub_sub_self h.anchor_mul_q_lt.le,
    GoldbachRound11.theta, GoldbachRound11.primeIncidence]
  simp [hnp]

theorem resource1_injective (N : ℕ) :
    Set.InjOn (resource1 N) {q | q ≤ N} := by
  intro q hq r hr heq
  dsimp only [Set.mem_setOf_eq] at hq hr
  dsimp only [resource1] at heq
  omega

theorem label_union_card_le {ι : Type*} [DecidableEq ι] (labels : Finset ι)
    (physicalVertex : ι → ℕ) : (labels.image physicalVertex).card ≤ labels.card :=
  Finset.card_image_le

#print axioms anchor
#print axioms resource1
#print axioms resource0
#print axioms witness1
#print axioms witness0
#print axioms quotient1
#print axioms quotient0
#print axioms modulus
#print axioms representative
#print axioms progressionIndex
#print axioms Cell
#print axioms anchor_spec
#print axioms anchor_three
#print axioms anchor_unit
#print axioms q_lt_N
#print axioms resource1_unit
#print axioms resource0_unit
#print axioms witness1_prime
#print axioms witness0_prime
#print axioms witness1_dvd
#print axioms witness0_dvd
#print axioms witness1_unit
#print axioms witness0_unit
#print axioms witness1_ge_anchor
#print axioms witness0_ge_anchor
#print axioms resource1_factorization
#print axioms resource0_factorization
#print axioms q_mod_witness1
#print axioms anchor_q_mod_witness0
#print axioms witness0_ne_anchor
#print axioms witnesses_distinct
#print axioms witnesses_coprime
#print axioms prime_unit_ge_anchor
#print axioms resources_coprime
#print axioms anchor_resource0_coprime
#print axioms anchor_witness0_coprime
#print axioms modulus_pos
#print axioms representative_lt
#print axioms representative_le
#print axioms progression_identity
#print axioms representative_mod_witness1
#print axioms representative_anchor_mod_witness0
#print axioms representative_is_actual_CRT
#print axioms representative_unique_linear_CRT
#print axioms distinct_prime_product_not_primePow
#print axioms anchor_q_rawLambda_zero
#print axioms reciprocal_axis1_prime
#print axioms reciprocal_axis0_rawLambda_zero
#print axioms reciprocal_axis0_theta_zero
#print axioms resource1_injective
#print axioms label_union_card_le

end
end GoldbachRound18.DoubleExtraction
