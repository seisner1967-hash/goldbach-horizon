import DoubleExtractionArithmetic
import FourFormRoots
import SelbergFourForms

namespace GoldbachRound18.DoubleExtraction

noncomputable section

def constant1 (N q : ℕ) : ℤ :=
  ((N - representative N q) / witness1 N q : ℕ)
def constant0 (N q : ℕ) : ℤ :=
  ((N - anchor N * representative N q) / witness0 N q : ℕ)

def slope (N e q : ℕ) : Fin 4 → ℤ :=
  ![(modulus N q : ℤ), -(e : ℤ) * modulus N q,
    -(witness0 N q : ℤ), -(anchor N : ℤ) * witness1 N q]

def constant (N e q : ℕ) : Fin 4 → ℤ :=
  ![(representative N q : ℤ), (N : ℤ) - e * representative N q,
    constant1 N q, constant0 N q]

def affine (N e q : ℕ) (i : Fin 4) (x : ℤ) : ℤ :=
  slope N e q i * x + constant N e q i

def dividedForm (N e q : ℕ) (x : ℤ) : ℤ :=
  affine N e q 0 x * affine N e q 1 x *
    affine N e q 2 x * affine N e q 3 x

def determinant (N e q : ℕ) (i j : Fin 4) : ℤ :=
  slope N e q i * constant N e q j - slope N e q j * constant N e q i

def slopeProduct (N e q : ℕ) : ℤ := ∏ i : Fin 4, slope N e q i

def determinantProduct (N e q : ℕ) : ℤ :=
  determinant N e q 0 1 * determinant N e q 0 2 * determinant N e q 0 3 *
  determinant N e q 1 2 * determinant N e q 1 3 * determinant N e q 2 3

def signedDelta (N e q : ℕ) : ℤ := slopeProduct N e q * determinantProduct N e q
def actualDelta (N e q : ℕ) : ℕ := (signedDelta N e q).natAbs

variable {N e q : ℕ}

theorem representative_le_N (h : Cell N q) : representative N q ≤ N :=
  representative_le.trans (q_lt_N h).le

theorem anchor_representative_le_N (h : Cell N q) :
    anchor N * representative N q ≤ N :=
  (Nat.mul_le_mul_left (anchor N) representative_le).trans h.anchor_mul_q_lt.le

theorem constant1_identity (h : Cell N q) :
    (witness1 N q : ℤ) * constant1 N q = (N : ℤ) - representative N q := by
  have hd : witness1 N q ∣ N - representative N q :=
    (Nat.modEq_iff_dvd' (representative_le_N h)).mp
      (representative_mod_witness1 h)
  have ht := Nat.mul_div_cancel' hd
  have hz : (witness1 N q : ℤ) *
      ((N - representative N q) / witness1 N q : ℕ) = (N - representative N q : ℕ) := by
    exact_mod_cast ht
  simpa only [constant1, Int.ofNat_sub (representative_le_N h)] using hz

theorem constant0_identity (h : Cell N q) :
    (witness0 N q : ℤ) * constant0 N q =
      (N : ℤ) - (anchor N : ℤ) * representative N q := by
  have hd : witness0 N q ∣ N - anchor N * representative N q :=
    (Nat.modEq_iff_dvd' (anchor_representative_le_N h)).mp
      (representative_anchor_mod_witness0 h)
  have ht := Nat.mul_div_cancel' hd
  have hz : (witness0 N q : ℤ) *
      ((N - anchor N * representative N q) / witness0 N q : ℕ) =
        (N - anchor N * representative N q : ℕ) := by exact_mod_cast ht
  simpa only [constant0, Int.ofNat_sub (anchor_representative_le_N h),
    Nat.cast_mul] using hz

theorem affine_q_at_index : affine N e q 0 (progressionIndex N q) = q := by
  have ht := progression_identity (N := N) (q := q)
  dsimp only [affine, slope, constant]
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have hz : (representative N q : ℤ) + (modulus N q : ℤ) * progressionIndex N q = q := by exact_mod_cast ht.symm
  simpa only [add_comm] using hz

theorem affine_target_at_index : affine N e q 1 (progressionIndex N q) =
    (N : ℤ) - (e : ℤ) * q := by
  have hz : (q : ℤ) = representative N q +
      (modulus N q : ℤ) * progressionIndex N q := by exact_mod_cast progression_identity
  simp only [affine, slope, constant, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [hz]
  ring

theorem affine_resource1_at_index (h : Cell N q) :
    affine N e q 2 (progressionIndex N q) = quotient1 N q := by
  have h1 := constant1_identity h
  have hf : (witness1 N q : ℤ) * quotient1 N q = (N - q : ℕ) := by
    have hh := resource1_factorization (N := N) (q := q)
    exact_mod_cast (show witness1 N q * quotient1 N q = N - q from hh)
  rw [Int.ofNat_sub (q_lt_N h).le] at hf
  have hq : (q : ℤ) = representative N q +
      (modulus N q : ℤ) * progressionIndex N q := by exact_mod_cast progression_identity
  have hp : (witness1 N q : ℤ) ≠ 0 := by exact_mod_cast (witness1_prime h).ne_zero
  apply (mul_left_cancel₀ hp)
  simp only [affine, slope, constant, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [modulus, Nat.cast_mul] at hq
  linear_combination h1 - hf + hq

theorem affine_resource0_at_index (h : Cell N q) :
    affine N e q 3 (progressionIndex N q) = quotient0 N q := by
  have h0 := constant0_identity h
  have hf : (witness0 N q : ℤ) * quotient0 N q =
      (N - anchor N * q : ℕ) := by exact_mod_cast resource0_factorization
  rw [Int.ofNat_sub h.anchor_mul_q_lt.le, Nat.cast_mul] at hf
  have hq : (q : ℤ) = representative N q +
      (modulus N q : ℤ) * progressionIndex N q := by exact_mod_cast progression_identity
  have hp : (witness0 N q : ℤ) ≠ 0 := by exact_mod_cast (witness0_prime h).ne_zero
  apply (mul_left_cancel₀ hp)
  simp only [affine, slope, constant, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [modulus, Nat.cast_mul] at hq
  linear_combination h0 - hf + (anchor N : ℤ) * hq

theorem dividedForm_at_index (h : Cell N q) :
    dividedForm N e q (progressionIndex N q) =
      (q : ℤ) * ((N : ℤ) - (e : ℤ) * q) * quotient1 N q * quotient0 N q := by
  simp only [dividedForm, affine_q_at_index, affine_target_at_index,
    affine_resource1_at_index h, affine_resource0_at_index h]

theorem determinant01 : determinant N e q 0 1 = (N : ℤ) * modulus N q := by
  simp only [determinant, slope, constant, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem determinant02 (h : Cell N q) :
    determinant N e q 0 2 = (N : ℤ) * witness0 N q := by
  have h1 := constant1_identity h
  simp only [determinant, slope, constant, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    modulus, Nat.cast_mul]
  linear_combination (witness0 N q : ℤ) * h1

theorem determinant03 (h : Cell N q) :
    determinant N e q 0 3 = (N : ℤ) * witness1 N q := by
  have h0 := constant0_identity h
  simp only [determinant, slope, constant, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    modulus, Nat.cast_mul]
  linear_combination (witness1 N q : ℤ) * h0

theorem determinant12 (h : Cell N q) :
    determinant N e q 1 2 = (N : ℤ) * witness0 N q * (1 - (e : ℤ)) := by
  have h1 := constant1_identity h
  simp only [determinant, slope, constant, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, modulus, Nat.cast_mul]
  linear_combination -(e : ℤ) * (witness0 N q : ℤ) * h1

theorem determinant13 (h : Cell N q) :
    determinant N e q 1 3 = (N : ℤ) * witness1 N q * ((anchor N : ℤ) - e) := by
  have h0 := constant0_identity h
  simp only [determinant, slope, constant, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, modulus, Nat.cast_mul]
  linear_combination -(e : ℤ) * (witness1 N q : ℤ) * h0

theorem determinant23 (h : Cell N q) :
    determinant N e q 2 3 = (N : ℤ) * ((anchor N : ℤ) - 1) := by
  have h1 := constant1_identity h
  have h0 := constant0_identity h
  simp only [determinant, slope, constant, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (anchor N : ℤ) * h1 - h0

theorem slopeProduct_eq : slopeProduct N e q =
    -(e : ℤ) * anchor N * (modulus N q : ℤ)^3 := by
  simp [slopeProduct, slope, Fin.prod_univ_succ, modulus]
  ring

theorem signedDelta_eq (h : Cell N q) : signedDelta N e q =
    -(N : ℤ)^6 * e * anchor N * (modulus N q : ℤ)^6 *
      ((e : ℤ) - 1) * ((e : ℤ) - anchor N) * ((anchor N : ℤ) - 1) := by
  simp only [signedDelta, determinantProduct, slopeProduct_eq, determinant01,
    determinant02 h, determinant03 h, determinant12 h, determinant13 h,
    determinant23 h, modulus, Nat.cast_mul]
  ring

theorem actualDelta_eq (h : Cell N q) (he : anchor N < e) : actualDelta N e q =
    N^6 * e * anchor N * (modulus N q)^6 * (e - 1) * (e - anchor N) * (anchor N - 1) := by
  have hp1 : 1 ≤ anchor N := by have := anchor_three h; omega
  have he1 : 1 ≤ e := by omega
  have hs : signedDelta N e q =
      -((N^6 * e * anchor N * (modulus N q)^6 *
        (e - 1) * (e - anchor N) * (anchor N - 1) : ℕ) : ℤ) := by
    rw [signedDelta_eq h]
    push_cast [Nat.cast_sub he1, Nat.cast_sub he.le, Nat.cast_sub hp1]
    ring
  simp only [actualDelta, hs, Int.natAbs_neg, Int.natAbs_ofNat]

theorem actualDelta_positive (h : Cell N q) (he : anchor N < e) : 0 < actualDelta N e q := by
  rw [actualDelta_eq h he]
  have hN := Nat.pos_of_ne_zero h.N_ne_zero
  have hp := anchor_three h
  have hL := modulus_pos h
  have h1 : 0 < e - 1 := by omega
  have he0 : 0 < e := by omega
  have heA : 0 < e - anchor N := Nat.sub_pos_of_lt he
  have hp1 : 0 < anchor N - 1 := by omega
  positivity

theorem prime_divisors_actualDelta (h : Cell N q) (he : anchor N < e)
    {p : ℕ} (hp : p.Prime) :
    p ∣ actualDelta N e q ↔ p ∣ GoldbachRound17.FourFormRoots.natDelta N e (anchor N) * modulus N q := by
  have hpN : p ∣ N^6 ↔ p ∣ N := ⟨hp.dvd_of_dvd_pow, fun h => dvd_pow h (by omega)⟩
  have hpL : p ∣ (modulus N q)^6 ↔ p ∣ modulus N q :=
    ⟨hp.dvd_of_dvd_pow, fun h => dvd_pow h (by omega)⟩
  rw [actualDelta_eq h he]
  simp only [GoldbachRound17.FourFormRoots.natDelta, hp.dvd_mul, hpN, hpL]
  tauto

#print axioms constant1
#print axioms constant0
#print axioms slope
#print axioms constant
#print axioms affine
#print axioms dividedForm
#print axioms determinant
#print axioms slopeProduct
#print axioms determinantProduct
#print axioms signedDelta
#print axioms actualDelta
#print axioms representative_le_N
#print axioms anchor_representative_le_N
#print axioms constant1_identity
#print axioms constant0_identity
#print axioms affine_q_at_index
#print axioms affine_target_at_index
#print axioms affine_resource1_at_index
#print axioms affine_resource0_at_index
#print axioms dividedForm_at_index
#print axioms determinant01
#print axioms determinant02
#print axioms determinant03
#print axioms determinant12
#print axioms determinant13
#print axioms determinant23
#print axioms slopeProduct_eq
#print axioms signedDelta_eq
#print axioms actualDelta_eq
#print axioms actualDelta_positive
#print axioms prime_divisors_actualDelta

end
end GoldbachRound18.DoubleExtraction
