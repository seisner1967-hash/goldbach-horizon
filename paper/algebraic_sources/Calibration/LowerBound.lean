import Mathlib.Algebra.Group.ForwardDiff
import Calibration.C1
import AlgebraicGoldbach.Soundness
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace AlgebraicGoldbach.LowerBound

open Finset Function

/-- A product of `k` successive positive factors when `n+k <= t`. -/
def falling (t n k : ℕ) : ℚ := ∏ j ∈ range k, ((t : ℚ) - (n + j : ℕ))

lemma falling_ne_zero {t n k : ℕ} (h : n + k ≤ t) : falling t n k ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro j hj
  have hj' := mem_range.mp hj
  have hlt : n + j < t := by omega
  have hcast : ((n + j : ℕ) : ℚ) < (t : ℚ) := by exact_mod_cast hlt
  exact sub_ne_zero.mpr (ne_of_gt hcast)

lemma falling_back (t n k : ℕ) :
    falling t n (k + 1) = falling t n k * ((t : ℚ) - (n + k : ℕ)) := by
  exact prod_range_succ _ _

lemma falling_front (t n k : ℕ) :
    falling t n (k + 1) = ((t : ℚ) - n) * falling t (n + 1) k := by
  unfold falling
  rw [prod_range_succ']
  have hprod : (∏ j ∈ range k, ((t : ℚ) - (n + (j + 1) : ℕ))) =
      ∏ j ∈ range k, ((t : ℚ) - (n + 1 + j : ℕ)) := by
    apply prod_congr rfl
    intro j _
    congr 2
    omega
  rw [hprod]
  simp only [Nat.add_zero]
  ring

/-- Exact finite difference of the inverse count residual, before it reaches a pole. -/
theorem inverse_count_fwdDiff (t k n : ℕ) (h : n + k < t) :
    (fwdDiff (1 : ℕ))^[k] (fun s : ℕ => 1 / ((s : ℚ) - t)) n =
      - (k.factorial : ℚ) / falling t n (k + 1) := by
  induction k generalizing n with
  | zero =>
      simp only [iterate_zero, id_eq, Nat.factorial_zero, Nat.cast_one]
      have hn : (n : ℚ) ≠ t := by exact_mod_cast (by omega : n ≠ t)
      norm_num [falling]
      field_simp [sub_ne_zero.mpr hn, sub_ne_zero.mpr hn.symm]
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      change (fwdDiff (1 : ℕ))^[k] (fun s : ℕ => 1 / ((s : ℚ) - t)) (n + 1) -
        (fwdDiff (1 : ℕ))^[k] (fun s : ℕ => 1 / ((s : ℚ) - t)) n = _
      rw [ih (n + 1) (by omega), ih n (by omega)]
      have hx := falling_ne_zero (t := t) (n := n) (k := k + 1) (by omega)
      have hy := falling_ne_zero (t := t) (n := n + 1) (k := k + 1) (by omega)
      have hz := falling_ne_zero (t := t) (n := n) (k := k + 2) (by omega)
      have hfront := falling_front t n (k + 1)
      have hback := falling_back t n (k + 1)
      have ha : ((t : ℚ) - n) / falling t n (k + 2) =
          1 / falling t (n + 1) (k + 1) := by
        apply (div_eq_div_iff hz hy).mpr
        simpa using hfront.symm
      have hb : ((t : ℚ) - (n + (k + 1) : ℕ)) / falling t n (k + 2) =
          1 / falling t n (k + 1) := by
        apply (div_eq_div_iff hz hx).mpr
        simpa [mul_comm] using hback.symm
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [show -(k.factorial : ℚ) / falling t (n + 1) (k + 1) =
        -(k.factorial : ℚ) * (1 / falling t (n + 1) (k + 1)) by ring]
      rw [show -(k.factorial : ℚ) / falling t n (k + 1) =
        -(k.factorial : ℚ) * (1 / falling t n (k + 1)) by ring]
      rw [← ha, ← hb]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- The top cube finite difference of the inverse cannot vanish. -/
theorem inverse_count_fwdDiff_ne_zero (t k : ℕ) (h : k < t) :
    (fwdDiff (1 : ℕ))^[k] (fun s : ℕ => 1 / ((s : ℚ) - t)) 0 ≠ 0 := by
  rw [inverse_count_fwdDiff t k 0 (by omega)]
  apply div_ne_zero
  · exact neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))
  · exact falling_ne_zero (by omega)







section Cube

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def boolValue (b : Bool) : ℚ := if b then 1 else 0

def cubeWeight (b : σ → Bool) : ℚ := ∏ i, if b i then 1 else -1

def cubeContrast (f : (σ → ℚ) → ℚ) : ℚ :=
  ∑ b : σ → Bool, cubeWeight b * f (fun i => boolValue (b i))

lemma cubeContrast_monomial_zero (d : σ →₀ ℕ) (c : ℚ) (hd : ∃ i, d i = 0) :
    cubeContrast (fun x => MvPolynomial.eval x (MvPolynomial.monomial d c)) = 0 := by
  classical
  unfold cubeContrast
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_pow]
  have hterm : ∀ b : σ → Bool,
      cubeWeight b * (c * ∏ i, boolValue (b i) ^ d i) =
      c * ∏ i, ((if b i then (1 : ℚ) else -1) * boolValue (b i) ^ d i) := by
    intro b
    unfold cubeWeight
    rw [prod_mul_distrib]
    ring
  simp_rw [hterm]
  rw [← mul_sum]
  have hsum := Fintype.prod_sum (fun i (b : Bool) =>
    (if b then (1 : ℚ) else -1) * boolValue b ^ d i)
  rw [← hsum]
  obtain ⟨i, hi⟩ := hd
  have hzero : (∑ b : Bool, (if b then (1 : ℚ) else -1) * boolValue b ^ d i) = 0 := by
    rw [hi]
    norm_num [Fintype.sum_bool, boolValue]
  rw [prod_eq_zero (mem_univ i) hzero, mul_zero]

/-- Every polynomial of total degree below the number of Boolean variables has zero cube contrast. -/
theorem cubeContrast_eval_zero_of_totalDegree_lt (A : MvPolynomial σ ℚ)
    (hA : A.totalDegree < Fintype.card σ) :
    cubeContrast (fun x => MvPolynomial.eval x A) = 0 := by
  classical
  have hexpand := MvPolynomial.as_sum A
  rw [hexpand]
  unfold cubeContrast
  simp only [map_sum, mul_sum]
  rw [sum_comm]
  apply sum_eq_zero
  intro d hd
  have hmissing : ∃ i, d i = 0 := by
    obtain ⟨i, hi⟩ := MvPolynomial.exists_degree_lt A 1 (by simpa using hA) hd
    exact ⟨i, by omega⟩
  exact cubeContrast_monomial_zero d (MvPolynomial.coeff d A) hmissing





def indicatorBool (S : Finset σ) (i : σ) : Bool := decide (i ∈ S)

def cubeEquiv : Finset σ ≃ (σ → Bool) where
  toFun := indicatorBool
  invFun := fun b => univ.filter (fun i => b i = true)
  left_inv := by
    intro S
    ext i
    simp [indicatorBool]
  right_inv := by
    intro b
    funext i
    cases hb : b i <;> simp [indicatorBool, hb]

lemma cubeWeight_indicator (S : Finset σ) :
    cubeWeight (indicatorBool S) = (-1 : ℚ) ^ (Fintype.card σ - S.card) := by
  unfold cubeWeight indicatorBool
  simp only [decide_eq_true_eq]
  rw [prod_ite]
  have hs : (univ.filter (fun i : σ => i ∈ S)) = S := by ext i; simp
  have hc : (univ.filter (fun i : σ => i ∉ S)) = univ \ S := by ext i; simp
  rw [hs, hc]
  simp [card_sdiff (subset_univ S)]

lemma boolValue_indicator_sum (S : Finset σ) :
    (∑ i, boolValue (indicatorBool S i)) = (S.card : ℚ) := by
  simp [boolValue, indicatorBool]

/-- Cube contrast is the top forward difference for a function of Boolean Hamming weight. -/
theorem cubeContrast_cardinality (f : ℕ → ℚ) :
    (∑ b : σ → Bool, cubeWeight b * f (univ.filter (fun i => b i = true)).card) =
      (fwdDiff (1 : ℕ))^[Fintype.card σ] f 0 := by
  have hsum : (∑ S : Finset σ, (-1 : ℚ) ^ (Fintype.card σ - S.card) * f S.card) =
      ∑ b : σ → Bool, cubeWeight b * f (univ.filter (fun i => b i = true)).card := by
    apply Fintype.sum_equiv cubeEquiv
    intro S
    change _ = cubeWeight (indicatorBool S) * f _
    rw [cubeWeight_indicator]
    have hfilter : (univ.filter (fun i : σ => indicatorBool S i = true)) = S := by
      ext i
      simp [indicatorBool]
    change _ = (-1 : ℚ) ^ (Fintype.card σ - S.card) *
      f (univ.filter (fun i : σ => indicatorBool S i = true)).card
    rw [hfilter]
  rw [← hsum]
  rw [← powerset_univ]
  rw [sum_powerset_apply_card (fun k => (-1 : ℚ) ^ (Fintype.card σ - k) * f k)]
  rw [fwdDiff_iter_eq_sum_shift]
  simp only [card_univ, zero_add, smul_eq_mul, nsmul_eq_mul, mul_one,
    zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
  apply sum_congr rfl
  intro k _
  ring

/-- The exact nonzero top contrast of the inverse count polynomial on the cube. -/
theorem inverse_count_cubeContrast (t : ℕ) :
    cubeContrast (fun x : σ → ℚ => 1 / ((∑ i, x i) - t)) =
      (fwdDiff (1 : ℕ))^[Fintype.card σ] (fun s : ℕ => 1 / ((s : ℚ) - t)) 0 := by
  have hcount : ∀ b : σ → Bool,
      (∑ i, boolValue (b i)) = ((univ.filter (fun i => b i = true)).card : ℚ) := by
    intro b
    rw [natCast_card_filter]
    apply sum_congr rfl
    intro i _
    cases hb : b i <;> simp [boolValue, hb]
  unfold cubeContrast
  simp_rw [hcount]
  exact cubeContrast_cardinality (fun s : ℕ => 1 / ((s : ℚ) - t))

/-- Any rational polynomial inverse of the count residual on the Boolean cube has full degree. -/
theorem boolean_inverse_totalDegree_ge (A : MvPolynomial σ ℚ) (t : ℕ)
    (ht : Fintype.card σ < t)
    (hA : ∀ b : σ → Bool,
      MvPolynomial.eval (fun i => boolValue (b i)) A *
        ((∑ i, boolValue (b i)) - t) = 1) :
    Fintype.card σ ≤ A.totalDegree := by
  by_contra hlt
  have hzero := cubeContrast_eval_zero_of_totalDegree_lt A (by omega)
  have heval : ∀ b : σ → Bool,
      MvPolynomial.eval (fun i => boolValue (b i)) A =
        1 / ((∑ i, boolValue (b i)) - t) := by
    intro b
    have hn : (∑ i, boolValue (b i)) - (t : ℚ) ≠ 0 := by
      have hb : (∑ i, boolValue (b i)) ≤ (Fintype.card σ : ℚ) := by
        calc
          _ ≤ ∑ _ : σ, (1 : ℚ) := sum_le_sum (fun i _ => by cases b i <;> norm_num [boolValue])
          _ = _ := by simp
      have hcast : (Fintype.card σ : ℚ) < (t : ℚ) := by exact_mod_cast ht
      exact sub_ne_zero.mpr (ne_of_lt (lt_of_le_of_lt hb hcast))
    exact (eq_div_iff hn).mpr (hA b)
  unfold cubeContrast at hzero
  simp_rw [heval] at hzero
  change cubeContrast (fun x : σ → ℚ => 1 / ((∑ i, x i) - t)) = 0 at hzero
  rw [inverse_count_cubeContrast] at hzero
  exact inverse_count_fwdDiff_ne_zero t (Fintype.card σ) ht hzero

end Cube

/-- Substituting variables by linear-or-constant polynomials cannot raise total degree. -/
theorem totalDegree_substitution_le {σ τ : Type*} (A : MvPolynomial σ ℚ)
    (v : σ → MvPolynomial τ ℚ) (hv : ∀ i, (v i).totalDegree ≤ 1) :
    (MvPolynomial.eval₂ MvPolynomial.C v A).totalDegree ≤ A.totalDegree := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum A]
  rw [MvPolynomial.eval₂_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [MvPolynomial.eval₂_monomial]
  calc
    _ ≤ (MvPolynomial.C (MvPolynomial.coeff d A)).totalDegree +
        (d.prod (fun i e => v i ^ e)).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (d.prod (fun i e => v i ^ e)).totalDegree := by simp
    _ ≤ ∑ i ∈ d.support, (v i ^ d i).totalDegree := MvPolynomial.totalDegree_finset_prod _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply sum_le_sum
      intro i _
      exact (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hv i))
    _ ≤ A.totalDegree := MvPolynomial.le_totalDegree hd

/-- The degree of the graded lex leading monomial is the total degree. -/
theorem totalDegree_eq_degLex_degree {σ : Type*} [Fintype σ] [LinearOrder σ]
    (A : MvPolynomial σ ℚ) :
    A.totalDegree = ((MonomialOrder.degLex : MonomialOrder σ).degree A).degree := by
  classical
  by_cases hA : A = 0
  · simp [hA]
  apply le_antisymm
  · unfold MvPolynomial.totalDegree
    apply Finset.sup_le
    intro d hd
    have horder := (MonomialOrder.degLex : MonomialOrder σ).le_degree hd
    exact Finsupp.DegLex.monotone_degree (MonomialOrder.degLex_le_iff.mp horder)
  · apply MvPolynomial.le_totalDegree
    apply MvPolynomial.mem_support_iff.mpr
    exact (MonomialOrder.coeff_degree_ne_zero_iff
      (m := (MonomialOrder.degLex : MonomialOrder σ))).mpr hA

/-- Total degree is additive under multiplication of nonzero rational polynomials. -/
theorem totalDegree_mul_eq {σ : Type*} [Fintype σ] [LinearOrder σ]
    (A B : MvPolynomial σ ℚ) (hA : A ≠ 0) (hB : B ≠ 0) :
    (A * B).totalDegree = A.totalDegree + B.totalDegree := by
  rw [totalDegree_eq_degLex_degree, totalDegree_eq_degLex_degree A,
    totalDegree_eq_degLex_degree B,
    (MonomialOrder.degLex : MonomialOrder σ).degree_mul hA hB, Finsupp.degree_add]

namespace Restriction

noncomputable section

open MvPolynomial Calibration

abbrev Vars (N : ℕ) := {i : Fin (N + 1) // i.val ∈ maximumSupport N}

noncomputable def supportEquiv (N : ℕ) : Vars N ≃ {p : ℕ // p ∈ maximumSupport N} where
  toFun := fun i => ⟨i.val.val, i.property⟩
  invFun := fun p => ⟨⟨p.val, Nat.lt_succ_of_le
    ((mem_primes.mp ((maximumSupport_independent N).1 p.property)).1)⟩, p.property⟩
  left_inv := by intro i; rfl
  right_inv := by intro p; rfl

lemma vars_card (N : ℕ) : Fintype.card (Vars N) = pi N - r N := by
  rw [Fintype.card_congr (supportEquiv N), Fintype.card_coe, maximumSupport_card]

noncomputable def restrictedVariable (N : ℕ) (i : Fin (N + 1)) : MvPolynomial (Vars N) ℚ :=
  if h : i.val ∈ maximumSupport N then X ⟨i, h⟩ else 0

noncomputable def polynomial (N : ℕ) (A : R N ℚ) : MvPolynomial (Vars N) ℚ :=
  eval₂ C (restrictedVariable N) A

noncomputable def point (N : ℕ) (b : Vars N → Bool) (i : Fin (N + 1)) : ℚ :=
  if h : i.val ∈ maximumSupport N then boolValue (b ⟨i, h⟩) else 0

lemma polynomial_degree_le (N : ℕ) (A : R N ℚ) :
    (polynomial N A).totalDegree ≤ A.totalDegree := by
  apply totalDegree_substitution_le
  intro i
  unfold restrictedVariable
  split_ifs <;> simp

lemma polynomial_eval (N : ℕ) (A : R N ℚ) (b : Vars N → Bool) :
    eval (fun i => boolValue (b i)) (polynomial N A) = eval (point N b) A := by
  rw [polynomial, eval_eval₂]
  congr 1
  · ext q
    simp
  · funext i
    unfold point restrictedVariable
    split_ifs <;> simp

lemma point_boolean (N : ℕ) (b : Vars N → Bool) (i : Fin (N + 1)) :
    point N b i ^ 2 - point N b i = 0 := by
  unfold point
  split_ifs with h
  · cases b ⟨i, h⟩ <;> norm_num [boolValue]
  · norm_num

lemma point_nonprime_zero (N : ℕ) (b : Vars N → Bool) (i : Fin (N + 1))
    (hi : ¬ Nat.Prime i.val) : point N b i = 0 := by
  have hnot : i.val ∉ maximumSupport N := by
    intro hmem
    exact hi (mem_primes.mp ((maximumSupport_independent N).1 hmem)).2
  simp [point, hnot]

lemma point_g_zero (N : ℕ) (b : Vars N → Bool) : eval (point N b) (AlgebraicGoldbach.g N ℚ) = 0 := by
  simp only [AlgebraicGoldbach.g, map_sum, map_mul, eval_X]
  apply sum_eq_zero
  intro i _
  by_cases hi : i.val ∈ maximumSupport N
  · have hq := (maximumSupport_independent N).2 i.val hi
    have hq' : (complement N i).val ∉ maximumSupport N := hq
    simp [point, hq']
  · simp [point, hi]

lemma point_sum (N : ℕ) (b : Vars N → Bool) :
    (∑ i : Fin (N + 1), point N b i) = ∑ i : Vars N, boolValue (b i) := by
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (fun i : Fin (N + 1) => i.val ∈ maximumSupport N) (point N b)
  have hpos : (∑ i : {i : Fin (N + 1) // i.val ∈ maximumSupport N}, point N b i) =
      ∑ i : Vars N, boolValue (b i) := by
    apply sum_congr rfl
    intro i _
    simp [point, i.property]
  have hneg : (∑ i : {i : Fin (N + 1) // i.val ∉ maximumSupport N}, point N b i) = 0 := by
    apply sum_eq_zero
    intro i _
    simp [point, i.property]
  rw [hpos, hneg, add_zero] at hsum
  exact hsum.symm

/-- Count residual at the full prime cardinality. -/
def countConstraint (N : ℕ) : R N ℚ := (∑ i : Fin (N + 1), X i) - C (pi N : ℚ)

/-- Composite zero constraints with the declared coarse zeros at zero and one. -/
def nonprimeConstraint (N : ℕ) (i : Fin (N + 1)) : R N ℚ :=
  if Nat.Prime i.val then 0 else X i

/-- The actual polynomial identity for the full-count calibration family. -/
def DpiCertificate (N : ℕ) (A B : R N ℚ)
    (U C : Fin (N + 1) → R N ℚ) : Prop :=
  1 = A * countConstraint N +
    (∑ i, U i * booleanConstraint i) +
    (∑ i, C i * nonprimeConstraint N i) + B * AlgebraicGoldbach.g N ℚ

/-- A full-count certificate restricts to an inverse of the count residual on the maximal independent cube. -/
theorem certificate_inverse (N : ℕ) (A B : R N ℚ)
    (U C : Fin (N + 1) → R N ℚ) (hcert : DpiCertificate N A B U C) :
    ∀ b : Vars N → Bool,
      eval (fun i => boolValue (b i)) (polynomial N A) *
        ((∑ i, boolValue (b i)) - (pi N : ℚ)) = 1 := by
  intro b
  have h := congrArg (MvPolynomial.eval (point N b)) hcert
  have hnonprime : ∀ i : Fin (N + 1), eval (point N b) (nonprimeConstraint N i) = 0 := by
    intro i
    by_cases hi : Nat.Prime i.val
    · simp [nonprimeConstraint, hi]
    · simp [nonprimeConstraint, hi, point_nonprime_zero N b i hi]
  have hboolean : ∀ i : Fin (N + 1), eval (point N b) (booleanConstraint i) = 0 := by
    intro i
    rw [booleanConstraint_eval]
    exact point_boolean N b i
  simp only [map_one, map_add, map_mul, map_sum] at h
  simp only [hboolean, hnonprime, point_g_zero N b, mul_zero, sum_const_zero,
    add_zero] at h
  rw [countConstraint] at h
  simp only [map_sub, map_sum, eval_X, eval_C, point_sum N b] at h
  rw [polynomial_eval]
  exact h.symm

/-- Existence of a certificate itself guarantees that the restricted target count exceeds cube dimension. -/
theorem certificate_count_gt_vars (N : ℕ) (A B : R N ℚ)
    (U C : Fin (N + 1) → R N ℚ) (hcert : DpiCertificate N A B U C) :
    Fintype.card (Vars N) < pi N := by
  have hle : Fintype.card (Vars N) ≤ pi N := by rw [vars_card]; omega
  by_contra hnot
  have heq : Fintype.card (Vars N) = pi N := by omega
  have h := certificate_inverse N A B U C hcert (fun _ => true)
  simp only [boolValue, Bool.true_eq_false, Bool.false_eq_true, ite_true, sum_const,
    card_univ, nsmul_eq_mul, mul_one] at h
  rw [heq, sub_self, mul_zero] at h
  norm_num at h

/-- A certificate forces the count multiplier to be nonzero. -/
theorem certificate_multiplier_ne_zero (N : ℕ) (A B : R N ℚ)
    (U C : Fin (N + 1) → R N ℚ) (hcert : DpiCertificate N A B U C) : A ≠ 0 := by
  intro hA
  have h := certificate_inverse N A B U C hcert (fun _ => false)
  rw [hA] at h
  simp [polynomial] at h

/-- Every full-count certificate has count multiplier degree at least `pi(N)-r(N)`. -/
theorem Dpi_multiplier_degree_lower_bound (N : ℕ)
    (A B : R N ℚ) (U C : Fin (N + 1) → R N ℚ)
    (hcert : DpiCertificate N A B U C) :
    pi N - r N ≤ A.totalDegree := by
  have ht := certificate_count_gt_vars N A B U C hcert
  have hdegree := boolean_inverse_totalDegree_ge (polynomial N A) (pi N) ht
    (certificate_inverse N A B U C hcert)
  rw [vars_card] at hdegree
  exact hdegree.trans (polynomial_degree_le N A)

lemma countConstraint_coeff (N : ℕ) :
    coeff (Finsupp.single (0 : Fin (N + 1)) 1) (countConstraint N) = (1 : ℚ) := by
  have hsingle : (0 : Fin (N + 1) →₀ ℕ) ≠ Finsupp.single 0 1 := by
    intro h
    have h0 := congrArg (fun d : Fin (N + 1) →₀ ℕ => d 0) h
    simp at h0
  simp only [countConstraint, coeff_sub, coeff_sum, coeff_C, coeff_X']
  simp [Finsupp.single_eq_single_iff, hsingle]

lemma countConstraint_ne_zero (N : ℕ) : countConstraint N ≠ 0 := by
  intro h
  have hc := countConstraint_coeff N
  rw [h, coeff_zero] at hc
  norm_num at hc

lemma countConstraint_totalDegree (N : ℕ) : (countConstraint N).totalDegree = 1 := by
  apply le_antisymm
  · unfold countConstraint
    apply (totalDegree_sub_C_le _ _).trans
    apply totalDegree_finsetSum_le
    intro i _
    simp
  · have hsupport : Finsupp.single (0 : Fin (N + 1)) 1 ∈ (countConstraint N).support := by
      apply mem_support_iff.mpr
      rw [countConstraint_coeff]
      norm_num
    simpa using MvPolynomial.le_totalDegree hsupport

/-- The standard degree of the count summand is at least `pi(N)-r(N)+1`. -/
theorem Dpi_standard_degree_lower_bound (N : ℕ)
    (A B : R N ℚ) (U C : Fin (N + 1) → R N ℚ)
    (hcert : DpiCertificate N A B U C) :
    pi N - r N + 1 ≤ (A * countConstraint N).totalDegree := by
  rw [totalDegree_mul_eq A (countConstraint N)
    (certificate_multiplier_ne_zero N A B U C hcert) (countConstraint_ne_zero N),
    countConstraint_totalDegree]
  exact Nat.add_le_add_right (Dpi_multiplier_degree_lower_bound N A B U C hcert) 1

/-- Any standard certificate degree bound must exceed the independent-cube dimension. -/
theorem Dpi_certificate_degree_bound (N d : ℕ)
    (A B : R N ℚ) (U C : Fin (N + 1) → R N ℚ)
    (hcert : DpiCertificate N A B U C)
    (hdegree : (A * countConstraint N).totalDegree ≤ d) :
    pi N - r N + 1 ≤ d :=
  (Dpi_standard_degree_lower_bound N A B U C hcert).trans hdegree

end

end Restriction

#print axioms inverse_count_fwdDiff
#print axioms boolean_inverse_totalDegree_ge
#print axioms Restriction.Dpi_multiplier_degree_lower_bound
#print axioms Restriction.Dpi_standard_degree_lower_bound
#print axioms Restriction.Dpi_certificate_degree_bound

end AlgebraicGoldbach.LowerBound
