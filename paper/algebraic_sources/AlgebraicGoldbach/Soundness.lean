import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Ring.Basic

/-!
The certificate soundness theorem is conditional on the supplied polynomial
identity and on the genuine prime point satisfying every supplied constraint.
It does not construct that identity or establish those constraints.
-/

namespace AlgebraicGoldbach

noncomputable section

open scoped BigOperators
open MvPolynomial

abbrev R (N : ℕ) (K : Type*) [CommSemiring K] := MvPolynomial (Fin (N + 1)) K

def complement (N : ℕ) (i : Fin (N + 1)) : Fin (N + 1) :=
  ⟨N - i.val, by omega⟩

def g (N : ℕ) (K : Type*) [CommSemiring K] : R N K :=
  ∑ i : Fin (N + 1), X i * X (complement N i)

def booleanConstraint {N : ℕ} {K : Type*} [CommRing K] (i : Fin (N + 1)) : R N K :=
  (X i : R N K) ^ 2 - X i

/- The only unconditional coarse constraints used here are exactly those allowed
in the mission. This family contains no SIEVE constraint. -/
def coarseAllowed {N : ℕ} (i : Fin (N + 1)) : Prop :=
  i.val = 0 ∨ i.val = 1 ∨ (Even i.val ∧ 2 < i.val)

def coarseConstraint {N : ℕ} {K : Type*} [CommRing K] (i : Fin (N + 1)) : R N K :=
  by classical exact if coarseAllowed i then X i else 0

def primeIndicator (n : ℕ) : ℕ := if n.Prime then 1 else 0

def primePoint (N : ℕ) (K : Type*) [CommSemiring K] : Fin (N + 1) → K :=
  fun i => if i.val.Prime then 1 else 0

def goldbachCount (N : ℕ) : ℕ :=
  ∑ i : Fin (N + 1), primeIndicator i.val * primeIndicator (N - i.val)

def Certificate {N : ℕ} {K : Type*} [CommRing K] {ι : Type*} [Fintype ι]
    (F A : ι → R N K) (U : Fin (N + 1) → R N K) (B : R N K) : Prop :=
  1 = (∑ j, A j * F j) + (∑ i, U i * booleanConstraint i) + B * g N K

theorem booleanConstraint_eval {N : ℕ} {K : Type*} [CommRing K]
    (x : Fin (N + 1) → K) (i : Fin (N + 1)) :
    eval x (booleanConstraint i) = x i ^ 2 - x i := by
  simp [booleanConstraint]

theorem booleanConstraint_zero_iff {N : ℕ} {K : Type*} [CommRing K] [IsDomain K]
    (x : Fin (N + 1) → K) (i : Fin (N + 1)) :
    eval x (booleanConstraint i) = 0 ↔ x i = 0 ∨ x i = 1 := by
  rw [booleanConstraint_eval]
  constructor
  · intro hz
    have hm : x i * (x i - 1) = 0 := by
      calc
        x i * (x i - 1) = x i ^ 2 - x i := by ring
        _ = 0 := hz
    rcases mul_eq_zero.mp hm with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (h | h) <;> simp [h]

theorem primePoint_boolean {N : ℕ} {K : Type*} [CommRing K] (i : Fin (N + 1)) :
    eval (primePoint N K) (booleanConstraint i) = 0 := by
  simp [booleanConstraint_eval, primePoint]

theorem primePoint_zero {N : ℕ} {K : Type*} [CommSemiring K]
    (i : Fin (N + 1)) (h : i.val = 0) : primePoint N K i = 0 := by
  simp [primePoint, h, Nat.not_prime_zero]

theorem primePoint_one {N : ℕ} {K : Type*} [CommSemiring K]
    (i : Fin (N + 1)) (h : i.val = 1) : primePoint N K i = 0 := by
  simp [primePoint, h, Nat.not_prime_one]

theorem primePoint_even_gt_two {N : ℕ} {K : Type*} [CommSemiring K]
    (i : Fin (N + 1)) (he : Even i.val) (ht : 2 < i.val) :
    primePoint N K i = 0 := by
  have hn : ¬i.val.Prime := by
    intro hp
    have htwo := hp.even_iff.mp he
    omega
  simp [primePoint, hn]

theorem primePoint_coarse {N : ℕ} {K : Type*} [CommRing K] (i : Fin (N + 1)) :
    eval (primePoint N K) (coarseConstraint i) = 0 := by
  classical
  by_cases h : coarseAllowed i
  · simp only [coarseConstraint, if_pos h, eval_X]
    rcases h with h | h | ⟨he, ht⟩
    · exact primePoint_zero (K := K) i h
    · exact primePoint_one (K := K) i h
    · exact primePoint_even_gt_two (K := K) i he ht
  · simp [coarseConstraint, h]

theorem certificate_excludes_common_zero {N : ℕ} {K : Type*}
    [CommRing K] [Nontrivial K] {ι : Type*} [Fintype ι]
    (F A : ι → R N K) (U : Fin (N + 1) → R N K) (B : R N K)
    (cert : Certificate F A U B) (x : Fin (N + 1) → K)
    (hF : ∀ j, eval x (F j) = 0)
    (hBool : ∀ i, eval x (booleanConstraint i) = 0)
    (hg : eval x (g N K) = 0) : False := by
  have h := congrArg (eval x) cert
  simp only [map_one, map_add, map_sum, map_mul] at h
  simp [hF, hBool, hg] at h

theorem certificate_nonzero_at_primePoint {N : ℕ} {K : Type*}
    [CommRing K] [Nontrivial K] {ι : Type*} [Fintype ι]
    (F A : ι → R N K) (U : Fin (N + 1) → R N K) (B : R N K)
    (cert : Certificate F A U B)
    (hF : ∀ j, eval (primePoint N K) (F j) = 0) :
    eval (primePoint N K) (g N K) ≠ 0 := by
  intro hg
  exact certificate_excludes_common_zero F A U B cert (primePoint N K) hF
    primePoint_boolean hg

theorem eval_g_primePoint {N : ℕ} {K : Type*} [CommSemiring K] :
    eval (primePoint N K) (g N K) = (goldbachCount N : K) := by
  simp [g, goldbachCount, primePoint, primeIndicator, complement, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_ite]

theorem goldbachCount_positive_iff (N : ℕ) :
    0 < goldbachCount N ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N := by
  classical
  constructor
  · intro hpos
    by_contra hn
    have hz : goldbachCount N = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hp : i.val.Prime
      · have hq : ¬(N - i.val).Prime := by
          intro hq
          exact hn ⟨i.val, N - i.val, hp, hq, by omega⟩
        simp [primeIndicator, hq]
      · simp [primeIndicator, hp]
    omega
  · rintro ⟨p, q, hp, hq, hs⟩
    have hpn : p < N + 1 := by omega
    let i : Fin (N + 1) := ⟨p, hpn⟩
    have hsub : N - p = q := by omega
    have ht : primeIndicator i.val * primeIndicator (N - i.val) = 1 := by
      simp [i, primeIndicator, hp, hq, hsub]
    have hle := Finset.single_le_sum
      (fun (j : Fin (N + 1)) _ => Nat.zero_le
        (primeIndicator j.val * primeIndicator (N - j.val))) (Finset.mem_univ i)
    rw [ht] at hle
    exact lt_of_lt_of_le (by decide : 0 < 1) hle

theorem goldbachCount_le (N : ℕ) : goldbachCount N ≤ N + 1 := by
  calc
    goldbachCount N ≤ ∑ _i : Fin (N + 1), (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [primeIndicator]
      split_ifs <;> simp
    _ = N + 1 := by simp

theorem certificate_goldbachCount_positive {N : ℕ} {K : Type*}
    [CommRing K] [Nontrivial K] {ι : Type*} [Fintype ι]
    (F A : ι → R N K) (U : Fin (N + 1) → R N K) (B : R N K)
    (cert : Certificate F A U B)
    (hF : ∀ j, eval (primePoint N K) (F j) = 0) :
    0 < goldbachCount N := by
  have hn := certificate_nonzero_at_primePoint F A U B cert hF
  rw [eval_g_primePoint] at hn
  have hcount : goldbachCount N ≠ 0 := by
    intro hz
    simp [hz] at hn
  exact Nat.pos_of_ne_zero hcount

theorem certificate_implies_goldbach {N : ℕ} {K : Type*}
    [CommRing K] [Nontrivial K] {ι : Type*} [Fintype ι]
    (F A : ι → R N K) (U : Fin (N + 1) → R N K) (B : R N K)
    (cert : Certificate F A U B)
    (hF : ∀ j, eval (primePoint N K) (F j) = 0) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N :=
  (goldbachCount_positive_iff N).mp
    (certificate_goldbachCount_positive F A U B cert hF)

theorem eval_g_rat_nonzero_iff (N : ℕ) :
    eval (primePoint N ℚ) (g N ℚ) ≠ 0 ↔ 0 < goldbachCount N := by
  rw [eval_g_primePoint]
  exact_mod_cast (Nat.pos_iff_ne_zero : 0 < goldbachCount N ↔ goldbachCount N ≠ 0).symm

theorem certificate_g_rat_positive {N : ℕ} {ι : Type*} [Fintype ι]
    (F A : ι → R N ℚ) (U : Fin (N + 1) → R N ℚ) (B : R N ℚ)
    (cert : Certificate F A U B)
    (hF : ∀ j, eval (primePoint N ℚ) (F j) = 0) :
    0 < eval (primePoint N ℚ) (g N ℚ) := by
  rw [eval_g_primePoint]
  exact_mod_cast certificate_goldbachCount_positive F A U B cert hF

/- Every nonnegative integer in a finite-field constraint must be bounded by
momentBound N k. The strict inequality in FiniteFieldPolicy makes reduction
faithful throughout that interval. A family using larger or negative integers
has to establish its own faithful bound; this file does not license it. -/
def momentBound (N k : ℕ) : ℕ := (N + 1) ^ (k + 1)

def FiniteFieldPolicy (N k p : ℕ) : Prop := p.Prime ∧ momentBound N k < p

theorem bounded_zmod_cast_injective {p bound : ℕ} (hb : bound < p)
    {a b : ℕ} (ha : a ≤ bound) (hbb : b ≤ bound) :
    (a : ZMod p) = (b : ZMod p) ↔ a = b := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt (ha.trans_lt hb),
      ZMod.val_natCast_of_lt (hbb.trans_lt hb)] using hv
  · intro h
    rw [h]

theorem bounded_zmod_cast_zero_iff {p bound m : ℕ} (hb : bound < p)
    (hm : m ≤ bound) : (m : ZMod p) = 0 ↔ m = 0 := by
  simpa only [Nat.cast_zero] using bounded_zmod_cast_injective hb hm (Nat.zero_le bound)

theorem goldbachCount_le_momentBound (N k : ℕ) : goldbachCount N ≤ momentBound N k :=
  (goldbachCount_le N).trans (Nat.le_self_pow (Nat.succ_ne_zero k) (N + 1))

theorem bounded_sum_le_momentBound {N k : ℕ} (f : Fin (N + 1) → ℕ)
    (hf : ∀ i, f i ≤ (N + 1) ^ k) : (∑ i, f i) ≤ momentBound N k := by
  calc
    (∑ i, f i) ≤ ∑ _i : Fin (N + 1), (N + 1) ^ k := by
      exact Finset.sum_le_sum (fun i _ => hf i)
    _ = (N + 1) * (N + 1) ^ k := by simp [Nat.mul_comm]
    _ = momentBound N k := by simp [momentBound, pow_succ, Nat.mul_comm]

theorem finiteFieldPolicy_g_nonzero_iff {N k p : ℕ} (policy : FiniteFieldPolicy N k p) :
    eval (primePoint N (ZMod p)) (g N (ZMod p)) ≠ 0 ↔ 0 < goldbachCount N := by
  rw [eval_g_primePoint, ne_eq,
    bounded_zmod_cast_zero_iff policy.2 (goldbachCount_le_momentBound N k)]
  exact Nat.pos_iff_ne_zero.symm

theorem finiteFieldPolicy_g_zero_iff {N k p : ℕ} (policy : FiniteFieldPolicy N k p) :
    eval (primePoint N (ZMod p)) (g N (ZMod p)) = 0 ↔ goldbachCount N = 0 := by
  rw [eval_g_primePoint]
  exact bounded_zmod_cast_zero_iff policy.2 (goldbachCount_le_momentBound N k)

end

end AlgebraicGoldbach
