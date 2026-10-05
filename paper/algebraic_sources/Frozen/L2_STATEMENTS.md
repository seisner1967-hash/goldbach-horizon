# Frozen L2 statement catalogue

These signatures are frozen for Judge review. The source uses real mathlib MvPolynomial objects. All certificate conclusions are explicitly conditional on the supplied identity and constraints vanishing at the prime point.

```lean
namespace AlgebraicGoldbach
theorem booleanConstraint_eval {N : ℕ} {K : Type*} [CommRing K]
    (x : Fin (N + 1) → K) (i : Fin (N + 1)) :
    eval x (booleanConstraint i) = x i ^ 2 - x i

theorem booleanConstraint_zero_iff {N : ℕ} {K : Type*} [CommRing K] [IsDomain K]
    (x : Fin (N + 1) → K) (i : Fin (N + 1)) :
    eval x (booleanConstraint i) = 0 ↔ x i = 0 ∨ x i = 1

theorem primePoint_boolean {N : ℕ} {K : Type*} [CommRing K] (i : Fin (N + 1)) :
    eval (primePoint N K) (booleanConstraint i) = 0

theorem primePoint_zero {N : ℕ} {K : Type*} [CommSemiring K]
    (i : Fin (N + 1)) (h : i.val = 0) : primePoint N K i = 0

theorem primePoint_one {N : ℕ} {K : Type*} [CommSemiring K]
    (i : Fin (N + 1)) (h : i.val = 1) : primePoint N K i = 0

theorem primePoint_even_gt_two {N : ℕ} {K : Type*} [CommSemiring K]
    (i : Fin (N + 1)) (he : Even i.val) (ht : 2 < i.val) :
    primePoint N K i = 0

theorem primePoint_coarse {N : ℕ} {K : Type*} [CommRing K] (i : Fin (N + 1)) :
    eval (primePoint N K) (coarseConstraint i) = 0

theorem certificate_excludes_common_zero {N : ℕ} {K : Type*}
    [CommRing K] [Nontrivial K] {ι : Type*} [Fintype ι]
    (F A : ι → R N K) (U : Fin (N + 1) → R N K) (B : R N K)
    (cert : Certificate F A U B) (x : Fin (N + 1) → K)
    (hF : ∀ j, eval x (F j) = 0)
    (hBool : ∀ i, eval x (booleanConstraint i) = 0)
    (hg : eval x (g N K) = 0) : False

theorem certificate_nonzero_at_primePoint {N : ℕ} {K : Type*}
    [CommRing K] [Nontrivial K] {ι : Type*} [Fintype ι]
    (F A : ι → R N K) (U : Fin (N + 1) → R N K) (B : R N K)
    (cert : Certificate F A U B)
    (hF : ∀ j, eval (primePoint N K) (F j) = 0) :
    eval (primePoint N K) (g N K) ≠ 0

theorem eval_g_primePoint {N : ℕ} {K : Type*} [CommSemiring K] :
    eval (primePoint N K) (g N K) = (goldbachCount N : K)

theorem goldbachCount_positive_iff (N : ℕ) :
    0 < goldbachCount N ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N

theorem goldbachCount_le (N : ℕ) : goldbachCount N ≤ N + 1

theorem certificate_goldbachCount_positive {N : ℕ} {K : Type*}
    [CommRing K] [Nontrivial K] {ι : Type*} [Fintype ι]
    (F A : ι → R N K) (U : Fin (N + 1) → R N K) (B : R N K)
    (cert : Certificate F A U B)
    (hF : ∀ j, eval (primePoint N K) (F j) = 0) :
    0 < goldbachCount N

theorem certificate_implies_goldbach {N : ℕ} {K : Type*}
    [CommRing K] [Nontrivial K] {ι : Type*} [Fintype ι]
    (F A : ι → R N K) (U : Fin (N + 1) → R N K) (B : R N K)
    (cert : Certificate F A U B)
    (hF : ∀ j, eval (primePoint N K) (F j) = 0) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N

theorem eval_g_rat_nonzero_iff (N : ℕ) :
    eval (primePoint N ℚ) (g N ℚ) ≠ 0 ↔ 0 < goldbachCount N

theorem certificate_g_rat_positive {N : ℕ} {ι : Type*} [Fintype ι]
    (F A : ι → R N ℚ) (U : Fin (N + 1) → R N ℚ) (B : R N ℚ)
    (cert : Certificate F A U B)
    (hF : ∀ j, eval (primePoint N ℚ) (F j) = 0) :
    0 < eval (primePoint N ℚ) (g N ℚ)

theorem bounded_zmod_cast_injective {p bound : ℕ} (hb : bound < p)
    {a b : ℕ} (ha : a ≤ bound) (hbb : b ≤ bound) :
    (a : ZMod p) = (b : ZMod p) ↔ a = b

theorem bounded_zmod_cast_zero_iff {p bound m : ℕ} (hb : bound < p)
    (hm : m ≤ bound) : (m : ZMod p) = 0 ↔ m = 0

theorem goldbachCount_le_momentBound (N k : ℕ) : goldbachCount N ≤ momentBound N k

theorem bounded_sum_le_momentBound {N k : ℕ} (f : Fin (N + 1) → ℕ)
    (hf : ∀ i, f i ≤ (N + 1) ^ k) : (∑ i, f i) ≤ momentBound N k

theorem finiteFieldPolicy_g_nonzero_iff {N k p : ℕ} (policy : FiniteFieldPolicy N k p) :
    eval (primePoint N (ZMod p)) (g N (ZMod p)) ≠ 0 ↔ 0 < goldbachCount N

theorem finiteFieldPolicy_g_zero_iff {N k p : ℕ} (policy : FiniteFieldPolicy N k p) :
    eval (primePoint N (ZMod p)) (g N (ZMod p)) = 0 ↔ goldbachCount N = 0

end AlgebraicGoldbach
```
