import AlgebraicGoldbach.BertrandFamily

namespace AlgebraicGoldbach.ProperBertrand

noncomputable section

open scoped BigOperators
open MvPolynomial

/- Only intervals (m,2m] with m>=2. No coarse or SIEVE equations are included. -/
abbrev Index (N : ℕ) := {m : Fin (N + 1) // 2 ≤ m.val ∧ 2 * m.val ≤ N}

def family (N : ℕ) : Index N → R N ℚ := fun m => bertrandPolynomial N m.val.val

def onePoint (N : ℕ) : Fin (N + 1) → ℚ := fun _ => 1

def exceptPoint (N : ℕ) (target : Fin (N + 1)) : Fin (N + 1) → ℚ :=
  fun i => if i = target then 0 else 1

theorem primePoint_family (N : ℕ) (m : Index N) :
    eval (primePoint N ℚ) (family N m) = 0 :=
  primePoint_bertrandPolynomial N m.val.val (by have := m.property.1; omega) m.property.2

theorem onePoint_boolean (N : ℕ) (i : Fin (N + 1)) :
    eval (onePoint N) (booleanConstraint i) = 0 := by
  simp [booleanConstraint_eval, onePoint]

theorem exceptPoint_boolean (N : ℕ) (target i : Fin (N + 1)) :
    eval (exceptPoint N target) (booleanConstraint i) = 0 := by
  rw [booleanConstraint_eval]
  unfold exceptPoint
  split_ifs <;> norm_num

theorem onePoint_family (N : ℕ) (m : Index N) : eval (onePoint N) (family N m) = 0 := by
  have hm := m.property
  let i : Fin (N + 1) := ⟨m.val.val + 1, by omega⟩
  have hi : i ∈ bertrandWindow N m.val.val := by
    simp only [bertrandWindow, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  simp only [family, bertrandPolynomial, map_prod]
  apply Finset.prod_eq_zero (i := i) hi
  simp [onePoint]

theorem exceptPoint_family (N : ℕ) (target : Fin (N + 1)) (m : Index N) :
    eval (exceptPoint N target) (family N m) = 0 := by
  have hm := m.property
  let i : Fin (N + 1) := ⟨m.val.val + 1, by omega⟩
  let j : Fin (N + 1) := ⟨m.val.val + 2, by omega⟩
  have hi : i ∈ bertrandWindow N m.val.val := by
    simp only [bertrandWindow, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hj : j ∈ bertrandWindow N m.val.val := by
    simp only [bertrandWindow, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hij : i ≠ j := by
    intro h
    have he := congrArg Fin.val h
    dsimp [i, j] at he
    omega
  simp only [family, bertrandPolynomial, map_prod]
  by_cases ht : target = i
  · apply Finset.prod_eq_zero (i := j) hj
    simp [exceptPoint, ht, hij.symm]
  · apply Finset.prod_eq_zero (i := i) hi
    simp [exceptPoint, Ne.symm ht]

theorem onePoint_differs_from_primePoint (N : ℕ) : onePoint N ≠ primePoint N ℚ := by
  intro h
  have hi := congrFun h (0 : Fin (N + 1))
  norm_num [onePoint, primePoint] at hi

theorem family_has_second_boolean_solution (N : ℕ) :
    (∀ m, eval (primePoint N ℚ) (family N m) = 0) ∧
    (∀ i, eval (primePoint N ℚ) (booleanConstraint i) = 0) ∧
    (∀ m, eval (onePoint N) (family N m) = 0) ∧
    (∀ i, eval (onePoint N) (booleanConstraint i) = 0) ∧
    onePoint N ≠ primePoint N ℚ :=
  ⟨primePoint_family N, primePoint_boolean, onePoint_family N,
    onePoint_boolean N, onePoint_differs_from_primePoint N⟩

theorem family_does_not_pin_any_coordinate (N : ℕ) (target : Fin (N + 1)) :
    (∀ m, eval (exceptPoint N target) (family N m) = 0) ∧
    (∀ i, eval (exceptPoint N target) (booleanConstraint i) = 0) ∧
    exceptPoint N target target = 0 ∧
    (∀ m, eval (onePoint N) (family N m) = 0) ∧
    (∀ i, eval (onePoint N) (booleanConstraint i) = 0) ∧
    onePoint N target = 1 := by
  exact ⟨exceptPoint_family N target, exceptPoint_boolean N target, by simp [exceptPoint],
    onePoint_family N, onePoint_boolean N, rfl⟩

theorem modelPoint_family (N : ℕ) (hN : 24 ≤ N) (m : Index N) :
    eval (modelPoint N) (family N m) = 0 :=
  modelPoint_bertrandPolynomial N hN m.val.val (by have := m.property.1; omega) m.property.2

theorem family_common_zero (N : ℕ) (hN : 24 ≤ N) :
    (∀ m, eval (modelPoint N) (family N m) = 0) ∧
    (∀ i, eval (modelPoint N) (booleanConstraint i) = 0) ∧
    eval (modelPoint N) (g N ℚ) = 0 :=
  ⟨modelPoint_family N hN, modelPoint_boolean N, modelPoint_g_zero N hN⟩

theorem family_no_certificate (N : ℕ) (hN : 24 ≤ N)
    (A : Index N → R N ℚ) (U : Fin (N + 1) → R N ℚ) (B : R N ℚ) :
    ¬ Certificate (family N) A U B := by
  intro cert
  exact certificate_excludes_common_zero (family N) A U B cert (modelPoint N)
    (modelPoint_family N hN) (modelPoint_boolean N) (modelPoint_g_zero N hN)

end
end AlgebraicGoldbach.ProperBertrand
