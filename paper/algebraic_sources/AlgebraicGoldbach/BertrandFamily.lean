import AlgebraicGoldbach.Soundness
import AlgebraicGoldbach.UniformNonpinning

namespace AlgebraicGoldbach

noncomputable section

open scoped BigOperators
open MvPolynomial

/- The Bertrand family is a finite family of actual polynomials. Its constants
and index conditions depend only on N and m, not on any prime-counting data.
It contains the allowed coarse constraints and every admissible Bertrand interval
nonemptiness constraint. Boolean constraints remain separate, as in Certificate.
-/
abbrev BertrandIndex (N : ℕ) :=
  {m : Fin (N + 1) // 1 ≤ m.val ∧ 2 * m.val ≤ N}

abbrev BertrandFamilyIndex (N : ℕ) := Fin (N + 1) ⊕ BertrandIndex N

def bertrandWindow (N m : ℕ) : Finset (Fin (N + 1)) :=
  Finset.univ.filter (fun i => m < i.val ∧ i.val ≤ 2 * m)

def bertrandPolynomial (N m : ℕ) : R N ℚ :=
  ∏ i ∈ bertrandWindow N m, (1 - X i)

def bertrandFamily (N : ℕ) : BertrandFamilyIndex N → R N ℚ
  | .inl i => coarseConstraint i
  | .inr m => bertrandPolynomial N m.val.val

def modelPoint (N : ℕ) : Fin (N + 1) → ℚ := fun i => (bit N i.val : ℚ)

theorem primePoint_bertrandPolynomial (N m : ℕ) (hm : 1 ≤ m) (hmN : 2 * m ≤ N) :
    eval (primePoint N ℚ) (bertrandPolynomial N m) = 0 := by
  obtain ⟨p, hp, hmp, hpm, hpN⟩ := prime_indicator_bertrand N m hm hmN
  let i : Fin (N + 1) := ⟨p, by omega⟩
  have hi : i ∈ bertrandWindow N m := by
    simp [bertrandWindow, i, hmp, hpm]
  simp only [bertrandPolynomial, map_prod]
  apply Finset.prod_eq_zero (i := i) hi
  simp [primePoint, i, hp]

theorem primePoint_bertrandFamily (N : ℕ) (j : BertrandFamilyIndex N) :
    eval (primePoint N ℚ) (bertrandFamily N j) = 0 := by
  rcases j with i | m
  · exact primePoint_coarse i
  · exact primePoint_bertrandPolynomial N m.val.val m.property.1 m.property.2

theorem modelPoint_boolean (N : ℕ) (i : Fin (N + 1)) :
    eval (modelPoint N) (booleanConstraint i) = 0 := by
  rw [booleanConstraint_eval]
  have hb : (bit N i.val : ℚ) * (bit N i.val : ℚ) = (bit N i.val : ℚ) := by
    exact_mod_cast bit_boolean N i.val
  simpa only [modelPoint, pow_two, sub_eq_zero] using hb

theorem modelPoint_coarse (N : ℕ) (hN : 24 ≤ N) (i : Fin (N + 1)) :
    eval (modelPoint N) (coarseConstraint i) = 0 := by
  classical
  by_cases h : coarseAllowed i
  · simp only [coarseConstraint, if_pos h, eval_X, modelPoint]
    obtain ⟨h0, h1, he⟩ := bit_coarse N hN
    rcases h with h | h | ⟨heven, ht⟩
    · simp [h, h0]
    · simp [h, h1]
    · have hmod : i.val % 2 = 0 := by
        exact Nat.even_iff.mp heven
      simp [he i.val ht hmod]
  · simp [coarseConstraint, h]

theorem modelPoint_bertrandPolynomial (N : ℕ) (hN : 24 ≤ N) (m : ℕ)
    (hm : 1 ≤ m) (hmN : 2 * m ≤ N) :
    eval (modelPoint N) (bertrandPolynomial N m) = 0 := by
  obtain ⟨n, hmn, hnm, hs⟩ := selected_bertrand N hN m hm hmN
  let i : Fin (N + 1) := ⟨n, by omega⟩
  have hi : i ∈ bertrandWindow N m := by
    simp [bertrandWindow, i, hmn, hnm]
  simp only [bertrandPolynomial, map_prod]
  apply Finset.prod_eq_zero (i := i) hi
  simp [modelPoint, i, bit, hs]

theorem modelPoint_bertrandFamily (N : ℕ) (hN : 24 ≤ N) (j : BertrandFamilyIndex N) :
    eval (modelPoint N) (bertrandFamily N j) = 0 := by
  rcases j with i | m
  · exact modelPoint_coarse N hN i
  · exact modelPoint_bertrandPolynomial N hN m.val.val m.property.1 m.property.2

theorem modelPoint_g_zero (N : ℕ) (hN : 24 ≤ N) :
    eval (modelPoint N) (g N ℚ) = 0 := by
  have hb := bit_goldbach_zero N hN
  rw [← Fin.sum_univ_eq_sum_range] at hb
  have hc : (∑ i : Fin (N + 1), (bit N i.val : ℚ) * (bit N (N - i.val) : ℚ)) = 0 := by
    exact_mod_cast hb
  simpa [g, modelPoint, complement] using hc

theorem modelPoint_differs_from_primePoint (N : ℕ) (hN : 24 ≤ N) :
    modelPoint N ≠ primePoint N ℚ := by
  intro h
  let i : Fin (N + 1) := ⟨9, by omega⟩
  have hi := congrFun h i
  obtain ⟨hbit, hprime⟩ := uniform_model_selects_composite_nine N hN
  have hpb : primePoint N ℚ i = (primeBit 9 : ℚ) := by
    simp [primePoint, primeBit, i]
  rw [hpb] at hi
  simp [modelPoint, i, hbit, hprime] at hi

theorem bertrandFamily_common_zero (N : ℕ) (hN : 24 ≤ N) :
    (∀ j, eval (modelPoint N) (bertrandFamily N j) = 0) ∧
    (∀ i, eval (modelPoint N) (booleanConstraint i) = 0) ∧
    eval (modelPoint N) (g N ℚ) = 0 :=
  ⟨modelPoint_bertrandFamily N hN, modelPoint_boolean N, modelPoint_g_zero N hN⟩

theorem bertrandFamily_has_second_boolean_solution (N : ℕ) (hN : 24 ≤ N) :
    (∀ j, eval (primePoint N ℚ) (bertrandFamily N j) = 0) ∧
    (∀ i, eval (primePoint N ℚ) (booleanConstraint i) = 0) ∧
    (∀ j, eval (modelPoint N) (bertrandFamily N j) = 0) ∧
    (∀ i, eval (modelPoint N) (booleanConstraint i) = 0) ∧
    modelPoint N ≠ primePoint N ℚ :=
  ⟨primePoint_bertrandFamily N, primePoint_boolean,
    modelPoint_bertrandFamily N hN, modelPoint_boolean N,
    modelPoint_differs_from_primePoint N hN⟩

theorem bertrandFamily_no_certificate (N : ℕ) (hN : 24 ≤ N)
    (A : BertrandFamilyIndex N → R N ℚ) (U : Fin (N + 1) → R N ℚ) (B : R N ℚ) :
    ¬Certificate (bertrandFamily N) A U B := by
  intro cert
  exact certificate_excludes_common_zero (bertrandFamily N) A U B cert (modelPoint N)
    (modelPoint_bertrandFamily N hN) (modelPoint_boolean N) (modelPoint_g_zero N hN)

end

end AlgebraicGoldbach
