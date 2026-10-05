import Mathlib

/-!
Rational raising injectivity below the middle layer of the actual finite-subset
lattice. This engine uses finite sums, signed commutation and rational order.
It makes no PC, finite-field, prime-count or Goldbach assertion.
-/

namespace AlgebraicGoldbach.BooleanLattice

noncomputable section
open scoped BigOperators
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def up (f : Finset σ → ℚ) (s : Finset σ) : ℚ :=
  ∑ i ∈ s, f (s.erase i)

def down (f : Finset σ → ℚ) (s : Finset σ) : ℚ :=
  ∑ i ∈ Finset.univ \ s, f (insert i s)

def raiseAt (i : σ) (f : Finset σ → ℚ) (s : Finset σ) : ℚ :=
  if i ∈ s then f (s.erase i) else 0

def lowerAt (i : σ) (f : Finset σ → ℚ) (s : Finset σ) : ℚ :=
  if i ∈ s then 0 else f (insert i s)

def toggle (i : σ) (s : Finset σ) : Finset σ :=
  if i ∈ s then s.erase i else insert i s

theorem toggle_involutive (i : σ) : Function.Involutive (toggle i) := by
  intro s
  by_cases hi : i ∈ s
  · simp [toggle, hi]
  · simp [toggle, hi]

theorem up_eq_sum (f : Finset σ → ℚ) (s : Finset σ) :
    up f s = ∑ i : σ, raiseAt i f s := by
  simp [up, raiseAt, Finset.sum_ite]

theorem down_eq_sum (f : Finset σ → ℚ) (s : Finset σ) :
    down f s = ∑ i : σ, lowerAt i f s := by
  have hs : Finset.univ \ s = Finset.univ.filter (fun i : σ => i ∉ s) := by
    ext i
    simp
  simp only [down, hs, Finset.sum_filter, lowerAt]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [hi]

theorem raiseAt_sum (i : σ) (F : σ → Finset σ → ℚ) (s : Finset σ) :
    raiseAt i (fun t => ∑ j : σ, F j t) s = ∑ j : σ, raiseAt i (F j) s := by
  by_cases hi : i ∈ s <;> simp [raiseAt, hi]

theorem lowerAt_sum (i : σ) (F : σ → Finset σ → ℚ) (s : Finset σ) :
    lowerAt i (fun t => ∑ j : σ, F j t) s = ∑ j : σ, lowerAt i (F j) s := by
  by_cases hi : i ∈ s <;> simp [lowerAt, hi]

theorem coordinate_adjoint (i : σ) (f h : Finset σ → ℚ) :
    (∑ s : Finset σ, raiseAt i f s * h s) =
      ∑ s : Finset σ, f s * lowerAt i h s := by
  have ht := (toggle_involutive i).bijective.sum_comp
    (fun s : Finset σ => raiseAt i f s * h s)
  rw [← ht]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hi : i ∈ s <;> simp [toggle, raiseAt, lowerAt, hi]

theorem coordinate_commute (i j : σ) (hij : i ≠ j) (f : Finset σ → ℚ)
    (s : Finset σ) :
    lowerAt i (raiseAt j f) s = raiseAt j (lowerAt i f) s := by
  by_cases hi : i ∈ s <;> by_cases hj : j ∈ s
  · simp [lowerAt, raiseAt, hi, hj, hij]
  · simp [lowerAt, raiseAt, hi, hj, hij]
  · simp [lowerAt, raiseAt, hi, hj, hij, Ne.symm hij,
      Finset.erase_insert_of_ne]
  · simp [lowerAt, raiseAt, hi, hj, hij, Ne.symm hij]

theorem coordinate_diagonal (i : σ) (f : Finset σ → ℚ) (s : Finset σ) :
    lowerAt i (raiseAt i f) s - raiseAt i (lowerAt i f) s =
      (if i ∈ s then (-1 : ℚ) else 1) * f s := by
  by_cases hi : i ∈ s <;> simp [lowerAt, raiseAt, hi]

theorem adjoint (f h : Finset σ → ℚ) :
    (∑ s : Finset σ, up f s * h s) = ∑ s : Finset σ, f s * down h s := by
  simp_rw [up_eq_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [coordinate_adjoint]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← down_eq_sum]

theorem commutator (f : Finset σ → ℚ) (s : Finset σ) :
    down (up f) s - up (down f) s =
      ((Fintype.card σ : ℚ) - 2 * (s.card : ℚ)) * f s := by
  have hdu : down (up f) s =
      ∑ i : σ, ∑ j : σ, lowerAt i (raiseAt j f) s := by
    rw [down_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hu : up f = fun t => ∑ j : σ, raiseAt j f t :=
      funext (up_eq_sum f)
    rw [hu, lowerAt_sum]
  have hud : up (down f) s =
      ∑ i : σ, ∑ j : σ, raiseAt j (lowerAt i f) s := by
    rw [up_eq_sum]
    calc
      (∑ j : σ, raiseAt j (down f) s) =
          ∑ j : σ, ∑ i : σ, raiseAt j (lowerAt i f) s := by
        apply Finset.sum_congr rfl
        intro j _
        have hd : down f = fun t => ∑ i : σ, lowerAt i f t :=
          funext (down_eq_sum f)
        rw [hd, raiseAt_sum]
      _ = _ := Finset.sum_comm
  have hsign : (∑ i : σ, if i ∈ s then (-1 : ℚ) else 1) =
      (Fintype.card σ : ℚ) - 2 * (s.card : ℚ) := by
    have hf : Finset.univ.filter (fun i : σ => i ∈ s) = s := by
      ext i
      simp
    have hc : Finset.univ.filter (fun i : σ => i ∉ s) = Finset.univ \ s := by
      ext i
      simp
    have hcard : (((Finset.univ \ s).card : ℕ) : ℚ) + (s.card : ℚ) =
        (Fintype.card σ : ℚ) := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
    rw [Finset.sum_ite, hf, hc]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_neg_one, mul_one]
    linarith
  rw [hdu, hud, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    (∑ i : σ, ∑ j : σ,
        (lowerAt i (raiseAt j f) s - raiseAt j (lowerAt i f) s)) =
        ∑ i : σ, (if i ∈ s then (-1 : ℚ) else 1) * f s := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · exact coordinate_diagonal i f s
      · intro j _ hji
        rw [coordinate_commute i j (Ne.symm hji)]
        exact sub_self _
      · simp
    _ = _ := by rw [← Finset.sum_mul, hsign]

theorem up_injective_below_middle
    (k : ℕ) (hk : 2 * k < Fintype.card σ)
    (f : Finset σ → ℚ)
    (hlayer : ∀ s : Finset σ, s.card ≠ k → f s = 0)
    (hup : ∀ s : Finset σ, up f s = 0) : f = 0 := by
  have hdu : ∀ s : Finset σ, down (up f) s = 0 := by
    intro s
    simp [down, hup]
  have hpoint : ∀ s : Finset σ,
      ((Fintype.card σ : ℚ) - 2 * (k : ℚ)) * (f s * f s) =
        -(up (down f) s * f s) := by
    intro s
    by_cases hs : s.card = k
    · have hcomm := commutator f s
      rw [hdu s, hs] at hcomm
      calc
        ((Fintype.card σ : ℚ) - 2 * (k : ℚ)) * (f s * f s) =
            (((Fintype.card σ : ℚ) - 2 * (k : ℚ)) * f s) * f s := by ring
        _ = (0 - up (down f) s) * f s := by rw [hcomm]
        _ = _ := by ring
    · simp [hlayer s hs]
  have hsum :
      ((Fintype.card σ : ℚ) - 2 * (k : ℚ)) *
          (∑ s : Finset σ, f s * f s) =
        -(∑ s : Finset σ, down f s * down f s) := by
    calc
      _ = ∑ s : Finset σ,
          ((Fintype.card σ : ℚ) - 2 * (k : ℚ)) * (f s * f s) :=
        Finset.mul_sum _ _ _
      _ = ∑ s : Finset σ, -(up (down f) s * f s) := by
        apply Finset.sum_congr rfl
        intro s _
        exact hpoint s
      _ = -(∑ s : Finset σ, up (down f) s * f s) :=
        Finset.sum_neg_distrib
      _ = _ := by rw [adjoint]
  have hpositive : 0 < (Fintype.card σ : ℚ) - 2 * (k : ℚ) := by
    have hq : 2 * (k : ℚ) < (Fintype.card σ : ℚ) := by exact_mod_cast hk
    exact sub_pos.mpr hq
  have hnonneg : 0 ≤ ∑ s : Finset σ, f s * f s :=
    Finset.sum_nonneg fun s _ => mul_self_nonneg (f s)
  have hdown_nonneg : 0 ≤ ∑ s : Finset σ, down f s * down f s :=
    Finset.sum_nonneg fun s _ => mul_self_nonneg (down f s)
  have hzero : (∑ s : Finset σ, f s * f s) = 0 := by
    apply le_antisymm _ hnonneg
    by_contra hn
    have hp := mul_pos hpositive (lt_of_not_ge hn)
    linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun s (_ : s ∈ (Finset.univ : Finset (Finset σ))) =>
      mul_self_nonneg (f s))).mp hzero
  funext s
  have hz : f s * f s = 0 := hterm s (Finset.mem_univ s)
  exact (mul_eq_zero.mp hz).elim id id

end
end AlgebraicGoldbach.BooleanLattice
