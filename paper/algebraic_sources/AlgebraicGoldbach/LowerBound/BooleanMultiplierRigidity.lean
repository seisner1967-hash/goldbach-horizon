import AlgebraicGoldbach.LowerBound.BooleanCoefficients
import AlgebraicGoldbach.LowerBound.BooleanLattice

set_option autoImplicit false

namespace AlgebraicGoldbach.BooleanCoefficients

open scoped BigOperators

/-- Actual rational count multiplication on subset functions, defined from the
unchanged accepted bit action. The rational parameter is unrestricted. -/
noncomputable def countMul
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (m : ℚ) (f : Finset σ → ℚ) (s : Finset σ) : ℚ :=
  (∑ i : σ, bitMul i f s) - m * f s

/-- The actual count action separates into its cardinality diagonal and the
accepted finite-subset raising operator. No condition on the parameter is used. -/
theorem countMul_eq_diagonal_add_up
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (m : ℚ) (f : Finset σ → ℚ) (s : Finset σ) :
    countMul m f s = ((s.card : ℚ) - m) * f s + BooleanLattice.up f s := by
  have hsum : (∑ i : σ, bitMul i f s) = ∑ i ∈ s, (f s + f (s.erase i)) := by
    calc
      _ = ∑ i ∈ s, bitMul i f s := by
        symm
        apply Finset.sum_subset (Finset.subset_univ s)
        intro i _hi hnot
        simp [bitMul, hnot]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [bitMul, hi]
  rw [countMul, hsum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  unfold BooleanLattice.up
  ring

/-- If a subset function and its actual count action vanish above a layer
strictly below the middle, the equality layer also vanishes. -/
theorem top_layer_vanishes_of_countMul_degree_le
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (m : ℚ) (k : ℕ) (hk : 2 * k < Fintype.card σ)
    (f : Finset σ → ℚ)
    (habove : ∀ s : Finset σ, k < s.card → f s = 0)
    (himage : ∀ s : Finset σ, k < s.card → countMul m f s = 0) :
    ∀ s : Finset σ, k ≤ s.card → f s = 0 := by
  let q : Finset σ → ℚ := fun s => if s.card = k then f s else 0
  have hlayer : ∀ s : Finset σ, s.card ≠ k → q s = 0 := by
    intro s hne
    simp [q, hne]
  have hup : ∀ s : Finset σ, BooleanLattice.up q s = 0 := by
    intro s
    by_cases hnext : s.card = k + 1
    · have hs : k < s.card := by omega
      have hupf : BooleanLattice.up f s = 0 := by
        have hc := himage s hs
        rw [countMul_eq_diagonal_add_up, habove s hs, mul_zero, zero_add] at hc
        exact hc
      calc
        BooleanLattice.up q s = BooleanLattice.up f s := by
          unfold BooleanLattice.up
          apply Finset.sum_congr rfl
          intro i hi
          have herase := Finset.card_erase_add_one hi
          have hcard : (s.erase i).card = k := by omega
          simp [q, hcard]
        _ = 0 := hupf
    · unfold BooleanLattice.up
      apply Finset.sum_eq_zero
      intro i hi
      have herase := Finset.card_erase_add_one hi
      have hcard : (s.erase i).card ≠ k := by omega
      simp [q, hcard]
  have hq : q = 0 := BooleanLattice.up_injective_below_middle k hk q hlayer hup
  intro s hs
  by_cases heq : s.card = k
  · have hzero := congrFun hq s
    simpa [q, heq] using hzero
  · exact habove s (by omega)

end AlgebraicGoldbach.BooleanCoefficients
