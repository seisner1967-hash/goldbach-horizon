import Calibration.LowerBound

/-!
Ordinary bounded polynomial calculus for the full D_pi calibration system,
and its actual restriction to Boolean knapsack on the maximum independent
prime support. This is a reduction, not a universal degree upper bound.
-/

namespace AlgebraicGoldbach.PCRestriction

noncomputable section
open scoped BigOperators
open MvPolynomial Calibration LowerBound.Restriction

/-- Ordinary PC: every axiom and every inferred line has total degree at most d.
The only rules are loading an input, a binary field-linear combination, and
multiplication by one variable. Zero is not an additional input or rule. -/
inductive Derives {σ : Type*} (G : Set (MvPolynomial σ ℚ)) (d : ℕ) :
    MvPolynomial σ ℚ → Prop
  | input {f} (hf : f ∈ G) (hdegree : f.totalDegree ≤ d) : Derives G d f
  | linear {f g} (hf : Derives G d f) (hg : Derives G d g) (a b : ℚ)
      (hdegree : (C a * f + C b * g).totalDegree ≤ d) :
      Derives G d (C a * f + C b * g)
  | mulVar {f} (hf : Derives G d f) (i : σ)
      (hdegree : (X i * f).totalDegree ≤ d) : Derives G d (X i * f)

namespace Derives

theorem degree_le {σ : Type*} {G : Set (MvPolynomial σ ℚ)} {d : ℕ}
    {f : MvPolynomial σ ℚ} (hf : Derives G d f) : f.totalDegree ≤ d := by
  cases hf with
  | input _ hdegree => exact hdegree
  | linear _ _ _ _ hdegree => exact hdegree
  | mulVar _ _ hdegree => exact hdegree

theorem scalar {σ : Type*} {G : Set (MvPolynomial σ ℚ)} {d : ℕ}
    {f : MvPolynomial σ ℚ} (hf : Derives G d f) (a : ℚ)
    (hdegree : (C a * f).totalDegree ≤ d) : Derives G d (C a * f) := by
  have h : Derives G d (C a * f + C 0 * f) :=
    Derives.linear hf hf a 0 (by simpa using hdegree)
  simpa using h

end Derives

def dpiGenerators (N : ℕ) : Set (R N ℚ) :=
  {f | f = countConstraint N ∨ f = g N ℚ ∨
    (∃ i, f = booleanConstraint i) ∨ (∃ i, f = nonprimeConstraint N i)}

def knapsackCount (σ : Type*) [Fintype σ] (m : ℕ) : MvPolynomial σ ℚ :=
  (∑ i : σ, X i) - C (m : ℚ)

def knapsackGenerators (σ : Type*) [Fintype σ] (m : ℕ) :
    Set (MvPolynomial σ ℚ) :=
  {f | f = knapsackCount σ m ∨ ∃ i : σ, f = X i ^ 2 - X i}

def Refutation {σ : Type*} (G : Set (MvPolynomial σ ℚ)) (d : ℕ) : Prop :=
  Derives G d 1

theorem polynomial_nonprime (N : ℕ) (i : Fin (N + 1)) :
    polynomial N (nonprimeConstraint N i) = 0 := by
  classical
  by_cases hp : Nat.Prime i.val
  · simp [nonprimeConstraint, hp, polynomial]
  · have hi : i.val ∉ maximumSupport N := by
      intro hi
      exact hp (mem_primes.mp ((maximumSupport_independent N).1 hi)).2
    simp [nonprimeConstraint, hp, polynomial, restrictedVariable, hi]

theorem polynomial_boolean (N : ℕ) (i : Fin (N + 1)) :
    polynomial N (booleanConstraint i) =
      if h : i.val ∈ maximumSupport N then
        (X (⟨i, h⟩ : Vars N)) ^ 2 - X (⟨i, h⟩ : Vars N) else 0 := by
  classical
  simp only [booleanConstraint, polynomial, eval₂_sub, eval₂_pow, eval₂_X]
  unfold restrictedVariable
  split_ifs <;> simp

theorem polynomial_g_zero (N : ℕ) : polynomial N (g N ℚ) = 0 := by
  classical
  simp only [g, polynomial, eval₂_sum, eval₂_mul, eval₂_X]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val ∈ maximumSupport N
  · have hq : (complement N i).val ∉ maximumSupport N :=
      (maximumSupport_independent N).2 i.val hi
    simp [restrictedVariable, hq]
  · simp [restrictedVariable, hi]

theorem restrictedVariable_sum (N : ℕ) :
    (∑ i : Fin (N + 1), restrictedVariable N i) = ∑ i : Vars N, X i := by
  classical
  have hsum := Fintype.sum_subtype_add_sum_subtype
    (fun i : Fin (N + 1) => i.val ∈ maximumSupport N) (restrictedVariable N)
  have hpos :
      (∑ i : {i : Fin (N + 1) // i.val ∈ maximumSupport N}, restrictedVariable N i) =
        ∑ i : Vars N, X i := by
    apply Finset.sum_congr rfl
    intro i _
    simp [restrictedVariable, i.property]
  have hneg :
      (∑ i : {i : Fin (N + 1) // i.val ∉ maximumSupport N}, restrictedVariable N i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [restrictedVariable, i.property]
  rw [hpos, hneg, add_zero] at hsum
  exact hsum.symm

theorem polynomial_count (N : ℕ) :
    polynomial N (countConstraint N) = knapsackCount (Vars N) (pi N) := by
  classical
  simp only [countConstraint, polynomial, eval₂_sub, eval₂_sum, eval₂_X, eval₂_C]
  rw [restrictedVariable_sum]
  rfl

theorem generator_image (N : ℕ) (f : R N ℚ) (hf : f ∈ dpiGenerators N) :
    polynomial N f = 0 ∨ polynomial N f ∈ knapsackGenerators (Vars N) (pi N) := by
  classical
  rcases hf with hcount | hg | ⟨i, hbool⟩ | ⟨i, hnonprime⟩
  · right
    exact Or.inl (hcount ▸ polynomial_count N)
  · left
    exact hg ▸ polynomial_g_zero N
  · rw [hbool, polynomial_boolean]
    split_ifs with hi
    · right
      exact Or.inr ⟨⟨i, hi⟩, rfl⟩
    · exact Or.inl rfl
  · left
    exact hnonprime ▸ polynomial_nonprime N i

/-- Zero images are omitted. Nonzero images have ordinary target PC derivations;
no zero axiom or Boolean-quotient rule is added to either calculus. -/
theorem derivation_restriction (N d : ℕ) (f : R N ℚ)
    (hf : Derives (dpiGenerators N) d f) :
    polynomial N f = 0 ∨
      Derives (knapsackGenerators (Vars N) (pi N)) d (polynomial N f) := by
  classical
  induction hf with
  | input hf hdegree =>
      rcases generator_image N _ hf with hz | hmem
      · exact Or.inl hz
      · exact Or.inr (Derives.input hmem ((polynomial_degree_le N _).trans hdegree))
  | @linear f g hf hg a b hdegree ihf ihg =>
      have he : polynomial N (C a * f + C b * g) =
          C a * polynomial N f + C b * polynomial N g := by
        simp [polynomial, eval₂_add, eval₂_mul]
      have hdeg := (polynomial_degree_le N (C a * f + C b * g)).trans hdegree
      rw [he] at hdeg ⊢
      rcases ihf with hzF | hF <;> rcases ihg with hzG | hG
      · left
        simp [hzF, hzG]
      · right
        simpa [hzF] using Derives.scalar hG b (by simpa [hzF] using hdeg)
      · right
        simpa [hzG] using Derives.scalar hF a (by simpa [hzG] using hdeg)
      · exact Or.inr (Derives.linear hF hG a b hdeg)
  | @mulVar f hf i hdegree ihf =>
      have he : polynomial N (X i * f) = restrictedVariable N i * polynomial N f := by
        simp [polynomial, eval₂_mul]
      have hdeg := (polynomial_degree_le N (X i * f)).trans hdegree
      rw [he] at hdeg ⊢
      by_cases hi : i.val ∈ maximumSupport N
      · rw [restrictedVariable, dif_pos hi] at hdeg ⊢
        rcases ihf with hz | hF
        · left
          simp [hz]
        · exact Or.inr (Derives.mulVar hF ⟨i, hi⟩ hdeg)
      · left
        simp [restrictedVariable, hi]

theorem dpi_refutation_restricts (N d : ℕ)
    (href : Refutation (dpiGenerators N) d) :
    Refutation (knapsackGenerators (Vars N) (pi N)) d := by
  rcases derivation_restriction N d 1 href with hz | htarget
  · simp [polynomial] at hz
  · simpa [Refutation, polynomial] using htarget

/-- Explicit external hypothesis. IPS TR97-042 Theorem 4.1, for nonzero real
coefficients, supplies this for all-one coefficients through Q -> R embedding.
That theorem is not formalized or assumed as an axiom in this project. -/
def KnapsackLowerBound (σ : Type*) [Fintype σ] : Prop :=
  1 ≤ Fintype.card σ → ∀ m d : ℕ,
    Refutation (knapsackGenerators σ m) d → (Fintype.card σ + 1) / 2 + 1 ≤ d

/-- Conditional consequence only: the ceil(alpha/2)+1 knapsack bound transfers
to actual ordinary D_pi PC refutations when alpha >= 1. -/
theorem dpi_degree_lower_bound_conditional (N d : ℕ)
    (hlower : KnapsackLowerBound (Vars N)) (halpha : 1 ≤ pi N - r N)
    (href : Refutation (dpiGenerators N) d) :
    (pi N - r N + 1) / 2 + 1 ≤ d := by
  have hcard : 1 ≤ Fintype.card (Vars N) := by simpa [vars_card] using halpha
  have h := hlower hcard (pi N) d (dpi_refutation_restricts N d href)
  simpa [vars_card] using h

end
end AlgebraicGoldbach.PCRestriction
