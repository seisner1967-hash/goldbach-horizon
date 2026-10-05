import AlgebraicGoldbach.Soundness
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
Ordinary rational literal-product families and the actual complement-pair
arithmetic cube. An exact finite covering inequality yields a full common zero.
The cube dimension is its actual finite cardinality; no closed N formula,
true-prime truth, SIEVE premise, or supplied common-zero interface is used.
-/

namespace AlgebraicGoldbach.LiteralCube

noncomputable section
open scoped BigOperators
open MvPolynomial

inductive Literal (N : ℕ) where
  | positive (i : Fin (N + 1))
  | negative (i : Fin (N + 1))
  deriving DecidableEq

def Literal.polynomial {N : ℕ} : Literal N → R N ℚ
  | .positive i => X i
  | .negative i => 1 - X i

structure Clause (N : ℕ) where
  coefficient : ℚ
  factors : List (Literal N)

def Clause.polynomial {N : ℕ} (C : Clause N) : R N ℚ :=
  MvPolynomial.C C.coefficient * (C.factors.map Literal.polynomial).prod

def family {N : ℕ} {ι : Type*} (C : ι → Clause N) (j : ι) : R N ℚ :=
  (C j).polynomial

def lowerPair (N : ℕ) (i : Fin (N + 1)) : Prop :=
  3 ≤ i.val ∧ i.val % 2 = 1 ∧ 2 * i.val < N

instance (N : ℕ) : DecidablePred (lowerPair N) :=
  fun i => inferInstanceAs (Decidable (3 ≤ i.val ∧ i.val % 2 = 1 ∧ 2 * i.val < N))

def freeIndex (N : ℕ) (i : Fin (N + 1)) : Prop :=
  i.val = 2 ∨ i.val = N - 1 ∨ lowerPair N i

instance (N : ℕ) : DecidablePred (freeIndex N) :=
  fun i => inferInstanceAs (Decidable (i.val = 2 ∨ i.val = N - 1 ∨ lowerPair N i))

abbrev CubeVar (N : ℕ) := {i : Fin (N + 1) // freeIndex N i}

def dimension (N : ℕ) : ℕ := Fintype.card (CubeVar N)

inductive Factor (σ : Type*) where
  | zero
  | one
  | bit (v : σ)
  | negBit (v : σ)
  deriving DecidableEq

def Factor.negate {σ : Type*} : Factor σ → Factor σ
  | .zero => .one
  | .one => .zero
  | .bit v => .negBit v
  | .negBit v => .bit v

def boolValue (b : Bool) : ℚ := if b then 1 else 0

def Factor.value {σ : Type*} (b : σ → Bool) : Factor σ → ℚ
  | .zero => 0
  | .one => 1
  | .bit v => boolValue (b v)
  | .negBit v => 1 - boolValue (b v)

def coordinateFactor (N : ℕ) (i : Fin (N + 1)) : Factor (CubeVar N) :=
  if h : freeIndex N i then .bit ⟨i, h⟩ else
  if h : lowerPair N (complement N i) then
    .negBit ⟨complement N i, Or.inr (Or.inr h)⟩ else .zero

def cubePoint (N : ℕ) (b : CubeVar N → Bool) : Fin (N + 1) → ℚ :=
  fun i => (coordinateFactor N i).value b

def effectiveLiteral {N : ℕ} : Literal N → Factor (CubeVar N)
  | .positive i => coordinateFactor N i
  | .negative i => (coordinateFactor N i).negate

def effectiveFactors {N : ℕ} (C : Clause N) : List (Factor (CubeVar N)) :=
  C.factors.map effectiveLiteral

def automatic {N : ℕ} (C : Clause N) : Prop :=
  C.coefficient = 0 ∨ Factor.zero ∈ effectiveFactors C ∨
    ∃ v : CubeVar N, Factor.bit v ∈ effectiveFactors C ∧
      Factor.negBit v ∈ effectiveFactors C

def effectiveSupport {N : ℕ} (C : Clause N) : Finset (CubeVar N) :=
  Finset.univ.filter (fun v =>
    Factor.bit v ∈ effectiveFactors C ∨ Factor.negBit v ∈ effectiveFactors C)

def width {N : ℕ} (C : Clause N) : ℕ := (effectiveSupport C).card

def weight {N : ℕ} (C : Clause N) : ℕ := by
  classical
  exact if automatic C then 0 else 2 ^ (dimension N - width C)

namespace Factor

theorem value_boolean {σ : Type*} (b : σ → Bool) (f : Factor σ) :
    (f.value b) ^ 2 - f.value b = 0 := by
  cases f with
  | zero => norm_num [value]
  | one => norm_num [value]
  | bit v => cases h : b v <;> norm_num [value, boolValue, h]
  | negBit v => cases h : b v <;> norm_num [value, boolValue, h]

theorem value_negate {σ : Type*} (b : σ → Bool) (f : Factor σ) :
    f.negate.value b = 1 - f.value b := by
  cases f <;> simp [negate, value]

end Factor

theorem cubePoint_boolean (N : ℕ) (b : CubeVar N → Bool) (i : Fin (N + 1)) :
    eval (cubePoint N b) (booleanConstraint i) = 0 := by
  rw [booleanConstraint_eval]
  exact Factor.value_boolean b (coordinateFactor N i)

theorem cubePoint_coarse_zero (N : ℕ) (heven : Even N) (hN : 6 ≤ N)
    (b : CubeVar N → Bool) (i : Fin (N + 1)) (hi : coarseAllowed i) :
    cubePoint N b i = 0 := by
  have hmod : N % 2 = 0 := Nat.even_iff.mp heven
  have hbound : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  simp only [coarseAllowed, Nat.even_iff] at hi
  have hf : ¬ freeIndex N i := by
    simp only [freeIndex, lowerPair]
    omega
  have hl : ¬ lowerPair N (complement N i) := by
    simp only [lowerPair, complement]
    omega
  simp [cubePoint, coordinateFactor, hf, hl, Factor.value]

theorem cubePoint_coarse (N : ℕ) (heven : Even N) (hN : 6 ≤ N)
    (b : CubeVar N → Bool) (i : Fin (N + 1)) :
    eval (cubePoint N b) (coarseConstraint i) = 0 := by
  classical
  by_cases hi : coarseAllowed i
  · simp [coarseConstraint, hi, cubePoint_coarse_zero N heven hN b i hi]
  · simp [coarseConstraint, hi]

theorem cubePoint_complement_product (N : ℕ) (heven : Even N) (hN : 6 ≤ N)
    (b : CubeVar N → Bool) (i : Fin (N + 1)) :
    cubePoint N b i * cubePoint N b (complement N i) = 0 := by
  classical
  have hmod : N % 2 = 0 := Nat.even_iff.mp heven
  have hbound : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  have hcc : complement N (complement N i) = i := by
    apply Fin.ext
    simp only [complement]
    omega
  by_cases hf : freeIndex N i
  · have hf0 := hf
    rcases hf with htwo | hlast | hl
    · have hc : coarseAllowed (complement N i) := by
        simp only [coarseAllowed, complement, Nat.even_iff]
        omega
      rw [cubePoint_coarse_zero N heven hN b (complement N i) hc, mul_zero]
    · have hc : coarseAllowed (complement N i) := by
        simp only [coarseAllowed, complement, Nat.even_iff]
        omega
      rw [cubePoint_coarse_zero N heven hN b (complement N i) hc, mul_zero]
    · have hfc : ¬ freeIndex N (complement N i) := by
        simp only [freeIndex, lowerPair, complement] at hl ⊢
        omega
      cases hb : b ⟨i, hf0⟩ <;>
        simp [cubePoint, coordinateFactor, hf0, hfc, hcc, hl, Factor.value, boolValue, hb]
  · by_cases hl : lowerPair N (complement N i)
    · have hfc : freeIndex N (complement N i) := Or.inr (Or.inr hl)
      cases hb : b ⟨complement N i, hfc⟩ <;>
        simp [cubePoint, coordinateFactor, hf, hfc, hl, Factor.value, boolValue, hb]
    · simp [cubePoint, coordinateFactor, hf, hl, Factor.value]

theorem cubePoint_g_zero (N : ℕ) (heven : Even N) (hN : 6 ≤ N)
    (b : CubeVar N → Bool) : eval (cubePoint N b) (g N ℚ) = 0 := by
  simp only [g, map_sum, map_mul, eval_X]
  apply Finset.sum_eq_zero
  intro i _
  exact cubePoint_complement_product N heven hN b i

theorem literal_eval {N : ℕ} (b : CubeVar N → Bool) (l : Literal N) :
    eval (cubePoint N b) l.polynomial = (effectiveLiteral l).value b := by
  cases l with
  | positive i => simp [Literal.polynomial, effectiveLiteral, cubePoint]
  | negative i => simp [Literal.polynomial, effectiveLiteral, cubePoint, Factor.value_negate]

theorem clause_eval {N : ℕ} (b : CubeVar N → Bool) (C : Clause N) :
    eval (cubePoint N b) C.polynomial =
      C.coefficient * ((effectiveFactors C).map (Factor.value b)).prod := by
  simp only [Clause.polynomial, map_mul, eval_C, map_list_prod, effectiveFactors, List.map_map]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro l _
  exact literal_eval b l

theorem automatic_eval_zero {N : ℕ} (C : Clause N) (ha : automatic C)
    (b : CubeVar N → Bool) : eval (cubePoint N b) C.polynomial = 0 := by
  classical
  rw [clause_eval]
  rcases ha with hc | hz | ⟨v, hp, hn⟩
  · simp [hc]
  · have hm : (0 : ℚ) ∈ (effectiveFactors C).map (Factor.value b) :=
      List.mem_map.mpr ⟨Factor.zero, hz, rfl⟩
    rw [List.prod_eq_zero hm, mul_zero]
  · have hm : (0 : ℚ) ∈ (effectiveFactors C).map (Factor.value b) := by
      cases hb : b v
      · exact List.mem_map.mpr ⟨Factor.bit v, hp, by simp [Factor.value, boolValue, hb]⟩
      · exact List.mem_map.mpr ⟨Factor.negBit v, hn, by simp [Factor.value, boolValue, hb]⟩
    rw [List.prod_eq_zero hm, mul_zero]

theorem clause_nonzero_iff {N : ℕ} (C : Clause N) (ha : ¬ automatic C)
    (b : CubeVar N → Bool) :
    eval (cubePoint N b) C.polynomial ≠ 0 ↔
      ∀ v : CubeVar N,
        (Factor.bit v ∈ effectiveFactors C → b v = true) ∧
        (Factor.negBit v ∈ effectiveFactors C → b v = false) := by
  classical
  have hc : C.coefficient ≠ 0 := fun h => ha (Or.inl h)
  have hz : Factor.zero ∉ effectiveFactors C := fun h => ha (Or.inr (Or.inl h))
  have hprod : ((effectiveFactors C).map (Factor.value b)).prod ≠ 0 ↔
      ∀ f ∈ effectiveFactors C, f.value b ≠ 0 := by
    simp [List.prod_eq_zero_iff]
  rw [clause_eval, mul_ne_zero_iff, and_iff_right hc, hprod]
  constructor
  · intro hf v
    constructor
    · intro hp
      have h := hf (Factor.bit v) hp
      cases hb : b v <;> simp_all [Factor.value, boolValue]
    · intro hn
      have h := hf (Factor.negBit v) hn
      cases hb : b v <;> simp_all [Factor.value, boolValue]
  · intro hb f hf
    cases f with
    | zero => exact False.elim (hz hf)
    | one => norm_num [Factor.value]
    | bit v => simp [Factor.value, boolValue, (hb v).1 hf]
    | negBit v => simp [Factor.value, boolValue, (hb v).2 hf]

def choices {N : ℕ} (C : Clause N) (v : CubeVar N) : Finset Bool := by
  classical
  exact if Factor.bit v ∈ effectiveFactors C then {true} else
    if Factor.negBit v ∈ effectiveFactors C then {false} else Finset.univ

def badSet {N : ℕ} (C : Clause N) : Finset (CubeVar N → Bool) := by
  classical
  exact Finset.univ.filter (fun b => eval (cubePoint N b) C.polynomial ≠ 0)

theorem choices_mem_iff {N : ℕ} (C : Clause N) (ha : ¬ automatic C)
    (v : CubeVar N) (q : Bool) :
    q ∈ choices C v ↔
      (Factor.bit v ∈ effectiveFactors C → q = true) ∧
      (Factor.negBit v ∈ effectiveFactors C → q = false) := by
  classical
  by_cases hp : Factor.bit v ∈ effectiveFactors C <;>
    by_cases hn : Factor.negBit v ∈ effectiveFactors C
  · exact False.elim (ha (Or.inr (Or.inr ⟨v, hp, hn⟩)))
  · simp [choices, hp, hn]
  · simp [choices, hp, hn]
  · simp [choices, hp, hn]

theorem badSet_eq_piFinset {N : ℕ} (C : Clause N) (ha : ¬ automatic C) :
    badSet C = Fintype.piFinset (choices C) := by
  classical
  ext b
  simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  rw [clause_nonzero_iff C ha b]
  constructor
  · intro h v
    exact (choices_mem_iff C ha v (b v)).mpr (h v)
  · intro h v
    exact (choices_mem_iff C ha v (b v)).mp (h v)

theorem choices_card {N : ℕ} (C : Clause N) (v : CubeVar N) :
    (choices C v).card = if v ∈ effectiveSupport C then 1 else 2 := by
  classical
  by_cases hp : Factor.bit v ∈ effectiveFactors C <;>
    by_cases hn : Factor.negBit v ∈ effectiveFactors C <;>
    simp [choices, effectiveSupport, hp, hn]

theorem badSet_card {N : ℕ} (C : Clause N) : (badSet C).card = weight C := by
  classical
  by_cases ha : automatic C
  · have hempty : badSet C = ∅ := by
      ext b
      simp [badSet, automatic_eval_zero C ha b]
    simp [hempty, weight, ha]
  · rw [badSet_eq_piFinset C ha, Fintype.card_piFinset]
    simp only [weight, if_neg ha]
    calc
      (∏ v : CubeVar N, (choices C v).card) =
          ∏ v : CubeVar N, if v ∈ effectiveSupport C then 1 else 2 := by
        apply Finset.prod_congr rfl
        intro v _
        exact choices_card C v
      _ = 2 ^ (dimension N - width C) := by
        have hs : (Finset.univ.filter (fun v : CubeVar N => v ∉ effectiveSupport C)) =
            Finset.univ \ effectiveSupport C := by ext v; simp
        rw [Finset.prod_ite]
        simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
        rw [hs, Finset.card_sdiff (Finset.subset_univ (effectiveSupport C)), Finset.card_univ]
        rfl

theorem cube_card (N : ℕ) : Fintype.card (CubeVar N → Bool) = 2 ^ dimension N := by
  classical
  rw [Fintype.card_fun]
  simp [dimension]

theorem weighted_common_zero (N : ℕ) (heven : Even N) (hN : 6 ≤ N)
    {ι : Type*} [Fintype ι] (C : ι → Clause N)
    (hcover : (∑ j : ι, weight (C j)) < 2 ^ dimension N) :
    ∃ b : CubeVar N → Bool,
      (∀ j : ι, eval (cubePoint N b) (family C j) = 0) ∧
      (∀ i : Fin (N + 1), eval (cubePoint N b) (booleanConstraint i) = 0) ∧
      (∀ i : Fin (N + 1), eval (cubePoint N b) (coarseConstraint i) = 0) ∧
      eval (cubePoint N b) (g N ℚ) = 0 := by
  classical
  let bad : Finset (CubeVar N → Bool) := Finset.univ.biUnion (fun j : ι => badSet (C j))
  have hcard : bad.card < Fintype.card (CubeVar N → Bool) := by
    calc
      bad.card ≤ ∑ j : ι, (badSet (C j)).card := Finset.card_biUnion_le
      _ = ∑ j : ι, weight (C j) := by simp_rw [badSet_card]
      _ < 2 ^ dimension N := hcover
      _ = Fintype.card (CubeVar N → Bool) := (cube_card N).symm
  have hex : ∃ b : CubeVar N → Bool, b ∉ bad := by
    by_contra h
    push_neg at h
    have hu : bad = Finset.univ := Finset.eq_univ_of_forall h
    simp [hu] at hcard
  obtain ⟨b, hb⟩ := hex
  refine ⟨b, ?_, fun i => cubePoint_boolean N b i,
    fun i => cubePoint_coarse N heven hN b i, cubePoint_g_zero N heven hN b⟩
  intro j
  change eval (cubePoint N b) (C j).polynomial = 0
  by_contra hj
  apply hb
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, by simp [badSet, hj]⟩

end
end AlgebraicGoldbach.LiteralCube
