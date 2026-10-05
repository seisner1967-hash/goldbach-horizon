# Frozen LITERAL_CUBE signatures

```lean
theorem value_boolean {σ : Type*} (b : σ → Bool) (f : Factor σ) :
    (f.value b) ^ 2 - f.value b = 0

theorem value_negate {σ : Type*} (b : σ → Bool) (f : Factor σ) :
    f.negate.value b = 1 - f.value b

theorem cubePoint_boolean (N : ℕ) (b : CubeVar N → Bool) (i : Fin (N + 1)) :
    eval (cubePoint N b) (booleanConstraint i) = 0

theorem cubePoint_coarse_zero (N : ℕ) (heven : Even N) (hN : 6 ≤ N)
    (b : CubeVar N → Bool) (i : Fin (N + 1)) (hi : coarseAllowed i) :
    cubePoint N b i = 0

theorem cubePoint_coarse (N : ℕ) (heven : Even N) (hN : 6 ≤ N)
    (b : CubeVar N → Bool) (i : Fin (N + 1)) :
    eval (cubePoint N b) (coarseConstraint i) = 0

theorem cubePoint_complement_product (N : ℕ) (heven : Even N) (hN : 6 ≤ N)
    (b : CubeVar N → Bool) (i : Fin (N + 1)) :
    cubePoint N b i * cubePoint N b (complement N i) = 0

theorem cubePoint_g_zero (N : ℕ) (heven : Even N) (hN : 6 ≤ N)
    (b : CubeVar N → Bool) : eval (cubePoint N b) (g N ℚ) = 0

theorem literal_eval {N : ℕ} (b : CubeVar N → Bool) (l : Literal N) :
    eval (cubePoint N b) l.polynomial = (effectiveLiteral l).value b

theorem clause_eval {N : ℕ} (b : CubeVar N → Bool) (C : Clause N) :
    eval (cubePoint N b) C.polynomial =
      C.coefficient * ((effectiveFactors C).map (Factor.value b)).prod

theorem automatic_eval_zero {N : ℕ} (C : Clause N) (ha : automatic C)
    (b : CubeVar N → Bool) : eval (cubePoint N b) C.polynomial = 0

theorem clause_nonzero_iff {N : ℕ} (C : Clause N) (ha : ¬ automatic C)
    (b : CubeVar N → Bool) :
    eval (cubePoint N b) C.polynomial ≠ 0 ↔
      ∀ v : CubeVar N,
        (Factor.bit v ∈ effectiveFactors C → b v = true) ∧
        (Factor.negBit v ∈ effectiveFactors C → b v = false)

theorem choices_mem_iff {N : ℕ} (C : Clause N) (ha : ¬ automatic C)
    (v : CubeVar N) (q : Bool) :
    q ∈ choices C v ↔
      (Factor.bit v ∈ effectiveFactors C → q = true) ∧
      (Factor.negBit v ∈ effectiveFactors C → q = false)

theorem badSet_eq_piFinset {N : ℕ} (C : Clause N) (ha : ¬ automatic C) :
    badSet C = Fintype.piFinset (choices C)

theorem choices_card {N : ℕ} (C : Clause N) (v : CubeVar N) :
    (choices C v).card = if v ∈ effectiveSupport C then 1 else 2

theorem badSet_card {N : ℕ} (C : Clause N) : (badSet C).card = weight C

theorem cube_card (N : ℕ) : Fintype.card (CubeVar N → Bool) = 2 ^ dimension N

theorem weighted_common_zero (N : ℕ) (heven : Even N) (hN : 6 ≤ N)
    {ι : Type*} [Fintype ι] (C : ι → Clause N)
    (hcover : (∑ j : ι, weight (C j)) < 2 ^ dimension N) :
    ∃ b : CubeVar N → Bool,
      (∀ j : ι, eval (cubePoint N b) (family C j) = 0) ∧
      (∀ i : Fin (N + 1), eval (cubePoint N b) (booleanConstraint i) = 0) ∧
      (∀ i : Fin (N + 1), eval (cubePoint N b) (coarseConstraint i) = 0) ∧
      eval (cubePoint N b) (g N ℚ) = 0
```
