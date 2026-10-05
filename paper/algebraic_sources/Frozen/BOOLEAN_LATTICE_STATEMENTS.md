# Frozen BOOLEAN_LATTICE signatures

```lean
theorem toggle_involutive {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) : Function.Involutive (toggle i)

theorem up_eq_sum {σ : Type*} [Fintype σ] [DecidableEq σ] (f : Finset σ → ℚ) (s : Finset σ) :
    up f s = ∑ i : σ, raiseAt i f s

theorem down_eq_sum {σ : Type*} [Fintype σ] [DecidableEq σ] (f : Finset σ → ℚ) (s : Finset σ) :
    down f s = ∑ i : σ, lowerAt i f s

theorem raiseAt_sum {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) (F : σ → Finset σ → ℚ) (s : Finset σ) :
    raiseAt i (fun t => ∑ j : σ, F j t) s = ∑ j : σ, raiseAt i (F j) s

theorem lowerAt_sum {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) (F : σ → Finset σ → ℚ) (s : Finset σ) :
    lowerAt i (fun t => ∑ j : σ, F j t) s = ∑ j : σ, lowerAt i (F j) s

theorem coordinate_adjoint {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) (f h : Finset σ → ℚ) :
    (∑ s : Finset σ, raiseAt i f s * h s) =
      ∑ s : Finset σ, f s * lowerAt i h s

theorem coordinate_commute {σ : Type*} [Fintype σ] [DecidableEq σ] (i j : σ) (hij : i ≠ j) (f : Finset σ → ℚ)
    (s : Finset σ) :
    lowerAt i (raiseAt j f) s = raiseAt j (lowerAt i f) s

theorem coordinate_diagonal {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) (f : Finset σ → ℚ) (s : Finset σ) :
    lowerAt i (raiseAt i f) s - raiseAt i (lowerAt i f) s =
      (if i ∈ s then (-1 : ℚ) else 1) * f s

theorem adjoint {σ : Type*} [Fintype σ] [DecidableEq σ] (f h : Finset σ → ℚ) :
    (∑ s : Finset σ, up f s * h s) = ∑ s : Finset σ, f s * down h s

theorem commutator {σ : Type*} [Fintype σ] [DecidableEq σ] (f : Finset σ → ℚ) (s : Finset σ) :
    down (up f) s - up (down f) s =
      ((Fintype.card σ : ℚ) - 2 * (s.card : ℚ)) * f s

theorem up_injective_below_middle {σ : Type*} [Fintype σ] [DecidableEq σ]
    (k : ℕ) (hk : 2 * k < Fintype.card σ)
    (f : Finset σ → ℚ)
    (hlayer : ∀ s : Finset σ, s.card ≠ k → f s = 0)
    (hup : ∀ s : Finset σ, up f s = 0) : f = 0
```
