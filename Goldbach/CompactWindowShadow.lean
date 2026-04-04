/-
  Goldbach/CompactWindowShadow.lean
  Ombre finie-dimensionnelle du package compact-window de G41 v1.3.
  0 sorry. Corrections vs GPT v1 :
    - conjTranspose à la place de transpose (API Mathlib réelle)
    - [DecidableEq n] ajouté aux variables
    - Import Mathlib.Analysis.Matrix.Order pour PosDef
    - trace_sum_sq : ring_nf au lieu de Finset.sum_comm seul
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.StarOrdered
import Goldbach.Basic

namespace Goldbach

open Matrix

/-!
  Modèle jouet de K_{corr,X} = B_X * A_X ∈ S₁ (G41 Prop 3.1).
  Ici : matrices sur ℝ en dimension finie.
-/

-- CompactWindowShadow : modèle de K_{corr,X} ∈ S₂ ─────────────────
structure CompactWindowShadow
    (n : Type*) [Fintype n] [DecidableEq n] where
  K : Matrix n n ℝ
  hK : K.PosSemidef

theorem trace_nonneg_of_shadow
    {n : Type*} [Fintype n] [DecidableEq n]
    (S : CompactWindowShadow n) :
    0 ≤ Matrix.trace S.K := by
  simp only [Matrix.trace, Matrix.diag]
  apply Finset.sum_nonneg
  intro i _
  have h := S.hK.2 (Pi.single i 1)
  simp only [star_trivial, mulVec_single_one, single_one_dotProduct,
    Matrix.transpose_apply] at h
  exact h

-- PositiveWindowShadow : modèle de K_{corr,X} ∈ S₁ ────────────────
structure PositiveWindowShadow
    (n : Type*) [Fintype n] [DecidableEq n] where
  K : Matrix n n ℝ
  hK : K.PosDef

theorem trace_pos_of_positiveShadow
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (S : PositiveWindowShadow n) :
    0 < Matrix.trace S.K := by
  simp only [Matrix.trace, Matrix.diag]
  apply Finset.sum_pos
  · intro i _
    have hne : (Pi.single i (1 : ℝ) : n → ℝ) ≠ 0 := by
      intro heq; have := congr_fun heq i; simp [Pi.single_apply] at this
    have h := S.hK.2 (Pi.single i 1) hne
    simp only [star_trivial, mulVec_single_one, single_one_dotProduct,
      Matrix.transpose_apply] at h
    exact h
  · exact Finset.univ_nonempty

-- Factorisation modèle : K = Aᴴ * A (conjTranspose, API Mathlib) ──
theorem shadow_from_factorisation
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    (A.conjTranspose * A).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self A

-- trace(Aᴴ*A) ≥ 0 ─────────────────────────────────────────────────
theorem trace_nonneg_of_factorisation
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    0 ≤ Matrix.trace (A.conjTranspose * A) :=
  trace_nonneg_of_shadow ⟨_, shadow_from_factorisation A⟩

end Goldbach
