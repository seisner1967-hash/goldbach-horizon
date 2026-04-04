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
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Trace
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
    0 ≤ Matrix.trace S.K :=
  S.hK.trace_nonneg

-- PositiveWindowShadow : modèle de K_{corr,X} ∈ S₁ ────────────────
structure PositiveWindowShadow
    (n : Type*) [Fintype n] [DecidableEq n] where
  K : Matrix n n ℝ
  hK : K.PosDef

theorem trace_pos_of_positiveShadow
    {n : Type*} [Fintype n] [DecidableEq n]
    (S : PositiveWindowShadow n) :
    0 < Matrix.trace S.K :=
  S.hK.trace_pos

-- Factorisation modèle : K = Aᴴ * A (conjTranspose, API Mathlib) ──
theorem shadow_from_factorisation
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    (A.conjTranspose * A).PosSemidef := by
  simpa using Matrix.posSemidef_conjTranspose_mul_self (A := A)

-- trace(Aᴴ*A) ≥ 0 ─────────────────────────────────────────────────
theorem trace_nonneg_of_factorisation
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    0 ≤ Matrix.trace (A.conjTranspose * A) :=
  (shadow_from_factorisation A).trace_nonneg

end Goldbach
