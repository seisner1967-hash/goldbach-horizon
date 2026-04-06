import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

open scoped BigOperators
open Real

namespace HorizonMT

/-!
# Interfaces

This file contains only:

1. The canonical MT1/MT2 parameterization
2. The abstract objects manipulated by the HorizonMT scaffold
3. The external analytic interface axioms

No bridge axioms belong in this file.
No MT1/MT2 theorem proofs belong in this file.
-/

/- ============================================================
   SECTION 1 — Global constants
   ============================================================ -/

axiom eulerGamma : ℝ
axiom C2 : ℝ
axiom C2_pos : 0 < C2

/- ============================================================
   SECTION 2 — Canonical MT1 parameters
   ============================================================ -/

structure MT1Params where
  B : ℝ
  A : ℝ
  hA : 1 < A
  hB : 1 < B
  hAB : A < B

def canonicalMT1 : MT1Params where
  B := 7
  A := 2
  hA := by norm_num
  hB := by norm_num
  hAB := by norm_num

def Q_of (p : MT1Params) (N : ℝ) : ℝ :=
  (Real.log N) ^ p.B

def y_of (p : MT1Params) (N : ℝ) : ℝ :=
  (Real.log N) ^ p.A

def X_of (p : MT1Params) (N : ℝ) : ℝ :=
  N / Q_of p N

def smoothRatio (X y : ℝ) : ℝ :=
  Real.log X / Real.log y

/- ============================================================
   SECTION 3 — External analytic primitives
   ============================================================ -/

/-- Dickman rho function (declared early because smoothMainTerm uses it). -/
axiom dickmanRho : ℝ → ℝ

axiom dickmanRho_nonneg :
  ∀ u : ℝ, 0 ≤ u → 0 ≤ dickmanRho u

axiom dickmanRho_one :
  dickmanRho 1 = 1

axiom dickmanRho_antitone :
  ∀ u v : ℝ, 0 ≤ u → u ≤ v → dickmanRho v ≤ dickmanRho u

axiom dickmanRho_le_one :
  ∀ u : ℝ, 0 ≤ u → dickmanRho u ≤ 1

axiom dickmanRho_bound_3_5 :
  dickmanRho 3.5 ≤ 0.01537

/-- Canonical smooth-number main term appearing in MT1. -/
def smoothMainTerm (p : MT1Params) (N : ℝ) : ℝ :=
  dickmanRho (p.B / p.A) * Real.exp eulerGamma * p.A * Real.log (Real.log N)

axiom smoothCount : ℝ → ℝ → ℝ

axiom smoothCount_nonneg :
  ∀ X y : ℝ, 0 ≤ smoothCount X y

axiom smoothAmplifier : ℝ → ℝ

axiom smoothAmplifier_nonneg :
  ∀ y : ℝ, 0 ≤ smoothAmplifier y

axiom singularSeries : ℕ → ℝ

axiom singularSeries_nonneg :
  ∀ r : ℕ, 0 ≤ singularSeries r

axiom singularSeriesSum : ℝ → ℝ

axiom singularSeriesSum_nonneg :
  ∀ H : ℝ, 0 ≤ singularSeriesSum H

axiom pi2 : ℝ → ℕ → ℝ

axiom pi2_nonneg :
  ∀ N : ℝ, ∀ r : ℕ, 0 ≤ pi2 N r

def pairMainTerm (N : ℝ) (r : ℕ) : ℝ :=
  singularSeries r * N / (Real.log N) ^ 2

def pairError (N : ℝ) (r : ℕ) : ℝ :=
  pi2 N r - pairMainTerm N r

axiom pairSecondMoment : ℝ → ℝ → ℝ

axiom pairSecondMoment_nonneg :
  ∀ N X : ℝ, 0 ≤ pairSecondMoment N X

/- ============================================================
   SECTION 4 — External analytic interface axioms
   ============================================================ -/

axiom gallagher_mean_value
  (H : ℝ) (hH : 1 ≤ H) :
  ∃ C : ℝ, 0 < C ∧
    |singularSeriesSum H - 2 * C2 * H| ≤
      C * Real.sqrt H * Real.log H

axiom hildebrand_tenenbaum
  (X y : ℝ) (hX : 2 ≤ X) (hy : 2 ≤ y) :
  ∃ C : ℝ, 0 < C ∧
    let u := smoothRatio X y
    |smoothCount X y - X * dickmanRho u| ≤
      C * X * dickmanRho u / Real.log y

axiom brun_titchmarsh_pairs
  (N : ℝ) (r : ℕ)
  (hN : 4 ≤ N) (hr_even : Even r) (hr_le : (r : ℝ) ≤ N) :
  ∃ C : ℝ, 0 < C ∧
    pi2 N r ≤ C * singularSeries r * N / (Real.log N) ^ 2

axiom mertens_product_variant
  (y : ℝ) (hy : 3 ≤ y) :
  ∃ C : ℝ, 0 < C ∧
    |smoothAmplifier y - Real.exp eulerGamma * Real.log y| ≤
      C * Real.exp eulerGamma / Real.log y

axiom bombieri_vinogradov_pairs
  (N X A0 : ℝ)
  (hN : 4 ≤ N) (hX : 1 ≤ X) (hXN : X ≤ N) (hA0 : 0 < A0) :
  ∃ C : ℝ, 0 < C ∧
    pairSecondMoment N X ≤
      C * N ^ 2 / (Real.log N) ^ (4 + A0)

/- ============================================================
   SECTION 5 — Horizon abstract target objects
   ============================================================ -/

axiom R_smooth : MT1Params → ℝ → ℝ
axiom R_smooth_le_y : MT1Params → ℝ → ℝ
axiom R_smooth_gt_y : MT1Params → ℝ → ℝ

axiom clusterCount : MT1Params → ℝ → ℝ

axiom clusterCount_nonneg :
  ∀ p : MT1Params, ∀ N : ℝ, 0 ≤ clusterCount p N

axiom meanPairVariance : MT1Params → ℝ → ℝ
axiom meanPairVariance_smooth : MT1Params → ℝ → ℝ
axiom meanPairVariance_rough : MT1Params → ℝ → ℝ

axiom meanPairVariance_nonneg :
  ∀ p : MT1Params, ∀ N : ℝ, 0 ≤ meanPairVariance p N

end HorizonMT
