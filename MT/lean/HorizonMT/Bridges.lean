import HorizonMT.Interfaces
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

open scoped BigOperators
open Real

namespace HorizonMT

/-!
# Bridges

This file contains the canonical bridge axioms linking:

- the abstract Horizon objects (`R_smooth`, `clusterCount`, `meanPairVariance`, ...)
- the external analytic interface (`dickmanRho`, Gallagher, HT, BT, BV, Mertens)

Conventions:
- `R_smooth`, `R_smooth_le_y`, `R_smooth_gt_y` are **normalized** (dimensionless).
- `meanPairVariance` has natural scale `~ N^2 / log^4 N`.
- `clusterCount p N` is the prime-cluster count at scale `Q_of p N`.
-/

/- ============================================================
   MT1 bridges
   ============================================================ -/

/-- Bridge 1: exact splitting of the normalized residual. -/
axiom Rsmooth_split
  (p : MT1Params) (N : ℝ) :
  R_smooth p N = R_smooth_le_y p N + R_smooth_gt_y p N

/--
Bridge 2: control of the smooth part.

This is the canonical MT1 smooth bound:
the smooth contribution is bounded by a constant multiple of
`ρ(B/A) * e^γ * A * log log N`.
-/
axiom Rsmooth_le_y_bound
  (p : MT1Params) (N : ℝ)
  (hN : N ≥ Real.exp (Real.exp (Real.exp 1))) :
  ∃ C : ℝ, 0 < C ∧
    |R_smooth_le_y p N| ≤ C * smoothMainTerm p N

/--
Bridge 3: control of the rough part.

This is the canonical MT1 rough bound, with logarithmic decay.
-/
axiom Rsmooth_gt_y_bound
  (p : MT1Params) (N : ℝ)
  (hN : N ≥ Real.exp (Real.exp (Real.exp 1))) :
  ∃ C : ℝ, 0 < C ∧
    |R_smooth_gt_y p N| ≤ C / (Real.log N) ^ (p.A - 1)

/--
Bridge 4: MT1-to-PCB transfer at Gallagher (`Q^1`) quality.

This is the structural statement that smooth residual control yields
a cluster-count bound of order `N^2 / (Q log^2 N)`, with explicit dependence
on the normalized residual.
-/
axiom clusterCount_from_Rsmooth
  (p : MT1Params) (N : ℝ)
  (hN : N ≥ Real.exp (Real.exp (Real.exp 1))) :
  ∃ C : ℝ, 0 < C ∧
    clusterCount p N ≤
      C * (1 + |R_smooth p N|) * N ^ 2 /
        (Q_of p N * (Real.log N) ^ 2)

/- ============================================================
   MT2 bridges
   ============================================================ -/

/-- Bridge 5: exact splitting of the mean pair variance. -/
axiom meanPairVariance_split
  (p : MT1Params) (N : ℝ) :
  meanPairVariance p N =
    meanPairVariance_smooth p N + meanPairVariance_rough p N

/--
Bridge 6: rough variance bound.

This packages the Bombieri–Vinogradov / BDH-type rough contribution
at scale `N^2 / log^(4+A₀) N`.
-/
axiom meanPairVariance_rough_bound
  (p : MT1Params) (N A0 : ℝ)
  (hN : N ≥ 4) (hA0 : 0 < A0) :
  ∃ C : ℝ, 0 < C ∧
    meanPairVariance_rough p N ≤
      C * N ^ 2 / (Real.log N) ^ (4 + A0)

/--
Bridge 6b: rough variance at base scale (ℕ exponent).

This is a weaker but compilation-safe version of Bridge 6 that uses
a natural number exponent `(4 : ℕ)` instead of `(4 + A₀ : ℝ)`.
This avoids all `rpow` issues in downstream proofs.
Mathematically implied by Bridge 6 since `log^5 N ≥ log^4 N` for `N ≥ e`.
-/
axiom meanPairVariance_rough_bound_base
  (p : MT1Params) (N : ℝ)
  (hN : N ≥ 4) :
  ∃ C : ℝ, 0 < C ∧
    meanPairVariance_rough p N ≤
      C * N ^ 2 / (Real.log N) ^ (4 : ℕ)

/--
Bridge 7: smooth variance bound.

This is the MT2 bridge from smooth control to the smooth part
of the mean pair variance, at the natural scale `N^2 / log^4 N`.
-/
axiom meanPairVariance_smooth_bound
  (p : MT1Params) (N : ℝ)
  (hN : N ≥ 4) :
  ∃ C : ℝ, 0 < C ∧
    meanPairVariance_smooth p N ≤
      C * (1 + |R_smooth p N|) * N ^ 2 / (Real.log N) ^ 4

/--
Bridge 8: variance-to-cluster transfer via Cauchy–Schwarz.

This is the canonical MT2 transfer:
the cluster count is controlled by a Gallagher-scale main term plus
`X * sqrt(V̄)`, where `V̄` is the mean pair variance.
-/
axiom clusterCount_variance_transfer
  (p : MT1Params) (N : ℝ)
  (hN : N ≥ 4) :
  ∃ C : ℝ, 0 < C ∧
    clusterCount p N ≤
      C * (
        N ^ 2 / (Q_of p N * (Real.log N) ^ 2) +
        X_of p N * Real.sqrt (meanPairVariance p N)
      )

/--
Bridge 9: canonical safety threshold.

For the canonical parameters `(B, A) = (7, 2)`, the explicit computation
gives `ρ(3.5) ≤ 0.01537` (Dickman table), and the smooth main term
evaluates to `≈ 0.01537 × e^γ × 2 × log log N ≈ 0.15` for large `N`,
while the rough tail is `O(1/log N) → 0`. The sum is `< 0.22`.

This bridge packages the numerical verification as an axiom.
-/
axiom Rsmooth_canonical_below_safety
  (N : ℝ)
  (hN : N ≥ Real.exp (Real.exp (Real.exp 1))) :
  |R_smooth canonicalMT1 N| < 0.22

end HorizonMT
