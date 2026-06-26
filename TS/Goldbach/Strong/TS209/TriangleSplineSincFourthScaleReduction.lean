import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TS.Goldbach.Strong.TS208.TriangleSplinePlancherelEvidenceProbe

namespace TS209
namespace Goldbach

open MeasureTheory
open scoped ENNReal

/-!
# TS209 - Triangle Spline Sinc-Fourth Scale Reduction

TS208 isolated the Wall 1 kernel-specific Plancherel evidence to one scalar
identity:

`integral xi, triangleSplineSincRealWeight xi ^ 2 = 2 / 3`.

The TS178 spectral weight is the canonical squared-sinc profile evaluated at
`Real.pi * xi`.  This sprint removes the normalization ambiguity by proving
that the standard unscaled scalar identity

`integral t, canonicalSincSq t ^ 2 = 2 * Real.pi / 3`

implies the TS208 target exactly.  Thus the remaining Wall 1 calculation is a
canonical `sinc^4` integral, not a project-specific Fourier-scale question.

TS209 does not prove the canonical `sinc^4` integral itself, does not prove a
general Plancherel theorem, and does not prove the explicit formula,
Gallagher comparison, or Goldbach.
-/

/-- Canonical unscaled squared-sinc profile. -/
noncomputable def canonicalSincSq
    (t : Real) :
    Real :=
  if t = 0 then
    1
  else
    (Real.sin t / t) ^ 2

/-- The canonical unscaled scalar `sinc^4` value still to be proved. -/
def CanonicalSincFourthIntegralValueStatement : Prop :=
  integral
    (volume : Measure Real)
    (fun t : Real => canonicalSincSq t ^ 2) =
      (2 * Real.pi) / 3

/-- The TS178 pi-scaled spectral weight is the canonical profile at `pi * xi`. -/
theorem triangleSplineSincRealWeight_eq_canonical_comp_pi
    (xi : Real) :
    TS178.Goldbach.triangleSplineSincRealWeight xi =
      canonicalSincSq (Real.pi * xi) := by
  rfl

/--
The canonical `sinc^4` value implies the TS208 pi-scaled scalar integral.

This is just the global Haar scaling identity for Lebesgue measure under
`t = Real.pi * xi`, plus `0 < Real.pi`.
-/
theorem ts208SincFourthIntegral_of_canonicalSincFourthIntegral
    (h_canon : CanonicalSincFourthIntegralValueStatement) :
    TS208.Goldbach.TriangleSplineSincFourthIntegralValueStatement := by
  unfold TS208.Goldbach.TriangleSplineSincFourthIntegralValueStatement
  unfold CanonicalSincFourthIntegralValueStatement at h_canon
  have hrewrite :
      integral
        (volume : Measure Real)
        (fun xi : Real =>
          TS178.Goldbach.triangleSplineSincRealWeight xi ^ 2)
      =
      integral
        (volume : Measure Real)
        (fun xi : Real =>
          canonicalSincSq (Real.pi * xi) ^ 2) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (by
      intro xi
      change
        TS178.Goldbach.triangleSplineSincRealWeight xi ^ 2 =
          canonicalSincSq (Real.pi * xi) ^ 2
      rw [triangleSplineSincRealWeight_eq_canonical_comp_pi])
  have hscale :
      integral
        (volume : Measure Real)
        (fun xi : Real =>
          canonicalSincSq (Real.pi * xi) ^ 2)
      =
      |1 / Real.pi| *
        integral
          (volume : Measure Real)
          (fun t : Real =>
            canonicalSincSq t ^ 2) := by
    simpa [one_div, smul_eq_mul] using
      (Measure.integral_comp_mul_left
        (g := fun t : Real => canonicalSincSq t ^ 2)
        Real.pi)
  have habs :
      |1 / Real.pi| = 1 / Real.pi := by
    exact abs_of_pos (div_pos zero_lt_one Real.pi_pos)
  calc
    integral
        (volume : Measure Real)
        (fun xi : Real =>
          TS178.Goldbach.triangleSplineSincRealWeight xi ^ 2)
        =
      integral
        (volume : Measure Real)
        (fun xi : Real =>
          canonicalSincSq (Real.pi * xi) ^ 2) := hrewrite
    _ =
      |1 / Real.pi| *
        integral
          (volume : Measure Real)
          (fun t : Real =>
            canonicalSincSq t ^ 2) := hscale
    _ = (2 / 3 : Real) := by
      rw [h_canon, habs]
      change (1 / Real.pi) * ((2 * Real.pi) / 3) = (2 / 3 : Real)
      field_simp [Real.pi_ne_zero]

/--
The canonical unscaled `sinc^4` identity would populate the TS204 triangle
spline Plancherel input evidence through the TS208 reduction.
-/
theorem triangleSplinePlancherelInputEvidence_of_canonicalSincFourthIntegral
    (h_canon : CanonicalSincFourthIntegralValueStatement) :
    TS204.Goldbach.TriangleSplinePlancherelInputEvidence
      TS204.Goldbach.triangleSplinePlancherelInputContract := by
  exact
    TS208.Goldbach.triangleSplinePlancherelInputEvidence_of_sincFourthIntegral
      (ts208SincFourthIntegral_of_canonicalSincFourthIntegral h_canon)

/-- Ledger recording the TS209 sinc-fourth scale reduction. -/
structure TriangleSplineSincFourthScaleReductionLedger where
  ts208_plancherel_probe :
    TS208.Goldbach.TriangleSplinePlancherelEvidenceProbeLedger

  canonical_sinc_fourth_statement :
    Prop

  canonical_statement_implies_ts208_statement :
    canonical_sinc_fourth_statement ->
      TS208.Goldbach.TriangleSplineSincFourthIntegralValueStatement

  canonical_statement_implies_ts204_plancherel_evidence :
    canonical_sinc_fourth_statement ->
      TS204.Goldbach.TriangleSplinePlancherelInputEvidence
        TS204.Goldbach.triangleSplinePlancherelInputContract

  canonical_sinc_fourth_integral_not_proved :
    True

  general_plancherel_not_proved :
    True

  explicit_formula_not_proved :
    True

  gallagher_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS209 sinc-fourth scale reduction ledger. -/
noncomputable def triangleSplineSincFourthScaleReductionLedger :
    TriangleSplineSincFourthScaleReductionLedger where
  ts208_plancherel_probe :=
    TS208.Goldbach.triangleSplinePlancherelEvidenceProbeLedger
  canonical_sinc_fourth_statement :=
    CanonicalSincFourthIntegralValueStatement
  canonical_statement_implies_ts208_statement :=
    ts208SincFourthIntegral_of_canonicalSincFourthIntegral
  canonical_statement_implies_ts204_plancherel_evidence :=
    triangleSplinePlancherelInputEvidence_of_canonicalSincFourthIntegral
  canonical_sinc_fourth_integral_not_proved := True.intro
  general_plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS209. -/
def TriangleSplineSincFourthScaleReductionTarget : Prop :=
  Nonempty TriangleSplineSincFourthScaleReductionLedger

/-- The TS209 sinc-fourth scale reduction target is populated. -/
theorem triangleSplineSincFourthScaleReductionTarget :
    TriangleSplineSincFourthScaleReductionTarget :=
  Nonempty.intro triangleSplineSincFourthScaleReductionLedger

end Goldbach
end TS209
