import Mathlib.Tactic
import TS.Goldbach.Strong.TS180.TriangleSplineTS94KernelEvidenceLedger
import TS.Goldbach.Strong.TS182.TriangleSplineDiscreteSieveTraceBridge
import TS.Goldbach.Strong.TS185.ExplicitFormulaZetaZeroFamilyLedger

namespace TS186
namespace Goldbach

/-!
# TS186 - Triangle Spline Main Term Normalization Bridge

TS184 makes the finite von Mangoldt side concrete.  TS185 prepares the
right-hand zeta-zero vocabulary.  This sprint closes the low-risk main-term
normalization needed between them: the triangle-spline kernel has value `1` at
the origin, so the future explicit-formula main term `X * F(0)` reduces to `X`.

The origin value was already proved when TS162 instantiated the triangle spline
as the trace kernel.  TS186 packages that value as a consumption bridge for the
explicit-formula front and also records the corresponding discrete weight at
`n = 0`.

TS186 does not prove the explicit formula, does not prove zeta-zero
summability, does not prove Plancherel, does not prove a sieve-trace
comparison, and does not prove Goldbach.
-/

/-- Continuous triangle-spline main-term normalization at the origin. -/
def TriangleSplineMainTermNormalizationStatement : Prop :=
  TS42.MellinJackson.triangleSpline 0 = 1

/-- The TS162 origin-value theorem supplies the main-term normalization. -/
theorem triangleSplineMainTermNormalization :
    TriangleSplineMainTermNormalizationStatement :=
  TS162.Goldbach.triangleSpline_zero

/-- The future continuous main term `X * F(0)` reduces to `X`. -/
def TriangleSplineScaledMainTermStatement
    (X : Nat) :
    Prop :=
  (X : Real) * TS42.MellinJackson.triangleSpline 0 = (X : Real)

/-- The continuous scaled main term is normalized for every natural scale. -/
theorem triangleSplineScaledMainTerm
    (X : Nat) :
    TriangleSplineScaledMainTermStatement X := by
  unfold TriangleSplineScaledMainTermStatement
  rw [triangleSplineMainTermNormalization]
  ring

/-- Discrete origin-weight normalization for positive scales. -/
def TriangleSplineDiscreteWeightAtZeroStatement
    (X : Nat) :
    Prop :=
  TS182.Goldbach.triangleSplineDiscreteWeight X 0 = 1

/-- The TS182 affine formula gives the discrete weight at zero. -/
theorem triangleSplineDiscreteWeightAtZero
    {X : Nat}
    (hX : 0 < X) :
    TriangleSplineDiscreteWeightAtZeroStatement X := by
  unfold TriangleSplineDiscreteWeightAtZeroStatement
  rw [TS182.Goldbach.triangleSplineDiscreteWeight_eq_one_sub
    hX (Nat.zero_le X)]
  norm_num

/-- The future discrete main term `X * F(0 / X)` reduces to `X`. -/
def TriangleSplineDiscreteScaledMainTermStatement
    (X : Nat) :
    Prop :=
  (X : Real) * TS182.Goldbach.triangleSplineDiscreteWeight X 0 =
    (X : Real)

/-- The discrete scaled main term is normalized for every positive scale. -/
theorem triangleSplineDiscreteScaledMainTerm
    {X : Nat}
    (hX : 0 < X) :
    TriangleSplineDiscreteScaledMainTermStatement X := by
  unfold TriangleSplineDiscreteScaledMainTermStatement
  rw [triangleSplineDiscreteWeightAtZero hX]
  ring

/-- Status markers for the TS186 main-term normalization bridge. -/
inductive MainTermNormalizationStatus where
  | continuousOriginValueReused
  | scaledMainTermNormalized
  | discreteOriginWeightNormalized
  deriving DecidableEq, Repr

/-- Ledger recording the TS186 main-term normalization bridge. -/
structure TriangleSplineMainTermNormalizationLedger where
  ts180_kernel_evidence :
    TS180.Goldbach.TriangleSplineTS94KernelEvidenceLedger

  ts185_zero_family_api :
    TS185.Goldbach.ExplicitFormulaZetaZeroFamilyLedger

  status :
    MainTermNormalizationStatus

  status_eq :
    status =
      MainTermNormalizationStatus.discreteOriginWeightNormalized

  origin_value :
    TriangleSplineMainTermNormalizationStatement

  scaled_main_term :
    forall X : Nat,
      TriangleSplineScaledMainTermStatement X

  discrete_origin_value :
    forall {X : Nat},
      0 < X ->
        TriangleSplineDiscreteWeightAtZeroStatement X

  discrete_scaled_main_term :
    forall {X : Nat},
      0 < X ->
        TriangleSplineDiscreteScaledMainTermStatement X

  explicit_formula_not_claimed :
    True

  zeta_zero_summability_not_claimed :
    True

  plancherel_not_claimed :
    True

  sieve_trace_comparison_not_claimed :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS186 main-term normalization ledger. -/
noncomputable def triangleSplineMainTermNormalizationLedger :
    TriangleSplineMainTermNormalizationLedger where
  ts180_kernel_evidence :=
    TS180.Goldbach.triangleSplineTS94KernelEvidenceLedger
  ts185_zero_family_api :=
    TS185.Goldbach.explicitFormulaZetaZeroFamilyLedger
  status := MainTermNormalizationStatus.discreteOriginWeightNormalized
  status_eq := rfl
  origin_value := triangleSplineMainTermNormalization
  scaled_main_term := triangleSplineScaledMainTerm
  discrete_origin_value := by
    intro X hX
    exact triangleSplineDiscreteWeightAtZero hX
  discrete_scaled_main_term := by
    intro X hX
    exact triangleSplineDiscreteScaledMainTerm hX
  explicit_formula_not_claimed := True.intro
  zeta_zero_summability_not_claimed := True.intro
  plancherel_not_claimed := True.intro
  sieve_trace_comparison_not_claimed := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS186. -/
def TriangleSplineMainTermNormalizationTarget : Prop :=
  Nonempty TriangleSplineMainTermNormalizationLedger

/-- The TS186 main-term normalization target is populated. -/
theorem triangleSplineMainTermNormalizationTarget :
    TriangleSplineMainTermNormalizationTarget :=
  Nonempty.intro triangleSplineMainTermNormalizationLedger

end Goldbach
end TS186
