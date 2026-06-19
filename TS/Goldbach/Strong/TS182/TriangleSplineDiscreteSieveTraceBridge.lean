import Mathlib.Tactic
import TS.Goldbach.Strong.TS181.ExplicitFormulaTraceBlueprint

namespace TS182
namespace Goldbach

/-!
# TS182 - Triangle Spline Discrete Sieve-Trace Bridge

TS181 opens the TS95 explicit-formula front by naming the local contracts that
would consume the TS180 triangle-spline kernel evidence.  This sprint moves in
the other direction: it connects the continuous triangle spline to the
discrete natural-number scale used by sieve and prime-sum ledgers.

For a positive scale `X`, the weight

`triangleSplineDiscreteWeight X n = triangleSpline ((n : Real) / X)`

is affine on `0 <= n <= X` and vanishes at and beyond `X`.  These elementary
facts are the local bridge needed before a later sprint can define weighted
von Mangoldt sums.

TS182 does not define a von Mangoldt sum, does not prove Plancherel, does not
construct zeta zeros, does not prove the explicit formula, and does not prove
Goldbach.
-/

/-- Discrete triangle-spline smoothing weight at scale `X`. -/
noncomputable def triangleSplineDiscreteWeight
    (X n : Nat) :
    Real :=
  TS42.MellinJackson.triangleSpline
    ((n : Real) / (X : Real))

/-- The discrete triangle-spline weight is nonnegative at every scale. -/
theorem triangleSplineDiscreteWeight_nonneg
    (X n : Nat) :
    0 <= triangleSplineDiscreteWeight X n := by
  unfold triangleSplineDiscreteWeight
  exact TS162.Goldbach.triangleSpline_nonneg _

/-- On the initial interval `n <= X`, the weight is the affine branch. -/
theorem triangleSplineDiscreteWeight_eq_one_sub
    {X n : Nat}
    (hX : 0 < X)
    (hn : n <= X) :
    triangleSplineDiscreteWeight X n =
      1 - (n : Real) / (X : Real) := by
  unfold triangleSplineDiscreteWeight
  apply TS56.MellinJackson.triangleSpline_eq_one_sub_of_right
  case hx0 =>
    exact div_nonneg (by exact_mod_cast Nat.zero_le n)
      (by exact_mod_cast Nat.zero_le X)
  case hx1 =>
    have hXreal : 0 < (X : Real) := by exact_mod_cast hX
    have hnreal : (n : Real) <= (X : Real) := by exact_mod_cast hn
    rw [div_le_one hXreal]
    simpa using hnreal

/-- At and beyond the scale `X`, the discrete weight vanishes. -/
theorem triangleSplineDiscreteWeight_eq_zero_of_X_le_n
    {X n : Nat}
    (hX : 0 < X)
    (hn : X <= n) :
    triangleSplineDiscreteWeight X n = 0 := by
  unfold triangleSplineDiscreteWeight
  have hXreal : 0 < (X : Real) := by exact_mod_cast hX
  have hnreal : (X : Real) <= (n : Real) := by exact_mod_cast hn
  have hratio :
      1 <= (n : Real) / (X : Real) := by
    rw [one_le_div hXreal]
    simpa using hnreal
  have habs :
      1 <= |(n : Real) / (X : Real)| :=
    le_trans hratio (le_abs_self _)
  exact TS162.Goldbach.triangleSpline_eq_zero_of_one_le_abs habs

/-- The boundary value at `n = X` is zero. -/
theorem triangleSplineDiscreteWeight_self
    {X : Nat}
    (hX : 0 < X) :
    triangleSplineDiscreteWeight X X = 0 :=
  triangleSplineDiscreteWeight_eq_zero_of_X_le_n hX le_rfl

/-- The affine and zero formulas agree at the boundary. -/
theorem triangleSplineDiscreteWeight_one_sub_at_boundary
    {X : Nat}
    (hX : 0 < X) :
    1 - (X : Real) / (X : Real) = 0 := by
  have hXreal : Not ((X : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt hX)
  field_simp [hXreal]

/-- Named status markers for the discrete sieve-trace bridge. -/
inductive TriangleSplineDiscreteBridgeStatus where
  | continuousKernelFromTS180
  | discreteWeightDefined
  | affineAndSupportFactsProved
  deriving DecidableEq, Repr

/-- Ledger recording the discrete evaluation of the triangle-spline kernel. -/
structure TriangleSplineDiscreteSieveTraceBridgeLedger where
  ts181_blueprint :
    TS181.Goldbach.TriangleSplineExplicitFormulaTraceBlueprintLedger

  status :
    TriangleSplineDiscreteBridgeStatus

  status_eq :
    status =
      TriangleSplineDiscreteBridgeStatus.affineAndSupportFactsProved

  discrete_weight :
    Nat -> Nat -> Real

  discrete_weight_eq :
    discrete_weight = triangleSplineDiscreteWeight

  discrete_weight_nonneg :
    forall X n : Nat,
      0 <= discrete_weight X n

  discrete_weight_eq_one_sub :
    forall {X n : Nat},
      0 < X ->
        n <= X ->
          discrete_weight X n =
            1 - (n : Real) / (X : Real)

  discrete_weight_eq_zero_of_X_le_n :
    forall {X n : Nat},
      0 < X ->
        X <= n ->
          discrete_weight X n = 0

  boundary_value :
    forall {X : Nat},
      0 < X ->
        discrete_weight X X = 0

  von_mangoldt_sum_not_defined :
    True

  plancherel_not_claimed :
    True

  zeta_zero_family_not_constructed :
    True

  explicit_formula_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS182 discrete sieve-trace bridge ledger. -/
noncomputable def triangleSplineDiscreteSieveTraceBridgeLedger :
    TriangleSplineDiscreteSieveTraceBridgeLedger where
  ts181_blueprint :=
    TS181.Goldbach.triangleSplineExplicitFormulaTraceBlueprintLedger
  status := TriangleSplineDiscreteBridgeStatus.affineAndSupportFactsProved
  status_eq := rfl
  discrete_weight := triangleSplineDiscreteWeight
  discrete_weight_eq := rfl
  discrete_weight_nonneg := triangleSplineDiscreteWeight_nonneg
  discrete_weight_eq_one_sub := by
    intro X n hX hn
    exact triangleSplineDiscreteWeight_eq_one_sub hX hn
  discrete_weight_eq_zero_of_X_le_n := by
    intro X n hX hn
    exact triangleSplineDiscreteWeight_eq_zero_of_X_le_n hX hn
  boundary_value := by
    intro X hX
    exact triangleSplineDiscreteWeight_self hX
  von_mangoldt_sum_not_defined := True.intro
  plancherel_not_claimed := True.intro
  zeta_zero_family_not_constructed := True.intro
  explicit_formula_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS182. -/
def TriangleSplineDiscreteSieveTraceBridgeTarget : Prop :=
  Nonempty TriangleSplineDiscreteSieveTraceBridgeLedger

/-- The TS182 discrete sieve-trace bridge target is populated. -/
theorem triangleSplineDiscreteSieveTraceBridgeTarget :
    TriangleSplineDiscreteSieveTraceBridgeTarget :=
  Nonempty.intro triangleSplineDiscreteSieveTraceBridgeLedger

end Goldbach
end TS182
