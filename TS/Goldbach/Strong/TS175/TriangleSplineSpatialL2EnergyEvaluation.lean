import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import TS.Goldbach.Strong.TS56.TriangleSplineBranchFormulae
import TS.Goldbach.Strong.TS174.TriangleSplinePlancherelInterfaceProbe

namespace TS175
namespace Goldbach

open MeasureTheory

/-!
# TS175 - Triangle Spline Spatial L2 Energy Evaluation

TS174 names the L2/Plancherel interface and leaves the actual Plancherel
isometry as a future analytic input.  This sprint evaluates the elementary
spatial square-energy constant of the triangle spline:

`int_{-1}^{1} triangleSpline(x)^2 dx = 2 / 3`.

This is the squared L2 norm on the time side, not the `eLpNorm` value itself.
The corresponding `eLpNorm` bridge, Plancherel theorem, spectral sinc
integrability, and explicit formula remain future work.
-/

/-- Spatial square-energy of the triangle spline over its support. -/
noncomputable def triangleSplineSpatialSquareEnergy :
    Real :=
  intervalIntegral
    (fun x : Real => (TS42.MellinJackson.triangleSpline x) ^ 2)
    (-1 : Real)
    1
    (volume : Measure Real)

/-- Target statement for the elementary spatial square-energy constant. -/
def TriangleSplineSpatialSquareEnergyStatement : Prop :=
  triangleSplineSpatialSquareEnergy = (2 / 3 : Real)

/-- The left affine branch contributes `1/3` to the square energy. -/
theorem leftBranchSquareIntegral_eq_one_third :
    intervalIntegral
      (fun x : Real => (1 + x) ^ 2)
      (-1 : Real)
      0
      (volume : Measure Real)
      =
    (1 / 3 : Real) := by
  have hpoly :
      (fun x : Real => (1 + x) ^ 2) =
        fun x : Real => 1 + 2 * x + x ^ 2 := by
    funext x
    ring
  rw [hpoly]
  have hconst :
      IntervalIntegrable
        (fun _x : Real => (1 : Real))
        volume
        (-1 : Real)
        0 := by
    apply Continuous.intervalIntegrable
    continuity
  have hlin :
      IntervalIntegrable
        (fun x : Real => 2 * x)
        volume
        (-1 : Real)
        0 := by
    apply Continuous.intervalIntegrable
    continuity
  have hsq :
      IntervalIntegrable
        (fun x : Real => x ^ 2)
        volume
        (-1 : Real)
        0 := by
    apply Continuous.intervalIntegrable
    continuity
  have hadd :
      IntervalIntegrable
        (fun x : Real => 1 + 2 * x)
        volume
        (-1 : Real)
        0 := by
    exact hconst.add hlin
  rw [intervalIntegral.integral_add hadd hsq]
  rw [intervalIntegral.integral_add hconst hlin]
  rw [intervalIntegral.integral_const_mul]
  norm_num [integral_one, integral_id, integral_pow]

/-- The right affine branch contributes `1/3` to the square energy. -/
theorem rightBranchSquareIntegral_eq_one_third :
    intervalIntegral
      (fun x : Real => (1 - x) ^ 2)
      (0 : Real)
      1
      (volume : Measure Real)
      =
    (1 / 3 : Real) := by
  have hpoly :
      (fun x : Real => (1 - x) ^ 2) =
        fun x : Real => 1 - 2 * x + x ^ 2 := by
    funext x
    ring
  rw [hpoly]
  have hconst :
      IntervalIntegrable
        (fun _x : Real => (1 : Real))
        volume
        (0 : Real)
        1 := by
    apply Continuous.intervalIntegrable
    continuity
  have hlin :
      IntervalIntegrable
        (fun x : Real => 2 * x)
        volume
        (0 : Real)
        1 := by
    apply Continuous.intervalIntegrable
    continuity
  have hsq :
      IntervalIntegrable
        (fun x : Real => x ^ 2)
        volume
        (0 : Real)
        1 := by
    apply Continuous.intervalIntegrable
    continuity
  have hsub :
      IntervalIntegrable
        (fun x : Real => 1 - 2 * x)
        volume
        (0 : Real)
        1 := by
    exact hconst.sub hlin
  rw [intervalIntegral.integral_add hsub hsq]
  rw [intervalIntegral.integral_sub hconst hlin]
  rw [intervalIntegral.integral_const_mul]
  norm_num [integral_one, integral_id, integral_pow]

/-- The squared triangle spline is interval-integrable on the left branch. -/
theorem triangleSplineSquare_intervalIntegrable_left :
    IntervalIntegrable
      (fun x : Real => (TS42.MellinJackson.triangleSpline x) ^ 2)
      volume
      (-1 : Real)
      0 := by
  have hbranch :
      IntervalIntegrable
        (fun x : Real => (1 + x) ^ 2)
        volume
        (-1 : Real)
        0 := by
    apply Continuous.intervalIntegrable
    continuity
  refine hbranch.congr ?_
  exact (ae_restrict_iff' measurableSet_uIoc).mpr (by
    filter_upwards with x hx
    have hxmem : (Set.Ioc (-1 : Real) 0) x := by
      simpa using hx
    have hx_left : -1 <= x := by
      exact le_of_lt hxmem.1
    have hx_right : x <= 0 := by
      exact hxmem.2
    rw [TS56.MellinJackson.triangleSpline_eq_one_add_of_left
      hx_left hx_right])

/-- The squared triangle spline is interval-integrable on the right branch. -/
theorem triangleSplineSquare_intervalIntegrable_right :
    IntervalIntegrable
      (fun x : Real => (TS42.MellinJackson.triangleSpline x) ^ 2)
      volume
      (0 : Real)
      1 := by
  have hbranch :
      IntervalIntegrable
        (fun x : Real => (1 - x) ^ 2)
        volume
        (0 : Real)
        1 := by
    apply Continuous.intervalIntegrable
    continuity
  refine hbranch.congr ?_
  exact (ae_restrict_iff' measurableSet_uIoc).mpr (by
    filter_upwards with x hx
    have hxmem : (Set.Ioc (0 : Real) 1) x := by
      simpa using hx
    have hx_left : 0 <= x := by
      exact le_of_lt hxmem.1
    have hx_right : x <= 1 := by
      exact hxmem.2
    rw [TS56.MellinJackson.triangleSpline_eq_one_sub_of_right
      hx_left hx_right])

/-- On the left interval, the squared spline equals the squared affine branch. -/
theorem triangleSplineSquare_left_eq_branch :
    intervalIntegral
      (fun x : Real => (TS42.MellinJackson.triangleSpline x) ^ 2)
      (-1 : Real)
      0
      (volume : Measure Real)
      =
    intervalIntegral
      (fun x : Real => (1 + x) ^ 2)
      (-1 : Real)
      0
      (volume : Measure Real) := by
  apply intervalIntegral.integral_congr
  intro x hx
  have hxmem : (Set.Icc (-1 : Real) 0) x := by
    simpa using hx
  change
    (TS42.MellinJackson.triangleSpline x) ^ 2 =
      (1 + x) ^ 2
  rw [TS56.MellinJackson.triangleSpline_eq_one_add_of_left
    hxmem.1 hxmem.2]

/-- On the right interval, the squared spline equals the squared affine branch. -/
theorem triangleSplineSquare_right_eq_branch :
    intervalIntegral
      (fun x : Real => (TS42.MellinJackson.triangleSpline x) ^ 2)
      (0 : Real)
      1
      (volume : Measure Real)
      =
    intervalIntegral
      (fun x : Real => (1 - x) ^ 2)
      (0 : Real)
      1
      (volume : Measure Real) := by
  apply intervalIntegral.integral_congr
  intro x hx
  have hxmem : (Set.Icc (0 : Real) 1) x := by
    simpa using hx
  change
    (TS42.MellinJackson.triangleSpline x) ^ 2 =
      (1 - x) ^ 2
  rw [TS56.MellinJackson.triangleSpline_eq_one_sub_of_right
    hxmem.1 hxmem.2]

/-- The spatial square-energy of the triangle spline is exactly `2/3`. -/
theorem triangleSplineSpatialSquareEnergy_eq_two_thirds :
    TriangleSplineSpatialSquareEnergyStatement := by
  unfold TriangleSplineSpatialSquareEnergyStatement
    triangleSplineSpatialSquareEnergy
  calc
    intervalIntegral
      (fun x : Real => (TS42.MellinJackson.triangleSpline x) ^ 2)
      (-1 : Real)
      1
      (volume : Measure Real)
        =
      intervalIntegral
        (fun x : Real => (TS42.MellinJackson.triangleSpline x) ^ 2)
        (-1 : Real)
        0
        (volume : Measure Real) +
      intervalIntegral
        (fun x : Real => (TS42.MellinJackson.triangleSpline x) ^ 2)
        (0 : Real)
        1
        (volume : Measure Real) := by
        exact
          (intervalIntegral.integral_add_adjacent_intervals
            triangleSplineSquare_intervalIntegrable_left
            triangleSplineSquare_intervalIntegrable_right).symm
    _ =
      intervalIntegral
        (fun x : Real => (1 + x) ^ 2)
        (-1 : Real)
        0
        (volume : Measure Real) +
      intervalIntegral
        (fun x : Real => (1 - x) ^ 2)
        (0 : Real)
        1
        (volume : Measure Real) := by
        rw [triangleSplineSquare_left_eq_branch,
          triangleSplineSquare_right_eq_branch]
    _ =
      (1 / 3 : Real) + (1 / 3 : Real) := by
        rw [leftBranchSquareIntegral_eq_one_third,
          rightBranchSquareIntegral_eq_one_third]
    _ =
      (2 / 3 : Real) := by
        norm_num

/-- Ledger for the TS175 spatial L2 square-energy evaluation. -/
structure TriangleSplineSpatialL2EnergyEvaluationLedger where
  ts174_plancherel_interface :
    TS174.Goldbach.TriangleSplinePlancherelInterfaceProbeLedger

  spatial_square_energy :
    Real

  spatial_square_energy_eq :
    spatial_square_energy =
      triangleSplineSpatialSquareEnergy

  spatial_square_energy_value :
    TriangleSplineSpatialSquareEnergyStatement

  eLpNorm_value_not_claimed :
    True

  plancherel_not_claimed :
    True

  spectral_sinc_integrability_not_claimed :
    True

  explicit_formula_not_claimed :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS175 spatial L2 square-energy ledger. -/
noncomputable def triangleSplineSpatialL2EnergyEvaluationLedger :
    TriangleSplineSpatialL2EnergyEvaluationLedger where
  ts174_plancherel_interface :=
    TS174.Goldbach.triangleSplinePlancherelInterfaceProbeLedger
  spatial_square_energy := triangleSplineSpatialSquareEnergy
  spatial_square_energy_eq := rfl
  spatial_square_energy_value :=
    triangleSplineSpatialSquareEnergy_eq_two_thirds
  eLpNorm_value_not_claimed := True.intro
  plancherel_not_claimed := True.intro
  spectral_sinc_integrability_not_claimed := True.intro
  explicit_formula_not_claimed := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS175. -/
def TriangleSplineSpatialL2EnergyEvaluationTarget : Prop :=
  Nonempty TriangleSplineSpatialL2EnergyEvaluationLedger

/-- The TS175 spatial L2 square-energy target is populated. -/
theorem triangleSplineSpatialL2EnergyEvaluationTarget :
    TriangleSplineSpatialL2EnergyEvaluationTarget :=
  Nonempty.intro triangleSplineSpatialL2EnergyEvaluationLedger

end Goldbach
end TS175
