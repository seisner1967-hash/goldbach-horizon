import Mathlib.Tactic
import TS.Goldbach.Strong.TS273.LogLinearMultiplicityCountingReduction

/-!
# TS274 - Minimal Jensen Inequality Backport

The locked Mathlib revision has analytic orders and isolated-zero machinery,
but it does not yet contain the modern circle-average, harmonic mean-value,
and divisor infrastructure used by the current Jensen theorem.  This sprint
backports the finite counting core that is independent of that infrastructure.

For finitely many zeros in an inner disk, every Jensen weight

`log (R / |z - c|)`

is at least `log (R / r)`.  Consequently, any upper bound on the weighted
Jensen mass yields the standard multiplicity-counting quotient.  The proof
below includes the radius geometry, logarithmic monotonicity, finite summation,
and division by the positive logarithmic weight.

The remaining analytic input is named exactly: an upper bound on the weighted
mass by the boundary logarithmic budget.  No circle-average identity, harmonic
mean-value theorem, concrete xi function, zero-counting estimate, explicit
formula, Gallagher estimate, OTSA bridge, or Goldbach statement is claimed.
-/

namespace TS274
namespace Goldbach

/-- Finite zero data in a strict pair of concentric disks. -/
structure FiniteJensenDiskData where
  center : Complex
  innerRadius : Real
  outerRadius : Real
  zeros : Finset Complex
  multiplicity : Complex -> Nat

  innerRadius_positive :
    0 < innerRadius

  innerRadius_lt_outerRadius :
    innerRadius < outerRadius

  zero_ne_center :
    forall z : Complex,
      Membership.mem zeros z ->
        Not (z = center)

  zero_mem_innerDisk :
    forall z : Complex,
      Membership.mem zeros z ->
        Complex.abs (z - center) <= innerRadius

/-- The logarithmic Jensen weight of one selected zero. -/
noncomputable def finiteJensenWeight
    (D : FiniteJensenDiskData)
    (z : Complex) :
    Real :=
  Real.log (D.outerRadius / Complex.abs (z - D.center))

/-- Multiplicity-weighted Jensen mass of the selected finite zero family. -/
noncomputable def finiteJensenWeightedMass
    (D : FiniteJensenDiskData) :
    Real :=
  Finset.sum D.zeros
    (fun z => (D.multiplicity z : Real) * finiteJensenWeight D z)

/-- Natural-valued multiplicity count of the selected finite zero family. -/
def finiteJensenMultiplicityCount
    (D : FiniteJensenDiskData) :
    Nat :=
  Finset.sum D.zeros D.multiplicity

/-- Real-valued multiplicity mass used by the finite inequality. -/
noncomputable def finiteJensenMultiplicityMass
    (D : FiniteJensenDiskData) :
    Real :=
  Finset.sum D.zeros (fun z => (D.multiplicity z : Real))

/-- The real multiplicity mass is the cast of the natural count. -/
theorem finiteJensenMultiplicityMass_eq_count
    (D : FiniteJensenDiskData) :
    finiteJensenMultiplicityMass D =
      (finiteJensenMultiplicityCount D : Real) := by
  simp [finiteJensenMultiplicityMass, finiteJensenMultiplicityCount]

/-- The outer radius is positive. -/
theorem finiteJensen_outerRadius_positive
    (D : FiniteJensenDiskData) :
    0 < D.outerRadius :=
  D.innerRadius_positive.trans D.innerRadius_lt_outerRadius

/-- The quotient of the two radii is strictly greater than one. -/
theorem finiteJensen_one_lt_outerRadius_div_innerRadius
    (D : FiniteJensenDiskData) :
    1 < D.outerRadius / D.innerRadius := by
  calc
    1 = D.innerRadius / D.innerRadius := by
      rw [div_self D.innerRadius_positive.ne']
    _ < D.outerRadius / D.innerRadius :=
      (div_lt_div_iff_of_pos_right D.innerRadius_positive).mpr
        D.innerRadius_lt_outerRadius

/-- The logarithmic gap between the outer and inner radii is positive. -/
theorem finiteJensen_logRadiusGap_positive
    (D : FiniteJensenDiskData) :
    0 < Real.log (D.outerRadius / D.innerRadius) :=
  Real.log_pos (finiteJensen_one_lt_outerRadius_div_innerRadius D)

/-- Every selected zero has positive distance from the center. -/
theorem finiteJensen_zeroDistance_positive
    (D : FiniteJensenDiskData)
    (z : Complex)
    (hz : Membership.mem D.zeros z) :
    0 < Complex.abs (z - D.center) := by
  rw [<- Complex.norm_eq_abs, norm_pos_iff]
  exact sub_ne_zero.mpr (D.zero_ne_center z hz)

/-- Every inner-disk zero contributes at least the inner-radius Jensen weight. -/
theorem finiteJensen_logRadiusGap_le_weight
    (D : FiniteJensenDiskData)
    (z : Complex)
    (hz : Membership.mem D.zeros z) :
    Real.log (D.outerRadius / D.innerRadius) <=
      finiteJensenWeight D z := by
  have hOuter : 0 <= D.outerRadius :=
    (finiteJensen_outerRadius_positive D).le
  have hDistance : 0 < Complex.abs (z - D.center) :=
    finiteJensen_zeroDistance_positive D z hz
  have hRatio :
      D.outerRadius / D.innerRadius <=
        D.outerRadius / Complex.abs (z - D.center) :=
    div_le_div_of_nonneg_left hOuter hDistance (D.zero_mem_innerDisk z hz)
  exact Real.strictMonoOn_log.monotoneOn
    (div_pos (finiteJensen_outerRadius_positive D) D.innerRadius_positive)
    (div_pos (finiteJensen_outerRadius_positive D) hDistance)
    hRatio

/-- The multiplicity mass times the common weight is below the weighted mass. -/
theorem finiteJensenMultiplicityMass_mul_logRadiusGap_le_weightedMass
    (D : FiniteJensenDiskData) :
    finiteJensenMultiplicityMass D *
        Real.log (D.outerRadius / D.innerRadius) <=
      finiteJensenWeightedMass D := by
  unfold finiteJensenMultiplicityMass finiteJensenWeightedMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro z hz
  exact mul_le_mul_of_nonneg_left
    (finiteJensen_logRadiusGap_le_weight D z hz)
    (Nat.cast_nonneg (D.multiplicity z))

/-- The single analytic input left by this finite Jensen backport. -/
def FiniteJensenWeightedUpperBoundStatement
    (D : FiniteJensenDiskData)
    (budget : Real) :
    Prop :=
  finiteJensenWeightedMass D <= budget

/-- A weighted Jensen bound yields the usual finite counting quotient. -/
theorem finiteJensenMultiplicityMass_le_budget_div_logRadiusGap
    (D : FiniteJensenDiskData)
    (budget : Real)
    (hBudget : FiniteJensenWeightedUpperBoundStatement D budget) :
    finiteJensenMultiplicityMass D <=
      budget / Real.log (D.outerRadius / D.innerRadius) := by
  have hLog : 0 < Real.log (D.outerRadius / D.innerRadius) :=
    finiteJensen_logRadiusGap_positive D
  have hProduct :
      finiteJensenMultiplicityMass D *
          Real.log (D.outerRadius / D.innerRadius) <= budget :=
    (finiteJensenMultiplicityMass_mul_logRadiusGap_le_weightedMass D).trans
      hBudget
  calc
    finiteJensenMultiplicityMass D =
        (finiteJensenMultiplicityMass D *
            Real.log (D.outerRadius / D.innerRadius)) /
          Real.log (D.outerRadius / D.innerRadius) := by
      field_simp
    _ <= budget / Real.log (D.outerRadius / D.innerRadius) :=
      (div_le_div_iff_of_pos_right hLog).mpr hProduct

/-- Natural multiplicity count version of the finite Jensen inequality. -/
theorem finiteJensenMultiplicityCount_le_budget_div_logRadiusGap
    (D : FiniteJensenDiskData)
    (budget : Real)
    (hBudget : FiniteJensenWeightedUpperBoundStatement D budget) :
    (finiteJensenMultiplicityCount D : Real) <=
      budget / Real.log (D.outerRadius / D.innerRadius) := by
  rw [<- finiteJensenMultiplicityMass_eq_count D]
  exact finiteJensenMultiplicityMass_le_budget_div_logRadiusGap D budget hBudget

/-- Boundary logarithmic budget appearing in the classical Jensen inequality. -/
noncomputable def finiteJensenBoundaryLogBudget
    (M : Real)
    (centerValue : Complex) :
    Real :=
  Real.log (M / Complex.abs centerValue)

/-- The boundary budget is nonnegative when it dominates the center norm. -/
theorem finiteJensenBoundaryLogBudget_nonnegative
    (M : Real)
    (centerValue : Complex)
    (hCenter : 0 < Complex.abs centerValue)
    (hBound : Complex.abs centerValue <= M) :
    0 <= finiteJensenBoundaryLogBudget M centerValue := by
  unfold finiteJensenBoundaryLogBudget
  apply Real.log_nonneg
  calc
    1 = Complex.abs centerValue / Complex.abs centerValue := by
      rw [div_self hCenter.ne']
    _ <= M / Complex.abs centerValue :=
      (div_le_div_iff_of_pos_right hCenter).mpr hBound

/-- The missing circle-average step, isolated at its exact finite conclusion. -/
def FiniteJensenBoundaryEstimateStatement
    (D : FiniteJensenDiskData)
    (f : Complex -> Complex)
    (M : Real) :
    Prop :=
  FiniteJensenWeightedUpperBoundStatement D
    (finiteJensenBoundaryLogBudget M (f D.center))

/-- The finite Jensen counting inequality from the exact boundary estimate. -/
theorem finiteJensenMultiplicityCount_le_boundaryLogQuotient
    (D : FiniteJensenDiskData)
    (f : Complex -> Complex)
    (M : Real)
    (hJensen : FiniteJensenBoundaryEstimateStatement D f M) :
    (finiteJensenMultiplicityCount D : Real) <=
      finiteJensenBoundaryLogBudget M (f D.center) /
        Real.log (D.outerRadius / D.innerRadius) :=
  finiteJensenMultiplicityCount_le_budget_div_logRadiusGap D
    (finiteJensenBoundaryLogBudget M (f D.center)) hJensen

/-- Concrete ledger for the functional finite Jensen backport. -/
structure MinimalJensenInequalityBackportLedger where
  ts273_logLinearReduction :
    TS273.Goldbach.LogLinearMultiplicityCountingReductionLedger

  radius_weight_lower_bound :
    forall (D : FiniteJensenDiskData) (z : Complex),
      Membership.mem D.zeros z ->
        Real.log (D.outerRadius / D.innerRadius) <=
          finiteJensenWeight D z

  finite_counting_inequality :
    forall (D : FiniteJensenDiskData) (budget : Real),
      FiniteJensenWeightedUpperBoundStatement D budget ->
        (finiteJensenMultiplicityCount D : Real) <=
          budget / Real.log (D.outerRadius / D.innerRadius)

  boundary_counting_inequality :
    forall (D : FiniteJensenDiskData) (f : Complex -> Complex) (M : Real),
      FiniteJensenBoundaryEstimateStatement D f M ->
        (finiteJensenMultiplicityCount D : Real) <=
          finiteJensenBoundaryLogBudget M (f D.center) /
            Real.log (D.outerRadius / D.innerRadius)

  circle_average_identity_not_backported : True
  harmonic_mean_value_not_backported : True
  analytic_zero_finset_not_constructed : True
  riemann_xi_not_defined : True
  zeta_counting_estimate_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- The TS274 ledger records the proved finite Jensen counting core. -/
noncomputable def minimalJensenInequalityBackportLedger :
    MinimalJensenInequalityBackportLedger where
  ts273_logLinearReduction :=
    TS273.Goldbach.logLinearMultiplicityCountingReductionLedger
  radius_weight_lower_bound := finiteJensen_logRadiusGap_le_weight
  finite_counting_inequality :=
    finiteJensenMultiplicityCount_le_budget_div_logRadiusGap
  boundary_counting_inequality :=
    finiteJensenMultiplicityCount_le_boundaryLogQuotient
  circle_average_identity_not_backported := True.intro
  harmonic_mean_value_not_backported := True.intro
  analytic_zero_finset_not_constructed := True.intro
  riemann_xi_not_defined := True.intro
  zeta_counting_estimate_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS274. -/
def MinimalJensenInequalityBackportTarget : Prop :=
  Nonempty MinimalJensenInequalityBackportLedger

/-- TS274 proves the finite Jensen counting core without analytic overclaim. -/
theorem minimalJensenInequalityBackportTarget :
    MinimalJensenInequalityBackportTarget :=
  Nonempty.intro minimalJensenInequalityBackportLedger

end Goldbach
end TS274
