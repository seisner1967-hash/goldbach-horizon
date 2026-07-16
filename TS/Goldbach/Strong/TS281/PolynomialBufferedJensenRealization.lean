import Mathlib.Tactic
import TS.Goldbach.Strong.TS280.CanonicalBoundaryNorm

/-!
# TS281 - Polynomial Buffered Jensen Realization

TS280 closed the generic finite Jensen chain for every supplied buffered
factorization.  This sprint constructs such a factorization for the concrete
finite zero polynomial itself.

For arbitrary `JensenFactorZeroData`, take

`f = finiteJensenZeroPolynomial`, `g = 1`.

The quotient is entire and nonvanishing, so this gives a genuine
`BufferedJensenFactorizationData`.  A finite product of the elementary bounds

`|z - rho| <= R + |rho - c|`

on the averaging sphere gives an explicit boundary majorant.  Thus the whole
TS274--TS280 Jensen pipeline is exercised without a compact supremum.

This is a polynomial realization, not a construction for Riemann xi.  No
Hadamard factorization, radius-growth estimate for xi, zeta-zero counting
estimate, explicit formula, Gallagher estimate, OTSA bridge, or Goldbach
statement is claimed.
-/

noncomputable section

namespace TS281
namespace Goldbach

open Complex Metric Set Topology

/-- The finite zero polynomial with constant nonvanishing quotient `1`. -/
noncomputable def polynomialBufferedJensenData
    (D : TS275.Goldbach.JensenFactorZeroData) :
    TS275.Goldbach.BufferedJensenFactorizationData where
  zeroData := D
  f := TS275.Goldbach.finiteJensenZeroPolynomial D
  g := fun _ => 1
  f_analytic :=
    TS275.Goldbach.finiteJensenZeroPolynomial_analyticOnNhd D _
  g_analytic := by
    intro z _
    exact analyticAt_const
  factorization := by
    intro z _
    simp
  g_nonzero := by
    intro z _
    exact one_ne_zero

/-- Factorwise radius bound used on the averaging sphere. -/
def polynomialBoundaryFactor
    (D : TS275.Goldbach.JensenFactorZeroData)
    (rho : Complex) : Real :=
  D.config.averagingRadius + Complex.abs (rho - D.config.center)

/-- Explicit finite-product boundary bound for the zero polynomial. -/
noncomputable def polynomialBoundaryNorm
    (D : TS275.Goldbach.JensenFactorZeroData) : Real :=
  max 1
    (Finset.prod D.factorZeros fun rho =>
      (polynomialBoundaryFactor D rho) ^ D.factorMultiplicity rho)

theorem polynomialBoundaryFactor_nonnegative
    (D : TS275.Goldbach.JensenFactorZeroData)
    (rho : Complex) :
    0 <= polynomialBoundaryFactor D rho := by
  unfold polynomialBoundaryFactor
  exact add_nonneg D.config.averagingRadius_positive.le
    (Complex.abs.nonneg (rho - D.config.center))

theorem abs_sub_le_polynomialBoundaryFactor
    (D : TS275.Goldbach.JensenFactorZeroData)
    (z rho : Complex)
    (hz :
      Complex.abs (z - D.config.center) = D.config.averagingRadius) :
    Complex.abs (z - rho) <= polynomialBoundaryFactor D rho := by
  have hDecompose :
      z - rho = (z - D.config.center) + (D.config.center - rho) := by
    ring
  rw [hDecompose]
  calc
    Complex.abs ((z - D.config.center) + (D.config.center - rho)) <=
        Complex.abs (z - D.config.center) +
          Complex.abs (D.config.center - rho) := by
      simpa [Complex.norm_eq_abs] using
        (norm_add_le (z - D.config.center) (D.config.center - rho))
    _ = polynomialBoundaryFactor D rho := by
      rw [hz]
      unfold polynomialBoundaryFactor
      congr 1
      rw [show D.config.center - rho = -(rho - D.config.center) by ring]
      exact AbsoluteValue.map_neg Complex.abs (rho - D.config.center)

theorem abs_zeroPolynomial_eq_factorProduct
    (D : TS275.Goldbach.JensenFactorZeroData)
    (z : Complex) :
    Complex.abs (TS275.Goldbach.finiteJensenZeroPolynomial D z) =
      Finset.prod D.factorZeros fun rho =>
        (Complex.abs (z - rho)) ^ D.factorMultiplicity rho := by
  classical
  unfold TS275.Goldbach.finiteJensenZeroPolynomial
  simp only [map_prod, map_pow]

theorem real_pow_le_real_pow_of_nonnegative
    {a b : Real}
    (ha : 0 <= a)
    (hab : a <= b)
    (n : Nat) :
    a ^ n <= b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hab ha (pow_nonneg (ha.trans hab) n)

theorem abs_zeroPolynomial_le_boundaryProduct
    (D : TS275.Goldbach.JensenFactorZeroData)
    (z : Complex)
    (hz :
      Complex.abs (z - D.config.center) = D.config.averagingRadius) :
    Complex.abs (TS275.Goldbach.finiteJensenZeroPolynomial D z) <=
      Finset.prod D.factorZeros fun rho =>
        (polynomialBoundaryFactor D rho) ^ D.factorMultiplicity rho := by
  rw [abs_zeroPolynomial_eq_factorProduct]
  refine Finset.prod_le_prod (fun rho _ => by positivity) ?_
  intro rho _
  exact real_pow_le_real_pow_of_nonnegative
      (Complex.abs.nonneg (z - rho))
      (abs_sub_le_polynomialBoundaryFactor D z rho hz)
      (D.factorMultiplicity rho)

theorem polynomialBoundaryNorm_positive
    (D : TS275.Goldbach.JensenFactorZeroData) :
    0 < polynomialBoundaryNorm D := by
  unfold polynomialBoundaryNorm
  exact zero_lt_one.trans_le (le_max_left _ _)

theorem abs_zeroPolynomial_le_polynomialBoundaryNorm
    (D : TS275.Goldbach.JensenFactorZeroData)
    (z : Complex)
    (hz :
      Complex.abs (z - D.config.center) = D.config.averagingRadius) :
    Complex.abs (TS275.Goldbach.finiteJensenZeroPolynomial D z) <=
      polynomialBoundaryNorm D :=
  (abs_zeroPolynomial_le_boundaryProduct D z hz).trans
    (le_max_right _ _)

/-- The explicit product bound fills the TS275 boundary contract. -/
noncomputable def polynomialBoundaryNormStatement
    (D : TS275.Goldbach.JensenFactorZeroData) :
    TS275.Goldbach.BoundaryNormOnAveragingSphereStatement
      (polynomialBufferedJensenData D) (polynomialBoundaryNorm D) where
  M_positive := polynomialBoundaryNorm_positive D
  norm_le := abs_zeroPolynomial_le_polynomialBoundaryNorm D

/-- Full finite Jensen boundary estimate for the concrete polynomial model. -/
theorem finiteJensenBoundaryEstimate_polynomial
    (D : TS275.Goldbach.JensenFactorZeroData) :
    TS274.Goldbach.FiniteJensenBoundaryEstimateStatement
      D.toJensenInnerZeroData.toFiniteJensenDiskData
      (TS275.Goldbach.finiteJensenZeroPolynomial D)
      (polynomialBoundaryNorm D) :=
  TS279.Goldbach.finiteJensenBoundaryEstimate_of_boundaryNorm
    (polynomialBufferedJensenData D)
    (polynomialBoundaryNorm D)
    (polynomialBoundaryNormStatement D)

/-- Explicit multiplicity-count quotient for the polynomial realization. -/
theorem finiteJensenMultiplicityCount_le_polynomialBoundaryNorm
    (D : TS275.Goldbach.JensenFactorZeroData) :
    (TS274.Goldbach.finiteJensenMultiplicityCount
        D.toJensenInnerZeroData.toFiniteJensenDiskData : Real) <=
      TS274.Goldbach.finiteJensenBoundaryLogBudget
          (polynomialBoundaryNorm D)
          (TS275.Goldbach.finiteJensenZeroPolynomial D D.config.center) /
        Real.log (D.config.averagingRadius / D.config.innerRadius) :=
  TS274.Goldbach.finiteJensenMultiplicityCount_le_boundaryLogQuotient
    D.toJensenInnerZeroData.toFiniteJensenDiskData
    (TS275.Goldbach.finiteJensenZeroPolynomial D)
    (polynomialBoundaryNorm D)
    (finiteJensenBoundaryEstimate_polynomial D)

/-- The canonical compact bound is no larger than the explicit product bound. -/
theorem canonicalBoundaryNorm_le_polynomialBoundaryNorm
    (D : TS275.Goldbach.JensenFactorZeroData) :
    TS280.Goldbach.canonicalBoundaryNorm (polynomialBufferedJensenData D) <=
      polynomialBoundaryNorm D := by
  unfold TS280.Goldbach.canonicalBoundaryNorm
  refine max_le
    (by
      unfold polynomialBoundaryNorm
      exact le_max_left _ _)
    ?_
  refine csSup_le ?_ ?_
  next =>
    exact Exists.intro
      (Complex.abs
        ((polynomialBufferedJensenData D).f
          (TS275.Goldbach.angularCirclePoint
            D.config.center D.config.averagingRadius 0)))
      (TS280.Goldbach.norm_mem_boundaryNormValues
        (polynomialBufferedJensenData D)
        (TS275.Goldbach.angularCirclePoint
          D.config.center D.config.averagingRadius 0)
        (TS275.Goldbach.angularCirclePoint_abs_sub_center
          D.config.center D.config.averagingRadius 0
          D.config.averagingRadius_positive.le))
  next =>
    intro value hValue
    cases' hValue with z hValue
    rw [<- hValue.2]
    rw [Metric.mem_sphere, dist_eq_norm, Complex.norm_eq_abs] at hValue
    exact abs_zeroPolynomial_le_polynomialBoundaryNorm D z hValue.1

structure PolynomialBufferedJensenRealizationLedger where
  ts280_canonical_boundary_norm :
    TS280.Goldbach.CanonicalBoundaryNormLedger

  buffered_polynomial_data :
    TS275.Goldbach.JensenFactorZeroData ->
      TS275.Goldbach.BufferedJensenFactorizationData

  explicit_boundary_norm :
    TS275.Goldbach.JensenFactorZeroData -> Real

  explicit_boundary_statement :
    forall D : TS275.Goldbach.JensenFactorZeroData,
      TS275.Goldbach.BoundaryNormOnAveragingSphereStatement
        (buffered_polynomial_data D) (explicit_boundary_norm D)

  polynomial_jensen_estimate :
    forall D : TS275.Goldbach.JensenFactorZeroData,
      TS274.Goldbach.FiniteJensenBoundaryEstimateStatement
        D.toJensenInnerZeroData.toFiniteJensenDiskData
        (TS275.Goldbach.finiteJensenZeroPolynomial D)
        (explicit_boundary_norm D)

  polynomial_counting_inequality :
    forall D : TS275.Goldbach.JensenFactorZeroData,
      (TS274.Goldbach.finiteJensenMultiplicityCount
          D.toJensenInnerZeroData.toFiniteJensenDiskData : Real) <=
        TS274.Goldbach.finiteJensenBoundaryLogBudget
            (explicit_boundary_norm D)
            (TS275.Goldbach.finiteJensenZeroPolynomial D D.config.center) /
          Real.log (D.config.averagingRadius / D.config.innerRadius)

  concrete_riemann_xi_not_defined : True
  xi_buffered_factorization_not_constructed : True
  xi_effective_radius_growth_not_proved : True
  zeta_zero_count_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_bridge_not_proved : True
  goldbach_not_claimed : True

noncomputable def polynomialBufferedJensenRealizationLedger :
    PolynomialBufferedJensenRealizationLedger where
  ts280_canonical_boundary_norm := TS280.Goldbach.canonicalBoundaryNormLedger
  buffered_polynomial_data := polynomialBufferedJensenData
  explicit_boundary_norm := polynomialBoundaryNorm
  explicit_boundary_statement := polynomialBoundaryNormStatement
  polynomial_jensen_estimate := finiteJensenBoundaryEstimate_polynomial
  polynomial_counting_inequality :=
    finiteJensenMultiplicityCount_le_polynomialBoundaryNorm
  concrete_riemann_xi_not_defined := True.intro
  xi_buffered_factorization_not_constructed := True.intro
  xi_effective_radius_growth_not_proved := True.intro
  zeta_zero_count_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_bridge_not_proved := True.intro
  goldbach_not_claimed := True.intro

def PolynomialBufferedJensenRealizationTarget : Prop :=
  Nonempty PolynomialBufferedJensenRealizationLedger

theorem polynomialBufferedJensenRealizationTarget :
    PolynomialBufferedJensenRealizationTarget :=
  Nonempty.intro polynomialBufferedJensenRealizationLedger

end Goldbach
end TS281
