import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import TS.Goldbach.Strong.TS286.RiemannXiMasterAPI

/-!
# TS287 - Riemann Xi Growth API Probe

TS286 exposed the complete xi/Jensen pipeline through a stable public API.
The remaining quantitative input is an explicit radius-dependent bound for
xi on the averaging sphere.

A global separated Gamma bound is not a sound primary interface: Gamma has
poles at the nonpositive integers, while the completed zeta expression has
the compensating cancellations.  This sprint therefore takes Mathlib's
entire regularized `completedRiemannZetaZero` as its primary growth object.

The elementary affine passage

`xi(z) = (z * (z - 1) * completedRiemannZetaZero(z) + 1) / 2`

is proved quantitatively and routed all the way to a finite Jensen
multiplicity-count bound.  Gamma and ordinary zeta contracts are recorded
only on safe regions for future construction of the primary input.

No complex Stirling bound, critical-strip zeta bound, effective completed
zeta growth, quantitative zero-counting asymptotic, explicit formula,
Gallagher estimate, OTSA bridge, or Goldbach theorem is claimed.
-/

noncomputable section

namespace TS287
namespace Goldbach

open Complex Metric Set Topology

/-- Standard target shape for a future explicit xi growth estimate. -/
noncomputable def xiGrowthEnvelope
    (C0 C1 R : Real) : Real :=
  Real.exp (C0 + C1 * R * Real.log (R + 2))

theorem xiGrowthEnvelope_positive
    (C0 C1 R : Real) :
    0 < xiGrowthEnvelope C0 C1 R :=
  Real.exp_pos _

/-- Final circle-growth statement anticipated by the quantitative pipeline. -/
structure XiCircleGrowthStatement
    (C0 C1 R0 : Real) : Prop where
  C0_nonnegative : 0 <= C0
  C1_nonnegative : 0 <= C1
  threshold_large : 2 <= R0
  norm_le :
    forall R : Real,
      R0 <= R ->
        forall z : Complex,
          Complex.abs z = R ->
            Complex.abs (TS.Goldbach.MasterAPI.xi z) <=
              xiGrowthEnvelope C0 C1 R

/-- Primary analytic input: a circle bound for the entire regularized
completed zeta function. -/
structure CompletedZetaZeroCircleGrowthStatement
    (A : Real -> Real) : Prop where
  norm_le :
    forall R : Real,
      2 <= R ->
        forall z : Complex,
          Complex.abs z = R ->
            Complex.abs (TS282.Goldbach.completedRiemannZetaZero z) <= A R

/-- Exploratory Gamma contract restricted to a pole-free right half-plane. -/
structure GammaSafeRightHalfPlaneGrowthStatement
    (G : Real -> Real) : Prop where
  norm_le :
    forall R : Real,
      2 <= R ->
        forall z : Complex,
          Complex.abs z <= R ->
          2 <= z.re ->
            Complex.abs (Complex.Gamma (z / 2)) <= G R

/-- Exploratory ordinary-zeta contract restricted to the Dirichlet region. -/
structure ZetaRightHalfPlaneGrowthStatement
    (Z : Real -> Real) : Prop where
  norm_le :
    forall R : Real,
      2 <= R ->
        forall z : Complex,
          Complex.abs z <= R ->
          2 <= z.re ->
            Complex.abs (riemannZeta z) <= Z R

/-- The locked Gamma API supplies differentiability away from its poles. -/
theorem gamma_differentiableAt_off_nonpositiveIntegers
    (s : Complex)
    (hs : forall m : Nat, Not (s = -m)) :
    DifferentiableAt Complex Complex.Gamma s :=
  Complex.differentiableAt_Gamma s hs

/-- The locked Gamma API supplies Euler's integral in the right half-plane. -/
theorem gamma_eq_eulerIntegral
    {s : Complex}
    (hs : 0 < s.re) :
    Complex.Gamma s = Complex.GammaIntegral s :=
  Complex.Gamma_eq_integral hs

/-- The locked zeta API supplies the Dirichlet series only for `1 < re s`. -/
theorem zeta_eq_dirichletSeries
    {s : Complex}
    (hs : 1 < s.re) :
    riemannZeta s =
      tsum (fun n : Nat => 1 / (n : Complex) ^ s) :=
  zeta_eq_tsum_one_div_nat_cpow hs

/-- Elementary control of the shifted linear factor on a radius-`R` circle. -/
theorem abs_sub_one_le
    (R : Real)
    (z : Complex)
    (hz : Complex.abs z = R) :
    Complex.abs (z - 1) <= R + 1 := by
  calc
    Complex.abs (z - 1) <= Complex.abs z + Complex.abs (1 : Complex) := by
      simpa [Complex.norm_eq_abs] using
        (norm_sub_le z (1 : Complex))
    _ = R + 1 := by
      rw [hz]
      norm_num

/-- The nonproblematic polynomial factor has quadratic radial growth. -/
theorem elementaryPolynomialFactor_bound
    (R : Real)
    (z : Complex)
    (hR : 0 <= R)
    (hz : Complex.abs z = R) :
    Complex.abs (z * (z - 1)) <= R * (R + 1) := by
  rw [Complex.abs.map_mul, hz]
  exact mul_le_mul_of_nonneg_left (abs_sub_one_le R z hz) hR

/-- Explicit xi majorant induced by a regularized completed-zeta majorant. -/
noncomputable def xiBoundaryMajorantFromCompletedZeta
    (A : Real -> Real)
    (R : Real) : Real :=
  max 1 ((R * (R + 1) * A R + 1) / 2)

theorem xiBoundaryMajorantFromCompletedZeta_positive
    (A : Real -> Real)
    (R : Real) :
    0 < xiBoundaryMajorantFromCompletedZeta A R := by
  unfold xiBoundaryMajorantFromCompletedZeta
  exact zero_lt_one.trans_le (le_max_left _ _)

/-- Exact algebraic bridge from regularized completed-zeta growth to xi
growth on a circle. -/
theorem xi_abs_le_boundaryMajorantFromCompletedZeta
    {A : Real -> Real}
    (H : CompletedZetaZeroCircleGrowthStatement A)
    (R : Real)
    (hR : 2 <= R)
    (z : Complex)
    (hz : Complex.abs z = R) :
    Complex.abs (TS.Goldbach.MasterAPI.xi z) <=
      xiBoundaryMajorantFromCompletedZeta A R := by
  have hRNonnegative : 0 <= R := zero_le_two.trans hR
  have hPolynomial := elementaryPolynomialFactor_bound R z hRNonnegative hz
  have hCompleted := H.norm_le R hR z hz
  have hProduct :
      Complex.abs
          (z * (z - 1) *
            TS282.Goldbach.completedRiemannZetaZero z) <=
        R * (R + 1) * A R := by
    rw [Complex.abs.map_mul]
    exact mul_le_mul hPolynomial hCompleted
      (Complex.abs.nonneg _)
      (mul_nonneg hRNonnegative (add_nonneg hRNonnegative zero_le_one))
  have hAdd :
      Complex.abs
          (z * (z - 1) *
              TS282.Goldbach.completedRiemannZetaZero z + 1) <=
        R * (R + 1) * A R + 1 := by
    calc
      Complex.abs
          (z * (z - 1) *
              TS282.Goldbach.completedRiemannZetaZero z + 1) <=
          Complex.abs
              (z * (z - 1) *
                TS282.Goldbach.completedRiemannZetaZero z) +
            Complex.abs (1 : Complex) := by
              simpa [Complex.norm_eq_abs] using
                (norm_add_le
                  (z * (z - 1) *
                    TS282.Goldbach.completedRiemannZetaZero z)
                  (1 : Complex))
      _ <= R * (R + 1) * A R + 1 := by
        simpa using add_le_add_right hProduct 1
  have hHalf :
      Complex.abs
          ((z * (z - 1) *
              TS282.Goldbach.completedRiemannZetaZero z + 1) / 2) <=
        (R * (R + 1) * A R + 1) / 2 := by
    rw [<- Complex.norm_eq_abs, norm_div, Complex.norm_eq_abs]
    norm_num
    exact (div_le_div_iff_of_pos_right (by norm_num : (0 : Real) < 2)).mpr hAdd
  rw [TS.Goldbach.MasterAPI.xi, TS282.Goldbach.riemannXiCandidate]
  exact hHalf.trans (le_max_right _ _)

namespace MasterAPIGeometry

@[simp]
theorem xi_geometry_center
    (r : Real)
    (hr : 0 < r) :
    (TS.Goldbach.MasterAPI.xi_geometry r hr).center = 0 := by
  rfl

@[simp]
theorem xi_geometry_innerRadius
    (r : Real)
    (hr : 0 < r) :
    (TS.Goldbach.MasterAPI.xi_geometry r hr).innerRadius = r := by
  rfl

@[simp]
theorem xi_factorization_config
    (r : Real)
    (hr : 0 < r) :
    (TS.Goldbach.MasterAPI.xi_factorization r hr).zeroData.config =
      TS.Goldbach.MasterAPI.xi_geometry r hr := by
  rfl

@[simp]
theorem xi_factorization_function
    (r : Real)
    (hr : 0 < r) :
    (TS.Goldbach.MasterAPI.xi_factorization r hr).f =
      TS.Goldbach.MasterAPI.xi := by
  rfl

end MasterAPIGeometry

/-- A primary completed-zeta growth input yields an explicit TS275 boundary
contract for the concrete xi factorization. -/
noncomputable def xi_explicitBoundaryNormStatement
    {A : Real -> Real}
    (H : CompletedZetaZeroCircleGrowthStatement A)
    (r : Real)
    (hr : 0 < r)
    (hLarge :
      2 <= (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius) :
    TS275.Goldbach.BoundaryNormOnAveragingSphereStatement
      (TS.Goldbach.MasterAPI.xi_factorization r hr)
      (xiBoundaryMajorantFromCompletedZeta A
        (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius) where
  M_positive := xiBoundaryMajorantFromCompletedZeta_positive _ _
  norm_le := by
    intro z hz
    have hzCircle :
        Complex.abs z =
          (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius := by
      simpa [MasterAPIGeometry.xi_geometry_center] using hz
    simpa [MasterAPIGeometry.xi_factorization_function] using
      (xi_abs_le_boundaryMajorantFromCompletedZeta H
        (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius
        hLarge z hzCircle)

/-- Explicit finite Jensen boundary estimate under the primary growth input. -/
theorem xi_finiteJensenBoundaryEstimate_explicit
    {A : Real -> Real}
    (H : CompletedZetaZeroCircleGrowthStatement A)
    (r : Real)
    (hr : 0 < r)
    (hLarge :
      2 <= (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius) :
    TS274.Goldbach.FiniteJensenBoundaryEstimateStatement
      (TS.Goldbach.MasterAPI.xi_disk_data r hr)
      TS.Goldbach.MasterAPI.xi
      (xiBoundaryMajorantFromCompletedZeta A
        (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius) := by
  simpa [TS.Goldbach.MasterAPI.xi_disk_data,
    TS.Goldbach.MasterAPI.xi_factorization,
    TS.Goldbach.MasterAPI.xi] using
    TS279.Goldbach.finiteJensenBoundaryEstimate_of_boundaryNorm
      (TS.Goldbach.MasterAPI.xi_factorization r hr)
      (xiBoundaryMajorantFromCompletedZeta A
        (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius)
      (xi_explicitBoundaryNormStatement H r hr hLarge)

/-- Terminal TS287 facade: a regularized completed-zeta circle bound gives a
fully explicit finite Jensen multiplicity-count quotient. -/
theorem xi_zero_count_le_explicit_completedZeta_majorant
    {A : Real -> Real}
    (H : CompletedZetaZeroCircleGrowthStatement A)
    (r : Real)
    (hr : 0 < r)
    (hLarge :
      2 <= (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius) :
    (TS274.Goldbach.finiteJensenMultiplicityCount
        (TS.Goldbach.MasterAPI.xi_disk_data r hr) : Real) <=
      TS274.Goldbach.finiteJensenBoundaryLogBudget
          (xiBoundaryMajorantFromCompletedZeta A
            (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius)
          (TS.Goldbach.MasterAPI.xi
            (TS.Goldbach.MasterAPI.xi_geometry r hr).center) /
        Real.log
          ((TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius /
            (TS.Goldbach.MasterAPI.xi_geometry r hr).innerRadius) :=
  TS274.Goldbach.finiteJensenMultiplicityCount_le_boundaryLogQuotient
    (TS.Goldbach.MasterAPI.xi_disk_data r hr)
    TS.Goldbach.MasterAPI.xi
    (xiBoundaryMajorantFromCompletedZeta A
      (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius)
    (xi_finiteJensenBoundaryEstimate_explicit H r hr hLarge)

/-- Ledger for the growth API probe and exact conditional routing. -/
structure RiemannXiGrowthAPIProbeLedger where
  ts286_master_api : TS286.Goldbach.RiemannXiMasterAPILedger
  elementary_polynomial_factor_bound :
    forall (R : Real) (z : Complex),
      0 <= R ->
      Complex.abs z = R ->
        Complex.abs (z * (z - 1)) <= R * (R + 1)
  completed_zeta_to_xi_growth :
    forall A : Real -> Real,
      CompletedZetaZeroCircleGrowthStatement A ->
        forall R : Real,
          2 <= R ->
            forall z : Complex,
              Complex.abs z = R ->
                Complex.abs (TS.Goldbach.MasterAPI.xi z) <=
                  xiBoundaryMajorantFromCompletedZeta A R
  explicit_growth_to_boundary_contract :
    forall A : Real -> Real,
      CompletedZetaZeroCircleGrowthStatement A ->
        forall r : Real,
          forall hr : 0 < r,
            2 <= (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius ->
              TS275.Goldbach.BoundaryNormOnAveragingSphereStatement
                (TS.Goldbach.MasterAPI.xi_factorization r hr)
                (xiBoundaryMajorantFromCompletedZeta A
                  (TS.Goldbach.MasterAPI.xi_geometry r hr).averagingRadius)
  complex_stirling_bound_not_proved : True
  critical_strip_zeta_bound_not_proved : True
  completed_zeta_effective_growth_not_proved : True
  quantitative_zero_count_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_bridge_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS287 ledger. -/
noncomputable def riemannXiGrowthAPIProbeLedger :
    RiemannXiGrowthAPIProbeLedger where
  ts286_master_api := TS286.Goldbach.riemannXiMasterAPILedger
  elementary_polynomial_factor_bound := elementaryPolynomialFactor_bound
  completed_zeta_to_xi_growth := by
    intro A H R hR z hz
    exact xi_abs_le_boundaryMajorantFromCompletedZeta H R hR z hz
  explicit_growth_to_boundary_contract := by
    intro A H r hr hLarge
    exact xi_explicitBoundaryNormStatement H r hr hLarge
  complex_stirling_bound_not_proved := True.intro
  critical_strip_zeta_bound_not_proved := True.intro
  completed_zeta_effective_growth_not_proved := True.intro
  quantitative_zero_count_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  otsa_bridge_not_proved := True.intro
  goldbach_not_claimed := True.intro

def RiemannXiGrowthAPIProbeTarget : Prop :=
  Nonempty RiemannXiGrowthAPIProbeLedger

theorem riemannXiGrowthAPIProbeTarget :
    RiemannXiGrowthAPIProbeTarget :=
  Nonempty.intro riemannXiGrowthAPIProbeLedger

end Goldbach
end TS287
