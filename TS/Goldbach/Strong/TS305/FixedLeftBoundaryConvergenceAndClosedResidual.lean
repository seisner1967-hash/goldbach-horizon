import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
import TS.Goldbach.Strong.TS304.ClosedCompletionCorrectionAndHorizontalDecay

/-!
# TS305 - Fixed Left Boundary Convergence and Closed Residual

The horizontal Perron sides tend to zero, but the fixed left side does not.
It converges to a genuine improper vertical integral.  This module separates
that limit from its truncation error and routes a height-independent bound to
the TS298 left-side interface.

The locked Mathlib revision has no complex digamma or Stirling estimate.  The
only remaining analytic input is therefore exposed as the named logarithmic
bound `FixedLeftArchimedeanBoundData`.  The functional equation and the
absolutely convergent reflected Dirichlet series turn it into a complete
`FixedLeftLogDerivativeBoundData`.  From that one input, all geometry,
absolute integrability, convergence, and contour routing are proved here.

No exceptional residue inventory, Perron inversion, meromorphic residue
theorem, infinite explicit formula, Gallagher estimate, OTSA bridge, or
Goldbach theorem is claimed.
-/

noncomputable section

namespace TS305
namespace Goldbach

open Complex Filter MeasureTheory Metric Set Topology
open scoped Interval Topology

/-! ## Fixed-left geometry -/

/-- Point on the fixed Perron line `re(s) = -3/2`. -/
noncomputable def fixedLeftPoint (t : Real) : Complex :=
  (TS294.Goldbach.fixedPerronLeft : Complex) + (t : Complex) * I

@[simp] theorem fixedLeftPoint_re (t : Real) :
    (fixedLeftPoint t).re = TS294.Goldbach.fixedPerronLeft := by
  simp [fixedLeftPoint]

@[simp] theorem fixedLeftPoint_im (t : Real) :
    (fixedLeftPoint t).im = t := by
  simp [fixedLeftPoint]

theorem fixedLeftPoint_ne_zero (t : Real) :
    Not (fixedLeftPoint t = 0) := by
  intro h
  have hRe := congrArg Complex.re h
  norm_num [fixedLeftPoint, TS294.Goldbach.fixedPerronLeft] at hRe

theorem fixedLeftPoint_add_one_ne_zero (t : Real) :
    Not (fixedLeftPoint t + 1 = 0) := by
  intro h
  have hRe := congrArg Complex.re h
  norm_num [fixedLeftPoint, TS294.Goldbach.fixedPerronLeft] at hRe

/-- The reflected point lies on the absolutely convergent line `re = 5/2`. -/
noncomputable def fixedLeftReflectedPoint (t : Real) : Complex :=
  1 - fixedLeftPoint t

@[simp] theorem fixedLeftReflectedPoint_re (t : Real) :
    (fixedLeftReflectedPoint t).re = 5 / 2 := by
  norm_num [fixedLeftReflectedPoint, fixedLeftPoint,
    TS294.Goldbach.fixedPerronLeft]

@[simp] theorem fixedLeftReflectedPoint_im (t : Real) :
    (fixedLeftReflectedPoint t).im = -t := by
  simp [fixedLeftReflectedPoint, fixedLeftPoint]

/-! ## Functional-equation reduction -/

/-- Explicit factor in Mathlib's `zeta(1-s)` functional equation. -/
noncomputable def zetaLeftReflectionFactor (s : Complex) : Complex :=
  2 * (2 * Real.pi : Complex) ^ (-s) * Complex.Gamma s *
    Complex.cos (Real.pi * s / 2)

/-- Logarithmic derivative of the explicit reflection factor. -/
noncomputable def zetaLeftReflectionCorrection (s : Complex) : Complex :=
  logDeriv zetaLeftReflectionFactor s

theorem riemannZeta_one_sub_eq_reflectionFactor_mul
    {s : Complex}
    (hs : 1 < s.re) :
    riemannZeta (1 - s) =
      zetaLeftReflectionFactor s * riemannZeta s := by
  have hNotNeg : forall n : Nat, Not (s = -(n : Complex)) := by
    intro n h
    have hRe := congrArg Complex.re h
    simp at hRe
    have hn : 0 <= (n : Real) := Nat.cast_nonneg n
    linarith
  have hNeOne : Not (s = 1) := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    linarith
  simpa [zetaLeftReflectionFactor] using
    (riemannZeta_one_sub hNotNeg hNeOne)

theorem zetaLeftReflectionFactor_differentiableAt
    {s : Complex}
    (hs : 1 < s.re) :
    DifferentiableAt Complex zetaLeftReflectionFactor s := by
  have hNotNeg : forall n : Nat, Not (s = -(n : Complex)) := by
    intro n h
    have hRe := congrArg Complex.re h
    simp at hRe
    have hn : 0 <= (n : Real) := Nat.cast_nonneg n
    linarith
  let base : Complex := (2 * Real.pi : Real)
  have hBase : Not (base = 0) := by
    dsimp [base]
    exact_mod_cast mul_ne_zero (by norm_num : Not ((2 : Real) = 0)) Real.pi_ne_zero
  letI : NeZero base := { out := hBase }
  unfold zetaLeftReflectionFactor
  simpa [base, Function.comp_def] using
    ((((differentiableAt_const (2 : Complex)).mul
      ((differentiableAt_const_cpow_of_neZero base (-s)).comp s
        differentiableAt_id.neg)).mul
      (Complex.differentiableAt_Gamma s hNotNeg)).mul
      (Complex.differentiableAt_cos.comp s
        (((differentiableAt_const (Real.pi : Complex)).mul
          differentiableAt_id).div_const 2)))

theorem zetaLeftReflectionFactor_ne_zero_reflected
    (t : Real) :
    Not (zetaLeftReflectionFactor (fixedLeftReflectedPoint t) = 0) := by
  have hFE := riemannZeta_one_sub_eq_reflectionFactor_mul
    (s := fixedLeftReflectedPoint t)
      (by norm_num [fixedLeftReflectedPoint, TS294.Goldbach.fixedPerronLeft])
  have hLeft :
      Not (riemannZeta (1 - fixedLeftReflectedPoint t) = 0) := by
    have hEq : 1 - fixedLeftReflectedPoint t = fixedLeftPoint t := by
      unfold fixedLeftReflectedPoint
      ring
    rw [hEq]
    exact TS296.Goldbach.riemannZeta_ne_zero_on_fixed_left t
  intro hFactor
  apply hLeft
  rw [hFE, hFactor, zero_mul]

/-- Absolute Dirichlet mass on the reflected line `re = 5/2`. -/
noncomputable def fixedLeftReflectedVonMangoldtMass : Real :=
  tsum (fun n : Nat =>
    norm (LSeries.term TS298.Goldbach.vM ((5 / 2 : Real) : Complex) n))

theorem fixedLeftReflectedVonMangoldtMass_summable :
    Summable (fun n : Nat =>
      norm (LSeries.term TS298.Goldbach.vM
        ((5 / 2 : Real) : Complex) n)) := by
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := ((5 / 2 : Real) : Complex)) (by norm_num)).norm

theorem fixedLeftReflectedVonMangoldtMass_nonnegative :
    0 <= fixedLeftReflectedVonMangoldtMass := by
  unfold fixedLeftReflectedVonMangoldtMass
  exact tsum_nonneg (fun n => norm_nonneg _)

theorem norm_LSeries_vM_fixedLeftReflected_le
    (t : Real) :
    norm
        (LSeries TS298.Goldbach.vM (fixedLeftReflectedPoint t)) <=
      fixedLeftReflectedVonMangoldtMass := by
  have hsum :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := fixedLeftReflectedPoint t)
        (by norm_num [fixedLeftReflectedPoint, TS294.Goldbach.fixedPerronLeft])
  unfold LSeries fixedLeftReflectedVonMangoldtMass
  refine (norm_tsum_le_tsum_norm hsum.norm).trans_eq ?_
  apply tsum_congr
  intro n
  simp only [LSeries.norm_term_eq]
  congr 1
  simp [TS298.Goldbach.vM]

/-- Exact reflection identity for the logarithmic derivative on the fixed
left line.  The first term is purely archimedean and the second term is an
absolutely convergent Dirichlet series on `re = 5/2`. -/
theorem neg_riemannZeta_logDerivative_fixedLeft_eq_reflection_sub_LSeries
    (t : Real) :
    -deriv riemannZeta (fixedLeftPoint t) / riemannZeta (fixedLeftPoint t) =
      zetaLeftReflectionCorrection (fixedLeftReflectedPoint t) -
        LSeries TS298.Goldbach.vM (fixedLeftReflectedPoint t) := by
  let u := fixedLeftReflectedPoint t
  have hu : 1 < u.re := by
    dsimp [u]
    norm_num [fixedLeftReflectedPoint, TS294.Goldbach.fixedPerronLeft]
  have huLeft : 1 - u = fixedLeftPoint t := by
    dsimp [u, fixedLeftReflectedPoint]
    ring
  have hFactor : Not (zetaLeftReflectionFactor u = 0) := by
    dsimp [u]
    exact zetaLeftReflectionFactor_ne_zero_reflected t
  have hRight : Not (riemannZeta u = 0) :=
    riemannZeta_ne_zero_of_one_lt_re hu
  have hLeft : Not (riemannZeta (1 - u) = 0) := by
    rw [huLeft]
    exact TS296.Goldbach.riemannZeta_ne_zero_on_fixed_left t
  have hFactorDiff :
      DifferentiableAt Complex zetaLeftReflectionFactor u :=
    zetaLeftReflectionFactor_differentiableAt hu
  have hRightDiff : DifferentiableAt Complex riemannZeta u := by
    apply differentiableAt_riemannZeta
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    linarith
  have hLeftDiff : DifferentiableAt Complex riemannZeta (1 - u) := by
    apply differentiableAt_riemannZeta
    intro h
    have hRe := congrArg Complex.re h
    rw [huLeft] at hRe
    norm_num [fixedLeftPoint, TS294.Goldbach.fixedPerronLeft] at hRe
  have hOneSubDiff :
      DifferentiableAt Complex (fun z : Complex => 1 - z) u :=
    (differentiableAt_const (1 : Complex)).sub differentiableAt_id
  have hEventually :
      Filter.EventuallyEq (nhds u)
        (fun z : Complex => riemannZeta (1 - z))
        (fun z => zetaLeftReflectionFactor z * riemannZeta z) := by
    filter_upwards [
      (isOpen_lt continuous_const continuous_re).mem_nhds hu] with z hz
    exact riemannZeta_one_sub_eq_reflectionFactor_mul hz
  have hDeriv := Filter.EventuallyEq.deriv_eq hEventually
  have hPoint := hEventually.eq_of_nhds
  have hProduct :=
    logDeriv_mul u hFactor hRight hFactorDiff hRightDiff
  have hLogReflection :
      logDeriv (fun z : Complex => riemannZeta (1 - z)) u =
        zetaLeftReflectionCorrection u + logDeriv riemannZeta u := by
    unfold zetaLeftReflectionCorrection logDeriv
    change
      deriv (fun z : Complex => riemannZeta (1 - z)) u /
          riemannZeta (1 - u) =
        deriv zetaLeftReflectionFactor u / zetaLeftReflectionFactor u +
          deriv riemannZeta u / riemannZeta u
    rw [hDeriv, hPoint]
    exact hProduct
  have hComp := logDeriv_comp hLeftDiff hOneSubDiff
  have hComp' :
      logDeriv (fun z : Complex => riemannZeta (1 - z)) u =
        -logDeriv riemannZeta (1 - u) := by
    rw [deriv_const_sub, deriv_id''] at hComp
    simpa [Function.comp_def] using hComp
  have hDirichlet :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hu
  have hDirichlet' :
      LSeries TS298.Goldbach.vM u = -logDeriv riemannZeta u := by
    change
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) u =
        -logDeriv riemannZeta u
    simpa [logDeriv, neg_div] using hDirichlet
  rw [<- huLeft]
  change
    -deriv riemannZeta (1 - u) / riemannZeta (1 - u) =
      zetaLeftReflectionCorrection u - LSeries TS298.Goldbach.vM u
  rw [neg_div]
  change
    -logDeriv riemannZeta (1 - u) =
      zetaLeftReflectionCorrection u - LSeries TS298.Goldbach.vM u
  rw [<- hComp', hLogReflection, hDirichlet']
  ring

/-- Arithmetic scale carried by `x^s` on the fixed left line. -/
noncomputable def fixedLeftScale (x : Nat) : Real :=
  (x : Real) ^ (-3 / 2 : Real)

theorem fixedLeftScale_nonnegative (x : Nat) :
    0 <= fixedLeftScale x := by
  unfold fixedLeftScale
  positivity

theorem nat_cpow_fixedLeftPoint_norm
    (x : Nat)
    (t : Real) :
    norm ((x : Complex) ^ fixedLeftPoint t) = fixedLeftScale x := by
  rw [Complex.norm_natCast_cpow_of_re_ne_zero]
  all_goals simp [fixedLeftScale, fixedLeftPoint,
    TS294.Goldbach.fixedPerronLeft]

theorem fixedLeftPoint_norm_sq (t : Real) :
    norm (fixedLeftPoint t) ^ 2 = 9 / 4 + t ^ 2 := by
  rw [<- Complex.normSq_eq_norm_sq]
  norm_num [Complex.normSq_apply, fixedLeftPoint,
    TS294.Goldbach.fixedPerronLeft]
  ring

theorem fixedLeftPoint_add_one_norm_sq (t : Real) :
    norm (fixedLeftPoint t + 1) ^ 2 = 1 / 4 + t ^ 2 := by
  rw [<- Complex.normSq_eq_norm_sq]
  norm_num [Complex.normSq_apply, fixedLeftPoint,
    TS294.Goldbach.fixedPerronLeft]
  ring

theorem one_add_sq_le_two_mul_fixedLeft_denominator_norm
    (t : Real) :
    1 + t ^ 2 <=
      2 * (norm (fixedLeftPoint t) * norm (fixedLeftPoint t + 1)) := by
  have h0 := norm_nonneg (fixedLeftPoint t)
  have h1 := norm_nonneg (fixedLeftPoint t + 1)
  have hs := fixedLeftPoint_norm_sq t
  have hs1 := fixedLeftPoint_add_one_norm_sq t
  have hSq :
      (1 + t ^ 2) ^ 2 <=
        (2 * (norm (fixedLeftPoint t) *
          norm (fixedLeftPoint t + 1))) ^ 2 := by
    rw [mul_pow]
    nlinarith [sq_nonneg t]
  have hRight :
      0 <= 2 * (norm (fixedLeftPoint t) *
        norm (fixedLeftPoint t + 1)) := by positivity
  nlinarith

theorem triangleSplineMellinKernel_fixedLeft_norm_le
    (t : Real) :
    norm
        (TS257.Goldbach.triangleSplineMellinKernel
          (fixedLeftPoint t)) <=
      2 / (1 + t ^ 2) := by
  unfold TS257.Goldbach.triangleSplineMellinKernel
  rw [norm_div, norm_one, norm_mul]
  have hbase : 0 < 1 + t ^ 2 := by positivity
  have hprod :
      0 < norm (fixedLeftPoint t) * norm (fixedLeftPoint t + 1) :=
    mul_pos (norm_pos_iff.mpr (fixedLeftPoint_ne_zero t))
      (norm_pos_iff.mpr (fixedLeftPoint_add_one_ne_zero t))
  have h := one_div_le_one_div_of_le (by positivity : 0 < (1 + t ^ 2) / 2)
    (show (1 + t ^ 2) / 2 <=
      norm (fixedLeftPoint t) * norm (fixedLeftPoint t + 1) by
      linarith [one_add_sq_le_two_mul_fixedLeft_denominator_norm t])
  calc
    1 / (norm (fixedLeftPoint t) * norm (fixedLeftPoint t + 1)) <=
        1 / ((1 + t ^ 2) / 2) := h
    _ = 2 / (1 + t ^ 2) := by field_simp

/-! ## The precise remaining logarithmic input -/

/-- The real logarithmic weight expected from the reflected Gamma factor. -/
noncomputable def fixedLeftLogWeight (t : Real) : Real :=
  1 + Real.log (|t| + 2)

theorem fixedLeftLogWeight_pos (t : Real) :
    0 < fixedLeftLogWeight t := by
  unfold fixedLeftLogWeight
  have hArg : 1 < |t| + 2 := by
    have := abs_nonneg t
    linarith
  linarith [Real.log_pos hArg]

theorem one_le_fixedLeftLogWeight (t : Real) :
    1 <= fixedLeftLogWeight t := by
  unfold fixedLeftLogWeight
  have hArg : 1 <= |t| + 2 := by
    have := abs_nonneg t
    linarith
  linarith [Real.log_nonneg hArg]

theorem fixedLeftLogWeight_div_one_add_sq_le_japanese
    (t : Real) :
    fixedLeftLogWeight t / (1 + t ^ 2) <=
      5 * (1 + |t| ^ 2) ^ (-3 / 4 : Real) := by
  let A : Real := 1 + |t| ^ 2
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hAbsLeSqrt : |t| <= Real.sqrt A := by
    rw [Real.le_sqrt (abs_nonneg t) hApos.le]
    dsimp [A]
    nlinarith
  have hOneLeSqrt : 1 <= Real.sqrt A := by
    rw [Real.le_sqrt (by norm_num) hApos.le]
    dsimp [A]
    nlinarith [sq_nonneg |t|]
  have hArg : |t| + 2 <= 4 * Real.sqrt A := by
    linarith
  have hQuarterNonneg : 0 <= A ^ (1 / 4 : Real) := by positivity
  have hQuarterSq :
      (A ^ (1 / 4 : Real)) ^ 2 = Real.sqrt A := by
    rw [Real.sqrt_eq_rpow]
    rw [<- Real.rpow_natCast]
    rw [<- Real.rpow_mul hApos.le]
    norm_num
  have hSqrtArg :
      (|t| + 2) ^ (1 / 2 : Real) <= 2 * A ^ (1 / 4 : Real) := by
    have hArgPos : 0 <= |t| + 2 := by positivity
    have hLeftSq :
        ((|t| + 2) ^ (1 / 2 : Real)) ^ 2 = |t| + 2 := by
      rw [<- Real.rpow_natCast, <- Real.rpow_mul hArgPos]
      norm_num
    have hLeftNonneg : 0 <= (|t| + 2) ^ (1 / 2 : Real) := by positivity
    nlinarith
  have hLog :
      Real.log (|t| + 2) <= 2 * (|t| + 2) ^ (1 / 2 : Real) := by
    simpa [mul_comm] using
      (Real.log_le_rpow_div (show 0 <= |t| + 2 by positivity)
        (show 0 < (1 / 2 : Real) by norm_num))
  have hQuarterOne : 1 <= A ^ (1 / 4 : Real) := by
    exact Real.one_le_rpow (by
      dsimp [A]
      nlinarith [sq_nonneg |t|]) (by norm_num)
  have hWeight : fixedLeftLogWeight t <= 5 * A ^ (1 / 4 : Real) := by
    unfold fixedLeftLogWeight
    linarith
  have hDen : 1 + t ^ 2 = A := by
    dsimp [A]
    rw [_root_.sq_abs]
  rw [hDen]
  calc
    fixedLeftLogWeight t / A <=
        (5 * A ^ (1 / 4 : Real)) / A :=
      div_le_div_of_nonneg_right hWeight hApos.le
    _ = 5 * A ^ (-3 / 4 : Real) := by
      rw [div_eq_mul_inv, <- Real.rpow_neg_one]
      rw [mul_assoc, <- Real.rpow_add hApos]
      norm_num
    _ = 5 * (1 + |t| ^ 2) ^ (-3 / 4 : Real) := by rfl

theorem fixedLeftLogKernel_integrable :
    Integrable
      (fun t : Real => fixedLeftLogWeight t / (1 + t ^ 2)) := by
  have hJapanese :
      Integrable
        (fun t : Real => 5 * (1 + norm t ^ 2) ^ (-3 / 4 : Real)) := by
    have hRaw :
        Integrable
          (fun t : Real =>
            (1 + norm t ^ 2) ^ (-(3 / 2 : Real) / 2))
          (volume : Measure Real) :=
      integrable_rpow_neg_one_add_norm_sq
        (E := Real) (r := (3 / 2 : Real)) (by norm_num)
    have hBase := hRaw.const_mul 5
    convert hBase using 1
    all_goals norm_num
  have hMeasurable :
      AEStronglyMeasurable
        (fun t : Real => fixedLeftLogWeight t / (1 + t ^ 2)) volume := by
    apply Continuous.aestronglyMeasurable
    unfold fixedLeftLogWeight
    have hArg : Continuous (fun t : Real => |t| + 2) :=
      continuous_abs.add continuous_const
    have hLog : Continuous (fun t : Real => Real.log (|t| + 2)) :=
      hArg.log (fun t => by positivity)
    have hNum : Continuous (fun t : Real => 1 + Real.log (|t| + 2)) :=
      continuous_const.add hLog
    have hDen : Continuous (fun t : Real => 1 + t ^ 2) := by fun_prop
    exact hNum.div hDen (fun t => by positivity)
  refine hJapanese.mono' hMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs]
  rw [_root_.abs_of_nonneg (by
    exact div_nonneg (fixedLeftLogWeight_pos t).le (by positivity))]
  exact fixedLeftLogWeight_div_one_add_sq_le_japanese t

/-- The fixed numerical mass of the logarithmic kernel on the real line. -/
noncomputable def fixedLeftLogKernelMass : Real :=
  integral (volume : Measure Real)
    (fun t : Real => fixedLeftLogWeight t / (1 + t ^ 2))

theorem fixedLeftLogKernelMass_nonnegative :
    0 <= fixedLeftLogKernelMass := by
  unfold fixedLeftLogKernelMass
  exact integral_nonneg (fun t =>
    div_nonneg (fixedLeftLogWeight_pos t).le (by positivity))

/--
The single analytic input not supplied by the locked Gamma API: logarithmic
growth of the explicit reflection factor.  Everything involving zeta on the
reflected line has already been discharged by absolute Dirichlet convergence.
-/
structure FixedLeftArchimedeanBoundData where
  constant : Real
  constant_nonnegative : 0 <= constant
  norm_le : forall t : Real,
    norm (zetaLeftReflectionCorrection (fixedLeftReflectedPoint t)) <=
      constant * fixedLeftLogWeight t

/-- Complete logarithmic bound on the fixed left line. -/
structure FixedLeftLogDerivativeBoundData where
  constant : Real
  constant_nonnegative : 0 <= constant
  norm_le : forall t : Real,
    norm
        (-deriv riemannZeta (fixedLeftPoint t) /
          riemannZeta (fixedLeftPoint t)) <=
      constant * fixedLeftLogWeight t

/-- Reflection plus absolute Dirichlet convergence converts the sole
archimedean input into the complete left-line logarithmic bound. -/
noncomputable def FixedLeftArchimedeanBoundData.toLogDerivativeBoundData
    (A : FixedLeftArchimedeanBoundData) :
    FixedLeftLogDerivativeBoundData where
  constant := A.constant + fixedLeftReflectedVonMangoldtMass
  constant_nonnegative :=
    add_nonneg A.constant_nonnegative
      fixedLeftReflectedVonMangoldtMass_nonnegative
  norm_le := by
    intro t
    rw [neg_riemannZeta_logDerivative_fixedLeft_eq_reflection_sub_LSeries]
    calc
      norm
          (zetaLeftReflectionCorrection (fixedLeftReflectedPoint t) -
            LSeries TS298.Goldbach.vM (fixedLeftReflectedPoint t)) <=
          norm (zetaLeftReflectionCorrection (fixedLeftReflectedPoint t)) +
            norm (LSeries TS298.Goldbach.vM
              (fixedLeftReflectedPoint t)) := norm_sub_le _ _
      _ <= A.constant * fixedLeftLogWeight t +
          fixedLeftReflectedVonMangoldtMass :=
        add_le_add (A.norm_le t) (norm_LSeries_vM_fixedLeftReflected_le t)
      _ <= A.constant * fixedLeftLogWeight t +
          fixedLeftReflectedVonMangoldtMass * fixedLeftLogWeight t := by
        apply add_le_add_left
        calc
          fixedLeftReflectedVonMangoldtMass =
              fixedLeftReflectedVonMangoldtMass * 1 := by ring
          _ <= fixedLeftReflectedVonMangoldtMass * fixedLeftLogWeight t :=
            mul_le_mul_of_nonneg_left (one_le_fixedLeftLogWeight t)
              fixedLeftReflectedVonMangoldtMass_nonnegative
      _ = (A.constant + fixedLeftReflectedVonMangoldtMass) *
          fixedLeftLogWeight t := by ring

/-- The scalar majorant for the fixed-left Perron integrand. -/
noncomputable def fixedLeftIntegrandMajorant
    (x : Nat)
    (B : FixedLeftLogDerivativeBoundData)
    (t : Real) : Real :=
  2 * B.constant * fixedLeftScale x *
    (fixedLeftLogWeight t / (1 + t ^ 2))

theorem fixedLeftIntegrandMajorant_nonnegative
    (x : Nat)
    (B : FixedLeftLogDerivativeBoundData)
    (t : Real) :
    0 <= fixedLeftIntegrandMajorant x B t := by
  unfold fixedLeftIntegrandMajorant
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) B.constant_nonnegative)
      (fixedLeftScale_nonnegative x))
    (div_nonneg (fixedLeftLogWeight_pos t).le (by positivity))

/-- The un-oriented scalar integrand on the fixed left line. -/
noncomputable def fixedLeftIntegrand
    (x : Nat)
    (t : Real) : Complex :=
  TS293.Goldbach.triangleSplinePerronIntegrand x (fixedLeftPoint t)

theorem fixedLeftIntegrand_norm_le
    (x : Nat)
    (B : FixedLeftLogDerivativeBoundData)
    (t : Real) :
    norm (fixedLeftIntegrand x t) <= fixedLeftIntegrandMajorant x B t := by
  unfold fixedLeftIntegrand TS293.Goldbach.triangleSplinePerronIntegrand
    fixedLeftIntegrandMajorant
  simp only [norm_mul]
  have hZeta := B.norm_le t
  have hPow := nat_cpow_fixedLeftPoint_norm x t
  have hKernel := triangleSplineMellinKernel_fixedLeft_norm_le t
  rw [hPow]
  calc
    norm
          (-deriv riemannZeta (fixedLeftPoint t) /
            riemannZeta (fixedLeftPoint t)) *
        fixedLeftScale x *
          norm
            (TS257.Goldbach.triangleSplineMellinKernel
              (fixedLeftPoint t)) <=
          (B.constant * fixedLeftLogWeight t) * fixedLeftScale x *
          (2 / (1 + t ^ 2)) := by
      refine mul_le_mul ?_ hKernel (norm_nonneg _)
        (mul_nonneg
          (mul_nonneg B.constant_nonnegative (fixedLeftLogWeight_pos t).le)
          (fixedLeftScale_nonnegative x))
      exact mul_le_mul_of_nonneg_right hZeta (fixedLeftScale_nonnegative x)
    _ =
        2 * B.constant * fixedLeftScale x *
          (fixedLeftLogWeight t / (1 + t ^ 2)) := by ring

theorem fixedLeftIntegrandMajorant_integrable
    (x : Nat)
    (B : FixedLeftLogDerivativeBoundData) :
    Integrable (fixedLeftIntegrandMajorant x B) := by
  have h := fixedLeftLogKernel_integrable.const_mul
    (2 * B.constant * fixedLeftScale x)
  convert h using 1

theorem continuous_fixedLeftPoint : Continuous fixedLeftPoint := by
  unfold fixedLeftPoint
  fun_prop

theorem continuous_riemannZeta_fixedLeft :
    Continuous (fun t : Real => riemannZeta (fixedLeftPoint t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hs1 : Not (fixedLeftPoint t = 1) := by
    intro h
    have hRe := congrArg Complex.re h
    norm_num [fixedLeftPoint, TS294.Goldbach.fixedPerronLeft] at hRe
  exact (differentiableAt_riemannZeta hs1).continuousAt.comp
    continuous_fixedLeftPoint.continuousAt

theorem continuous_fixedLeftPower
    (x : Nat)
    (hx : 0 < x) :
    Continuous (fun t : Real => (x : Complex) ^ fixedLeftPoint t) := by
  apply continuous_fixedLeftPoint.const_cpow
  left
  exact_mod_cast (ne_of_gt hx)

theorem continuous_fixedLeftMellinKernel :
    Continuous
      (fun t : Real =>
        TS257.Goldbach.triangleSplineMellinKernel (fixedLeftPoint t)) := by
  unfold TS257.Goldbach.triangleSplineMellinKernel
  exact continuous_const.div
    (continuous_fixedLeftPoint.mul (continuous_fixedLeftPoint.add continuous_const))
    (fun t => mul_ne_zero (fixedLeftPoint_ne_zero t)
      (fixedLeftPoint_add_one_ne_zero t))

theorem fixedLeftIntegrand_aestronglyMeasurable
    (x : Nat)
    (hx : 0 < x) :
    AEStronglyMeasurable (fixedLeftIntegrand x) := by
  have hPointMeasurable : Measurable fixedLeftPoint :=
    continuous_fixedLeftPoint.measurable
  have hDeriv : StronglyMeasurable
      (fun t : Real => deriv riemannZeta (fixedLeftPoint t)) :=
    (stronglyMeasurable_deriv riemannZeta).comp_measurable hPointMeasurable
  have hZeta : StronglyMeasurable
      (fun t : Real => riemannZeta (fixedLeftPoint t)) :=
    continuous_riemannZeta_fixedLeft.stronglyMeasurable
  have hLogDerivMeasurable : Measurable
      (fun t : Real =>
        -deriv riemannZeta (fixedLeftPoint t) /
          riemannZeta (fixedLeftPoint t)) :=
    hDeriv.measurable.neg.div hZeta.measurable
  have hLogDeriv : StronglyMeasurable
      (fun t : Real =>
        -deriv riemannZeta (fixedLeftPoint t) /
          riemannZeta (fixedLeftPoint t)) :=
    hLogDerivMeasurable.stronglyMeasurable
  have hPow : StronglyMeasurable
      (fun t : Real => (x : Complex) ^ fixedLeftPoint t) :=
    (continuous_fixedLeftPower x hx).stronglyMeasurable
  have hKernel : StronglyMeasurable
      (fun t : Real =>
        TS257.Goldbach.triangleSplineMellinKernel (fixedLeftPoint t)) :=
    continuous_fixedLeftMellinKernel.stronglyMeasurable
  unfold fixedLeftIntegrand TS293.Goldbach.triangleSplinePerronIntegrand
  exact ((hLogDeriv.mul hPow).mul hKernel).aestronglyMeasurable

theorem fixedLeftIntegrand_integrable
    (x : Nat)
    (hx : 0 < x)
    (B : FixedLeftLogDerivativeBoundData) :
    Integrable (fixedLeftIntegrand x) := by
  exact (fixedLeftIntegrandMajorant_integrable x B).mono'
    (fixedLeftIntegrand_aestronglyMeasurable x hx)
    (Filter.Eventually.of_forall (fixedLeftIntegrand_norm_le x B))

/-- Height-independent `O(x^(-3/2))` envelope for the full left integral. -/
noncomputable def fixedLeftUniformBound
    (x : Nat)
    (B : FixedLeftLogDerivativeBoundData) : Real :=
  2 * B.constant * fixedLeftScale x * fixedLeftLogKernelMass

theorem fixedLeftUniformBound_nonnegative
    (x : Nat)
    (B : FixedLeftLogDerivativeBoundData) :
    0 <= fixedLeftUniformBound x B := by
  unfold fixedLeftUniformBound
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) B.constant_nonnegative)
      (fixedLeftScale_nonnegative x))
    fixedLeftLogKernelMass_nonnegative

/-! ## Improper limit and contour compatibility -/

/-- The full upward-oriented fixed-left vertical integral. -/
noncomputable def fixedLeftBoundaryLimit (x : Nat) : Complex :=
  I * integral (volume : Measure Real) (fixedLeftIntegrand x)

/-- Symmetric finite truncation of the upward-oriented fixed-left side. -/
noncomputable def fixedLeftBoundaryTruncation
    (x : Nat)
    (tau : Real) : Complex :=
  I * intervalIntegral (fun t : Real => fixedLeftIntegrand x t) (-tau) tau
    (volume : Measure Real)

theorem fixedLeftBoundaryLimit_norm_le
    (x : Nat)
    (B : FixedLeftLogDerivativeBoundData) :
    norm (fixedLeftBoundaryLimit x) <= fixedLeftUniformBound x B := by
  unfold fixedLeftBoundaryLimit fixedLeftUniformBound
  rw [norm_mul, norm_I, one_mul]
  have hNorm :
      norm ((integral (volume : Measure Real)) (fixedLeftIntegrand x)) <=
        (integral (volume : Measure Real))
          (fixedLeftIntegrandMajorant x B) :=
    MeasureTheory.norm_integral_le_of_norm_le
      (fixedLeftIntegrandMajorant_integrable x B)
      (Filter.Eventually.of_forall (fixedLeftIntegrand_norm_le x B))
  calc
    norm ((integral (volume : Measure Real)) (fixedLeftIntegrand x)) <=
        (integral (volume : Measure Real))
          (fixedLeftIntegrandMajorant x B) := hNorm
    _ = 2 * B.constant * fixedLeftScale x * fixedLeftLogKernelMass := by
      unfold fixedLeftIntegrandMajorant fixedLeftLogKernelMass
      rw [MeasureTheory.integral_mul_left]

theorem fixedLeftBoundaryTruncation_tendsto
    (x : Nat)
    (hx : 0 < x)
    (B : FixedLeftLogDerivativeBoundData) :
    Tendsto (fixedLeftBoundaryTruncation x) atTop
      (nhds (fixedLeftBoundaryLimit x)) := by
  unfold fixedLeftBoundaryTruncation fixedLeftBoundaryLimit
  apply Tendsto.const_mul
  exact intervalIntegral_tendsto_integral
    (fixedLeftIntegrand_integrable x hx B)
    tendsto_neg_atTop_atBot tendsto_id

theorem fixedLeftBoundaryTruncation_norm_le
    (x : Nat)
    (B : FixedLeftLogDerivativeBoundData)
    {tau : Real}
    (hTau : 0 <= tau) :
    norm (fixedLeftBoundaryTruncation x tau) <=
      fixedLeftUniformBound x B := by
  unfold fixedLeftBoundaryTruncation
  rw [norm_mul, norm_I, one_mul]
  have hOrder : -tau <= tau := by linarith
  rw [intervalIntegral.integral_of_le hOrder]
  let S : Set Real := Set.Ioc (-tau) tau
  have hNorm :
      norm ((integral (volume.restrict S)) (fixedLeftIntegrand x)) <=
        (integral (volume.restrict S))
          (fixedLeftIntegrandMajorant x B) :=
    MeasureTheory.norm_integral_le_of_norm_le
      (fixedLeftIntegrandMajorant_integrable x B).integrableOn
      (Filter.Eventually.of_forall (fixedLeftIntegrand_norm_le x B))
  have hSetLe :
      (integral (volume.restrict S))
          (fixedLeftIntegrandMajorant x B) <=
        (integral (volume : Measure Real))
          (fixedLeftIntegrandMajorant x B) := by
    have hMono := setIntegral_mono_set
      (t := Set.univ)
      (s := S)
      (fixedLeftIntegrandMajorant_integrable x B).integrableOn
      (Filter.Eventually.of_forall (fun t =>
        fixedLeftIntegrandMajorant_nonnegative x B t))
      (Set.subset_univ S).eventuallyLE
    simpa using hMono
  calc
    norm ((integral (volume.restrict S)) (fixedLeftIntegrand x)) <=
        (integral (volume.restrict S))
          (fixedLeftIntegrandMajorant x B) := hNorm
    _ <= (integral (volume : Measure Real))
          (fixedLeftIntegrandMajorant x B) := hSetLe
    _ = fixedLeftUniformBound x B := by
      unfold fixedLeftIntegrandMajorant fixedLeftUniformBound
        fixedLeftLogKernelMass
      rw [MeasureTheory.integral_mul_left]

/-- Difference between the full left integral and its symmetric truncation. -/
noncomputable def fixedLeftBoundaryResidual
    (x : Nat)
    (tau : Real) : Complex :=
  fixedLeftBoundaryLimit x - fixedLeftBoundaryTruncation x tau

theorem fixedLeftBoundaryResidual_tendsto_zero
    (x : Nat)
    (hx : 0 < x)
    (B : FixedLeftLogDerivativeBoundData) :
    Tendsto (fixedLeftBoundaryResidual x) atTop (nhds 0) := by
  unfold fixedLeftBoundaryResidual
  convert tendsto_const_nhds.sub
    (fixedLeftBoundaryTruncation_tendsto x hx B) using 1
  simp

theorem strongHeightTau_tendsto_atTop :
    Tendsto TS296.Goldbach.strongHeightTau atTop atTop := by
  exact tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall (fun T =>
      (TS296.Goldbach.strongHeightTau_gt T).le))
    tendsto_natCast_atTop_atTop

theorem fixedLeftBoundaryResidual_strongHeight_tendsto_zero
    (x : Nat)
    (hx : 0 < x)
    (B : FixedLeftLogDerivativeBoundData) :
    Tendsto
      (fun T : Nat =>
        fixedLeftBoundaryResidual x (TS296.Goldbach.strongHeightTau T))
      atTop (nhds 0) :=
  (fixedLeftBoundaryResidual_tendsto_zero x hx B).comp
    strongHeightTau_tendsto_atTop

theorem perronLeftForwardIntegral_eq_fixedLeftBoundaryTruncation
    (x : Nat)
    (D : TS293.Goldbach.PerronRectangle)
    (hLeft : D.left = TS294.Goldbach.fixedPerronLeft) :
    TS293.Goldbach.perronLeftForwardIntegral x D =
      fixedLeftBoundaryTruncation x D.tau := by
  unfold TS293.Goldbach.perronLeftForwardIntegral
    fixedLeftBoundaryTruncation fixedLeftIntegrand fixedLeftPoint
  rw [hLeft]

/-- Concrete discharge of the TS298 fixed-left input. -/
noncomputable def fixedLeftSideBoundData
    (x T : Nat)
    (hT : 1 <= T)
    (B : FixedLeftLogDerivativeBoundData) :
    TS298.Goldbach.FixedLeftSideBoundData x T hT where
  bound := fixedLeftUniformBound x B
  bound_nonnegative := fixedLeftUniformBound_nonnegative x B
  norm_le := by
    rw [perronLeftForwardIntegral_eq_fixedLeftBoundaryTruncation
      x
      (TS296.Goldbach.strongCleanPerronContourData T hT).toPerronRectangle
      rfl]
    exact fixedLeftBoundaryTruncation_norm_le x B
      (TS296.Goldbach.strongHeightTau_pos hT).le

/-- Direct TS298 routing from the sole archimedean logarithmic input. -/
noncomputable def fixedLeftSideBoundData_of_archimedean
    (x T : Nat)
    (hT : 1 <= T)
    (A : FixedLeftArchimedeanBoundData) :
    TS298.Goldbach.FixedLeftSideBoundData x T hT :=
  fixedLeftSideBoundData x T hT A.toLogDerivativeBoundData

/-- The strong-height truncation residual tends to zero from the sole
archimedean logarithmic input. -/
theorem fixedLeftBoundaryResidual_strongHeight_tendsto_zero_of_archimedean
    (x : Nat)
    (hx : 0 < x)
    (A : FixedLeftArchimedeanBoundData) :
    Tendsto
      (fun T : Nat =>
        fixedLeftBoundaryResidual x (TS296.Goldbach.strongHeightTau T))
      atTop (nhds 0) :=
  fixedLeftBoundaryResidual_strongHeight_tendsto_zero
    x hx A.toLogDerivativeBoundData

structure FixedLeftBoundaryLedger where
  fixed_geometry_proved : True
  reflected_right_line_identified : True
  functional_reflection_identity_proved : True
  reflected_dirichlet_mass_proved : True
  full_log_bound_reduced_to_archimedean_input : True
  mellin_kernel_quadratic_bound_proved : True
  logarithmic_weight_integrable : True
  improper_left_limit_defined : True
  truncations_converge_to_left_limit : True
  left_limit_not_claimed_zero : True
  uniform_left_bound_proved_from_log_input : True
  ts298_left_side_routing_proved : True
  logarithmic_gamma_rate_not_proved : True
  sharp_log_over_T_tail_rate_not_proved : True
  exceptional_inventory_not_completed : True
  perron_inversion_not_proved : True
  meromorphic_residue_theorem_not_proved : True
  infinite_explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def fixedLeftBoundaryLedger : FixedLeftBoundaryLedger :=
  { fixed_geometry_proved := True.intro
    reflected_right_line_identified := True.intro
    functional_reflection_identity_proved := True.intro
    reflected_dirichlet_mass_proved := True.intro
    full_log_bound_reduced_to_archimedean_input := True.intro
    mellin_kernel_quadratic_bound_proved := True.intro
    logarithmic_weight_integrable := True.intro
    improper_left_limit_defined := True.intro
    truncations_converge_to_left_limit := True.intro
    left_limit_not_claimed_zero := True.intro
    uniform_left_bound_proved_from_log_input := True.intro
    ts298_left_side_routing_proved := True.intro
    logarithmic_gamma_rate_not_proved := True.intro
    sharp_log_over_T_tail_rate_not_proved := True.intro
    exceptional_inventory_not_completed := True.intro
    perron_inversion_not_proved := True.intro
    meromorphic_residue_theorem_not_proved := True.intro
    infinite_explicit_formula_not_proved := True.intro
    gallagher_not_proved := True.intro
    otsa_not_proved := True.intro
    goldbach_not_claimed := True.intro }

end Goldbach
end TS305
