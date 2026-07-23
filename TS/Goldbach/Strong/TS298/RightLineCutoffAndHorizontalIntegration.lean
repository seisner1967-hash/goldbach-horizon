import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TS.Goldbach.Strong.TS297.XiZetaHorizontalPerronBridge

/-!
# TS298 - Right-Line Cutoff and Integrated Horizontal Reduction

This module closes the Perron cutoff on the absolutely convergent line
`re(s) = 2`. It proves an explicit `1 / T` bound using the von Mangoldt
L-series mass and the quadratic spline Mellin kernel.

It also integrates the exact TS297 pointwise envelopes over the two fixed
horizontal sides. Their width is exactly `7 / 2`. No rate is claimed for the
reciprocal zero load, the local logarithm sphere bound, or the completion
correction. The fixed left side and the exceptional residue inventory remain
explicit inputs when the results are routed into TS294.

No Perron inversion, meromorphic residue theorem, infinite explicit formula,
Gallagher estimate, OTSA bridge, or Goldbach theorem is claimed here.
-/

noncomputable section

namespace TS298
namespace Goldbach

open Complex MeasureTheory Set
open scoped Interval

def vM : Nat -> Complex :=
  fun n => (ArithmeticFunction.vonMangoldt n : Complex)

noncomputable def rightLineVonMangoldtMass : Real :=
  tsum (fun n : Nat => norm (LSeries.term vM (2 : Complex) n))

theorem rightLineVonMangoldtMass_summable :
    Summable (fun n : Nat => norm (LSeries.term vM (2 : Complex) n)) := by
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (2 : Complex))
    (by norm_num)).norm

theorem norm_LSeries_vM_fixed_right_le
    (t : Real) :
    norm (LSeries vM ((2 : Complex) + (t : Complex) * I)) <=
      rightLineVonMangoldtMass := by
  have hsum :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := (2 : Complex) + (t : Complex) * I) (by simp)
  unfold LSeries rightLineVonMangoldtMass
  refine (norm_tsum_le_tsum_norm hsum.norm).trans_eq ?_
  apply tsum_congr
  intro n
  simp only [LSeries.norm_term_eq]
  congr 1
  simp [vM]

theorem fixed_right_norm_sq
    (t : Real) :
    norm ((2 : Complex) + (t : Complex) * I) ^ 2 = 4 + t ^ 2 := by
  rw [<- Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

theorem fixed_right_add_one_norm_sq
    (t : Real) :
    norm (((2 : Complex) + (t : Complex) * I) + 1) ^ 2 = 9 + t ^ 2 := by
  rw [<- Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

theorem one_add_sq_le_fixed_right_denominator_norm
    (t : Real) :
    1 + t ^ 2 <=
      norm ((2 : Complex) + (t : Complex) * I) *
        norm (((2 : Complex) + (t : Complex) * I) + 1) := by
  have h0 := norm_nonneg ((2 : Complex) + (t : Complex) * I)
  have h1 := norm_nonneg (((2 : Complex) + (t : Complex) * I) + 1)
  have hs := fixed_right_norm_sq t
  have hs1 := fixed_right_add_one_norm_sq t
  have hle :
      norm ((2 : Complex) + (t : Complex) * I) <=
        norm (((2 : Complex) + (t : Complex) * I) + 1) := by
    nlinarith
  nlinarith

theorem triangleSplineMellinKernel_fixed_right_norm_le
    (t : Real) :
    norm
        (TS257.Goldbach.triangleSplineMellinKernel
          ((2 : Complex) + (t : Complex) * I)) <=
      1 / (1 + t ^ 2) := by
  unfold TS257.Goldbach.triangleSplineMellinKernel
  rw [norm_div, norm_one, norm_mul]
  rw [one_div]
  have hbase : 0 < 1 + t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hprod :
      0 <
        norm ((2 : Complex) + (t : Complex) * I) *
          norm (((2 : Complex) + (t : Complex) * I) + 1) :=
    hbase.trans_le (one_add_sq_le_fixed_right_denominator_norm t)
  simpa [one_div] using one_div_le_one_div_of_le hbase
    (one_add_sq_le_fixed_right_denominator_norm t)

theorem nat_cpow_fixed_right_norm
    (x : Nat)
    (t : Real) :
    norm ((x : Complex) ^ ((2 : Complex) + (t : Complex) * I)) =
      (x : Real) ^ 2 := by
  rw [Complex.norm_natCast_cpow_of_re_ne_zero]
  all_goals simp [Real.rpow_two]

theorem vM_abscissa_lt_two :
    LSeries.abscissaOfAbsConv vM < ((2 : Real) : EReal) := by
  have hsum :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := ((3 / 2 : Real) : Complex)) (by norm_num)
  have hle :
      LSeries.abscissaOfAbsConv vM <= ((3 / 2 : Real) : EReal) := by
    simpa using hsum.abscissaOfAbsConv_le
  exact hle.trans_lt (by norm_num)

theorem continuous_LSeries_vM_fixed_right :
    Continuous
      (fun t : Real =>
        LSeries vM ((2 : Complex) + (t : Complex) * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hs :
      LSeries.abscissaOfAbsConv vM <
        (((2 : Complex) + (t : Complex) * I).re : EReal) := by
    simpa using vM_abscissa_lt_two
  exact ((LSeries_analyticOnNhd vM) _ hs).continuousAt.comp_of_eq
    (continuousAt_const.add
      (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)) rfl

noncomputable def rightLineScale (x : Nat) : Real :=
  max 1 ((x : Real) ^ 2)

theorem rightLineScale_nonnegative (x : Nat) :
    0 <= rightLineScale x := by
  unfold rightLineScale
  positivity

theorem nat_sq_le_rightLineScale (x : Nat) :
    (x : Real) ^ 2 <= rightLineScale x := by
  exact le_max_right _ _

theorem triangleSplinePerronIntegrand_fixed_right_norm_le
    (x : Nat)
    (t : Real) :
    norm
        (TS293.Goldbach.triangleSplinePerronIntegrand x
          ((2 : Complex) + (t : Complex) * I)) <=
      rightLineVonMangoldtMass * rightLineScale x * (1 / (1 + t ^ 2)) := by
  rw [TS293.Goldbach.triangleSplinePerronIntegrand_eq_vonMangoldtLSeries
    x (s := (2 : Complex) + (t : Complex) * I) (by simp)]
  unfold TS293.Goldbach.triangleSplineVonMangoldtLSeriesIntegrand
  change
    norm
        (LSeries vM ((2 : Complex) + (t : Complex) * I) *
          (x : Complex) ^ ((2 : Complex) + (t : Complex) * I) *
          TS257.Goldbach.triangleSplineMellinKernel
            ((2 : Complex) + (t : Complex) * I)) <= _
  simp only [norm_mul]
  have hmass : 0 <= rightLineVonMangoldtMass := by
    unfold rightLineVonMangoldtMass
    exact tsum_nonneg (fun n => norm_nonneg _)
  have hL := norm_LSeries_vM_fixed_right_le t
  have hxNorm := nat_cpow_fixed_right_norm x t
  have hK := triangleSplineMellinKernel_fixed_right_norm_le t
  calc
    norm (LSeries vM ((2 : Complex) + (t : Complex) * I)) *
          norm ((x : Complex) ^ ((2 : Complex) + (t : Complex) * I)) *
          norm
            (TS257.Goldbach.triangleSplineMellinKernel
              ((2 : Complex) + (t : Complex) * I)) <=
        rightLineVonMangoldtMass * (x : Real) ^ 2 * (1 / (1 + t ^ 2)) := by
      refine mul_le_mul ?_ hK (norm_nonneg _)
        (mul_nonneg hmass (sq_nonneg _))
      exact mul_le_mul hL hxNorm.le (norm_nonneg _) hmass
    _ <= rightLineVonMangoldtMass * rightLineScale x * (1 / (1 + t ^ 2)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (nat_sq_le_rightLineScale x) hmass)
        (by positivity : 0 <= (1 / (1 + t ^ 2) : Real))

theorem continuous_triangleSplinePerronIntegrand_fixed_right
    (x : Nat) :
    Continuous
      (fun t : Real =>
        TS293.Goldbach.triangleSplinePerronIntegrand x
          ((2 : Complex) + (t : Complex) * I)) := by
  let s : Real -> Complex :=
    fun t => (2 : Complex) + (t : Complex) * I
  have hs : Continuous s :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  by_cases hx : x = 0
  case pos =>
    subst x
    have hzero :
        (fun t : Real =>
          TS293.Goldbach.triangleSplinePerronIntegrand 0 (s t)) =
          (fun _ : Real => (0 : Complex)) := by
      funext t
      unfold TS293.Goldbach.triangleSplinePerronIntegrand
      have hs0 : Not (s t = 0) := by
        intro h
        have hre := congrArg Complex.re h
        simp [s] at hre
      simp only [Nat.cast_zero]
      rw [Complex.zero_cpow hs0]
      simp
    rw [hzero]
    exact continuous_const
  case neg =>
    have hPow : Continuous (fun t : Real => (x : Complex) ^ (s t)) :=
      continuous_const.cpow hs
        (fun _ => Complex.natCast_mem_slitPlane.mpr hx)
    have hKernel :
        Continuous
          (fun t : Real =>
            TS257.Goldbach.triangleSplineMellinKernel (s t)) := by
      unfold TS257.Goldbach.triangleSplineMellinKernel
      exact continuous_const.div
        (hs.mul (hs.add continuous_const))
        (fun t =>
          TS257.Goldbach.triangleSplineMellinKernel_denominator_ne_zero_of_re_pos
            (s t) (by simp [s]))
    have hL :
        Continuous (fun t : Real => LSeries vM (s t)) := by
      simpa [s] using continuous_LSeries_vM_fixed_right
    have hProduct :
        Continuous
          (fun t : Real =>
            LSeries vM (s t) * (x : Complex) ^ (s t) *
              TS257.Goldbach.triangleSplineMellinKernel (s t)) :=
      (hL.mul hPow).mul hKernel
    convert hProduct using 1
    funext t
    rw [TS293.Goldbach.triangleSplinePerronIntegrand_eq_vonMangoldtLSeries
      x (s := s t) (by simp [s])]
    rfl

theorem integrable_triangleSplinePerronIntegrand_fixed_right
    (x : Nat) :
    Integrable
      (fun t : Real =>
        TS293.Goldbach.triangleSplinePerronIntegrand x
          ((2 : Complex) + (t : Complex) * I)) := by
  have hmajorant :
      Integrable
        (fun t : Real =>
          rightLineVonMangoldtMass * rightLineScale x * (1 / (1 + t ^ 2))) :=
    by
      simpa [one_div] using integrable_inv_one_add_sq.const_mul
        (rightLineVonMangoldtMass * rightLineScale x)
  exact hmajorant.mono'
    (continuous_triangleSplinePerronIntegrand_fixed_right x).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (triangleSplinePerronIntegrand_fixed_right_norm_le x))

theorem perronRightLineCutoffAdjustment_eq_tail
    (x : Nat)
    (D : TS293.Goldbach.PerronRectangle)
    (hRight : D.right = 2) :
    TS293.Goldbach.perronRightLineCutoffAdjustment x D =
      TS293.Goldbach.normalizeContourIntegral
        (I *
          (integral (volume.restrict (Ioc (-D.tau) D.tau).compl)
            (fun t : Real =>
              TS293.Goldbach.triangleSplinePerronIntegrand x
                ((2 : Complex) + (t : Complex) * I)))) := by
  let f : Real -> Complex :=
    fun t =>
      TS293.Goldbach.triangleSplinePerronIntegrand x
        ((2 : Complex) + (t : Complex) * I)
  have hInt : Integrable f := by
    simpa [f] using integrable_triangleSplinePerronIntegrand_fixed_right x
  have hTau : -D.tau <= D.tau := by
    linarith [D.tau_pos]
  have hCompl :
      integral (volume.restrict (Ioc (-D.tau) D.tau).compl) f =
        integral volume f -
          integral (volume.restrict (Ioc (-D.tau) D.tau)) f :=
    MeasureTheory.setIntegral_compl
      (s := Ioc (-D.tau) D.tau) measurableSet_Ioc hInt
  unfold TS293.Goldbach.perronRightLineCutoffAdjustment
    TS293.Goldbach.fullPerronRightLineValue
    TS293.Goldbach.finitePerronRightValue
    TS293.Goldbach.perronRightIntegral
    TS293.Goldbach.normalizeContourIntegral
  rw [hRight]
  simp only [Complex.ofReal_ofNat]
  rw [intervalIntegral.integral_of_le hTau]
  have hCompl' :
      integral (volume.restrict (Ioc (-D.tau) D.tau).compl)
          (fun t : Real =>
            TS293.Goldbach.triangleSplinePerronIntegrand x
              ((2 : Complex) + (t : Complex) * I)) =
        integral volume
            (fun t : Real =>
              TS293.Goldbach.triangleSplinePerronIntegrand x
                ((2 : Complex) + (t : Complex) * I)) -
          integral (volume.restrict (Ioc (-D.tau) D.tau))
            (fun t : Real =>
              TS293.Goldbach.triangleSplinePerronIntegrand x
                ((2 : Complex) + (t : Complex) * I)) := by
    simpa [f] using hCompl
  rw [(sub_div _ _ _).symm, (mul_sub _ _ _).symm, hCompl'.symm]

theorem inv_one_add_sq_le_rpow_neg_two
    {t : Real}
    (ht : 0 < t) :
    1 / (1 + t ^ 2) <= t ^ (-2 : Real) := by
  rw [Real.rpow_neg (le_of_lt ht)]
  norm_num [Real.rpow_two]
  have hbase : 0 < 1 + t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hsquare : 0 < t ^ 2 := pow_pos ht 2
  simpa [one_div] using one_div_le_one_div_of_le hsquare (by nlinarith)

theorem integral_Ioi_inv_one_add_sq_le_inv
    {tau : Real}
    (hTau : 0 < tau) :
    integral (volume.restrict (Ioi tau))
        (fun t : Real => 1 / (1 + t ^ 2)) <=
      1 / tau := by
  have hLeft :
      IntegrableOn (fun t : Real => 1 / (1 + t ^ 2)) (Ioi tau) :=
    by simpa [one_div] using integrable_inv_one_add_sq.integrableOn (s := Ioi tau)
  have hRight :
      IntegrableOn (fun t : Real => t ^ (-2 : Real)) (Ioi tau) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hTau
  calc
    integral (volume.restrict (Ioi tau))
        (fun t : Real => 1 / (1 + t ^ 2)) <=
        integral (volume.restrict (Ioi tau))
          (fun t : Real => t ^ (-2 : Real)) := by
      exact MeasureTheory.setIntegral_mono_on hLeft hRight measurableSet_Ioi
        (fun t ht => inv_one_add_sq_le_rpow_neg_two (lt_of_le_of_lt hTau.le ht))
    _ = 1 / tau := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) hTau]
      norm_num [Real.rpow_neg_one]

theorem integral_compl_Ioc_inv_one_add_sq_le
    {tau : Real}
    (hTau : 0 < tau) :
    integral (volume.restrict (Ioc (-tau) tau).compl)
        (fun t : Real => 1 / (1 + t ^ 2)) <=
      2 / tau := by
  have hNeg :
      integral (volume.restrict (Iic (-tau)))
          (fun t : Real => 1 / (1 + t ^ 2)) =
        integral (volume.restrict (Ioi tau))
          (fun t : Real => 1 / (1 + t ^ 2)) := by
    convert integral_comp_neg_Iic (-tau)
      (fun t : Real => 1 / (1 + t ^ 2)) using 1 <;> simp
  have hLeft :
      IntegrableOn (fun t : Real => 1 / (1 + t ^ 2)) (Iic (-tau)) :=
    by simpa [one_div] using
      integrable_inv_one_add_sq.integrableOn (s := Iic (-tau))
  have hRight :
      IntegrableOn (fun t : Real => 1 / (1 + t ^ 2)) (Ioi tau) :=
    by simpa [one_div] using
      integrable_inv_one_add_sq.integrableOn (s := Ioi tau)
  have hSet : (Ioc (-tau) tau).compl = Set.union (Iic (-tau)) (Ioi tau) := by
    ext t
    change (Not (-tau < t /\ t <= tau)) <-> t <= -tau \/ tau < t
    constructor
    case mp =>
      intro h
      by_cases hLeft : t <= -tau
      case pos => exact Or.inl hLeft
      case neg =>
        exact Or.inr (lt_of_not_ge (fun hRight =>
          h (And.intro (lt_of_not_ge hLeft) hRight)))
    case mpr =>
      intro h ht
      cases h with
      | inl hLeft => exact (not_lt_of_ge hLeft) ht.1
      | inr hRight => exact (not_lt_of_ge ht.2) hRight
  have hUnion :
      integral (volume.restrict (Set.union (Iic (-tau)) (Ioi tau)))
          (fun t : Real => 1 / (1 + t ^ 2)) =
        integral (volume.restrict (Iic (-tau)))
            (fun t : Real => 1 / (1 + t ^ 2)) +
          integral (volume.restrict (Ioi tau))
            (fun t : Real => 1 / (1 + t ^ 2)) := by
    simpa [one_div] using
      MeasureTheory.setIntegral_union
        (Iic_disjoint_Ioi (le_of_lt (neg_lt_self hTau)))
        measurableSet_Ioi hLeft hRight
  rw [hSet]
  rw [hUnion]
  rw [hNeg]
  have hPos := integral_Ioi_inv_one_add_sq_le_inv hTau
  rw [div_eq_mul_inv]
  rw [one_div] at hPos
  linarith

noncomputable def rightLineCutoffConstant : Real :=
  rightLineVonMangoldtMass / Real.pi

theorem rightLineCutoffConstant_nonnegative :
    0 <= rightLineCutoffConstant := by
  unfold rightLineCutoffConstant
  exact div_nonneg
    (by
      unfold rightLineVonMangoldtMass
      exact tsum_nonneg (fun n => norm_nonneg _))
    Real.pi_pos.le

theorem perronRightLineCutoffAdjustment_norm_le_fixed
    (x : Nat)
    (D : TS293.Goldbach.PerronRectangle)
    (hRight : D.right = 2) :
    norm (TS293.Goldbach.perronRightLineCutoffAdjustment x D) <=
      rightLineCutoffConstant * rightLineScale x / D.tau := by
  let f : Real -> Complex :=
    fun t =>
      TS293.Goldbach.triangleSplinePerronIntegrand x
        ((2 : Complex) + (t : Complex) * I)
  let C : Real := rightLineVonMangoldtMass * rightLineScale x
  let tail : Set Real := (Ioc (-D.tau) D.tau).compl
  have hC : 0 <= C := by
    exact mul_nonneg
      (by
        unfold rightLineVonMangoldtMass
        exact tsum_nonneg (fun n => norm_nonneg _))
      (rightLineScale_nonnegative x)
  have hMajor : Integrable (fun t : Real => C * (1 / (1 + t ^ 2))) :=
    by simpa [one_div] using integrable_inv_one_add_sq.const_mul C
  have hNormIntegral :
      norm (integral (volume.restrict tail) f) <=
        integral (volume.restrict tail)
          (fun t : Real => C * (1 / (1 + t ^ 2))) := by
    exact MeasureTheory.norm_integral_le_of_norm_le hMajor.integrableOn
      (Filter.Eventually.of_forall (fun t => by
        change
          norm
              (TS293.Goldbach.triangleSplinePerronIntegrand x
                ((2 : Complex) + (t : Complex) * I)) <=
            C * (1 / (1 + t ^ 2))
        exact triangleSplinePerronIntegrand_fixed_right_norm_le x t))
  have hMajorIntegral :
      integral (volume.restrict tail)
          (fun t : Real => C * (1 / (1 + t ^ 2))) <=
        C * (2 / D.tau) := by
    rw [MeasureTheory.integral_mul_left]
    exact mul_le_mul_of_nonneg_left
      (integral_compl_Ioc_inv_one_add_sq_le D.tau_pos) hC
  rw [perronRightLineCutoffAdjustment_eq_tail x D hRight]
  unfold TS293.Goldbach.normalizeContourIntegral
  rw [norm_div, norm_mul, norm_I, one_mul]
  have hDen :
      norm (((2 * Real.pi : Real) : Complex) * I) = 2 * Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hDen]
  have hNumerator :
      norm
          (integral (volume.restrict tail) f) <=
        C * (2 / D.tau) :=
    hNormIntegral.trans hMajorIntegral
  calc
    norm (integral (volume.restrict tail) f) / (2 * Real.pi) <=
        (C * (2 / D.tau)) / (2 * Real.pi) := by
      exact div_le_div_of_nonneg_right hNumerator (by positivity)
    _ = rightLineCutoffConstant * rightLineScale x / D.tau := by
      unfold C rightLineCutoffConstant
      field_simp [Real.pi_ne_zero, ne_of_gt D.tau_pos]
      ring

theorem perronRightLineCutoffAdjustment_norm_le_strongHeight
    (x T : Nat)
    (hT : 1 <= T) :
    norm
        (TS293.Goldbach.perronRightLineCutoffAdjustment x
          (TS296.Goldbach.strongCleanPerronContourData T hT).toPerronRectangle) <=
      rightLineCutoffConstant * rightLineScale x / (T : Real) := by
  let D := TS296.Goldbach.strongCleanPerronContourData T hT
  have hFixed :
      norm
          (TS293.Goldbach.perronRightLineCutoffAdjustment x
            D.toPerronRectangle) <=
        rightLineCutoffConstant * rightLineScale x / D.tau := by
    exact perronRightLineCutoffAdjustment_norm_le_fixed x D.toPerronRectangle
      (by simpa [D, TS294.Goldbach.fixedPerronRight] using D.right_eq_fixed)
  have hNumerator :
      0 <= rightLineCutoffConstant * rightLineScale x :=
    mul_nonneg rightLineCutoffConstant_nonnegative
      (rightLineScale_nonnegative x)
  calc
    norm
        (TS293.Goldbach.perronRightLineCutoffAdjustment x
          D.toPerronRectangle) <=
        rightLineCutoffConstant * rightLineScale x / D.tau := hFixed
    _ <= rightLineCutoffConstant * rightLineScale x / (T : Real) := by
      exact div_le_div_of_nonneg_left hNumerator
        (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hT)) D.height_ge

noncomputable def topHorizontalPerronEnvelope
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real) : Real :=
  TS297.Goldbach.topZetaLogDerivativeEnvelope T hT sigma *
    norm ((x : Complex) ^ (TS297.Goldbach.topHorizontalPoint T sigma)) *
      norm
        (TS257.Goldbach.triangleSplineMellinKernel
          (TS297.Goldbach.topHorizontalPoint T sigma))

noncomputable def bottomHorizontalPerronEnvelope
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real) : Real :=
  TS297.Goldbach.bottomZetaLogDerivativeEnvelope T hT sigma *
    norm ((x : Complex) ^ (TS297.Goldbach.bottomHorizontalPoint T sigma)) *
      norm
        (TS257.Goldbach.triangleSplineMellinKernel
          (TS297.Goldbach.bottomHorizontalPoint T sigma))

theorem topHorizontalPerronEnvelope_nonnegative
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    0 <= topHorizontalPerronEnvelope x T hT sigma := by
  unfold topHorizontalPerronEnvelope
  exact mul_nonneg
    (mul_nonneg
      ((norm_nonneg _).trans
        (TS297.Goldbach.neg_riemannZeta_logDerivative_norm_le_top T hT sigma))
      (norm_nonneg _))
    (norm_nonneg _)

theorem bottomHorizontalPerronEnvelope_nonnegative
    (x T : Nat)
    (hT : 1 <= T)
    (sigma : Real) :
    0 <= bottomHorizontalPerronEnvelope x T hT sigma := by
  unfold bottomHorizontalPerronEnvelope
  exact mul_nonneg
    (mul_nonneg
      ((norm_nonneg _).trans
        (TS297.Goldbach.neg_riemannZeta_logDerivative_norm_le_bottom T hT sigma))
      (norm_nonneg _))
    (norm_nonneg _)

/-- Uniform evidence for the exact TS297 pointwise horizontal envelopes. -/
structure HorizontalUniformEnvelopeData
    (x T : Nat)
    (hT : 1 <= T) where
  topBound : Real
  bottomBound : Real
  topBound_nonnegative : 0 <= topBound
  bottomBound_nonnegative : 0 <= bottomBound
  topEnvelope_le :
    forall sigma : Real,
      Membership.mem
          (Icc TS294.Goldbach.fixedPerronLeft
            TS294.Goldbach.fixedPerronRight) sigma ->
        topHorizontalPerronEnvelope x T hT sigma <= topBound
  bottomEnvelope_le :
    forall sigma : Real,
      Membership.mem
          (Icc TS294.Goldbach.fixedPerronLeft
            TS294.Goldbach.fixedPerronRight) sigma ->
        bottomHorizontalPerronEnvelope x T hT sigma <= bottomBound

theorem fixedPerronWidth :
    norm (TS294.Goldbach.fixedPerronRight -
      TS294.Goldbach.fixedPerronLeft : Real) = 7 / 2 := by
  norm_num [TS294.Goldbach.fixedPerronRight,
    TS294.Goldbach.fixedPerronLeft]

theorem perronTopForwardIntegral_norm_le_uniform
    (x T : Nat)
    (hT : 1 <= T)
    (H : HorizontalUniformEnvelopeData x T hT) :
    norm
        (TS293.Goldbach.perronTopForwardIntegral x
          (TS296.Goldbach.strongCleanPerronContourData T hT).toPerronRectangle) <=
      (7 / 2 : Real) * H.topBound := by
  let D := TS296.Goldbach.strongCleanPerronContourData T hT
  have hSide :
      norm
          (intervalIntegral
            (fun sigma : Real =>
              TS293.Goldbach.triangleSplinePerronIntegrand x
                (TS297.Goldbach.topHorizontalPoint T sigma))
            TS294.Goldbach.fixedPerronLeft
            TS294.Goldbach.fixedPerronRight
            (volume : Measure Real)) <=
        H.topBound *
          norm (TS294.Goldbach.fixedPerronRight -
            TS294.Goldbach.fixedPerronLeft : Real) := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro sigma hSigma
    have hOrder :
        TS294.Goldbach.fixedPerronLeft <=
          TS294.Goldbach.fixedPerronRight := by
      norm_num [TS294.Goldbach.fixedPerronLeft,
        TS294.Goldbach.fixedPerronRight]
    have hIoc :
        Membership.mem
          (Ioc TS294.Goldbach.fixedPerronLeft
            TS294.Goldbach.fixedPerronRight) sigma := by
      simpa [uIoc_of_le hOrder] using hSigma
    exact
      (TS297.Goldbach.triangleSplinePerronIntegrand_norm_le_top
        x T hT sigma).trans
        (H.topEnvelope_le sigma (Ioc_subset_Icc_self hIoc))
  change
    norm
        (intervalIntegral
          (fun sigma : Real =>
            TS293.Goldbach.triangleSplinePerronIntegrand x
              (TS297.Goldbach.topHorizontalPoint T sigma))
          TS294.Goldbach.fixedPerronLeft
          TS294.Goldbach.fixedPerronRight
          (volume : Measure Real)) <= _
  rw [fixedPerronWidth] at hSide
  nlinarith

theorem perronBottomIntegral_norm_le_uniform
    (x T : Nat)
    (hT : 1 <= T)
    (H : HorizontalUniformEnvelopeData x T hT) :
    norm
        (TS293.Goldbach.perronBottomIntegral x
          (TS296.Goldbach.strongCleanPerronContourData T hT).toPerronRectangle) <=
      (7 / 2 : Real) * H.bottomBound := by
  have hSide :
      norm
          (intervalIntegral
            (fun sigma : Real =>
              TS293.Goldbach.triangleSplinePerronIntegrand x
                (TS297.Goldbach.bottomHorizontalPoint T sigma))
            TS294.Goldbach.fixedPerronLeft
            TS294.Goldbach.fixedPerronRight
            (volume : Measure Real)) <=
        H.bottomBound *
          norm (TS294.Goldbach.fixedPerronRight -
            TS294.Goldbach.fixedPerronLeft : Real) := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro sigma hSigma
    have hOrder :
        TS294.Goldbach.fixedPerronLeft <=
          TS294.Goldbach.fixedPerronRight := by
      norm_num [TS294.Goldbach.fixedPerronLeft,
        TS294.Goldbach.fixedPerronRight]
    have hIoc :
        Membership.mem
          (Ioc TS294.Goldbach.fixedPerronLeft
            TS294.Goldbach.fixedPerronRight) sigma := by
      simpa [uIoc_of_le hOrder] using hSigma
    exact
      (TS297.Goldbach.triangleSplinePerronIntegrand_norm_le_bottom
        x T hT sigma).trans
        (H.bottomEnvelope_le sigma (Ioc_subset_Icc_self hIoc))
  change
    norm
        (intervalIntegral
          (fun sigma : Real =>
            TS293.Goldbach.triangleSplinePerronIntegrand x
              (TS297.Goldbach.bottomHorizontalPoint T sigma))
          TS294.Goldbach.fixedPerronLeft
          TS294.Goldbach.fixedPerronRight
          (volume : Measure Real)) <= _
  rw [fixedPerronWidth] at hSide
  nlinarith

/-- The still-open fixed-left-side estimate, kept separate from TS298. -/
structure FixedLeftSideBoundData
    (x T : Nat)
    (hT : 1 <= T) where
  bound : Real
  bound_nonnegative : 0 <= bound
  norm_le :
    norm
        (TS293.Goldbach.perronLeftForwardIntegral x
          (TS296.Goldbach.strongCleanPerronContourData T hT).toPerronRectangle) <=
      bound

/-- TS294 non-right-side data with both horizontal fields discharged. -/
noncomputable def integratedHorizontalNonRightSideBounds
    (x T : Nat)
    (hT : 1 <= T)
    (H : HorizontalUniformEnvelopeData x T hT)
    (L : FixedLeftSideBoundData x T hT) :
    TS294.Goldbach.PerronNonRightSideBounds x
      (TS296.Goldbach.strongCleanPerronContourData T hT).toPerronRectangle where
  bottomBound := (7 / 2 : Real) * H.bottomBound
  topBound := (7 / 2 : Real) * H.topBound
  leftBound := L.bound
  bottomBound_nonnegative := mul_nonneg (by norm_num) H.bottomBound_nonnegative
  topBound_nonnegative := mul_nonneg (by norm_num) H.topBound_nonnegative
  leftBound_nonnegative := L.bound_nonnegative
  bottom_norm_le := perronBottomIntegral_norm_le_uniform x T hT H
  top_norm_le := perronTopForwardIntegral_norm_le_uniform x T hT H
  left_norm_le := L.norm_le

/-- An independently certified bound for the finite exceptional inventory. -/
structure ExceptionalResidueBoundData
    (x T : Nat)
    (hT : 1 <= T)
    (E : TS293.Goldbach.PerronExceptionalResidueInventory x
      (TS296.Goldbach.strongCleanPerronContourData T hT).toPerronRectangle) where
  bound : Real
  bound_nonnegative : 0 <= bound
  norm_le :
    norm (TS293.Goldbach.exceptionalResidueContribution E) <= bound

/--
Route the unconditional right cutoff and integrated horizontal reduction into
the complete TS294 component interface. The left side and exceptional residues
remain explicit inputs.
-/
noncomputable def canonicalContourComponentBounds
    (x T : Nat)
    (hT : 1 <= T)
    (H : HorizontalUniformEnvelopeData x T hT)
    (L : FixedLeftSideBoundData x T hT)
    (E : TS293.Goldbach.PerronExceptionalResidueInventory x
      (TS296.Goldbach.strongCleanPerronContourData T hT).toPerronRectangle)
    (X : ExceptionalResidueBoundData x T hT E) :
    TS294.Goldbach.TriangleSplineContourComponentBounds x T
      (TS296.Goldbach.strongCleanPerronContourData T hT) E where
  exceptionalBound := X.bound
  rightCutoffBound :=
    rightLineCutoffConstant * rightLineScale x / (T : Real)
  exceptionalBound_nonnegative := X.bound_nonnegative
  rightCutoffBound_nonnegative := by
    exact div_nonneg
      (mul_nonneg rightLineCutoffConstant_nonnegative
        (rightLineScale_nonnegative x))
      (Nat.cast_nonneg T)
  exceptional_norm_le := X.norm_le
  nonRightSides := integratedHorizontalNonRightSideBounds x T hT H L
  rightCutoff_norm_le :=
    perronRightLineCutoffAdjustment_norm_le_strongHeight x T hT

/-- The TS294 residual estimate after the two TS298 reductions. -/
theorem canonicalContourResidualComplex_norm_le
    (x T : Nat)
    (hT : 1 <= T)
    (H : HorizontalUniformEnvelopeData x T hT)
    (L : FixedLeftSideBoundData x T hT)
    (E : TS293.Goldbach.PerronExceptionalResidueInventory x
      (TS296.Goldbach.strongCleanPerronContourData T hT).toPerronRectangle)
    (X : ExceptionalResidueBoundData x T hT E) :
    norm
        (TS293.Goldbach.triangleSplineContourResidualComplex x T
          (TS296.Goldbach.strongCleanPerronContourData T hT).toCleanPerronContourData
          E) <=
      TS294.Goldbach.triangleSplineContourResidualEnvelope
        (canonicalContourComponentBounds x T hT H L E X) := by
  exact TS294.Goldbach.triangleSplineContourResidualComplex_norm_le
    x T hT (TS296.Goldbach.strongCleanPerronContourData T hT) E
      (canonicalContourComponentBounds x T hT H L E X)

structure RightLineCutoffHorizontalLedger where
  von_mangoldt_mass_summable : True
  right_line_kernel_bound_proved : True
  right_line_integrand_integrable : True
  cutoff_tail_identity_proved : True
  cutoff_inverse_height_bound_proved : True
  horizontal_width_exact : True
  horizontal_uniform_integration_proved : True
  ts294_routing_proved : True
  horizontal_uniform_rate_not_proved : True
  reciprocal_load_rate_not_proved : True
  logarithm_sphere_rate_not_proved : True
  completion_correction_rate_not_proved : True
  left_boundary_not_estimated : True
  exceptional_inventory_not_completed : True
  perron_inversion_not_proved : True
  meromorphic_residue_theorem_not_proved : True
  infinite_explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def rightLineCutoffHorizontalLedger : RightLineCutoffHorizontalLedger :=
  { von_mangoldt_mass_summable := True.intro
    right_line_kernel_bound_proved := True.intro
    right_line_integrand_integrable := True.intro
    cutoff_tail_identity_proved := True.intro
    cutoff_inverse_height_bound_proved := True.intro
    horizontal_width_exact := True.intro
    horizontal_uniform_integration_proved := True.intro
    ts294_routing_proved := True.intro
    horizontal_uniform_rate_not_proved := True.intro
    reciprocal_load_rate_not_proved := True.intro
    logarithm_sphere_rate_not_proved := True.intro
    completion_correction_rate_not_proved := True.intro
    left_boundary_not_estimated := True.intro
    exceptional_inventory_not_completed := True.intro
    perron_inversion_not_proved := True.intro
    meromorphic_residue_theorem_not_proved := True.intro
    infinite_explicit_formula_not_proved := True.intro
    gallagher_not_proved := True.intro
    otsa_not_proved := True.intro
    goldbach_not_claimed := True.intro }

end Goldbach
end TS298
