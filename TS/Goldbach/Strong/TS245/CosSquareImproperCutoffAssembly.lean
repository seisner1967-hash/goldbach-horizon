import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TS.Goldbach.Strong.TS218.SincFourthScalingEvennessDischarge
import TS.Goldbach.Strong.TS221.CosSquareFiniteTripleIPPDischarge
import TS.Goldbach.Strong.TS224.CosSquareIPPPrimitiveZeroRightAsymptotic
import TS.Goldbach.Strong.TS244.DirichletProductCutoffThirdDerivativeDischarge

/-!
# TS245 - Cos-Square Improper Cutoff Assembly

TS244 proved that the third-derivative cutoff integral tends to `pi`.  This
sprint identifies the cutoff of the cos-square Haar kernel with its Lebesgue
integral on the positive half-line and executes the limiting assembly isolated
in TS219.

The integrability of the Haar kernel is transported from the canonical
sinc-fourth integrability proved in TS218.  The product-filter convergence is
then obtained from the ordinary improper-integral theorem at the upper endpoint
and a direct zero-right estimate at the lower endpoint.
-/

namespace TS245
namespace Goldbach

open Filter MeasureTheory
open scoped Topology

/-- The cos-square Haar kernel is integrable on the positive half-line. -/
theorem cosSquareHaarKernel_integrableOn_Ioi :
    IntegrableOn
      TS213.Goldbach.cosSquareHaarKernel
      (Set.Ioi (0 : Real))
      volume := by
  have hcanonical :
      IntegrableOn
        TS213.Goldbach.canonicalSincFourthKernel
        (Set.Ioi (0 : Real))
        volume :=
    TS218.Goldbach.canonicalSincFourthKernel_integrable.integrableOn
  have hscaled_with_constant :
      IntegrableOn
        (fun u : Real =>
          4 * TS213.Goldbach.cosSquareHaarKernel (2 * u))
        (Set.Ioi (0 : Real))
        volume :=
    hcanonical.congr_fun
      (fun u hu =>
        TS218.Goldbach.canonicalSincFourthKernel_scaling_pointwise u hu)
      measurableSet_Ioi
  have hscaled :
      IntegrableOn
        (fun u : Real => TS213.Goldbach.cosSquareHaarKernel (2 * u))
        (Set.Ioi (0 : Real))
        volume := by
    have hquarter :
        IntegrableOn
          (fun u : Real =>
            (1 / 4 : Real) *
              (4 * TS213.Goldbach.cosSquareHaarKernel (2 * u)))
          (Set.Ioi (0 : Real))
          volume :=
      hscaled_with_constant.const_mul (1 / 4 : Real)
    refine hquarter.congr_fun ?_ measurableSet_Ioi
    intro u hu
    dsimp
    ring
  have htransport :=
    (integrableOn_Ioi_comp_mul_left_iff
      TS213.Goldbach.cosSquareHaarKernel
      (0 : Real)
      (by norm_num : (0 : Real) < 2)).mp hscaled
  simpa using htransport

/-- Near zero, the positive-half-line Haar kernel is bounded by `1/4`. -/
theorem cosSquareHaarKernel_abs_le_quarter
    (x : Real)
    (hx : 0 < x) :
    |TS213.Goldbach.cosSquareHaarKernel x| <= (1 / 4 : Real) := by
  have hrem :=
    TS224.Goldbach.cosSquareRemainder_abs_le_quarter_fourth x
  have hx4 : 0 < x ^ 4 := pow_pos hx 4
  unfold TS213.Goldbach.cosSquareHaarKernel
  rw [abs_div, abs_pow, abs_of_pos hx]
  calc
    |TS213.Goldbach.cosSquareRemainder x| / x ^ 4 <=
        (x ^ 4 / 4) / x ^ 4 := by
      exact div_le_div_of_nonneg_right hrem hx4.le
    _ = (1 / 4 : Real) := by
      field_simp [ne_of_gt hx]
      ring

/-- The lower partial integral vanishes as its positive endpoint tends to zero. -/
theorem cosSquareHaarPartialIntegralZeroRight :
    Tendsto
      (fun eps : Real =>
        intervalIntegral
          TS213.Goldbach.cosSquareHaarKernel
          0
          eps
          volume)
      (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
      (nhds (0 : Real)) := by
  have hid :
      Tendsto
        (fun eps : Real => eps)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
        (nhds (0 : Real)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hmajor :
      Tendsto
        (fun eps : Real => (1 / 4 : Real) * eps)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
        (nhds (0 : Real)) := by
    simpa using hid.const_mul (1 / 4 : Real)
  have habs :
      Tendsto
        (fun eps : Real =>
          |intervalIntegral
            TS213.Goldbach.cosSquareHaarKernel
            0
            eps
            volume|)
        (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
        (nhds (0 : Real)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hmajor
    next =>
      exact Eventually.of_forall (fun eps => abs_nonneg _)
    next =>
      filter_upwards [self_mem_nhdsWithin] with eps heps
      change 0 < eps at heps
      have hbound :
          forall x : Real,
            Set.Mem (Set.uIoc (0 : Real) eps) x ->
              norm (TS213.Goldbach.cosSquareHaarKernel x) <=
                (1 / 4 : Real) := by
        intro x hx
        rw [Set.uIoc_of_le heps.le] at hx
        simpa [Real.norm_eq_abs] using
          cosSquareHaarKernel_abs_le_quarter x hx.1
      have hnorm :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : Real))
          (b := eps)
          (C := (1 / 4 : Real))
          (f := TS213.Goldbach.cosSquareHaarKernel)
          hbound
      simpa [Real.norm_eq_abs, abs_of_pos heps] using hnorm
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Real.norm_eq_abs] using habs

/-- The product-filter cutoff integrals converge to the Lebesgue half-line integral. -/
theorem cosSquareImproperCutoffConvergence :
    TS219.Goldbach.CosSquareImproperCutoffConvergenceStatement := by
  unfold TS219.Goldbach.CosSquareImproperCutoffConvergenceStatement
  unfold TS213.Goldbach.cosSquareImproperIntegral
  have hupper :
      Tendsto
        (fun T : Real =>
          intervalIntegral
            TS213.Goldbach.cosSquareHaarKernel
            0
            T
            volume)
        atTop
        (nhds
          (integral
            (volume.restrict (Set.Ioi (0 : Real)))
            TS213.Goldbach.cosSquareHaarKernel)) :=
    intervalIntegral_tendsto_integral_Ioi
      0
      cosSquareHaarKernel_integrableOn_Ioi
      tendsto_id
  have hT :
      Tendsto
        (fun p : Prod Real Real =>
          intervalIntegral
            TS213.Goldbach.cosSquareHaarKernel
            0
            p.2
            volume)
        TS219.Goldbach.cosSquareCutoffFilter
        (nhds
          (integral
            (volume.restrict (Set.Ioi (0 : Real)))
            TS213.Goldbach.cosSquareHaarKernel)) :=
    hupper.comp tendsto_snd
  have heps :
      Tendsto
        (fun p : Prod Real Real =>
          intervalIntegral
            TS213.Goldbach.cosSquareHaarKernel
            0
            p.1
            volume)
        TS219.Goldbach.cosSquareCutoffFilter
        (nhds (0 : Real)) :=
    cosSquareHaarPartialIntegralZeroRight.comp tendsto_fst
  have hdiff := hT.sub heps
  have htarget :
      Tendsto
        (fun p : Prod Real Real =>
          intervalIntegral
              TS213.Goldbach.cosSquareHaarKernel
              0
              p.2
              volume -
            intervalIntegral
              TS213.Goldbach.cosSquareHaarKernel
              0
              p.1
              volume)
        TS219.Goldbach.cosSquareCutoffFilter
        (nhds
          (integral
            (volume.restrict (Set.Ioi (0 : Real)))
            TS213.Goldbach.cosSquareHaarKernel)) := by
    simpa using hdiff
  have hdecomp :
      Filter.Eventually
        (fun p : Prod Real Real =>
          intervalIntegral
              TS213.Goldbach.cosSquareHaarKernel
              0
              p.2
              volume -
            intervalIntegral
              TS213.Goldbach.cosSquareHaarKernel
              0
              p.1
              volume =
            intervalIntegral
              TS213.Goldbach.cosSquareHaarKernel
              p.1
              p.2
              volume)
        TS219.Goldbach.cosSquareCutoffFilter := by
    unfold TS219.Goldbach.cosSquareCutoffFilter
    have hpos :
        Filter.Eventually
          (fun eps : Real => 0 < eps)
          (nhdsWithin (0 : Real) (Set.Ioi (0 : Real))) := by
      filter_upwards [self_mem_nhdsWithin] with eps heps
      exact heps
    filter_upwards [Filter.prod_mem_prod hpos
      (eventually_gt_atTop (0 : Real))] with p hp
    cases hp with
    | intro heps hTpos =>
    change 0 < p.1 at heps
    change 0 < p.2 at hTpos
    have h0eps :
        IntervalIntegrable
          TS213.Goldbach.cosSquareHaarKernel
          volume
          0
          p.1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le heps.le]
      exact
        cosSquareHaarKernel_integrableOn_Ioi.mono_set
          Set.Ioc_subset_Ioi_self
    have h0T :
        IntervalIntegrable
          TS213.Goldbach.cosSquareHaarKernel
          volume
          0
          p.2 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hTpos.le]
      exact
        cosSquareHaarKernel_integrableOn_Ioi.mono_set
          Set.Ioc_subset_Ioi_self
    exact
      intervalIntegral.integral_interval_sub_left h0T h0eps
  exact htarget.congr' hdecomp

/-- The four TS219 cutoff inputs imply the cos-square value. -/
theorem cosSquareTripleIPPCutoffAssembly :
    TS219.Goldbach.CosSquareTripleIPPCutoffAssemblyStatement := by
  intro himproper hfinite hboundary hthird
  unfold TS219.Goldbach.CosSquareImproperCutoffConvergenceStatement at himproper
  unfold TS219.Goldbach.CosSquareFiniteTripleIPPStatement at hfinite
  unfold TS219.Goldbach.CosSquareBoundaryVanishingStatement at hboundary
  unfold TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement at hthird
  unfold TS213.Goldbach.CosSquareIntegralValueStatement
  have hrhs :
      Tendsto
        (fun p : Prod Real Real =>
          (1 / 6 : Real) *
              intervalIntegral
                (fun x : Real =>
                  TS213.Goldbach.cosSquareThirdDerivativeKernel x)
                p.1
                p.2
                volume +
            TS219.Goldbach.cosSquareTripleIPPBoundarySum p.1 p.2)
        TS219.Goldbach.cosSquareCutoffFilter
        (nhds (Real.pi / 6)) := by
    have hsum := (hthird.const_mul (1 / 6 : Real)).add hboundary
    convert hsum using 1
    ring_nf
  have heq :
      Filter.Eventually
        (fun p : Prod Real Real =>
          (1 / 6 : Real) *
                intervalIntegral
                  (fun x : Real =>
                    TS213.Goldbach.cosSquareThirdDerivativeKernel x)
                  p.1
                  p.2
                  volume +
              TS219.Goldbach.cosSquareTripleIPPBoundarySum p.1 p.2 =
            intervalIntegral
              (fun x : Real => TS213.Goldbach.cosSquareHaarKernel x)
              p.1
              p.2
              volume)
        TS219.Goldbach.cosSquareCutoffFilter := by
    unfold TS219.Goldbach.cosSquareCutoffFilter
    have hsmall :
        Filter.Eventually
          (fun eps : Real => eps < 1)
          (nhdsWithin (0 : Real) (Set.Ioi (0 : Real))) := by
      have hsmall_nhds :
          Filter.Eventually
            (fun eps : Real => eps < 1)
            (nhds (0 : Real)) :=
        Iio_mem_nhds (show (0 : Real) < 1 by norm_num)
      exact hsmall_nhds.filter_mono nhdsWithin_le_nhds
    have hpos :
        Filter.Eventually
          (fun eps : Real => 0 < eps)
          (nhdsWithin (0 : Real) (Set.Ioi (0 : Real))) := by
      filter_upwards [self_mem_nhdsWithin] with eps heps
      exact heps
    filter_upwards [Filter.prod_mem_prod (hpos.and hsmall)
      (eventually_gt_atTop (1 : Real))] with p hp
    cases hp with
    | intro hp_first hT_gt_one =>
    cases hp_first with
    | intro heps heps_lt_one =>
    change 0 < p.1 at heps
    change p.1 < 1 at heps_lt_one
    change 1 < p.2 at hT_gt_one
    have hepsT : p.1 < p.2 := by
      linarith
    exact (hfinite p.1 p.2 heps hepsT).symm
  have hhaar := hrhs.congr' heq
  letI : NeBot TS219.Goldbach.cosSquareCutoffFilter := by
    unfold TS219.Goldbach.cosSquareCutoffFilter
    exact Filter.prod_neBot.2
      (And.intro (nhdsGT_neBot (0 : Real)) (by infer_instance))
  exact tendsto_nhds_unique himproper hhaar

/-- Concrete TS219 cutoff assembly bridge. -/
def cosSquareTripleIPPCutoffBridge :
    TS219.Goldbach.CosSquareTripleIPPCutoffBridge where
  assembly := cosSquareTripleIPPCutoffAssembly

/-- All TS219 cutoff evidence is now available. -/
noncomputable def cosSquareTripleIPPCutoffEvidence :
    TS219.Goldbach.CosSquareTripleIPPCutoffEvidence where
  improper_cutoff_convergence :=
    cosSquareImproperCutoffConvergence
  finite_triple_ipp :=
    TS221.Goldbach.cosSquareFiniteTripleIPP
  boundary_vanishing :=
    TS224.Goldbach.cosSquareBoundaryVanishing
  third_derivative_cutoff_value :=
    TS244.Goldbach.cosSquareThirdDerivativeCutoffValue
  cutoff_bridge :=
    cosSquareTripleIPPCutoffBridge

/-- The positive-half-line cos-square integral has value `pi/6`. -/
theorem cosSquareImproperIntegralValue :
    TS213.Goldbach.CosSquareIntegralValueStatement :=
  TS219.Goldbach.cosSquareIntegralValue_of_cutoffEvidence
    cosSquareTripleIPPCutoffEvidence

/-- Ledger recording the TS245 cos-square cutoff assembly. -/
structure CosSquareImproperCutoffAssemblyLedger where
  ts244_cutoff_discharge :
    TS244.Goldbach.DirichletProductCutoffThirdDerivativeDischargeLedger

  haar_kernel_integrable :
    IntegrableOn
      TS213.Goldbach.cosSquareHaarKernel
      (Set.Ioi (0 : Real))
      volume

  improper_cutoff_convergence_proved :
    TS219.Goldbach.CosSquareImproperCutoffConvergenceStatement

  cutoff_assembly_proved :
    TS219.Goldbach.CosSquareTripleIPPCutoffAssemblyStatement

  cos_square_integral_value_proved :
    TS213.Goldbach.CosSquareIntegralValueStatement

  canonical_sinc_fourth_value_not_proved : True
  plancherel_not_proved : True
  explicit_formula_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS245 discharge ledger. -/
noncomputable def cosSquareImproperCutoffAssemblyLedger :
    CosSquareImproperCutoffAssemblyLedger where
  ts244_cutoff_discharge :=
    TS244.Goldbach.dirichletProductCutoffThirdDerivativeDischargeLedger
  haar_kernel_integrable :=
    cosSquareHaarKernel_integrableOn_Ioi
  improper_cutoff_convergence_proved :=
    cosSquareImproperCutoffConvergence
  cutoff_assembly_proved :=
    cosSquareTripleIPPCutoffAssembly
  cos_square_integral_value_proved :=
    cosSquareImproperIntegralValue
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS245. -/
def CosSquareImproperCutoffAssemblyTarget : Prop :=
  Nonempty CosSquareImproperCutoffAssemblyLedger

/-- TS245 target: the cos-square cutoff route now evaluates to `pi/6`. -/
theorem cosSquareImproperCutoffAssemblyTarget :
    CosSquareImproperCutoffAssemblyTarget :=
  Nonempty.intro cosSquareImproperCutoffAssemblyLedger

end Goldbach
end TS245
