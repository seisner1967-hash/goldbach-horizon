import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TS.Goldbach.Strong.TS217.DirichletImproperReformulationBridge

namespace TS218
namespace Goldbach

open MeasureTheory

/-!
# TS218 - Sinc-Fourth Scaling and Evenness Discharge

TS213 reduced the canonical sinc-fourth value to five scalar obligations.
TS214 discharged the third-derivative formula, while TS217 corrected the
Dirichlet side to use cutoff or Abel improper targets.

This sprint discharges the two elementary integral obligations that remain
independent of Dirichlet and the triple integration by parts:

* the half-line scaling identity from `x = 2*u`;
* the full-line evenness identity for the canonical `sinc^4` kernel.

The scaling proof uses the pointwise identity

`canonicalSincFourthKernel u = 4 * cosSquareHaarKernel (2*u)`

on `0 < u`, followed by Mathlib's positive half-line change of variables.
The evenness proof first derives global integrability of the canonical kernel
from TS178's pi-scaled spectral integrability and the TS209 pi scaling, then
splits the full-line integral into positive and non-positive halves and maps
the non-positive half by `x -> -x`.

TS218 does not prove the Dirichlet cutoff or Abel value, does not prove the
improper triple IPP statement, does not prove the canonical sinc-fourth value,
and does not prove Plancherel, the explicit formula, Gallagher, or Goldbach.
-/

/-- The canonical `sinc^4` kernel is even. -/
theorem canonicalSincFourthKernel_even
    (x : Real) :
    TS213.Goldbach.canonicalSincFourthKernel (-x) =
      TS213.Goldbach.canonicalSincFourthKernel x := by
  unfold TS213.Goldbach.canonicalSincFourthKernel TS209.Goldbach.canonicalSincSq
  by_cases hx : x = 0
  case pos =>
    simp [hx]
  case neg =>
    have hneg : Ne (-x) 0 := by
      exact neg_ne_zero.mpr hx
    simp [hx, hneg, Real.sin_neg]

/-- The elementary identity `1 - cos (2*u) = 2*sin(u)^2`. -/
theorem one_sub_cos_two_mul_eq_two_sin_sq
    (u : Real) :
    1 - Real.cos (2 * u) = 2 * Real.sin u ^ 2 := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq u]

/--
Pointwise scaling behind the substitution `x = 2*u`.

On the positive half-line the canonical `sinc^4` kernel is four times the
cosine-square Haar kernel evaluated at `2*u`; the extra factor `1/2` comes
from the measure change in `halfLineSincFourthScaling`.
-/
theorem canonicalSincFourthKernel_scaling_pointwise
    (u : Real)
    (hu : 0 < u) :
    TS213.Goldbach.canonicalSincFourthKernel u =
      4 * TS213.Goldbach.cosSquareHaarKernel (2 * u) := by
  have hu_ne : Ne u 0 := ne_of_gt hu
  have htwo_ne : Ne (2 : Real) 0 := by
    norm_num
  have htwo_u_ne : Ne (2 * u) 0 := mul_ne_zero htwo_ne hu_ne
  unfold TS213.Goldbach.canonicalSincFourthKernel
    TS213.Goldbach.cosSquareHaarKernel
    TS213.Goldbach.cosSquareRemainder
    TS209.Goldbach.canonicalSincSq
  simp [hu_ne, htwo_u_ne]
  rw [one_sub_cos_two_mul_eq_two_sin_sq u]
  field_simp [hu_ne]
  ring

/-- TS218 discharges the TS213 half-line scaling obligation. -/
theorem halfLineSincFourthScaling :
    TS213.Goldbach.HalfLineSincFourthScalingStatement := by
  unfold TS213.Goldbach.HalfLineSincFourthScalingStatement
  unfold TS213.Goldbach.halfLineCanonicalSincFourthIntegral
    TS213.Goldbach.cosSquareImproperIntegral
  have hrewrite :
      integral
        (volume.restrict (Set.Ioi (0 : Real)))
        TS213.Goldbach.canonicalSincFourthKernel =
      integral
        (volume.restrict (Set.Ioi (0 : Real)))
        (fun u : Real => 4 * TS213.Goldbach.cosSquareHaarKernel (2 * u)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact canonicalSincFourthKernel_scaling_pointwise u hu
  have hscale :
      integral
        (volume.restrict (Set.Ioi (0 : Real)))
        (fun u : Real => TS213.Goldbach.cosSquareHaarKernel (2 * u)) =
      (1 / (2 : Real)) *
        integral
          (volume.restrict (Set.Ioi (0 : Real)))
          TS213.Goldbach.cosSquareHaarKernel := by
    simpa [one_div, smul_eq_mul] using
      (integral_comp_mul_left_Ioi
        TS213.Goldbach.cosSquareHaarKernel
        (0 : Real)
        (by norm_num : (0 : Real) < 2))
  calc
    integral
        (volume.restrict (Set.Ioi (0 : Real)))
        TS213.Goldbach.canonicalSincFourthKernel
        =
      integral
        (volume.restrict (Set.Ioi (0 : Real)))
        (fun u : Real => 4 * TS213.Goldbach.cosSquareHaarKernel (2 * u)) := hrewrite
    _ =
      4 *
        integral
          (volume.restrict (Set.Ioi (0 : Real)))
          (fun u : Real => TS213.Goldbach.cosSquareHaarKernel (2 * u)) := by
        rw [integral_mul_left]
    _ =
      2 *
        integral
          (volume.restrict (Set.Ioi (0 : Real)))
          TS213.Goldbach.cosSquareHaarKernel := by
        rw [hscale]
        ring

/--
The canonical unscaled `sinc^4` kernel is integrable.

This is obtained from the TS178 integrability of the pi-scaled spectral weight
and the TS209 identity between that weight and the canonical profile composed
with multiplication by `Real.pi`.
-/
theorem canonicalSincFourthKernel_integrable :
    Integrable
      TS213.Goldbach.canonicalSincFourthKernel
      (volume : Measure Real) := by
  have hscaled :
      Integrable
        (fun xi : Real =>
          TS213.Goldbach.canonicalSincFourthKernel (Real.pi * xi))
        (volume : Measure Real) := by
    refine TS178.Goldbach.triangleSplineSincRealWeight_sq_integrable.congr ?_
    exact Filter.Eventually.of_forall (by
      intro xi
      change
        TS178.Goldbach.triangleSplineSincRealWeight xi ^ 2 =
          TS209.Goldbach.canonicalSincSq (Real.pi * xi) ^ 2
      rw [TS209.Goldbach.triangleSplineSincRealWeight_eq_canonical_comp_pi])
  exact
    (MeasureTheory.integrable_comp_mul_left_iff
      (g := TS213.Goldbach.canonicalSincFourthKernel)
      Real.pi_ne_zero).mp hscaled

/-- TS218 discharges the TS213 full-line evenness obligation. -/
theorem fullLineSincFourthEvenness :
    TS213.Goldbach.FullLineSincFourthEvennessStatement := by
  unfold TS213.Goldbach.FullLineSincFourthEvennessStatement
  unfold TS213.Goldbach.fullLineCanonicalSincFourthIntegral
    TS213.Goldbach.halfLineCanonicalSincFourthIntegral
  have hsplit :=
    integral_add_compl
      (f := TS213.Goldbach.canonicalSincFourthKernel)
      (s := Set.Ioi (0 : Real))
      measurableSet_Ioi
      canonicalSincFourthKernel_integrable
  rw [Set.compl_Ioi] at hsplit
  have hneg :
      integral
        (volume.restrict (Set.Iic (0 : Real)))
        TS213.Goldbach.canonicalSincFourthKernel =
      integral
        (volume.restrict (Set.Ioi (0 : Real)))
        TS213.Goldbach.canonicalSincFourthKernel := by
    calc
      integral
          (volume.restrict (Set.Iic (0 : Real)))
          TS213.Goldbach.canonicalSincFourthKernel =
        integral
          (volume.restrict (Set.Iic (0 : Real)))
          (fun x : Real =>
            TS213.Goldbach.canonicalSincFourthKernel (-x)) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (by
            intro x
            exact (canonicalSincFourthKernel_even x).symm)
      _ =
        integral
          (volume.restrict (Set.Ioi (0 : Real)))
          TS213.Goldbach.canonicalSincFourthKernel := by
          simpa using
            (integral_comp_neg_Iic
              (c := (0 : Real))
              (f := TS213.Goldbach.canonicalSincFourthKernel))
  calc
    integral
        (volume : Measure Real)
        TS213.Goldbach.canonicalSincFourthKernel =
      integral
          (volume.restrict (Set.Ioi (0 : Real)))
          TS213.Goldbach.canonicalSincFourthKernel +
        integral
          (volume.restrict (Set.Iic (0 : Real)))
          TS213.Goldbach.canonicalSincFourthKernel := hsplit.symm
    _ =
      2 *
        integral
          (volume.restrict (Set.Ioi (0 : Real)))
          TS213.Goldbach.canonicalSincFourthKernel := by
        rw [hneg]
        ring

/-- Ledger recording the TS218 scaling and evenness discharge. -/
structure SincFourthScalingEvennessDischargeLedger where
  ts217_dirichlet_reformulation :
    TS217.Goldbach.DirichletImproperReformulationLedger

  scaling_statement :
    Prop

  scaling_statement_eq :
    scaling_statement = TS213.Goldbach.HalfLineSincFourthScalingStatement

  scaling_proved :
    scaling_statement

  evenness_statement :
    Prop

  evenness_statement_eq :
    evenness_statement = TS213.Goldbach.FullLineSincFourthEvennessStatement

  evenness_proved :
    evenness_statement

  canonical_integrability :
    Integrable
      TS213.Goldbach.canonicalSincFourthKernel
      (volume : Measure Real)

  dirichlet_cutoff_not_proved :
    True

  dirichlet_abel_not_proved :
    True

  improper_triple_ipp_not_proved :
    True

  canonical_sinc_fourth_value_not_proved :
    True

  plancherel_not_proved :
    True

  explicit_formula_not_proved :
    True

  gallagher_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS218 scaling and evenness discharge ledger. -/
noncomputable def sincFourthScalingEvennessDischargeLedger :
    SincFourthScalingEvennessDischargeLedger where
  ts217_dirichlet_reformulation :=
    TS217.Goldbach.dirichletImproperReformulationLedger
  scaling_statement := TS213.Goldbach.HalfLineSincFourthScalingStatement
  scaling_statement_eq := rfl
  scaling_proved := halfLineSincFourthScaling
  evenness_statement := TS213.Goldbach.FullLineSincFourthEvennessStatement
  evenness_statement_eq := rfl
  evenness_proved := fullLineSincFourthEvenness
  canonical_integrability := canonicalSincFourthKernel_integrable
  dirichlet_cutoff_not_proved := True.intro
  dirichlet_abel_not_proved := True.intro
  improper_triple_ipp_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS218. -/
def SincFourthScalingEvennessDischargeTarget :
    Prop :=
  Nonempty SincFourthScalingEvennessDischargeLedger

theorem sincFourthScalingEvennessDischargeTarget :
    SincFourthScalingEvennessDischargeTarget :=
  Nonempty.intro sincFourthScalingEvennessDischargeLedger

end Goldbach
end TS218
