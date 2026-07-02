import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TS.Goldbach.Strong.TS214.CosSquareThirdDerivativeFormulaDischarge

namespace TS215
namespace Goldbach

open MeasureTheory

/-!
# TS215 - Dirichlet Sine Integral API Probe

TS213 introduced the positive-frequency Dirichlet sine integral as the second
scalar obligation in the direct non-Plancherel route to the canonical
`sinc^4` value:

`forall a > 0, integral_0^infty sin (a*x) / x = pi / 2`.

TS215 does not prove this integral.  It probes the local Mathlib API needed for
the route.  The bundled Mathlib exposes the positive-half-line scaling theorem
`integral_comp_mul_left_Ioi`, but no ready-made `sin x / x` Dirichlet value was
located in the local search.  The sprint therefore records a fail-closed split:
the TS213 Dirichlet obligation follows from a unit-frequency Dirichlet value and
a positive-frequency scaling statement, while the actual analytic value remains
open.

No Dirichlet integral, improper IPP, scaling of the singular sine kernel,
Plancherel theorem, or Goldbach theorem is claimed.
-/

/-- Status of the local API probe for the Dirichlet sine integral. -/
inductive DirichletSineIntegralAPIStatus where
  /-- The base `sin x / x` integral value was not located as a ready-made theorem. -/
  | baseValueNotLocated
  /-- Mathlib's positive-half-line scaling theorem is available. -/
  | ioiScalingAvailable
  deriving DecidableEq, Repr

/-- Unit-frequency Dirichlet sine integral target. -/
def DirichletUnitFrequencyStatement :
    Prop :=
  integral
    (volume.restrict (Set.Ioi (0 : Real)))
    (TS213.Goldbach.sineDirichletKernel 1) =
    Real.pi / 2

/-- Positive-frequency scaling target for the Dirichlet sine kernel. -/
def DirichletPositiveFrequencyScalingStatement :
    Prop :=
  forall a : Real,
    0 < a ->
      integral
        (volume.restrict (Set.Ioi (0 : Real)))
        (TS213.Goldbach.sineDirichletKernel a) =
      integral
        (volume.restrict (Set.Ioi (0 : Real)))
        (TS213.Goldbach.sineDirichletKernel 1)

/-- The available Mathlib positive-half-line scaling API, stated in project form. -/
def IoiScalingAPISymbolAvailable :
    Prop :=
  forall g : Real -> Real,
    forall a b : Real,
      0 < b ->
        integral
          (volume.restrict (Set.Ioi a))
          (fun x : Real => g (b * x)) =
        (1 / b) *
          integral
            (volume.restrict (Set.Ioi (b * a)))
            g

/-- Mathlib supplies the positive-half-line scaling theorem. -/
theorem ioiScalingAPISymbolAvailable :
    IoiScalingAPISymbolAvailable := by
  intro g a b hb
  simpa [one_div, smul_eq_mul] using
    (integral_comp_mul_left_Ioi g a hb)

/--
The TS213 all-positive-frequency Dirichlet input follows from the unit value and
the positive-frequency scaling statement.
-/
theorem dirichletSineIntegral_of_unitValue_and_scaling
    (h_unit :
      DirichletUnitFrequencyStatement)
    (h_scaling :
      DirichletPositiveFrequencyScalingStatement) :
    TS213.Goldbach.DirichletSineIntegralStatement := by
  intro a ha
  calc
    integral
        (volume.restrict (Set.Ioi (0 : Real)))
        (TS213.Goldbach.sineDirichletKernel a)
        =
      integral
        (volume.restrict (Set.Ioi (0 : Real)))
        (TS213.Goldbach.sineDirichletKernel 1) :=
        h_scaling a ha
    _ = Real.pi / 2 := h_unit

/-- Ledger recording the TS215 Dirichlet sine integral API probe. -/
structure DirichletSineIntegralAPIProbeLedger where
  ts214_derivative_discharge :
    TS214.Goldbach.CosSquareThirdDerivativeFormulaDischargeLedger

  base_value_status :
    DirichletSineIntegralAPIStatus

  base_value_status_eq :
    base_value_status =
      DirichletSineIntegralAPIStatus.baseValueNotLocated

  ioi_scaling_status :
    DirichletSineIntegralAPIStatus

  ioi_scaling_status_eq :
    ioi_scaling_status =
      DirichletSineIntegralAPIStatus.ioiScalingAvailable

  unit_frequency_statement :
    Prop

  unit_frequency_statement_eq :
    unit_frequency_statement = DirichletUnitFrequencyStatement

  positive_frequency_scaling_statement :
    Prop

  positive_frequency_scaling_statement_eq :
    positive_frequency_scaling_statement =
      DirichletPositiveFrequencyScalingStatement

  ioi_scaling_api_statement :
    Prop

  ioi_scaling_api_statement_eq :
    ioi_scaling_api_statement =
      IoiScalingAPISymbolAvailable

  ioi_scaling_api_available :
    ioi_scaling_api_statement

  unit_and_scaling_imply_ts213_dirichlet :
    unit_frequency_statement ->
      positive_frequency_scaling_statement ->
        TS213.Goldbach.DirichletSineIntegralStatement

  dirichlet_unit_frequency_not_proved :
    True

  dirichlet_positive_frequency_scaling_not_proved :
    True

  ts213_dirichlet_statement_not_proved :
    True

  improper_triple_ipp_not_proved :
    True

  sinc_fourth_scaling_not_proved :
    True

  sinc_fourth_evenness_not_proved :
    True

  canonical_sinc_fourth_integral_not_proved :
    True

  plancherel_not_used :
    True

  explicit_formula_not_proved :
    True

  gallagher_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS215 API-probe ledger. -/
noncomputable def dirichletSineIntegralAPIProbeLedger :
    DirichletSineIntegralAPIProbeLedger where
  ts214_derivative_discharge :=
    TS214.Goldbach.cosSquareThirdDerivativeFormulaDischargeLedger
  base_value_status :=
    DirichletSineIntegralAPIStatus.baseValueNotLocated
  base_value_status_eq := rfl
  ioi_scaling_status :=
    DirichletSineIntegralAPIStatus.ioiScalingAvailable
  ioi_scaling_status_eq := rfl
  unit_frequency_statement :=
    DirichletUnitFrequencyStatement
  unit_frequency_statement_eq := rfl
  positive_frequency_scaling_statement :=
    DirichletPositiveFrequencyScalingStatement
  positive_frequency_scaling_statement_eq := rfl
  ioi_scaling_api_statement :=
    IoiScalingAPISymbolAvailable
  ioi_scaling_api_statement_eq := rfl
  ioi_scaling_api_available :=
    ioiScalingAPISymbolAvailable
  unit_and_scaling_imply_ts213_dirichlet :=
    dirichletSineIntegral_of_unitValue_and_scaling
  dirichlet_unit_frequency_not_proved := True.intro
  dirichlet_positive_frequency_scaling_not_proved := True.intro
  ts213_dirichlet_statement_not_proved := True.intro
  improper_triple_ipp_not_proved := True.intro
  sinc_fourth_scaling_not_proved := True.intro
  sinc_fourth_evenness_not_proved := True.intro
  canonical_sinc_fourth_integral_not_proved := True.intro
  plancherel_not_used := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS215. -/
def DirichletSineIntegralAPIProbeTarget :
    Prop :=
  Nonempty DirichletSineIntegralAPIProbeLedger

/-- The TS215 Dirichlet sine integral API-probe target is populated. -/
theorem dirichletSineIntegralAPIProbeTarget :
    DirichletSineIntegralAPIProbeTarget :=
  Nonempty.intro dirichletSineIntegralAPIProbeLedger

end Goldbach
end TS215
