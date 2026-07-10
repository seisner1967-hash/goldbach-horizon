import TS.Goldbach.Strong.TS248.WallOneFinalAnalyticInputConsumption

/-!
# TS249 - Effective Explicit Formula Constants Discharge

TS248 reduced the final analytic evidence package to effective explicit-formula
evidence and Gallagher evidence.  TS206 still required six fields for its
explicit-formula evidence, including admissibility of the constants package.

This sprint constructs a flexible constants family whose nonnegative constants
are supplied as `NNReal` values and whose lower scale is positive by
construction.  It proves admissibility unconditionally and reduces the TS206
evidence to four analytic fields plus the TS181 compatibility field.

No explicit-formula identity, main-term identification, zero bound, residual
bound, TS181 compatibility, Gallagher estimate, OTSA bridge, or Goldbach
theorem is proved here.
-/

namespace TS249
namespace Goldbach

/--
Flexible effective constants with nonnegativity and positive lower scale built
into their parameter types.
-/
noncomputable def admissibleExplicitFormulaConstants
    (mainTermModel : Nat -> Real)
    (zeroConstant residualConstant : NNReal)
    (zeroScalePower zeroLogPower residualScalePower residualLogPower : Nat)
    (lowerScaleOffset : Nat) :
    TS206.Goldbach.TriangleSplineExplicitFormulaConstants where
  mainTermModel :=
    mainTermModel
  zeroConstant :=
    zeroConstant
  zeroScalePower :=
    zeroScalePower
  zeroLogPower :=
    zeroLogPower
  residualConstant :=
    residualConstant
  residualScalePower :=
    residualScalePower
  residualLogPower :=
    residualLogPower
  lowerScale :=
    lowerScaleOffset + 1

/-- Every constants package in the TS249 family is TS206-admissible. -/
theorem admissibleExplicitFormulaConstants_admissible
    (mainTermModel : Nat -> Real)
    (zeroConstant residualConstant : NNReal)
    (zeroScalePower zeroLogPower residualScalePower residualLogPower : Nat)
    (lowerScaleOffset : Nat) :
    TS206.Goldbach.triangleSplineExplicitFormulaConstantsAdmissible
      (admissibleExplicitFormulaConstants
        mainTermModel
        zeroConstant
        residualConstant
        zeroScalePower
        zeroLogPower
        residualScalePower
        residualLogPower
        lowerScaleOffset) := by
  refine And.intro zeroConstant.coe_nonneg ?_
  exact And.intro residualConstant.coe_nonneg (by
    simp [admissibleExplicitFormulaConstants])

/--
The four scale-dependent analytic fields remaining after constants
admissibility is discharged.
-/
structure TriangleSplineExplicitFormulaCoreEvidence
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants) where
  explicit_formula_identity :
    (TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K)
      |>.explicit_formula_identity_statement

  main_term_identification :
    (TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K)
      |>.main_term_identification_statement

  zero_contribution_bound :
    (TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K)
      |>.zero_contribution_bound_statement

  residual_bound :
    (TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K)
      |>.residual_bound_statement

/--
Build complete TS206 evidence from core analytic evidence, admissible constants,
and the still-separate TS181 compatibility evidence.
-/
noncomputable def explicitFormulaEvidence_of_core
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (constantsAdmissible :
      TS206.Goldbach.triangleSplineExplicitFormulaConstantsAdmissible K)
    (core : TriangleSplineExplicitFormulaCoreEvidence K)
    (compatibility :
      TS206.Goldbach.TriangleSplineExplicitFormulaTS181CompatibilityStatement) :
    TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputEvidence
      (TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K) where
  explicit_formula_identity :=
    core.explicit_formula_identity
  main_term_identification :=
    core.main_term_identification
  zero_contribution_bound :=
    core.zero_contribution_bound
  residual_bound :=
    core.residual_bound
  effective_constants :=
    constantsAdmissible
  compatibility_with_ts181_blueprint :=
    compatibility

/--
Specialized TS206 evidence constructor for the automatically admissible TS249
constants family.
-/
noncomputable def explicitFormulaEvidence_of_admissibleConstants
    (mainTermModel : Nat -> Real)
    (zeroConstant residualConstant : NNReal)
    (zeroScalePower zeroLogPower residualScalePower residualLogPower : Nat)
    (lowerScaleOffset : Nat)
    (core :
      TriangleSplineExplicitFormulaCoreEvidence
        (admissibleExplicitFormulaConstants
          mainTermModel
          zeroConstant
          residualConstant
          zeroScalePower
          zeroLogPower
          residualScalePower
          residualLogPower
          lowerScaleOffset))
    (compatibility :
      TS206.Goldbach.TriangleSplineExplicitFormulaTS181CompatibilityStatement) :
    TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputEvidence
      (TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract
        (admissibleExplicitFormulaConstants
          mainTermModel
          zeroConstant
          residualConstant
          zeroScalePower
          zeroLogPower
          residualScalePower
          residualLogPower
          lowerScaleOffset)) :=
  explicitFormulaEvidence_of_core
    (admissibleExplicitFormulaConstants
      mainTermModel
      zeroConstant
      residualConstant
      zeroScalePower
      zeroLogPower
      residualScalePower
      residualLogPower
      lowerScaleOffset)
    (admissibleExplicitFormulaConstants_admissible
      mainTermModel
      zeroConstant
      residualConstant
      zeroScalePower
      zeroLogPower
      residualScalePower
      residualLogPower
      lowerScaleOffset)
    core
    compatibility

/--
Feed the reduced TS206 evidence and Gallagher evidence into the TS248 final
analytic package.  Wall 1 and constants admissibility require no arguments.
-/
noncomputable def finalAnalyticEvidence_of_coreCompatibilityGallagher
    (mainTermModel : Nat -> Real)
    (zeroConstant residualConstant : NNReal)
    (zeroScalePower zeroLogPower residualScalePower residualLogPower : Nat)
    (lowerScaleOffset : Nat)
    (core :
      TriangleSplineExplicitFormulaCoreEvidence
        (admissibleExplicitFormulaConstants
          mainTermModel
          zeroConstant
          residualConstant
          zeroScalePower
          zeroLogPower
          residualScalePower
          residualLogPower
          lowerScaleOffset))
    (compatibility :
      TS206.Goldbach.TriangleSplineExplicitFormulaTS181CompatibilityStatement)
    (gallagher : TS204.Goldbach.TriangleSplineGallagherInputContract)
    (gallagherEvidence :
      TS204.Goldbach.TriangleSplineGallagherInputEvidence gallagher) :
    TS204.Goldbach.FinalTriangleSplineAnalyticInputEvidence
      (TS248.Goldbach.finalAnalyticContractsForEffectiveExplicitFormula
        (admissibleExplicitFormulaConstants
          mainTermModel
          zeroConstant
          residualConstant
          zeroScalePower
          zeroLogPower
          residualScalePower
          residualLogPower
          lowerScaleOffset)
        gallagher) :=
  TS248.Goldbach.finalAnalyticEvidence_of_effectiveExplicitFormulaGallagher
    (admissibleExplicitFormulaConstants
      mainTermModel
      zeroConstant
      residualConstant
      zeroScalePower
      zeroLogPower
      residualScalePower
      residualLogPower
      lowerScaleOffset)
    gallagher
    (explicitFormulaEvidence_of_admissibleConstants
      mainTermModel
      zeroConstant
      residualConstant
      zeroScalePower
      zeroLogPower
      residualScalePower
      residualLogPower
      lowerScaleOffset
      core
      compatibility)
    gallagherEvidence

/-- Ledger recording the effective-constants discharge. -/
structure EffectiveExplicitFormulaConstantsDischargeLedger where
  ts248_wall_one_consumption :
    TS248.Goldbach.WallOneFinalAnalyticInputConsumptionLedger

  admissible_constants_family :
    forall
      (mainTermModel : Nat -> Real)
      (zeroConstant residualConstant : NNReal)
      (zeroScalePower zeroLogPower residualScalePower residualLogPower : Nat)
      (lowerScaleOffset : Nat),
        TS206.Goldbach.triangleSplineExplicitFormulaConstantsAdmissible
          (admissibleExplicitFormulaConstants
            mainTermModel
            zeroConstant
            residualConstant
            zeroScalePower
            zeroLogPower
            residualScalePower
            residualLogPower
            lowerScaleOffset)

  core_evidence_type_defined : True
  explicit_formula_evidence_constructor_defined : True
  final_analytic_evidence_constructor_defined : True

  explicit_formula_identity_not_proved : True
  main_term_identification_not_proved : True
  zero_contribution_bound_not_proved : True
  residual_bound_not_proved : True
  ts181_compatibility_not_proved : True
  gallagher_evidence_not_proved : True
  final_analytic_to_otsa_bridge_not_proved : True
  otsa_conclusion_bridge_not_proved : True
  goldbach_not_claimed_unconditionally : True

/-- Concrete TS249 constants-discharge ledger. -/
noncomputable def effectiveExplicitFormulaConstantsDischargeLedger :
    EffectiveExplicitFormulaConstantsDischargeLedger where
  ts248_wall_one_consumption :=
    TS248.Goldbach.wallOneFinalAnalyticInputConsumptionLedger
  admissible_constants_family :=
    admissibleExplicitFormulaConstants_admissible
  core_evidence_type_defined := True.intro
  explicit_formula_evidence_constructor_defined := True.intro
  final_analytic_evidence_constructor_defined := True.intro
  explicit_formula_identity_not_proved := True.intro
  main_term_identification_not_proved := True.intro
  zero_contribution_bound_not_proved := True.intro
  residual_bound_not_proved := True.intro
  ts181_compatibility_not_proved := True.intro
  gallagher_evidence_not_proved := True.intro
  final_analytic_to_otsa_bridge_not_proved := True.intro
  otsa_conclusion_bridge_not_proved := True.intro
  goldbach_not_claimed_unconditionally := True.intro

/-- Target proposition for TS249. -/
def EffectiveExplicitFormulaConstantsDischargeTarget : Prop :=
  Nonempty EffectiveExplicitFormulaConstantsDischargeLedger

/-- TS249 target: effective constants admissibility is discharged. -/
theorem effectiveExplicitFormulaConstantsDischargeTarget :
    EffectiveExplicitFormulaConstantsDischargeTarget :=
  Nonempty.intro effectiveExplicitFormulaConstantsDischargeLedger

end Goldbach
end TS249
