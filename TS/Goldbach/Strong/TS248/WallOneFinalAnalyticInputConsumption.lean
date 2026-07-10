import TS.Goldbach.Strong.TS205.FinalAnalyticInputsToOTSARoutingBridge
import TS.Goldbach.Strong.TS206.ExplicitFormulaEffectiveStatement
import TS.Goldbach.Strong.TS247.TriangleSplinePlancherelEvidenceAssembly

/-!
# TS248 - Wall One Final Analytic Input Consumption

TS247 assembled the concrete triangle-spline Plancherel evidence required by
TS204.  This sprint consumes that term in the final analytic input bundle.

The resulting constructors require only effective explicit-formula evidence
and Gallagher evidence.  A supplied TS205 adapter then yields the five TS200
OTSA input slots, and a supplied TS200 conclusion bridge yields the conditional
binary Goldbach output.

No explicit-formula evidence, Gallagher evidence, TS205 adapter, TS200
conclusion bridge, or unconditional Goldbach theorem is proved here.
-/

namespace TS248
namespace Goldbach

/--
Final analytic contracts with the concrete Wall 1 Plancherel contract fixed.
-/
noncomputable def finalAnalyticContractsWithWallOne
    (explicitFormula :
      TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputContract)
    (gallagher : TS204.Goldbach.TriangleSplineGallagherInputContract) :
    TS204.Goldbach.FinalTriangleSplineAnalyticInputContracts where
  plancherel :=
    TS204.Goldbach.triangleSplinePlancherelInputContract
  explicit_formula :=
    explicitFormula
  gallagher :=
    gallagher

/-- The Plancherel field of the reduced contract bundle is fixed by TS247. -/
theorem finalAnalyticContractsWithWallOne_plancherel
    (explicitFormula :
      TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputContract)
    (gallagher : TS204.Goldbach.TriangleSplineGallagherInputContract) :
    (finalAnalyticContractsWithWallOne explicitFormula gallagher).plancherel =
      TS204.Goldbach.triangleSplinePlancherelInputContract :=
  rfl

/--
Populate the final TS204 analytic evidence from the two remaining evidence
families.  The Plancherel field is supplied unconditionally by TS247.
-/
noncomputable def finalAnalyticEvidence_of_remainingInputs
    (explicitFormula :
      TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputContract)
    (gallagher : TS204.Goldbach.TriangleSplineGallagherInputContract)
    (explicitFormulaEvidence :
      TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputEvidence
        explicitFormula)
    (gallagherEvidence :
      TS204.Goldbach.TriangleSplineGallagherInputEvidence gallagher) :
    TS204.Goldbach.FinalTriangleSplineAnalyticInputEvidence
      (finalAnalyticContractsWithWallOne explicitFormula gallagher) where
  plancherel :=
    TS247.Goldbach.triangleSplinePlancherelEvidence
  explicit_formula :=
    explicitFormulaEvidence
  gallagher :=
    gallagherEvidence

/--
Specialize the reduced bundle to the concrete effective explicit-formula
contract family defined by TS206.
-/
noncomputable def finalAnalyticContractsForEffectiveExplicitFormula
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (gallagher : TS204.Goldbach.TriangleSplineGallagherInputContract) :
    TS204.Goldbach.FinalTriangleSplineAnalyticInputContracts :=
  finalAnalyticContractsWithWallOne
    (TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K)
    gallagher

/--
Build the TS204 evidence bundle for the concrete TS206 explicit-formula
contract once the remaining two evidence terms are supplied.
-/
noncomputable def finalAnalyticEvidence_of_effectiveExplicitFormulaGallagher
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (gallagher : TS204.Goldbach.TriangleSplineGallagherInputContract)
    (explicitFormulaEvidence :
      TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputEvidence
        (TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K))
    (gallagherEvidence :
      TS204.Goldbach.TriangleSplineGallagherInputEvidence gallagher) :
    TS204.Goldbach.FinalTriangleSplineAnalyticInputEvidence
      (finalAnalyticContractsForEffectiveExplicitFormula K gallagher) :=
  finalAnalyticEvidence_of_remainingInputs
    (TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K)
    gallagher
    explicitFormulaEvidence
    gallagherEvidence

/--
Route the reduced final analytic evidence into the five TS200 OTSA input slots
when a TS205 adapter is supplied.
-/
noncomputable def otsaInputEvidence_of_remainingAnalyticInputs
    (explicitFormula :
      TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputContract)
    (gallagher : TS204.Goldbach.TriangleSplineGallagherInputContract)
    (explicitFormulaEvidence :
      TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputEvidence
        explicitFormula)
    (gallagherEvidence :
      TS204.Goldbach.TriangleSplineGallagherInputEvidence gallagher)
    (bridge :
      TS205.Goldbach.FinalAnalyticToOTSAInputBridge
        (finalAnalyticContractsWithWallOne explicitFormula gallagher)) :
    TS200.Goldbach.OTSAInputEvidence bridge.otsa_contracts :=
  TS205.Goldbach.otsaInputEvidence_of_finalAnalyticEvidence
    (finalAnalyticContractsWithWallOne explicitFormula gallagher)
    (finalAnalyticEvidence_of_remainingInputs
      explicitFormula
      gallagher
      explicitFormulaEvidence
      gallagherEvidence)
    bridge

/--
Conditional terminal router with Wall 1 already discharged.  Goldbach remains
an output and is not present in any input evidence package.
-/
theorem binaryGoldbach_of_remainingAnalyticInputs
    (explicitFormula :
      TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputContract)
    (gallagher : TS204.Goldbach.TriangleSplineGallagherInputContract)
    (explicitFormulaEvidence :
      TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputEvidence
        explicitFormula)
    (gallagherEvidence :
      TS204.Goldbach.TriangleSplineGallagherInputEvidence gallagher)
    (bridge :
      TS205.Goldbach.FinalAnalyticToOTSAInputBridge
        (finalAnalyticContractsWithWallOne explicitFormula gallagher))
    (conclusionBridge :
      TS200.Goldbach.OTSAConclusionBridge bridge.otsa_contracts) :
    TS200.Goldbach.BinaryGoldbachStatement :=
  TS205.Goldbach.binaryGoldbach_of_finalAnalyticBridge
    (finalAnalyticContractsWithWallOne explicitFormula gallagher)
    (finalAnalyticEvidence_of_remainingInputs
      explicitFormula
      gallagher
      explicitFormulaEvidence
      gallagherEvidence)
    bridge
    conclusionBridge

/-- Ledger recording the concrete Wall 1 consumption. -/
structure WallOneFinalAnalyticInputConsumptionLedger where
  ts247_wall_one_assembly :
    TS247.Goldbach.TriangleSplinePlancherelEvidenceAssemblyLedger

  concrete_plancherel_evidence :
    TS204.Goldbach.TriangleSplinePlancherelInputEvidence
      TS204.Goldbach.triangleSplinePlancherelInputContract

  reduced_evidence_constructor :
    forall
      (explicitFormula :
        TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputContract)
      (gallagher : TS204.Goldbach.TriangleSplineGallagherInputContract),
        TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputEvidence
            explicitFormula ->
          TS204.Goldbach.TriangleSplineGallagherInputEvidence gallagher ->
            TS204.Goldbach.FinalTriangleSplineAnalyticInputEvidence
              (finalAnalyticContractsWithWallOne explicitFormula gallagher)

  explicit_formula_evidence_not_proved : True
  gallagher_evidence_not_proved : True
  final_analytic_to_otsa_bridge_not_proved : True
  otsa_conclusion_bridge_not_proved : True
  goldbach_not_claimed_unconditionally : True

/-- Concrete TS248 Wall 1 consumption ledger. -/
noncomputable def wallOneFinalAnalyticInputConsumptionLedger :
    WallOneFinalAnalyticInputConsumptionLedger where
  ts247_wall_one_assembly :=
    TS247.Goldbach.triangleSplinePlancherelEvidenceAssemblyLedger
  concrete_plancherel_evidence :=
    TS247.Goldbach.triangleSplinePlancherelEvidence
  reduced_evidence_constructor :=
    finalAnalyticEvidence_of_remainingInputs
  explicit_formula_evidence_not_proved := True.intro
  gallagher_evidence_not_proved := True.intro
  final_analytic_to_otsa_bridge_not_proved := True.intro
  otsa_conclusion_bridge_not_proved := True.intro
  goldbach_not_claimed_unconditionally := True.intro

/-- Target proposition for TS248. -/
def WallOneFinalAnalyticInputConsumptionTarget : Prop :=
  Nonempty WallOneFinalAnalyticInputConsumptionLedger

/-- TS248 target: Wall 1 is consumed by the final analytic input package. -/
theorem wallOneFinalAnalyticInputConsumptionTarget :
    WallOneFinalAnalyticInputConsumptionTarget :=
  Nonempty.intro wallOneFinalAnalyticInputConsumptionLedger

end Goldbach
end TS248
