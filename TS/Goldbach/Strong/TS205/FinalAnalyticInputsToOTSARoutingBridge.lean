import Mathlib.Tactic
import TS.Goldbach.Strong.TS200.OTSANonCircularConsumptionInterface
import TS.Goldbach.Strong.TS204.FinalAnalyticInputsSpecification

namespace TS205
namespace Goldbach

/-!
# TS205 - Final Analytic Inputs to OTSA Routing Bridge

TS204 specified the final triangle-spline analytic input families.  TS200
specified the non-circular OTSA interface in which Goldbach is an output, never
an input.

This sprint builds the routing adapter between them.  A supplied bridge may
turn final analytic evidence into evidence for the five TS200 OTSA input slots.
If, in addition, a TS200 `OTSAConclusionBridge` is supplied, then the binary
Goldbach output follows by the TS200 routing theorem.

No analytic input, OTSA input slot, conclusion bridge, or Goldbach theorem is
proved here.
-/

/--
A non-circular adapter from final triangle-spline analytic evidence to a chosen
TS200 OTSA input contract package.

The adapter is itself future evidence.  It records how final analytic evidence
would populate the five OTSA input slots, but it does not prove those
implications here.
-/
structure FinalAnalyticToOTSAInputBridge
    (contracts : TS204.Goldbach.FinalTriangleSplineAnalyticInputContracts) where
  otsa_contracts :
    TS200.Goldbach.OTSAInputContracts

  trace_constant_bound_from_final_analytic :
    TS204.Goldbach.FinalTriangleSplineAnalyticInputEvidence contracts ->
      otsa_contracts.trace_constant_bound_statement

  mellin_tail_bound_from_final_analytic :
    TS204.Goldbach.FinalTriangleSplineAnalyticInputEvidence contracts ->
      otsa_contracts.mellin_tail_bound_statement

  sieve_budget_replacement_from_final_analytic :
    TS204.Goldbach.FinalTriangleSplineAnalyticInputEvidence contracts ->
      otsa_contracts.sieve_budget_replacement_statement

  final_otsa_inequality_from_final_analytic :
    TS204.Goldbach.FinalTriangleSplineAnalyticInputEvidence contracts ->
      otsa_contracts.final_otsa_inequality_statement

  combinatorial_reduction_from_final_analytic :
    TS204.Goldbach.FinalTriangleSplineAnalyticInputEvidence contracts ->
      otsa_contracts.combinatorial_reduction_statement

/--
Turn final analytic evidence into TS200 OTSA input evidence, provided a bridge
from the final analytic inputs to the five TS200 slots is supplied.
-/
noncomputable def otsaInputEvidence_of_finalAnalyticEvidence
    (contracts : TS204.Goldbach.FinalTriangleSplineAnalyticInputContracts)
    (evidence : TS204.Goldbach.FinalTriangleSplineAnalyticInputEvidence contracts)
    (bridge : FinalAnalyticToOTSAInputBridge contracts) :
    TS200.Goldbach.OTSAInputEvidence bridge.otsa_contracts where
  trace_constant_bound :=
    bridge.trace_constant_bound_from_final_analytic evidence
  mellin_tail_bound :=
    bridge.mellin_tail_bound_from_final_analytic evidence
  sieve_budget_replacement :=
    bridge.sieve_budget_replacement_from_final_analytic evidence
  final_otsa_inequality :=
    bridge.final_otsa_inequality_from_final_analytic evidence
  combinatorial_reduction :=
    bridge.combinatorial_reduction_from_final_analytic evidence

/--
Conditional routing theorem.

This is not an unconditional Goldbach theorem.  It says that if final analytic
evidence is supplied, if a non-circular adapter turns it into TS200 OTSA input
evidence, and if a TS200 conclusion bridge is supplied, then the TS200 binary
Goldbach output follows.
-/
theorem binaryGoldbach_of_finalAnalyticBridge
    (contracts : TS204.Goldbach.FinalTriangleSplineAnalyticInputContracts)
    (evidence : TS204.Goldbach.FinalTriangleSplineAnalyticInputEvidence contracts)
    (bridge : FinalAnalyticToOTSAInputBridge contracts)
    (conclusion_bridge :
      TS200.Goldbach.OTSAConclusionBridge bridge.otsa_contracts) :
    TS200.Goldbach.BinaryGoldbachStatement :=
  TS200.Goldbach.binaryGoldbach_of_otsaConclusionBridge
    bridge.otsa_contracts
    (otsaInputEvidence_of_finalAnalyticEvidence contracts evidence bridge)
    conclusion_bridge

/-- Ledger for the TS205 routing interface. -/
structure FinalAnalyticToOTSARoutingBridgeLedger where
  ts200_interface :
    TS200.Goldbach.OTSANonCircularConsumptionLedger

  ts204_specification :
    TS204.Goldbach.FinalAnalyticInputsSpecificationLedger

  bridge_type_defined :
    True

  evidence_constructor_defined :
    True

  conditional_routing_theorem_defined :
    True

  analytic_inputs_not_proved :
    True

  otsa_inputs_not_proved :
    True

  otsa_conclusion_bridge_not_proved :
    True

  goldbach_not_claimed_unconditionally :
    True

/-- Concrete TS205 routing bridge ledger. -/
noncomputable def finalAnalyticToOTSARoutingBridgeLedger :
    FinalAnalyticToOTSARoutingBridgeLedger where
  ts200_interface :=
    TS200.Goldbach.otsaNonCircularConsumptionLedger
  ts204_specification :=
    TS204.Goldbach.finalAnalyticInputsSpecificationLedger
  bridge_type_defined := True.intro
  evidence_constructor_defined := True.intro
  conditional_routing_theorem_defined := True.intro
  analytic_inputs_not_proved := True.intro
  otsa_inputs_not_proved := True.intro
  otsa_conclusion_bridge_not_proved := True.intro
  goldbach_not_claimed_unconditionally := True.intro

/-- Target proposition for TS205. -/
def FinalAnalyticToOTSARoutingBridgeTarget : Prop :=
  Nonempty FinalAnalyticToOTSARoutingBridgeLedger

/-- The TS205 routing bridge target is populated. -/
theorem finalAnalyticToOTSARoutingBridgeTarget :
    FinalAnalyticToOTSARoutingBridgeTarget :=
  Nonempty.intro finalAnalyticToOTSARoutingBridgeLedger

end Goldbach
end TS205
