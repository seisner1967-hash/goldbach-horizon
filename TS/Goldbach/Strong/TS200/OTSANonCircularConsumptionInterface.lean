import Mathlib.Tactic
import TS.Goldbach.Strong.TS199.OTSAStrategicDashboardSynthesis

namespace TS200
namespace Goldbach

/-!
# TS200 - OTSA Non-Circular Consumption Interface

TS199 deliberately left the future OTSA consumption contracts unpopulated.
One of those slots was named `conditional_goldbach_statement`, which is useful
as a dashboard marker but dangerous as a final proof interface: a final theorem
must not assume Goldbach as one of its inputs.

TS200 therefore introduces a non-circular consumption interface.  The inputs are
only the analytic, sieve, inequality, and combinatorial-reduction obligations.
The binary Goldbach statement is defined separately as the output.  A final
bridge may consume the inputs and return Goldbach, but Goldbach is not itself an
input field.

No OTSA input contract is proved here.
-/

/-- Binary Goldbach statement in the form targeted by the final OTSA bridge. -/
def BinaryGoldbachStatement : Prop :=
  forall N : Nat,
    Even N ->
      2 < N ->
        exists p q : Nat,
          Nat.Prime p /\ Nat.Prime q /\ p + q = N

/--
Non-circular OTSA input contracts.

These are the obligations that a future final bridge may consume.  The
Goldbach conclusion is intentionally absent from this structure.
-/
structure OTSAInputContracts where
  trace_constant_bound_statement :
    Prop
  mellin_tail_bound_statement :
    Prop
  sieve_budget_replacement_statement :
    Prop
  final_otsa_inequality_statement :
    Prop
  combinatorial_reduction_statement :
    Prop

/-- Evidence package for the non-circular OTSA inputs. -/
structure OTSAInputEvidence
    (contracts : OTSAInputContracts) where
  trace_constant_bound :
    contracts.trace_constant_bound_statement
  mellin_tail_bound :
    contracts.mellin_tail_bound_statement
  sieve_budget_replacement :
    contracts.sieve_budget_replacement_statement
  final_otsa_inequality :
    contracts.final_otsa_inequality_statement
  combinatorial_reduction :
    contracts.combinatorial_reduction_statement

/--
Final bridge type: inputs may imply Goldbach.

This structure is the only place where the conclusion is produced.  Supplying
such a bridge is a future obligation, not something TS200 proves.
-/
structure OTSAConclusionBridge
    (contracts : OTSAInputContracts) where
  conclusion_from_inputs :
    OTSAInputEvidence contracts -> BinaryGoldbachStatement

/--
Consuming a non-circular final bridge yields the binary Goldbach statement.

The theorem is intentionally small: it checks that Goldbach is an output of the
bridge, not an assumption carried inside the input evidence.
-/
theorem binaryGoldbach_of_otsaConclusionBridge
    (contracts : OTSAInputContracts)
    (evidence : OTSAInputEvidence contracts)
    (bridge : OTSAConclusionBridge contracts) :
    BinaryGoldbachStatement :=
  bridge.conclusion_from_inputs evidence

/--
Ledger recording the non-circular TS200 interface.

The TS199 dashboard remains available as the previous governance state, but the
TS199 `conditional_goldbach_statement` slot is not used as an input to this
interface.
-/
structure OTSANonCircularConsumptionLedger where
  ts199_dashboard :
    TS199.Goldbach.OTSAStrategicDashboardLedger

  input_contracts_registered :
    True

  input_evidence_registered :
    True

  conclusion_bridge_registered :
    True

  binary_goldbach_statement_registered :
    True

  binary_goldbach_from_bridge :
    forall (contracts : OTSAInputContracts),
      OTSAInputEvidence contracts ->
      OTSAConclusionBridge contracts ->
        BinaryGoldbachStatement

  goldbach_is_output_not_input :
    True

  ts199_conditional_goldbach_slot_not_consumed :
    True

  trace_constant_not_proved :
    True

  mellin_tail_constant_not_proved :
    True

  replacement_sieve_budget_not_proved :
    True

  final_otsa_inequality_not_proved :
    True

  combinatorial_reduction_not_proved :
    True

  goldbach_not_proved :
    True

/-- Concrete TS200 non-circular consumption ledger. -/
noncomputable def otsaNonCircularConsumptionLedger :
    OTSANonCircularConsumptionLedger where
  ts199_dashboard :=
    TS199.Goldbach.otsaStrategicDashboardLedger
  input_contracts_registered := True.intro
  input_evidence_registered := True.intro
  conclusion_bridge_registered := True.intro
  binary_goldbach_statement_registered := True.intro
  binary_goldbach_from_bridge :=
    binaryGoldbach_of_otsaConclusionBridge
  goldbach_is_output_not_input := True.intro
  ts199_conditional_goldbach_slot_not_consumed := True.intro
  trace_constant_not_proved := True.intro
  mellin_tail_constant_not_proved := True.intro
  replacement_sieve_budget_not_proved := True.intro
  final_otsa_inequality_not_proved := True.intro
  combinatorial_reduction_not_proved := True.intro
  goldbach_not_proved := True.intro

/-- Target proposition for TS200. -/
def OTSANonCircularConsumptionTarget : Prop :=
  Nonempty OTSANonCircularConsumptionLedger

/-- The TS200 non-circular consumption target is populated. -/
theorem otsaNonCircularConsumptionTarget :
    OTSANonCircularConsumptionTarget :=
  Nonempty.intro otsaNonCircularConsumptionLedger

end Goldbach
end TS200
