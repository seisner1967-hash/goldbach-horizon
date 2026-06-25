import Mathlib.Tactic
import TS.Goldbach.Strong.TS174.TriangleSplinePlancherelInterfaceProbe
import TS.Goldbach.Strong.TS181.ExplicitFormulaTraceBlueprint
import TS.Goldbach.Strong.TS188.TriangleSplineAnalyticWall1PlancherelContractBridge
import TS.Goldbach.Strong.TS200.OTSANonCircularConsumptionInterface
import TS.Goldbach.Strong.TS203.TruncatedHaarTransport

namespace TS204
namespace Goldbach

open scoped ENNReal

/-!
# TS204 - Final Analytic Inputs Specification

TS200 introduced the non-circular OTSA consumption interface: Goldbach is an
output, never an input.  TS203 then supplied the first concrete truncated Haar
transport theorem for Wall 0.

This sprint starts the major conditional-reduction phase by naming the three
final analytic input families that a future OTSA bridge may consume:

1. the triangle-spline Plancherel input;
2. an effective explicit-formula input for the triangle-spline weight;
3. a Gallagher / large-sieve comparison input adapted to the smoothing.

The sprint deliberately separates contract types from evidence types.  It does
not populate the effective explicit-formula or Gallagher contracts, does not
prove any OTSA input slot, and does not prove Goldbach.
-/

/-- Plancherel input contract for the triangle-spline package. -/
structure TriangleSplinePlancherelInputContract where
  /-- The Wall 1 Plancherel statement specialized to the triangle spline. -/
  plancherel_statement :
    Prop

  /-- The spectral energy transport obtained once Plancherel evidence is supplied. -/
  spectral_energy_transport_statement :
    Prop

/-- Evidence for a triangle-spline Plancherel input contract. -/
structure TriangleSplinePlancherelInputEvidence
    (contract : TriangleSplinePlancherelInputContract) where
  plancherel :
    contract.plancherel_statement

  spectral_energy_transport :
    contract.spectral_energy_transport_statement

/--
The concrete triangle-spline Plancherel input shape already stabilized by
TS174 and TS188.

The first field remains unproved.  The second field is a conditional transport
theorem already proved in TS188.
-/
noncomputable def triangleSplinePlancherelInputContract :
    TriangleSplinePlancherelInputContract where
  plancherel_statement :=
    TS174.Goldbach.TriangleSplinePlancherelIsometryStatement
  spectral_energy_transport_statement :=
    TS174.Goldbach.TriangleSplinePlancherelIsometryStatement ->
      TS174.Goldbach.triangleSplineSincL2Energy =
        ENNReal.ofReal (Real.sqrt (2 / 3))

/-- The conditional Plancherel-to-energy transport is already available from TS188. -/
theorem triangleSplinePlancherelEnergyTransport_available :
    triangleSplinePlancherelInputContract.spectral_energy_transport_statement := by
  exact TS188.Goldbach.sincL2Energy_of_wall1_plancherel_evidence

/--
Effective explicit-formula input contract for the triangle-spline weight.

These are final analytic obligations, not placeholders to be filled by `True`.
Future sprints must instantiate these fields with concrete statements involving
von Mangoldt sums, zero sums, residual terms, and effective constants.
-/
structure TriangleSplineExplicitFormulaEffectiveInputContract where
  explicit_formula_identity_statement :
    Prop

  main_term_identification_statement :
    Prop

  zero_contribution_bound_statement :
    Prop

  residual_bound_statement :
    Prop

  effective_constants_statement :
    Prop

  compatibility_with_ts181_blueprint_statement :
    Prop

/-- Evidence for the effective explicit-formula input contract. -/
structure TriangleSplineExplicitFormulaEffectiveInputEvidence
    (contract : TriangleSplineExplicitFormulaEffectiveInputContract) where
  explicit_formula_identity :
    contract.explicit_formula_identity_statement

  main_term_identification :
    contract.main_term_identification_statement

  zero_contribution_bound :
    contract.zero_contribution_bound_statement

  residual_bound :
    contract.residual_bound_statement

  effective_constants :
    contract.effective_constants_statement

  compatibility_with_ts181_blueprint :
    contract.compatibility_with_ts181_blueprint_statement

/--
Gallagher / large-sieve comparison input contract for the triangle-spline
smoothing.

These fields are the future Wall 4 obligations needed before an OTSA bridge may
turn trace and tail estimates into a two-prime correlation statement.
-/
structure TriangleSplineGallagherInputContract where
  variance_bound_statement :
    Prop

  smoothed_large_sieve_statement :
    Prop

  scale_transfer_statement :
    Prop

  effective_constants_statement :
    Prop

  correlation_to_otsa_statement :
    Prop

/-- Evidence for the Gallagher / large-sieve input contract. -/
structure TriangleSplineGallagherInputEvidence
    (contract : TriangleSplineGallagherInputContract) where
  variance_bound :
    contract.variance_bound_statement

  smoothed_large_sieve :
    contract.smoothed_large_sieve_statement

  scale_transfer :
    contract.scale_transfer_statement

  effective_constants :
    contract.effective_constants_statement

  correlation_to_otsa :
    contract.correlation_to_otsa_statement

/--
The three final analytic input contract families.

This structure intentionally contains no Goldbach conclusion.  It records only
the analytic inputs that may feed a future non-circular OTSA bridge.
-/
structure FinalTriangleSplineAnalyticInputContracts where
  plancherel :
    TriangleSplinePlancherelInputContract

  explicit_formula :
    TriangleSplineExplicitFormulaEffectiveInputContract

  gallagher :
    TriangleSplineGallagherInputContract

/-- Evidence for the final analytic input families. -/
structure FinalTriangleSplineAnalyticInputEvidence
    (contracts : FinalTriangleSplineAnalyticInputContracts) where
  plancherel :
    TriangleSplinePlancherelInputEvidence contracts.plancherel

  explicit_formula :
    TriangleSplineExplicitFormulaEffectiveInputEvidence contracts.explicit_formula

  gallagher :
    TriangleSplineGallagherInputEvidence contracts.gallagher

/-- Final analytic evidence exposes the Plancherel field, but does not prove it here. -/
theorem plancherel_statement_of_finalAnalyticEvidence
    (contracts : FinalTriangleSplineAnalyticInputContracts)
    (evidence : FinalTriangleSplineAnalyticInputEvidence contracts) :
    contracts.plancherel.plancherel_statement :=
  evidence.plancherel.plancherel

/-- Final analytic evidence exposes the effective explicit-formula identity. -/
theorem explicit_formula_identity_of_finalAnalyticEvidence
    (contracts : FinalTriangleSplineAnalyticInputContracts)
    (evidence : FinalTriangleSplineAnalyticInputEvidence contracts) :
    contracts.explicit_formula.explicit_formula_identity_statement :=
  evidence.explicit_formula.explicit_formula_identity

/-- Final analytic evidence exposes the Gallagher variance bound. -/
theorem gallagher_variance_bound_of_finalAnalyticEvidence
    (contracts : FinalTriangleSplineAnalyticInputContracts)
    (evidence : FinalTriangleSplineAnalyticInputEvidence contracts) :
    contracts.gallagher.variance_bound_statement :=
  evidence.gallagher.variance_bound

/--
Ledger recording the TS204 final analytic input specification.

The ledger references TS200 to certify non-circularity and TS203 to record that
the truncated Wall 0 Haar ingredient is already available.  It does not create
or populate the final analytic evidence.
-/
structure FinalAnalyticInputsSpecificationLedger where
  ts200_non_circular_interface :
    TS200.Goldbach.OTSANonCircularConsumptionLedger

  truncated_haar_transport_available :
    TS203.Goldbach.TruncatedHaarTransportStatement

  plancherel_contract_type_defined :
    True

  explicit_formula_contract_type_defined :
    True

  gallagher_contract_type_defined :
    True

  final_contract_bundle_defined :
    True

  final_evidence_bundle_defined :
    True

  plancherel_transport_conditional_available :
    triangleSplinePlancherelInputContract.spectral_energy_transport_statement

  otsa_input_slots_not_populated :
    True

  binary_goldbach_not_an_input :
    True

  explicit_formula_not_proved :
    True

  gallagher_not_proved :
    True

  plancherel_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS204 final analytic input specification ledger. -/
noncomputable def finalAnalyticInputsSpecificationLedger :
    FinalAnalyticInputsSpecificationLedger where
  ts200_non_circular_interface :=
    TS200.Goldbach.otsaNonCircularConsumptionLedger
  truncated_haar_transport_available :=
    TS203.Goldbach.truncatedHaarTransportStatement
  plancherel_contract_type_defined := True.intro
  explicit_formula_contract_type_defined := True.intro
  gallagher_contract_type_defined := True.intro
  final_contract_bundle_defined := True.intro
  final_evidence_bundle_defined := True.intro
  plancherel_transport_conditional_available :=
    triangleSplinePlancherelEnergyTransport_available
  otsa_input_slots_not_populated := True.intro
  binary_goldbach_not_an_input := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  plancherel_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS204. -/
def FinalAnalyticInputsSpecificationTarget : Prop :=
  Nonempty FinalAnalyticInputsSpecificationLedger

/-- The TS204 final analytic input specification target is populated. -/
theorem finalAnalyticInputsSpecificationTarget :
    FinalAnalyticInputsSpecificationTarget :=
  Nonempty.intro finalAnalyticInputsSpecificationLedger

end Goldbach
end TS204
