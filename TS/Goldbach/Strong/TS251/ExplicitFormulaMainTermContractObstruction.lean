import TS.Goldbach.Strong.TS250.ExplicitFormulaStructuralCompatibilityDischarge

/-!
# TS251 - Explicit Formula Main-Term Contract Obstruction

TS250 reduced the current TS206 evidence package to four analytic fields.  This
sprint audits the quantifiers in the main-term field before attempting to prove
it.

The TS206 identity constrains only

```text
leftSide = mainTerm - zeroContribution + residualTerm.
```

For any proposed main-term model, one may increase `mainTerm` by one and choose
`zeroContribution` so that the identity still holds.  Therefore the current
universal main-term identification field is false whenever the lower scale is
positive, in particular for every TS206-admissible constants package.

TS251 records the obstruction and defines a corrected core target in which the
identity and main-term identification belong to the same existential witness.
No explicit formula or analytic bound is proved here.
-/

namespace TS251
namespace Goldbach

/--
Counterexample data with a shifted main term.  The zero contribution is chosen
so that the TS206 identity remains true.
-/
noncomputable def shiftedMainTermData
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (X : Nat) :
    TS206.Goldbach.TriangleSplineExplicitFormulaData X where
  mainTerm :=
    K.mainTermModel X + 1
  zeroContribution :=
    K.mainTermModel X + 1 -
      TS206.Goldbach.triangleSplineExplicitFormulaLeftSide X
  residualTerm :=
    0

/-- The shifted data satisfies the current TS206 explicit-formula identity. -/
theorem shiftedMainTermData_identity
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (X : Nat) :
    TS206.Goldbach.triangleSplineExplicitFormulaIdentity
      X
      (shiftedMainTermData K X) := by
  unfold TS206.Goldbach.triangleSplineExplicitFormulaIdentity
  simp [shiftedMainTermData]

/--
The current universal main-term identification statement is impossible at any
positive lower scale.
-/
theorem mainTermIdentificationStatement_not_provable
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (hLowerScale : 0 < K.lowerScale) :
    Not
      ((TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K)
        |>.main_term_identification_statement) := by
  intro hMainTerm
  have hShifted :=
    hMainTerm
      K.lowerScale
      hLowerScale
      (le_refl K.lowerScale)
      (shiftedMainTermData K K.lowerScale)
      (shiftedMainTermData_identity K K.lowerScale)
  unfold TS206.Goldbach.triangleSplineExplicitFormulaMainTermIdentification at hShifted
  simp [shiftedMainTermData] at hShifted

/--
Consequently, the TS249 four-field core evidence is uninhabited for every
TS206-admissible constants package.
-/
theorem coreEvidence_not_nonempty
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (hAdmissible :
      TS206.Goldbach.triangleSplineExplicitFormulaConstantsAdmissible K) :
    Not (Nonempty (TS249.Goldbach.TriangleSplineExplicitFormulaCoreEvidence K)) := by
  intro hCore
  cases hCore with
  | intro core =>
      exact
        (mainTermIdentificationStatement_not_provable K hAdmissible.2.2)
          core.main_term_identification

/--
Corrected identity target: the data witness must satisfy both the explicit
formula identity and the selected main-term model.
-/
def ExplicitFormulaIdentityWithMainTermStatement
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants) :
    Prop :=
  forall X : Nat,
    0 < X ->
      K.lowerScale <= X ->
        exists D : TS206.Goldbach.TriangleSplineExplicitFormulaData X,
          TS206.Goldbach.triangleSplineExplicitFormulaIdentity X D /\
            TS206.Goldbach.triangleSplineExplicitFormulaMainTermIdentification
              K X D

/--
Corrected analytic core.  Main-term identification is attached to the data
selected by the identity instead of being required for every possible
decomposition of the same scalar left side.
-/
structure CorrectedTriangleSplineExplicitFormulaCoreEvidence
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants) where
  identity_with_main_term :
    ExplicitFormulaIdentityWithMainTermStatement K

  zero_contribution_bound :
    (TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K)
      |>.zero_contribution_bound_statement

  residual_bound :
    (TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K)
      |>.residual_bound_statement

/-- Ledger recording the TS206 main-term contract obstruction. -/
structure ExplicitFormulaMainTermContractObstructionLedger where
  ts250_structural_compatibility :
    TS250.Goldbach.ExplicitFormulaStructuralCompatibilityDischargeLedger

  shifted_identity_counterexample :
    forall
      (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
      (X : Nat),
        TS206.Goldbach.triangleSplineExplicitFormulaIdentity
          X
          (shiftedMainTermData K X)

  current_main_term_contract_impossible :
    forall
      (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants),
        TS206.Goldbach.triangleSplineExplicitFormulaConstantsAdmissible K ->
          Not
            ((TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K)
              |>.main_term_identification_statement)

  current_core_evidence_uninhabited :
    forall
      (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants),
        TS206.Goldbach.triangleSplineExplicitFormulaConstantsAdmissible K ->
          Not
            (Nonempty
              (TS249.Goldbach.TriangleSplineExplicitFormulaCoreEvidence K))

  corrected_identity_statement_defined : True
  corrected_core_evidence_type_defined : True

  corrected_ts206_contract_not_yet_installed : True
  explicit_formula_identity_not_proved : True
  main_term_identification_not_proved : True
  zero_contribution_bound_not_proved : True
  residual_bound_not_proved : True
  gallagher_evidence_not_proved : True
  final_analytic_to_otsa_bridge_not_proved : True
  otsa_conclusion_bridge_not_proved : True
  goldbach_not_claimed_unconditionally : True

/-- Concrete TS251 obstruction ledger. -/
noncomputable def explicitFormulaMainTermContractObstructionLedger :
    ExplicitFormulaMainTermContractObstructionLedger where
  ts250_structural_compatibility :=
    TS250.Goldbach.explicitFormulaStructuralCompatibilityDischargeLedger
  shifted_identity_counterexample :=
    shiftedMainTermData_identity
  current_main_term_contract_impossible :=
    fun K hAdmissible =>
      mainTermIdentificationStatement_not_provable K hAdmissible.2.2
  current_core_evidence_uninhabited :=
    coreEvidence_not_nonempty
  corrected_identity_statement_defined := True.intro
  corrected_core_evidence_type_defined := True.intro
  corrected_ts206_contract_not_yet_installed := True.intro
  explicit_formula_identity_not_proved := True.intro
  main_term_identification_not_proved := True.intro
  zero_contribution_bound_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_evidence_not_proved := True.intro
  final_analytic_to_otsa_bridge_not_proved := True.intro
  otsa_conclusion_bridge_not_proved := True.intro
  goldbach_not_claimed_unconditionally := True.intro

/-- Target proposition for TS251. -/
def ExplicitFormulaMainTermContractObstructionTarget : Prop :=
  Nonempty ExplicitFormulaMainTermContractObstructionLedger

/-- TS251 target: the current main-term contract obstruction is proved. -/
theorem explicitFormulaMainTermContractObstructionTarget :
    ExplicitFormulaMainTermContractObstructionTarget :=
  Nonempty.intro explicitFormulaMainTermContractObstructionLedger

end Goldbach
end TS251
