import TS.Goldbach.Strong.TS252.CorrectedExplicitFormulaContractInstallation

/-!
# TS253 - Explicit Formula Bounds Contract Obstruction

TS252 corrected the identity and main-term quantifiers but retained the TS206
universal zero and residual bound statements.  This sprint audits those two
fields before analytic work begins.

At a fixed scale, identity plus main-term identification still leaves one free
real parameter among `zeroContribution` and `residualTerm`.  TS253 chooses that
parameter to be the absolute value of the proposed majorant plus one, then
adjusts the other component to preserve the identity.  Each universal bound is
therefore false at every positive lower scale.

TS253 defines a fully corrected statement in which identity, main term, and
both bounds belong to the same existential data witness.
-/

namespace TS253
namespace Goldbach

/-- Scalar majorant used by the TS206 zero-contribution bound. -/
noncomputable def zeroContributionMajorant
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (X : Nat) :
    Real :=
  K.zeroConstant *
    ((X : Real) ^ K.zeroScalePower) *
      ((Real.log (X : Real)) ^ K.zeroLogPower)

/-- Scalar majorant used by the TS206 residual bound. -/
noncomputable def residualMajorant
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (X : Nat) :
    Real :=
  K.residualConstant *
    ((X : Real) ^ K.residualScalePower) *
      ((Real.log (X : Real)) ^ K.residualLogPower)

/--
Data satisfying identity and the main-term model while violating the proposed
zero-contribution majorant.
-/
noncomputable def zeroBoundCounterexampleData
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (X : Nat) :
    TS206.Goldbach.TriangleSplineExplicitFormulaData X where
  mainTerm :=
    K.mainTermModel X
  zeroContribution :=
    abs (zeroContributionMajorant K X) + 1
  residualTerm :=
    TS206.Goldbach.triangleSplineExplicitFormulaLeftSide X -
      K.mainTermModel X +
        (abs (zeroContributionMajorant K X) + 1)

/-- The zero-bound counterexample still satisfies the explicit-formula identity. -/
theorem zeroBoundCounterexampleData_identity
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (X : Nat) :
    TS206.Goldbach.triangleSplineExplicitFormulaIdentity
      X
      (zeroBoundCounterexampleData K X) := by
  unfold TS206.Goldbach.triangleSplineExplicitFormulaIdentity
  simp [zeroBoundCounterexampleData]

/-- The zero-bound counterexample uses the selected main-term model. -/
theorem zeroBoundCounterexampleData_mainTerm
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (X : Nat) :
    TS206.Goldbach.triangleSplineExplicitFormulaMainTermIdentification
      K
      X
      (zeroBoundCounterexampleData K X) :=
  rfl

/-- The zero-bound counterexample exceeds the proposed majorant. -/
theorem zeroBoundCounterexampleData_not_bound
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (X : Nat) :
    Not
      (TS206.Goldbach.triangleSplineExplicitFormulaZeroContributionBound
        K
        X
        (zeroBoundCounterexampleData K X)) := by
  change
    Not
      (abs (abs (zeroContributionMajorant K X) + 1) <=
        zeroContributionMajorant K X)
  intro hBound
  have hNonneg : 0 <= abs (zeroContributionMajorant K X) + 1 := by
    positivity
  rw [abs_of_nonneg hNonneg] at hBound
  have hMajorantLeAbs :
      zeroContributionMajorant K X <= abs (zeroContributionMajorant K X) :=
    le_abs_self (zeroContributionMajorant K X)
  linarith

/--
Data satisfying identity and the main-term model while violating the proposed
residual majorant.
-/
noncomputable def residualBoundCounterexampleData
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (X : Nat) :
    TS206.Goldbach.TriangleSplineExplicitFormulaData X where
  mainTerm :=
    K.mainTermModel X
  zeroContribution :=
    K.mainTermModel X +
      (abs (residualMajorant K X) + 1) -
        TS206.Goldbach.triangleSplineExplicitFormulaLeftSide X
  residualTerm :=
    abs (residualMajorant K X) + 1

/-- The residual-bound counterexample still satisfies the identity. -/
theorem residualBoundCounterexampleData_identity
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (X : Nat) :
    TS206.Goldbach.triangleSplineExplicitFormulaIdentity
      X
      (residualBoundCounterexampleData K X) := by
  unfold TS206.Goldbach.triangleSplineExplicitFormulaIdentity
  simp [residualBoundCounterexampleData]
  ring

/-- The residual-bound counterexample uses the selected main-term model. -/
theorem residualBoundCounterexampleData_mainTerm
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (X : Nat) :
    TS206.Goldbach.triangleSplineExplicitFormulaMainTermIdentification
      K
      X
      (residualBoundCounterexampleData K X) :=
  rfl

/-- The residual-bound counterexample exceeds the proposed majorant. -/
theorem residualBoundCounterexampleData_not_bound
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (X : Nat) :
    Not
      (TS206.Goldbach.triangleSplineExplicitFormulaResidualBound
        K
        X
        (residualBoundCounterexampleData K X)) := by
  change
    Not
      (abs (abs (residualMajorant K X) + 1) <=
        residualMajorant K X)
  intro hBound
  have hNonneg : 0 <= abs (residualMajorant K X) + 1 := by
    positivity
  rw [abs_of_nonneg hNonneg] at hBound
  have hMajorantLeAbs :
      residualMajorant K X <= abs (residualMajorant K X) :=
    le_abs_self (residualMajorant K X)
  linarith

/-- The current universal zero-contribution statement is impossible. -/
theorem zeroContributionBoundStatement_not_provable
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (hLowerScale : 0 < K.lowerScale) :
    Not
      ((TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K)
        |>.zero_contribution_bound_statement) := by
  intro hZeroBound
  have hAtLowerScale :=
    hZeroBound
      K.lowerScale
      hLowerScale
      (le_refl K.lowerScale)
      (zeroBoundCounterexampleData K K.lowerScale)
      (zeroBoundCounterexampleData_identity K K.lowerScale)
      (zeroBoundCounterexampleData_mainTerm K K.lowerScale)
  exact (zeroBoundCounterexampleData_not_bound K K.lowerScale) hAtLowerScale

/-- The current universal residual statement is impossible. -/
theorem residualBoundStatement_not_provable
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (hLowerScale : 0 < K.lowerScale) :
    Not
      ((TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K)
        |>.residual_bound_statement) := by
  intro hResidualBound
  have hAtLowerScale :=
    hResidualBound
      K.lowerScale
      hLowerScale
      (le_refl K.lowerScale)
      (residualBoundCounterexampleData K K.lowerScale)
      (residualBoundCounterexampleData_identity K K.lowerScale)
      (residualBoundCounterexampleData_mainTerm K K.lowerScale)
  exact (residualBoundCounterexampleData_not_bound K K.lowerScale) hAtLowerScale

/-- The TS251 corrected core remains uninhabited under the retained bounds. -/
theorem correctedCoreEvidence_not_nonempty
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (hLowerScale : 0 < K.lowerScale) :
    Not
      (Nonempty
        (TS251.Goldbach.CorrectedTriangleSplineExplicitFormulaCoreEvidence K)) := by
  intro hCore
  cases hCore with
  | intro core =>
      exact
        (zeroContributionBoundStatement_not_provable K hLowerScale)
          core.zero_contribution_bound

/-- The TS252 corrected evidence is also uninhabited for admissible constants. -/
theorem correctedExplicitFormulaEvidence_not_nonempty
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (hAdmissible :
      TS206.Goldbach.triangleSplineExplicitFormulaConstantsAdmissible K) :
    Not (Nonempty (TS252.Goldbach.CorrectedExplicitFormulaEffectiveEvidence K)) := by
  intro hEvidence
  cases hEvidence with
  | intro evidence =>
      exact
        (zeroContributionBoundStatement_not_provable K hAdmissible.2.2)
          evidence.zero_contribution_bound

/--
Fully corrected target: all four analytic properties belong to the same data
witness at each admissible scale.
-/
def FullyCorrectedExplicitFormulaStatement
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants) :
    Prop :=
  forall X : Nat,
    0 < X ->
      K.lowerScale <= X ->
        exists D : TS206.Goldbach.TriangleSplineExplicitFormulaData X,
          TS206.Goldbach.triangleSplineExplicitFormulaIdentity X D /\
            TS206.Goldbach.triangleSplineExplicitFormulaMainTermIdentification
              K X D /\
              TS206.Goldbach.triangleSplineExplicitFormulaZeroContributionBound
                K X D /\
                TS206.Goldbach.triangleSplineExplicitFormulaResidualBound K X D

/-- Evidence wrapper for the fully corrected analytic target. -/
structure FullyCorrectedExplicitFormulaCoreEvidence
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants) where
  formula_with_main_term_and_bounds :
    FullyCorrectedExplicitFormulaStatement K

/-- Ledger recording both retained-bound obstructions. -/
structure ExplicitFormulaBoundsContractObstructionLedger where
  ts252_corrected_contract :
    TS252.Goldbach.CorrectedExplicitFormulaContractInstallationLedger

  zero_bound_contract_impossible :
    forall K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants,
      0 < K.lowerScale ->
        Not
          ((TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K)
            |>.zero_contribution_bound_statement)

  residual_bound_contract_impossible :
    forall K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants,
      0 < K.lowerScale ->
        Not
          ((TS206.Goldbach.triangleSplineExplicitFormulaEffectiveContract K)
            |>.residual_bound_statement)

  ts252_corrected_evidence_uninhabited :
    forall K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants,
      TS206.Goldbach.triangleSplineExplicitFormulaConstantsAdmissible K ->
        Not
          (Nonempty
            (TS252.Goldbach.CorrectedExplicitFormulaEffectiveEvidence K))

  fully_corrected_statement_defined : True
  fully_corrected_core_type_defined : True

  fully_corrected_contract_not_yet_installed : True
  fully_corrected_formula_not_proved : True
  actual_zeta_zero_family_not_constructed : True
  gallagher_evidence_not_proved : True
  final_analytic_to_otsa_bridge_not_proved : True
  otsa_conclusion_bridge_not_proved : True
  goldbach_not_claimed_unconditionally : True

/-- Concrete TS253 bounds-obstruction ledger. -/
noncomputable def explicitFormulaBoundsContractObstructionLedger :
    ExplicitFormulaBoundsContractObstructionLedger where
  ts252_corrected_contract :=
    TS252.Goldbach.correctedExplicitFormulaContractInstallationLedger
  zero_bound_contract_impossible :=
    zeroContributionBoundStatement_not_provable
  residual_bound_contract_impossible :=
    residualBoundStatement_not_provable
  ts252_corrected_evidence_uninhabited :=
    correctedExplicitFormulaEvidence_not_nonempty
  fully_corrected_statement_defined := True.intro
  fully_corrected_core_type_defined := True.intro
  fully_corrected_contract_not_yet_installed := True.intro
  fully_corrected_formula_not_proved := True.intro
  actual_zeta_zero_family_not_constructed := True.intro
  gallagher_evidence_not_proved := True.intro
  final_analytic_to_otsa_bridge_not_proved := True.intro
  otsa_conclusion_bridge_not_proved := True.intro
  goldbach_not_claimed_unconditionally := True.intro

/-- Target proposition for TS253. -/
def ExplicitFormulaBoundsContractObstructionTarget : Prop :=
  Nonempty ExplicitFormulaBoundsContractObstructionLedger

/-- TS253 target: both retained universal bounds are proved impossible. -/
theorem explicitFormulaBoundsContractObstructionTarget :
    ExplicitFormulaBoundsContractObstructionTarget :=
  Nonempty.intro explicitFormulaBoundsContractObstructionLedger

end Goldbach
end TS253
