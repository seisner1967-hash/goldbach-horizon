import TS.Goldbach.Strong.TS254.FullyCorrectedExplicitFormulaContractInstallation

/-!
# TS255 - Fully Corrected Explicit Formula Analytic Decomposition

TS254 installed a contract requiring one data witness to satisfy the explicit
formula identity, main-term identification, and both analytic bounds.  This
sprint factors that monolithic obligation through two named real functions of
the scale.

The main term is fixed definitionally by the constants package.  The named
zero and residual functions then determine a canonical explicit-formula data
witness.  Three concrete propositions, expressed with the existing TS206
predicates, require the identity and the two bounds for that same witness.

The assembly theorem is proved here.  The named functions, their analytic
identity, and their bounds are not constructed or proved in this sprint.
-/

namespace TS255
namespace Goldbach

/-- A named zero-contribution function of the natural scale. -/
def ZeroContributionFunction := Nat -> Real

/-- A named residual-term function of the natural scale. -/
def ResidualTermFunction := Nat -> Real

/--
Canonical explicit-formula data determined by a constants package and the two
named analytic functions.
-/
noncomputable def decomposedExplicitFormulaData
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (zeroFn : ZeroContributionFunction)
    (residualFn : ResidualTermFunction)
    (X : Nat) :
    TS206.Goldbach.TriangleSplineExplicitFormulaData X where
  mainTerm :=
    K.mainTermModel X
  zeroContribution :=
    zeroFn X
  residualTerm :=
    residualFn X

/-- The canonical data uses the selected main-term model definitionally. -/
theorem decomposedExplicitFormulaData_mainTerm
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (zeroFn : ZeroContributionFunction)
    (residualFn : ResidualTermFunction)
    (X : Nat) :
    TS206.Goldbach.triangleSplineExplicitFormulaMainTermIdentification
      K
      X
      (decomposedExplicitFormulaData K zeroFn residualFn X) :=
  rfl

/-- Explicit-formula identity for the canonical named data. -/
def NamedExplicitFormulaIdentityStatement
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (zeroFn : ZeroContributionFunction)
    (residualFn : ResidualTermFunction) :
    Prop :=
  forall X : Nat,
    0 < X ->
      K.lowerScale <= X ->
        TS206.Goldbach.triangleSplineExplicitFormulaIdentity
          X
          (decomposedExplicitFormulaData K zeroFn residualFn X)

/-- Zero-contribution bound for the same canonical named data. -/
def NamedZeroContributionBoundStatement
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (zeroFn : ZeroContributionFunction)
    (residualFn : ResidualTermFunction) :
    Prop :=
  forall X : Nat,
    0 < X ->
      K.lowerScale <= X ->
        TS206.Goldbach.triangleSplineExplicitFormulaZeroContributionBound
          K
          X
          (decomposedExplicitFormulaData K zeroFn residualFn X)

/-- Residual bound for the same canonical named data. -/
def NamedResidualBoundStatement
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (zeroFn : ZeroContributionFunction)
    (residualFn : ResidualTermFunction) :
    Prop :=
  forall X : Nat,
    0 < X ->
      K.lowerScale <= X ->
        TS206.Goldbach.triangleSplineExplicitFormulaResidualBound
          K
          X
          (decomposedExplicitFormulaData K zeroFn residualFn X)

/--
Named analytic obligations sufficient for the fully corrected TS253 core.
Every statement refers to the same two functions and canonical data witness.
-/
structure DecomposedExplicitFormulaObligations
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants) where
  zeroFn : ZeroContributionFunction
  residualFn : ResidualTermFunction
  explicit_formula_identity :
    NamedExplicitFormulaIdentityStatement K zeroFn residualFn
  zero_contribution_bound :
    NamedZeroContributionBoundStatement K zeroFn residualFn
  residual_bound :
    NamedResidualBoundStatement K zeroFn residualFn

/--
The named decomposition constructs the fully corrected single-witness core.
-/
noncomputable def fullyCorrectedCoreEvidence_of_decomposed
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (decomposed : DecomposedExplicitFormulaObligations K) :
    TS253.Goldbach.FullyCorrectedExplicitFormulaCoreEvidence K where
  formula_with_main_term_and_bounds := by
    intro X hX hScale
    refine
      Exists.intro
        (decomposedExplicitFormulaData
          K decomposed.zeroFn decomposed.residualFn X) ?_
    refine And.intro (decomposed.explicit_formula_identity X hX hScale) ?_
    refine
      And.intro
        (decomposedExplicitFormulaData_mainTerm
          K decomposed.zeroFn decomposed.residualFn X) ?_
    refine And.intro (decomposed.zero_contribution_bound X hX hScale) ?_
    exact decomposed.residual_bound X hX hScale

/--
The named decomposition, admissible constants, and TS181 compatibility build
fully corrected TS254 explicit-formula evidence.
-/
noncomputable def fullyCorrectedExplicitFormulaEvidence_of_decomposed
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (constantsAdmissible :
      TS206.Goldbach.triangleSplineExplicitFormulaConstantsAdmissible K)
    (decomposed : DecomposedExplicitFormulaObligations K)
    (compatibility :
      TS206.Goldbach.TriangleSplineExplicitFormulaTS181CompatibilityStatement) :
    TS254.Goldbach.FullyCorrectedExplicitFormulaEffectiveEvidence K :=
  TS254.Goldbach.fullyCorrectedExplicitFormulaEvidence_of_core
    K
    constantsAdmissible
    (fullyCorrectedCoreEvidence_of_decomposed K decomposed)
    compatibility

/--
Specialized evidence constructor with TS249 admissibility and TS250 structural
compatibility already populated.
-/
noncomputable def fullyCorrectedExplicitFormulaEvidence_of_specializedDecomposed
    (mainTermModel : Nat -> Real)
    (zeroConstant residualConstant : NNReal)
    (zeroScalePower zeroLogPower residualScalePower residualLogPower : Nat)
    (lowerScaleOffset : Nat)
    (decomposed :
      DecomposedExplicitFormulaObligations
        (TS249.Goldbach.admissibleExplicitFormulaConstants
          mainTermModel
          zeroConstant
          residualConstant
          zeroScalePower
          zeroLogPower
          residualScalePower
          residualLogPower
          lowerScaleOffset)) :
    TS254.Goldbach.FullyCorrectedExplicitFormulaEffectiveEvidence
      (TS249.Goldbach.admissibleExplicitFormulaConstants
        mainTermModel
        zeroConstant
        residualConstant
        zeroScalePower
        zeroLogPower
        residualScalePower
        residualLogPower
        lowerScaleOffset) :=
  fullyCorrectedExplicitFormulaEvidence_of_decomposed
    (TS249.Goldbach.admissibleExplicitFormulaConstants
      mainTermModel
      zeroConstant
      residualConstant
      zeroScalePower
      zeroLogPower
      residualScalePower
      residualLogPower
      lowerScaleOffset)
    (TS249.Goldbach.admissibleExplicitFormulaConstants_admissible
      mainTermModel
      zeroConstant
      residualConstant
      zeroScalePower
      zeroLogPower
      residualScalePower
      residualLogPower
      lowerScaleOffset)
    decomposed
    TS250.Goldbach.structuralExplicitFormulaTS181Compatibility

/-- Ledger recording the real analytic decomposition and its assembly routes. -/
structure ExplicitFormulaAnalyticDecompositionLedger where
  ts254_contract_installation :
    TS254.Goldbach.FullyCorrectedExplicitFormulaContractInstallationLedger

  decomposition_supplies_core :
    forall K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants,
      DecomposedExplicitFormulaObligations K ->
        TS253.Goldbach.FullyCorrectedExplicitFormulaCoreEvidence K

  decomposition_supplies_effective_evidence :
    forall K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants,
      TS206.Goldbach.triangleSplineExplicitFormulaConstantsAdmissible K ->
        DecomposedExplicitFormulaObligations K ->
          TS206.Goldbach.TriangleSplineExplicitFormulaTS181CompatibilityStatement ->
            TS254.Goldbach.FullyCorrectedExplicitFormulaEffectiveEvidence K

  named_function_types_defined : True
  canonical_data_constructor_defined : True
  named_obligation_types_defined : True

  named_zero_function_not_constructed : True
  named_residual_function_not_constructed : True
  named_identity_not_proved : True
  named_zero_bound_not_proved : True
  named_residual_bound_not_proved : True
  actual_zeta_zero_family_not_constructed : True
  contour_residual_decomposition_not_constructed : True
  gallagher_evidence_not_proved : True
  final_analytic_to_otsa_bridge_not_proved : True
  otsa_conclusion_bridge_not_proved : True
  goldbach_not_claimed_unconditionally : True

/-- Concrete TS255 analytic-decomposition ledger. -/
noncomputable def explicitFormulaAnalyticDecompositionLedger :
    ExplicitFormulaAnalyticDecompositionLedger where
  ts254_contract_installation :=
    TS254.Goldbach.fullyCorrectedExplicitFormulaContractInstallationLedger
  decomposition_supplies_core :=
    fullyCorrectedCoreEvidence_of_decomposed
  decomposition_supplies_effective_evidence :=
    fullyCorrectedExplicitFormulaEvidence_of_decomposed
  named_function_types_defined := True.intro
  canonical_data_constructor_defined := True.intro
  named_obligation_types_defined := True.intro
  named_zero_function_not_constructed := True.intro
  named_residual_function_not_constructed := True.intro
  named_identity_not_proved := True.intro
  named_zero_bound_not_proved := True.intro
  named_residual_bound_not_proved := True.intro
  actual_zeta_zero_family_not_constructed := True.intro
  contour_residual_decomposition_not_constructed := True.intro
  gallagher_evidence_not_proved := True.intro
  final_analytic_to_otsa_bridge_not_proved := True.intro
  otsa_conclusion_bridge_not_proved := True.intro
  goldbach_not_claimed_unconditionally := True.intro

/-- Target proposition for TS255. -/
def ExplicitFormulaAnalyticDecompositionTarget : Prop :=
  Nonempty ExplicitFormulaAnalyticDecompositionLedger

/-- TS255 target: the monolithic analytic witness is factored and assembled. -/
theorem explicitFormulaAnalyticDecompositionTarget :
    ExplicitFormulaAnalyticDecompositionTarget :=
  Nonempty.intro explicitFormulaAnalyticDecompositionLedger

end Goldbach
end TS255
