import TS.Goldbach.Strong.TS185.ExplicitFormulaZetaZeroFamilyLedger
import TS.Goldbach.Strong.TS255.FullyCorrectedExplicitFormulaAnalyticDecomposition

/-!
# TS256 - Riemann Zeta Zero Truncated Contribution

TS255 factored the fully corrected explicit-formula witness through named zero
and residual functions.  This sprint defines a concrete finite-sum shape for
the zero function without assuming RH or choosing a premature Mellin
normalization.

A TS185 zero-family API contract is paired with a scale-dependent finite set
that contains exactly the selected zeros below a stated height.  Multiplicity
comes from TS185 and the spectral summand remains a named parameter.  The real
part of the resulting finite complex sum supplies a TS255 zero function.

No zero-family API contract, finite truncation, spectral summand, reality
property, explicit-formula identity, or analytic bound is proved here.
-/

namespace TS256
namespace Goldbach

/-- Scale-dependent height used for a finite zero truncation. -/
def ZeroTruncationHeightFunction := Nat -> Real

/-- Spectral contribution of one zero at one natural scale. -/
def ZeroSpectralSummand := Nat -> Complex -> Complex

/--
Finite zero data at every scale for a fixed TS185 zeta-zero API contract.
Completeness is relative to the contract's selected zero set and height.
-/
structure RiemannZetaZeroTruncationData
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract) where
  height : ZeroTruncationHeightFunction
  zeros : Nat -> Finset Complex

  height_nonnegative :
    forall X : Nat,
      0 <= height X

  zeros_mem_zeroSet :
    forall (X : Nat) (rho : Complex),
      Membership.mem (zeros X) rho ->
        C.zeroSet rho

  zeros_height_bounded :
    forall (X : Nat) (rho : Complex),
      Membership.mem (zeros X) rho ->
        abs rho.im <= height X

  zeros_complete_below_height :
    forall (X : Nat) (rho : Complex),
      C.zeroSet rho ->
        abs rho.im <= height X ->
          Membership.mem (zeros X) rho

/-- Every listed element is a genuine nontrivial Riemann-zeta zero. -/
theorem truncation_mem_nontrivialRiemannZetaZero
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : RiemannZetaZeroTruncationData C)
    (X : Nat)
    (rho : Complex)
    (hMem : Membership.mem (truncation.zeros X) rho) :
    TS185.Goldbach.nontrivialRiemannZetaZeroPredicate rho := by
  unfold TS185.Goldbach.nontrivialRiemannZetaZeroPredicate
  exact
    And.intro
      (C.zeroSet_is_zeta_zero rho
        (truncation.zeros_mem_zeroSet X rho hMem))
      (C.zeroSet_in_critical_strip rho
        (truncation.zeros_mem_zeroSet X rho hMem))

/-- A truncation retains the TS93 family ledger supplied by its TS185 contract. -/
def ts93ZeroFamilyLedger_of_truncation
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (_truncation : RiemannZetaZeroTruncationData C) :
    TS93.Goldbach.ZetaZeroFamilyLedger :=
  TS185.Goldbach.zetaZeroFamilyLedger_of_apiContract C

/-- Finite complex sum over the selected zeros, counted with multiplicity. -/
noncomputable def zetaZeroTruncatedComplexSum
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : RiemannZetaZeroTruncationData C)
    (summand : ZeroSpectralSummand)
    (X : Nat) :
    Complex :=
  Finset.sum
    (truncation.zeros X)
    (fun rho => (C.multiplicity rho : Complex) * summand X rho)

/-- Real part of the finite complex zero sum. -/
noncomputable def zetaZeroTruncatedRealContribution
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : RiemannZetaZeroTruncationData C)
    (summand : ZeroSpectralSummand)
    (X : Nat) :
    Real :=
  (zetaZeroTruncatedComplexSum C truncation summand X).re

/-- The truncated contribution as the TS255 named zero function. -/
noncomputable def truncatedZeroContributionFunction
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : RiemannZetaZeroTruncationData C)
    (summand : ZeroSpectralSummand) :
    TS255.Goldbach.ZeroContributionFunction :=
  fun X => zetaZeroTruncatedRealContribution C truncation summand X

/-- Future conjugation-symmetry target for the finite complex sum. -/
def TruncatedZeroSumRealityStatement
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : RiemannZetaZeroTruncationData C)
    (summand : ZeroSpectralSummand) :
    Prop :=
  forall X : Nat,
    (zetaZeroTruncatedComplexSum C truncation summand X).im = 0

/-- Identification of a named TS255 zero function with this truncation. -/
def TruncatedZeroContributionIdentificationStatement
    (zeroFn : TS255.Goldbach.ZeroContributionFunction)
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : RiemannZetaZeroTruncationData C)
    (summand : ZeroSpectralSummand) :
    Prop :=
  zeroFn = truncatedZeroContributionFunction C truncation summand

/-- The canonical truncated function satisfies its identification target. -/
theorem truncatedZeroContributionFunction_identification
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : RiemannZetaZeroTruncationData C)
    (summand : ZeroSpectralSummand) :
    TruncatedZeroContributionIdentificationStatement
      (truncatedZeroContributionFunction C truncation summand)
      C
      truncation
      summand :=
  rfl

/--
Assemble TS255 decomposed obligations once the identity and both bounds have
been proved for the truncated zero function and a named residual function.
-/
noncomputable def decomposedObligations_of_truncatedZeroContribution
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : RiemannZetaZeroTruncationData C)
    (summand : ZeroSpectralSummand)
    (residualFn : TS255.Goldbach.ResidualTermFunction)
    (identity :
      TS255.Goldbach.NamedExplicitFormulaIdentityStatement
        K
        (truncatedZeroContributionFunction C truncation summand)
        residualFn)
    (zeroBound :
      TS255.Goldbach.NamedZeroContributionBoundStatement
        K
        (truncatedZeroContributionFunction C truncation summand)
        residualFn)
    (residualBound :
      TS255.Goldbach.NamedResidualBoundStatement
        K
        (truncatedZeroContributionFunction C truncation summand)
        residualFn) :
    TS255.Goldbach.DecomposedExplicitFormulaObligations K where
  zeroFn :=
    truncatedZeroContributionFunction C truncation summand
  residualFn :=
    residualFn
  explicit_formula_identity :=
    identity
  zero_contribution_bound :=
    zeroBound
  residual_bound :=
    residualBound

/--
The truncated zero contribution and the three named analytic proofs construct
the fully corrected TS253 core.
-/
noncomputable def fullyCorrectedCoreEvidence_of_truncatedZeroContribution
    (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : RiemannZetaZeroTruncationData C)
    (summand : ZeroSpectralSummand)
    (residualFn : TS255.Goldbach.ResidualTermFunction)
    (identity :
      TS255.Goldbach.NamedExplicitFormulaIdentityStatement
        K
        (truncatedZeroContributionFunction C truncation summand)
        residualFn)
    (zeroBound :
      TS255.Goldbach.NamedZeroContributionBoundStatement
        K
        (truncatedZeroContributionFunction C truncation summand)
        residualFn)
    (residualBound :
      TS255.Goldbach.NamedResidualBoundStatement
        K
        (truncatedZeroContributionFunction C truncation summand)
        residualFn) :
    TS253.Goldbach.FullyCorrectedExplicitFormulaCoreEvidence K :=
  TS255.Goldbach.fullyCorrectedCoreEvidence_of_decomposed
    K
    (decomposedObligations_of_truncatedZeroContribution
      K C truncation summand residualFn identity zeroBound residualBound)

/-- Ledger recording the finite zeta-zero contribution interface. -/
structure RiemannZetaZeroTruncatedContributionLedger where
  ts185_zero_api :
    TS185.Goldbach.ExplicitFormulaZetaZeroFamilyLedger

  ts255_analytic_decomposition :
    TS255.Goldbach.ExplicitFormulaAnalyticDecompositionLedger

  truncation_to_ts93_ledger :
    forall C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract,
      RiemannZetaZeroTruncationData C ->
        TS93.Goldbach.ZetaZeroFamilyLedger

  truncation_to_zero_function :
    forall C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract,
      RiemannZetaZeroTruncationData C ->
        ZeroSpectralSummand ->
          TS255.Goldbach.ZeroContributionFunction

  truncation_to_decomposed_obligations :
    forall
      (K : TS206.Goldbach.TriangleSplineExplicitFormulaConstants)
      (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
      (truncation : RiemannZetaZeroTruncationData C)
      (summand : ZeroSpectralSummand)
      (residualFn : TS255.Goldbach.ResidualTermFunction),
      TS255.Goldbach.NamedExplicitFormulaIdentityStatement
          K (truncatedZeroContributionFunction C truncation summand) residualFn ->
        TS255.Goldbach.NamedZeroContributionBoundStatement
            K (truncatedZeroContributionFunction C truncation summand) residualFn ->
          TS255.Goldbach.NamedResidualBoundStatement
              K (truncatedZeroContributionFunction C truncation summand) residualFn ->
            TS255.Goldbach.DecomposedExplicitFormulaObligations K

  zero_api_contract_not_constructed : True
  finite_truncation_not_constructed : True
  concrete_spectral_summand_not_defined : True
  truncated_sum_reality_not_proved : True
  named_identity_not_proved : True
  named_zero_bound_not_proved : True
  named_residual_function_not_constructed : True
  named_residual_bound_not_proved : True
  infinite_zero_sum_not_defined : True
  zero_density_estimate_not_proved : True
  riemann_hypothesis_not_claimed : True
  gallagher_evidence_not_proved : True
  final_analytic_to_otsa_bridge_not_proved : True
  otsa_conclusion_bridge_not_proved : True
  goldbach_not_claimed_unconditionally : True

/-- Concrete TS256 finite-zero contribution ledger. -/
noncomputable def riemannZetaZeroTruncatedContributionLedger :
    RiemannZetaZeroTruncatedContributionLedger where
  ts185_zero_api :=
    TS185.Goldbach.explicitFormulaZetaZeroFamilyLedger
  ts255_analytic_decomposition :=
    TS255.Goldbach.explicitFormulaAnalyticDecompositionLedger
  truncation_to_ts93_ledger :=
    ts93ZeroFamilyLedger_of_truncation
  truncation_to_zero_function :=
    truncatedZeroContributionFunction
  truncation_to_decomposed_obligations :=
    decomposedObligations_of_truncatedZeroContribution
  zero_api_contract_not_constructed := True.intro
  finite_truncation_not_constructed := True.intro
  concrete_spectral_summand_not_defined := True.intro
  truncated_sum_reality_not_proved := True.intro
  named_identity_not_proved := True.intro
  named_zero_bound_not_proved := True.intro
  named_residual_function_not_constructed := True.intro
  named_residual_bound_not_proved := True.intro
  infinite_zero_sum_not_defined := True.intro
  zero_density_estimate_not_proved := True.intro
  riemann_hypothesis_not_claimed := True.intro
  gallagher_evidence_not_proved := True.intro
  final_analytic_to_otsa_bridge_not_proved := True.intro
  otsa_conclusion_bridge_not_proved := True.intro
  goldbach_not_claimed_unconditionally := True.intro

/-- Target proposition for TS256. -/
def RiemannZetaZeroTruncatedContributionTarget : Prop :=
  Nonempty RiemannZetaZeroTruncatedContributionLedger

/-- TS256 target: a finite zeta-zero contribution interface is installed. -/
theorem riemannZetaZeroTruncatedContributionTarget :
    RiemannZetaZeroTruncatedContributionTarget :=
  Nonempty.intro riemannZetaZeroTruncatedContributionLedger

end Goldbach
end TS256
