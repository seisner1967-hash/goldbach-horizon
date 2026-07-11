import Mathlib.Tactic
import TS.Goldbach.Strong.TS258.ZeroSummandConjugationFiniteReality

/-!
# TS259 - Zero Multiplicity Conjugation Extension

TS258 proved finite zero-sum reality under one explicit premise: multiplicity
is invariant under complex conjugation.  The historical TS185 contract does not
carry that premise.

This sprint installs a parallel wrapper containing a base TS185 contract and
exactly the missing multiplicity proof.  TS185 is not modified.  Once such a
wrapper is supplied, the TS258 reality and lossless-projection results no
longer require a separate premise at each use.

No concrete zero family, multiplicity realization, explicit-formula identity,
analytic bound, or Goldbach statement is proved here.
-/

namespace TS259
namespace Goldbach

/-- A TS185 zero-family contract enriched by conjugate multiplicities. -/
structure RiemannZetaZeroFamilyMultiplicityConjugationContract where
  base : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract

  multiplicity_conjugate :
    TS258.Goldbach.ZeroMultiplicityConjugationInvariantStatement base

namespace RiemannZetaZeroFamilyMultiplicityConjugationContract

/-- Build the extension from a base TS185 contract and the missing proof. -/
def ofBase
    (base : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (hMultiplicity :
      TS258.Goldbach.ZeroMultiplicityConjugationInvariantStatement base) :
    RiemannZetaZeroFamilyMultiplicityConjugationContract where
  base := base
  multiplicity_conjugate := hMultiplicity

/-- Forget the additional multiplicity proof and recover the TS185 contract. -/
def toTS185
    (C : RiemannZetaZeroFamilyMultiplicityConjugationContract) :
    TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract :=
  C.base

end RiemannZetaZeroFamilyMultiplicityConjugationContract

/-- Every enriched contract supplies the exact TS258 premise. -/
theorem extendedContract_multiplicityConjugation
    (C : RiemannZetaZeroFamilyMultiplicityConjugationContract) :
    TS258.Goldbach.ZeroMultiplicityConjugationInvariantStatement C.base :=
  C.multiplicity_conjugate

/-- TS256 truncation data over the base contract of an enriched package. -/
abbrev RiemannZetaZeroMultiplicityConjugationTruncationData
    (C : RiemannZetaZeroFamilyMultiplicityConjugationContract) :=
  TS256.Goldbach.RiemannZetaZeroTruncationData C.base

/-- The finite complex sum is fixed by conjugation for an enriched package. -/
theorem extendedTruncation_complexSum_star
    (C : RiemannZetaZeroFamilyMultiplicityConjugationContract)
    (truncation : RiemannZetaZeroMultiplicityConjugationTruncationData C)
    (X : Nat) :
    star
        (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
          C.base truncation X) =
      TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
        C.base truncation X :=
  TS258.Goldbach.triangleSplineZeroTruncatedComplexSum_star
    C.base truncation C.multiplicity_conjugate X

/-- The finite complex sum has zero imaginary part. -/
theorem extendedTruncation_complexSum_im_eq_zero
    (C : RiemannZetaZeroFamilyMultiplicityConjugationContract)
    (truncation : RiemannZetaZeroMultiplicityConjugationTruncationData C)
    (X : Nat) :
    (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
      C.base truncation X).im = 0 :=
  TS258.Goldbach.triangleSplineZeroTruncatedComplexSum_im_eq_zero
    C.base truncation C.multiplicity_conjugate X

/-- The TS256 finite-sum reality target follows from the enriched package. -/
theorem extendedTruncation_zeroSumReality
    (C : RiemannZetaZeroFamilyMultiplicityConjugationContract)
    (truncation : RiemannZetaZeroMultiplicityConjugationTruncationData C) :
    TS256.Goldbach.TruncatedZeroSumRealityStatement
      C.base truncation TS257.Goldbach.triangleSplineZeroSpectralSummand :=
  TS258.Goldbach.truncatedZeroSumReality_of_multiplicity_conjugation
    C.base truncation C.multiplicity_conjugate

/-- The complex sum equals the embedding of its real part. -/
theorem extendedTruncation_complexSum_eq_ofReal_re
    (C : RiemannZetaZeroFamilyMultiplicityConjugationContract)
    (truncation : RiemannZetaZeroMultiplicityConjugationTruncationData C)
    (X : Nat) :
    TS257.Goldbach.triangleSplineZeroTruncatedComplexSum C.base truncation X =
      ((TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
        C.base truncation X).re : Complex) :=
  TS258.Goldbach.triangleSplineZeroTruncatedComplexSum_eq_ofReal_re
    C.base truncation C.multiplicity_conjugate X

/-- The TS255 real projection recovers the complete finite complex sum. -/
theorem extendedTruncation_realProjectionLossless
    (C : RiemannZetaZeroFamilyMultiplicityConjugationContract)
    (truncation : RiemannZetaZeroMultiplicityConjugationTruncationData C)
    (X : Nat) :
    ((TS257.Goldbach.triangleSplineZeroContributionFunction
      C.base truncation X : Real) : Complex) =
      TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
        C.base truncation X :=
  TS258.Goldbach.triangleSplineZeroContributionFunction_coe_eq_complexSum
    C.base truncation C.multiplicity_conjugate X

/-- Real absolute value transports exactly to the complex spectral modulus. -/
theorem extendedTruncation_realAbs_eq_complexAbs
    (C : RiemannZetaZeroFamilyMultiplicityConjugationContract)
    (truncation : RiemannZetaZeroMultiplicityConjugationTruncationData C)
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          C.base truncation X) =
      Complex.abs
        (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
          C.base truncation X) := by
  have hAbs :=
    congrArg Complex.abs
      (extendedTruncation_realProjectionLossless C truncation X)
  simpa only [Complex.abs_ofReal] using hAbs

/-- Ledger recording the enriched API and its exact consequences. -/
structure ZeroMultiplicityConjugationExtensionLedger where
  ts258_conjugation_reality :
    TS258.Goldbach.ZeroSummandConjugationFiniteRealityLedger

  extension_constructor :
    forall
      (base : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract),
      TS258.Goldbach.ZeroMultiplicityConjugationInvariantStatement base ->
        RiemannZetaZeroFamilyMultiplicityConjugationContract

  extension_supplies_ts258_premise :
    forall C : RiemannZetaZeroFamilyMultiplicityConjugationContract,
      TS258.Goldbach.ZeroMultiplicityConjugationInvariantStatement C.base

  extended_zero_sum_reality :
    forall
      (C : RiemannZetaZeroFamilyMultiplicityConjugationContract)
      (truncation : RiemannZetaZeroMultiplicityConjugationTruncationData C),
      TS256.Goldbach.TruncatedZeroSumRealityStatement
        C.base truncation TS257.Goldbach.triangleSplineZeroSpectralSummand

  extended_real_projection_lossless :
    forall
      (C : RiemannZetaZeroFamilyMultiplicityConjugationContract)
      (truncation : RiemannZetaZeroMultiplicityConjugationTruncationData C)
      (X : Nat),
      ((TS257.Goldbach.triangleSplineZeroContributionFunction
        C.base truncation X : Real) : Complex) =
        TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
          C.base truncation X

  extended_real_abs_eq_complex_abs :
    forall
      (C : RiemannZetaZeroFamilyMultiplicityConjugationContract)
      (truncation : RiemannZetaZeroMultiplicityConjugationTruncationData C)
      (X : Nat),
      abs
          (TS257.Goldbach.triangleSplineZeroContributionFunction
            C.base truncation X) =
        Complex.abs
          (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
            C.base truncation X)

  historical_ts185_not_modified : True
  concrete_extended_contract_not_constructed : True
  multiplicity_realization_not_proved : True
  explicit_formula_identity_not_proved : True
  zero_contribution_bound_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS259 ledger. -/
noncomputable def zeroMultiplicityConjugationExtensionLedger :
    ZeroMultiplicityConjugationExtensionLedger where
  ts258_conjugation_reality :=
    TS258.Goldbach.zeroSummandConjugationFiniteRealityLedger
  extension_constructor :=
    RiemannZetaZeroFamilyMultiplicityConjugationContract.ofBase
  extension_supplies_ts258_premise :=
    extendedContract_multiplicityConjugation
  extended_zero_sum_reality := extendedTruncation_zeroSumReality
  extended_real_projection_lossless :=
    extendedTruncation_realProjectionLossless
  extended_real_abs_eq_complex_abs :=
    extendedTruncation_realAbs_eq_complexAbs
  historical_ts185_not_modified := True.intro
  concrete_extended_contract_not_constructed := True.intro
  multiplicity_realization_not_proved := True.intro
  explicit_formula_identity_not_proved := True.intro
  zero_contribution_bound_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS259. -/
def ZeroMultiplicityConjugationExtensionTarget : Prop :=
  Nonempty ZeroMultiplicityConjugationExtensionLedger

/-- TS259 target: the honest multiplicity extension is installed. -/
theorem zeroMultiplicityConjugationExtensionTarget :
    ZeroMultiplicityConjugationExtensionTarget :=
  Nonempty.intro zeroMultiplicityConjugationExtensionLedger

end Goldbach
end TS259
