import Mathlib.Tactic
import TS.Goldbach.Strong.TS257.TriangleSplineMellinSpectralSummand

/-!
# TS258 - Zero Summand Conjugation and Finite Reality

TS257 fixed the concrete triangle-spline zero summand.  This sprint proves
that the summand commutes with complex conjugation and that every TS256
truncation is closed under conjugation.

TS185 does not yet require multiplicities to be invariant under conjugation.
That property is therefore kept as one explicit premise.  Under this premise,
the finite weighted zero sum is fixed by conjugation, has zero imaginary part,
and is exactly the complex embedding of the real contribution used by TS255.

No zero-density estimate, explicit-formula identity, or Goldbach statement is
proved here.
-/

namespace TS258
namespace Goldbach

open scoped BigOperators

/-- The missing TS185 property needed to pair weighted conjugate zeros. -/
def ZeroMultiplicityConjugationInvariantStatement
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract) :
    Prop :=
  forall rho : Complex,
    C.zeroSet rho ->
      C.multiplicity (star rho) = C.multiplicity rho

/-- The concrete Mellin summand commutes with complex conjugation. -/
theorem triangleSplineZeroSpectralSummand_star
    (X : Nat)
    (rho : Complex) :
    TS257.Goldbach.triangleSplineZeroSpectralSummand X (star rho) =
      star (TS257.Goldbach.triangleSplineZeroSpectralSummand X rho) := by
  unfold TS257.Goldbach.triangleSplineZeroSpectralSummand
  have hArg : Not (((X : Complex).arg) = Real.pi) := by
    rw [Complex.natCast_arg]
    exact ne_of_lt Real.pi_pos
  have hPow :
      (X : Complex) ^ star rho = star ((X : Complex) ^ rho) := by
    simpa using (Complex.cpow_conj (X : Complex) rho hArg)
  rw [hPow]
  simp

/-- TS257's named conjugation target is now discharged. -/
theorem triangleSplineZeroSpectralSummandConjugation :
    TS257.Goldbach.TriangleSplineZeroSpectralSummandConjugationStatement := by
  intro X rho hX
  exact triangleSplineZeroSpectralSummand_star X rho

/-- Every complete height truncation is closed under complex conjugation. -/
theorem truncation_zeros_star_mem
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : TS256.Goldbach.RiemannZetaZeroTruncationData C)
    (X : Nat)
    (rho : Complex)
    (hMem : Membership.mem (truncation.zeros X) rho) :
    Membership.mem (truncation.zeros X) (star rho) := by
  apply truncation.zeros_complete_below_height
  exact C.conjugate_closed rho (truncation.zeros_mem_zeroSet X rho hMem)
  simpa using truncation.zeros_height_bounded X rho hMem

/-- One weighted term of the concrete finite zero sum. -/
noncomputable def triangleSplineWeightedZeroTerm
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (X : Nat)
    (rho : Complex) :
    Complex :=
  (C.multiplicity rho : Complex) *
    TS257.Goldbach.triangleSplineZeroSpectralSummand X rho

/-- Weighted conjugate terms agree when multiplicities agree. -/
theorem triangleSplineWeightedZeroTerm_star
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (hMultiplicity : ZeroMultiplicityConjugationInvariantStatement C)
    (X : Nat)
    (rho : Complex)
    (hZero : C.zeroSet rho) :
    triangleSplineWeightedZeroTerm C X (star rho) =
      star (triangleSplineWeightedZeroTerm C X rho) := by
  unfold triangleSplineWeightedZeroTerm
  rw [hMultiplicity rho hZero]
  rw [triangleSplineZeroSpectralSummand_star X rho]
  simp

/-- The finite weighted zero sum is fixed by conjugation. -/
theorem triangleSplineZeroTruncatedComplexSum_star
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : TS256.Goldbach.RiemannZetaZeroTruncationData C)
    (hMultiplicity : ZeroMultiplicityConjugationInvariantStatement C)
    (X : Nat) :
    star (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum C truncation X) =
      TS257.Goldbach.triangleSplineZeroTruncatedComplexSum C truncation X := by
  let s := truncation.zeros X
  let f := triangleSplineWeightedZeroTerm C X
  have hForward :
      forall rho : Complex,
        Membership.mem s rho -> Membership.mem s (Equiv.star rho) := by
    intro rho hMem
    exact truncation_zeros_star_mem C truncation X rho hMem
  have hBackward :
      forall rho : Complex,
        Membership.mem s (Equiv.star rho) -> Membership.mem s rho := by
    intro rho hMem
    have hStar := truncation_zeros_star_mem C truncation X (star rho) hMem
    simpa using hStar
  have hMemIff :
      forall rho : Complex,
        Membership.mem s rho <-> Membership.mem s (Equiv.star rho) :=
    fun rho => Iff.intro (hForward rho) (hBackward rho)
  have hReindex :
      Finset.sum s (fun rho => f (star rho)) = Finset.sum s f := by
    exact
      Finset.sum_equiv
        (Equiv.star)
        hMemIff
        (fun _rho _hMem => rfl)
  change star (Finset.sum s f) = Finset.sum s f
  rw [star_sum]
  calc
    Finset.sum s (fun rho => star (f rho)) =
        Finset.sum s (fun rho => f (star rho)) := by
      apply Finset.sum_congr rfl
      intro rho hMem
      symm
      apply triangleSplineWeightedZeroTerm_star C hMultiplicity X rho
      exact truncation.zeros_mem_zeroSet X rho hMem
    _ = Finset.sum s f := hReindex

/-- The concrete truncated zero sum has zero imaginary part. -/
theorem triangleSplineZeroTruncatedComplexSum_im_eq_zero
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : TS256.Goldbach.RiemannZetaZeroTruncationData C)
    (hMultiplicity : ZeroMultiplicityConjugationInvariantStatement C)
    (X : Nat) :
    (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum C truncation X).im = 0 := by
  have hStar :=
    triangleSplineZeroTruncatedComplexSum_star C truncation hMultiplicity X
  have hIm := congrArg Complex.im hStar
  change
    -(TS257.Goldbach.triangleSplineZeroTruncatedComplexSum C truncation X).im =
      (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum C truncation X).im
    at hIm
  linarith

/-- The TS256 reality target follows from multiplicity conjugation invariance. -/
theorem truncatedZeroSumReality_of_multiplicity_conjugation
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : TS256.Goldbach.RiemannZetaZeroTruncationData C)
    (hMultiplicity : ZeroMultiplicityConjugationInvariantStatement C) :
    TS256.Goldbach.TruncatedZeroSumRealityStatement
      C truncation TS257.Goldbach.triangleSplineZeroSpectralSummand := by
  intro X
  exact
    triangleSplineZeroTruncatedComplexSum_im_eq_zero
      C truncation hMultiplicity X

/-- Taking the real part loses no information once the sum is real. -/
theorem triangleSplineZeroTruncatedComplexSum_eq_ofReal_re
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : TS256.Goldbach.RiemannZetaZeroTruncationData C)
    (hMultiplicity : ZeroMultiplicityConjugationInvariantStatement C)
    (X : Nat) :
    TS257.Goldbach.triangleSplineZeroTruncatedComplexSum C truncation X =
      ((TS257.Goldbach.triangleSplineZeroTruncatedComplexSum C truncation X).re :
        Complex) := by
  apply Complex.ext
  next => simp
  next =>
    simp [triangleSplineZeroTruncatedComplexSum_im_eq_zero
      C truncation hMultiplicity X]

/-- The TS255 real zero function embeds back to the full complex sum. -/
theorem triangleSplineZeroContributionFunction_coe_eq_complexSum
    (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
    (truncation : TS256.Goldbach.RiemannZetaZeroTruncationData C)
    (hMultiplicity : ZeroMultiplicityConjugationInvariantStatement C)
    (X : Nat) :
    ((TS257.Goldbach.triangleSplineZeroContributionFunction C truncation X : Real) :
        Complex) =
      TS257.Goldbach.triangleSplineZeroTruncatedComplexSum C truncation X := by
  symm
  exact
    triangleSplineZeroTruncatedComplexSum_eq_ofReal_re
      C truncation hMultiplicity X

/-- Ledger recording conjugation and finite-sum reality. -/
structure ZeroSummandConjugationFiniteRealityLedger where
  ts257_spectral_summand :
    TS257.Goldbach.TriangleSplineMellinSpectralSummandLedger

  summand_conjugation :
    TS257.Goldbach.TriangleSplineZeroSpectralSummandConjugationStatement

  truncation_star_closed :
    forall
      (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
      (truncation : TS256.Goldbach.RiemannZetaZeroTruncationData C)
      (X : Nat)
      (rho : Complex),
      Membership.mem (truncation.zeros X) rho ->
        Membership.mem (truncation.zeros X) (star rho)

  reality_from_multiplicity_conjugation :
    forall
      (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
      (truncation : TS256.Goldbach.RiemannZetaZeroTruncationData C),
      ZeroMultiplicityConjugationInvariantStatement C ->
        TS256.Goldbach.TruncatedZeroSumRealityStatement
          C truncation TS257.Goldbach.triangleSplineZeroSpectralSummand

  real_projection_loses_no_information :
    forall
      (C : TS185.Goldbach.RiemannZetaZeroFamilyAPIBindingContract)
      (truncation : TS256.Goldbach.RiemannZetaZeroTruncationData C),
      ZeroMultiplicityConjugationInvariantStatement C ->
        forall X : Nat,
          ((TS257.Goldbach.triangleSplineZeroContributionFunction C truncation X : Real) :
              Complex) =
            TS257.Goldbach.triangleSplineZeroTruncatedComplexSum C truncation X

  multiplicity_conjugation_invariance_not_proved : True
  ts185_not_modified : True
  mellin_integral_not_evaluated : True
  explicit_formula_identity_not_proved : True
  zero_contribution_bound_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS258 ledger. -/
noncomputable def zeroSummandConjugationFiniteRealityLedger :
    ZeroSummandConjugationFiniteRealityLedger where
  ts257_spectral_summand :=
    TS257.Goldbach.triangleSplineMellinSpectralSummandLedger
  summand_conjugation := triangleSplineZeroSpectralSummandConjugation
  truncation_star_closed := truncation_zeros_star_mem
  reality_from_multiplicity_conjugation :=
    truncatedZeroSumReality_of_multiplicity_conjugation
  real_projection_loses_no_information :=
    triangleSplineZeroContributionFunction_coe_eq_complexSum
  multiplicity_conjugation_invariance_not_proved := True.intro
  ts185_not_modified := True.intro
  mellin_integral_not_evaluated := True.intro
  explicit_formula_identity_not_proved := True.intro
  zero_contribution_bound_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS258. -/
def ZeroSummandConjugationFiniteRealityTarget : Prop :=
  Nonempty ZeroSummandConjugationFiniteRealityLedger

/-- TS258 target: conjugation and conditional finite-sum reality are assembled. -/
theorem zeroSummandConjugationFiniteRealityTarget :
    ZeroSummandConjugationFiniteRealityTarget :=
  Nonempty.intro zeroSummandConjugationFiniteRealityLedger

end Goldbach
end TS258
