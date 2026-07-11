import Mathlib.Tactic
import TS.Goldbach.Strong.TS265.ConcreteFiniteHeightZeroTruncation

/-!
# TS266 - Concrete Finite Zero-Sum Triangle Majorization

TS265 constructed the exact finite set of nontrivial Riemann-zeta zeros below
height `X` and proved that the corresponding triangle-spline spectral sum is
real.  This sprint performs the first unconditional majorization of that sum.

The finite complex sum is bounded by the sum of the norms of its weighted
terms.  The exact TS265 transport then gives the same bound for the real zero
contribution used by TS255.  Finally, two named assumptions reduce this norm
mass to a product of a zero-counting bound and a uniform per-term bound.

No zero-counting estimate, uniform spectral-term estimate, zero-density
theorem, explicit-formula identity, residual bound, Gallagher estimate, or
Goldbach statement is proved.
-/

namespace TS266
namespace Goldbach

/-- One multiplicity-weighted term in the concrete finite zero sum. -/
noncomputable def concreteFiniteHeightZeroTerm
    (X : Nat)
    (rho : Complex) :
    Complex :=
  (TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho :
      Complex) *
    TS257.Goldbach.triangleSplineZeroSpectralSummand X rho

/-- Sum of the complex norms of all weighted terms below height `X`. -/
noncomputable def concreteFiniteHeightZeroNormMass
    (X : Nat) :
    Real :=
  Finset.sum
    (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X)
    (fun rho => Complex.abs (concreteFiniteHeightZeroTerm X rho))

/-- The TS257 complex sum is definitionally the sum of the concrete terms. -/
theorem concreteFiniteHeightZeroTruncatedComplexSum_eq_sum
    (X : Nat) :
    TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
        TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
        TS265.Goldbach.concreteFiniteHeightTruncationData X =
      Finset.sum
        (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X)
        (fun rho => concreteFiniteHeightZeroTerm X rho) :=
  rfl

/-- Triangle inequality for the concrete finite complex zero sum. -/
theorem concreteFiniteHeightZeroTruncatedComplexSum_abs_le_normMass
    (X : Nat) :
    Complex.abs
        (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      concreteFiniteHeightZeroNormMass X := by
  rw [concreteFiniteHeightZeroTruncatedComplexSum_eq_sum]
  change
    norm
        (Finset.sum
          (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X)
          (fun rho => concreteFiniteHeightZeroTerm X rho)) <=
      Finset.sum
        (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X)
        (fun rho => norm (concreteFiniteHeightZeroTerm X rho))
  exact norm_sum_le
    (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X)
    (fun rho => concreteFiniteHeightZeroTerm X rho)

/-- Triangle inequality transported to the real TS255 zero contribution. -/
theorem concreteFiniteHeightZeroContribution_abs_le_normMass
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      concreteFiniteHeightZeroNormMass X := by
  rw [TS265.Goldbach.concreteFiniteHeightTruncation_realAbs_eq_complexAbs]
  exact concreteFiniteHeightZeroTruncatedComplexSum_abs_le_normMass X

/--
A nonnegative uniform bound for every weighted term selected at scale `X`.
-/
def ConcreteFiniteHeightZeroUniformTermBoundStatement
    (termBound : Nat -> Real) :
    Prop :=
  (forall X : Nat, 0 <= termBound X) /\
    forall (X : Nat) (rho : Complex),
      Membership.mem
          (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X) rho ->
        Complex.abs (concreteFiniteHeightZeroTerm X rho) <= termBound X

/-- A real upper bound for the number of selected zeros at each scale. -/
def ConcreteFiniteHeightZeroCountingBoundStatement
    (countBound : Nat -> Real) :
    Prop :=
  forall X : Nat,
    ((TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X).card : Real) <=
      countBound X

/-- The norm mass is reduced to counting times a uniform per-term bound. -/
theorem concreteFiniteHeightZeroNormMass_le_count_mul_term
    (termBound countBound : Nat -> Real)
    (hTerm : ConcreteFiniteHeightZeroUniformTermBoundStatement termBound)
    (hCount : ConcreteFiniteHeightZeroCountingBoundStatement countBound)
    (X : Nat) :
    concreteFiniteHeightZeroNormMass X <=
      countBound X * termBound X := by
  calc
    concreteFiniteHeightZeroNormMass X <=
        Finset.sum
          (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X)
          (fun _ => termBound X) := by
      apply Finset.sum_le_sum
      intro rho hRho
      exact hTerm.2 X rho hRho
    _ =
        ((TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X).card :
            Real) * termBound X := by
      simp
    _ <= countBound X * termBound X :=
      mul_le_mul_of_nonneg_right (hCount X) (hTerm.1 X)

/-- Final finite-sum reduction to the two named analytic majorants. -/
theorem concreteFiniteHeightZeroContribution_abs_le_count_mul_term
    (termBound countBound : Nat -> Real)
    (hTerm : ConcreteFiniteHeightZeroUniformTermBoundStatement termBound)
    (hCount : ConcreteFiniteHeightZeroCountingBoundStatement countBound)
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      countBound X * termBound X :=
  (concreteFiniteHeightZeroContribution_abs_le_normMass X).trans
    (concreteFiniteHeightZeroNormMass_le_count_mul_term
      termBound countBound hTerm hCount X)

/-- Ledger recording the concrete finite zero-sum majorization. -/
structure ConcreteFiniteZeroSumTriangleMajorizationLedger where
  ts265_concrete_truncation :
    TS265.Goldbach.ConcreteFiniteHeightZeroTruncationLedger

  weighted_term :
    Nat -> Complex -> Complex

  weighted_term_eq :
    weighted_term = concreteFiniteHeightZeroTerm

  norm_mass :
    Nat -> Real

  norm_mass_eq :
    norm_mass = concreteFiniteHeightZeroNormMass

  complex_triangle_bound :
    forall X : Nat,
      Complex.abs
          (TS257.Goldbach.triangleSplineZeroTruncatedComplexSum
            TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
            TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
        norm_mass X

  real_triangle_bound :
    forall X : Nat,
      abs
          (TS257.Goldbach.triangleSplineZeroContributionFunction
            TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
            TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
        norm_mass X

  counting_uniform_term_reduction :
    forall termBound countBound : Nat -> Real,
      ConcreteFiniteHeightZeroUniformTermBoundStatement termBound ->
        ConcreteFiniteHeightZeroCountingBoundStatement countBound ->
          forall X : Nat,
            abs
                (TS257.Goldbach.triangleSplineZeroContributionFunction
                  TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
                  TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
              countBound X * termBound X

  effective_uniform_term_bound_not_proved : True
  effective_zero_counting_bound_not_proved : True
  zero_density_theorem_not_proved : True
  explicit_formula_identity_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS266 finite-sum majorization ledger. -/
noncomputable def concreteFiniteZeroSumTriangleMajorizationLedger :
    ConcreteFiniteZeroSumTriangleMajorizationLedger where
  ts265_concrete_truncation :=
    TS265.Goldbach.concreteFiniteHeightZeroTruncationLedger
  weighted_term :=
    concreteFiniteHeightZeroTerm
  weighted_term_eq :=
    rfl
  norm_mass :=
    concreteFiniteHeightZeroNormMass
  norm_mass_eq :=
    rfl
  complex_triangle_bound :=
    concreteFiniteHeightZeroTruncatedComplexSum_abs_le_normMass
  real_triangle_bound :=
    concreteFiniteHeightZeroContribution_abs_le_normMass
  counting_uniform_term_reduction :=
    concreteFiniteHeightZeroContribution_abs_le_count_mul_term
  effective_uniform_term_bound_not_proved := True.intro
  effective_zero_counting_bound_not_proved := True.intro
  zero_density_theorem_not_proved := True.intro
  explicit_formula_identity_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS266. -/
def ConcreteFiniteZeroSumTriangleMajorizationTarget : Prop :=
  Nonempty ConcreteFiniteZeroSumTriangleMajorizationLedger

/-- TS266 target: the finite zero sum has a reusable triangle majorization. -/
theorem concreteFiniteZeroSumTriangleMajorizationTarget :
    ConcreteFiniteZeroSumTriangleMajorizationTarget :=
  Nonempty.intro concreteFiniteZeroSumTriangleMajorizationLedger

end Goldbach
end TS266
