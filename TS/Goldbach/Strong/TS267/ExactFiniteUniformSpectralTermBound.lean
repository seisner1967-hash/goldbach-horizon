import Mathlib.Tactic
import TS.Goldbach.Strong.TS266.ConcreteFiniteZeroSumTriangleMajorization

/-!
# TS267 - Exact Finite Uniform Spectral-Term Bound

TS266 reduced the concrete finite zero contribution to a nonnegative uniform
per-term bound and a real zero-counting bound.  Since TS265 supplies an exact
finite set at every scale, this sprint constructs the least uniform bound on
that set as a finite supremum in `NNReal`.

The resulting bound fills the TS266 uniform-term input without an additional
hypothesis.  The exact real cardinality also fills the counting input and gives
an unconditional cardinality-times-supremum estimate.  These exact functions
are noncomputable and are not closed-form analytic estimates.

No multiplicity bound, denominator lower bound, zero-counting asymptotic,
zero-density theorem, explicit-formula identity, residual bound, Gallagher
estimate, or Goldbach statement is proved.
-/

namespace TS267
namespace Goldbach

/-- The exact nonnegative magnitude of one TS266 weighted term. -/
noncomputable def concreteFiniteHeightZeroTermMagnitude
    (X : Nat)
    (rho : Complex) :
    NNReal :=
  Real.toNNReal
    (Complex.abs (TS266.Goldbach.concreteFiniteHeightZeroTerm X rho))

/-- The exact finite supremum of all selected weighted-term magnitudes. -/
noncomputable def concreteFiniteHeightExactUniformTermBoundNNReal
    (X : Nat) :
    NNReal :=
  Finset.sup
    (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X)
    (concreteFiniteHeightZeroTermMagnitude X)

/-- Real-valued form of the exact finite uniform term bound. -/
noncomputable def concreteFiniteHeightExactUniformTermBound
    (X : Nat) :
    Real :=
  concreteFiniteHeightExactUniformTermBoundNNReal X

/-- The exact finite uniform bound is nonnegative at every scale. -/
theorem concreteFiniteHeightExactUniformTermBound_nonnegative
    (X : Nat) :
    0 <= concreteFiniteHeightExactUniformTermBound X := by
  unfold concreteFiniteHeightExactUniformTermBound
  exact NNReal.coe_nonneg _

/-- Every selected weighted term is bounded by the exact finite supremum. -/
theorem concreteFiniteHeightZeroTerm_abs_le_exactUniformTermBound
    (X : Nat)
    (rho : Complex)
    (hRho : Membership.mem
      (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X) rho) :
    Complex.abs (TS266.Goldbach.concreteFiniteHeightZeroTerm X rho) <=
      concreteFiniteHeightExactUniformTermBound X := by
  unfold concreteFiniteHeightExactUniformTermBound
  rw [show
    Complex.abs (TS266.Goldbach.concreteFiniteHeightZeroTerm X rho) =
        (concreteFiniteHeightZeroTermMagnitude X rho : Real) by
      unfold concreteFiniteHeightZeroTermMagnitude
      symm
      exact Real.coe_toNNReal _ (Complex.abs.nonneg _)]
  exact NNReal.coe_le_coe.mpr (Finset.le_sup hRho)

/-- The exact finite supremum fills the TS266 uniform-term input. -/
theorem concreteFiniteHeightExactUniformTermBound_statement :
    TS266.Goldbach.ConcreteFiniteHeightZeroUniformTermBoundStatement
      concreteFiniteHeightExactUniformTermBound :=
  And.intro
    concreteFiniteHeightExactUniformTermBound_nonnegative
    concreteFiniteHeightZeroTerm_abs_le_exactUniformTermBound

/--
The exact finite supremum is no larger than any other TS266 uniform bound.
-/
theorem concreteFiniteHeightExactUniformTermBound_le_of_uniformBound
    (bound : Nat -> Real)
    (hBound :
      TS266.Goldbach.ConcreteFiniteHeightZeroUniformTermBoundStatement bound)
    (X : Nat) :
    concreteFiniteHeightExactUniformTermBound X <= bound X := by
  let boundNNReal : NNReal := Real.toNNReal (bound X)
  unfold concreteFiniteHeightExactUniformTermBound
  rw [show bound X = (boundNNReal : Real) by
    unfold boundNNReal
    symm
    exact Real.coe_toNNReal _ (hBound.1 X)]
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_le
  intro rho hRho
  apply NNReal.coe_le_coe.mp
  change
    (concreteFiniteHeightZeroTermMagnitude X rho : Real) <=
      (boundNNReal : Real)
  rw [show
      (concreteFiniteHeightZeroTermMagnitude X rho : Real) =
        Complex.abs (TS266.Goldbach.concreteFiniteHeightZeroTerm X rho) by
    unfold concreteFiniteHeightZeroTermMagnitude
    exact Real.coe_toNNReal _ (Complex.abs.nonneg _)]
  rw [show (boundNNReal : Real) = bound X by
    unfold boundNNReal
    exact Real.coe_toNNReal _ (hBound.1 X)]
  exact hBound.2 X rho hRho

/-- Exact real cardinality of the concrete finite zero selection. -/
noncomputable def concreteFiniteHeightExactCountBound
    (X : Nat) :
    Real :=
  (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X).card

/-- The exact cardinality fills the TS266 counting input by reflexivity. -/
theorem concreteFiniteHeightExactCountBound_statement :
    TS266.Goldbach.ConcreteFiniteHeightZeroCountingBoundStatement
      concreteFiniteHeightExactCountBound := by
  intro X
  exact le_rfl

/-- Unconditional finite contribution bound using both exact finite values. -/
theorem concreteFiniteHeightZeroContribution_abs_le_exactCount_mul_exactUniform
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      concreteFiniteHeightExactCountBound X *
        concreteFiniteHeightExactUniformTermBound X :=
  TS266.Goldbach.concreteFiniteHeightZeroContribution_abs_le_count_mul_term
    concreteFiniteHeightExactUniformTermBound
    concreteFiniteHeightExactCountBound
    concreteFiniteHeightExactUniformTermBound_statement
    concreteFiniteHeightExactCountBound_statement
    X

/-- Any future counting estimate combines with the exact uniform term bound. -/
theorem concreteFiniteHeightZeroContribution_abs_le_count_mul_exactUniform
    (countBound : Nat -> Real)
    (hCount :
      TS266.Goldbach.ConcreteFiniteHeightZeroCountingBoundStatement countBound)
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      countBound X * concreteFiniteHeightExactUniformTermBound X :=
  TS266.Goldbach.concreteFiniteHeightZeroContribution_abs_le_count_mul_term
    concreteFiniteHeightExactUniformTermBound
    countBound
    concreteFiniteHeightExactUniformTermBound_statement
    hCount
    X

/-- Ledger recording the exact finite uniform spectral-term bound. -/
structure ExactFiniteUniformSpectralTermBoundLedger where
  ts266_triangle_majorization :
    TS266.Goldbach.ConcreteFiniteZeroSumTriangleMajorizationLedger

  exact_uniform_bound :
    Nat -> Real

  exact_uniform_bound_eq :
    exact_uniform_bound = concreteFiniteHeightExactUniformTermBound

  exact_uniform_bound_supplies_ts266 :
    TS266.Goldbach.ConcreteFiniteHeightZeroUniformTermBoundStatement
      exact_uniform_bound

  exact_uniform_bound_minimal :
    forall bound : Nat -> Real,
      TS266.Goldbach.ConcreteFiniteHeightZeroUniformTermBoundStatement bound ->
        forall X : Nat,
          exact_uniform_bound X <= bound X

  exact_count_bound :
    Nat -> Real

  exact_count_bound_eq :
    exact_count_bound = concreteFiniteHeightExactCountBound

  exact_count_bound_supplies_ts266 :
    TS266.Goldbach.ConcreteFiniteHeightZeroCountingBoundStatement
      exact_count_bound

  exact_product_bound :
    forall X : Nat,
      abs
          (TS257.Goldbach.triangleSplineZeroContributionFunction
            TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
            TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
        exact_count_bound X * exact_uniform_bound X

  closed_form_uniform_term_bound_not_proved : True
  effective_multiplicity_bound_not_proved : True
  effective_denominator_lower_bound_not_proved : True
  effective_zero_counting_bound_not_proved : True
  zero_density_theorem_not_proved : True
  explicit_formula_identity_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS267 exact finite uniform-bound ledger. -/
noncomputable def exactFiniteUniformSpectralTermBoundLedger :
    ExactFiniteUniformSpectralTermBoundLedger where
  ts266_triangle_majorization :=
    TS266.Goldbach.concreteFiniteZeroSumTriangleMajorizationLedger
  exact_uniform_bound :=
    concreteFiniteHeightExactUniformTermBound
  exact_uniform_bound_eq :=
    rfl
  exact_uniform_bound_supplies_ts266 :=
    concreteFiniteHeightExactUniformTermBound_statement
  exact_uniform_bound_minimal :=
    concreteFiniteHeightExactUniformTermBound_le_of_uniformBound
  exact_count_bound :=
    concreteFiniteHeightExactCountBound
  exact_count_bound_eq :=
    rfl
  exact_count_bound_supplies_ts266 :=
    concreteFiniteHeightExactCountBound_statement
  exact_product_bound :=
    concreteFiniteHeightZeroContribution_abs_le_exactCount_mul_exactUniform
  closed_form_uniform_term_bound_not_proved := True.intro
  effective_multiplicity_bound_not_proved := True.intro
  effective_denominator_lower_bound_not_proved := True.intro
  effective_zero_counting_bound_not_proved := True.intro
  zero_density_theorem_not_proved := True.intro
  explicit_formula_identity_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS267. -/
def ExactFiniteUniformSpectralTermBoundTarget : Prop :=
  Nonempty ExactFiniteUniformSpectralTermBoundLedger

/-- TS267 target: the least exact finite uniform term bound is assembled. -/
theorem exactFiniteUniformSpectralTermBoundTarget :
    ExactFiniteUniformSpectralTermBoundTarget :=
  Nonempty.intro exactFiniteUniformSpectralTermBoundLedger

end Goldbach
end TS267
