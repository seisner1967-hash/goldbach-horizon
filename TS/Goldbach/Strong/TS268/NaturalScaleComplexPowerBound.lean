import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import TS.Goldbach.Strong.TS267.ExactFiniteUniformSpectralTermBound

/-!
# TS268 - Natural-Scale Complex-Power Bound

TS267 constructed the least exact uniform bound for the concrete finite
spectral terms.  This sprint extracts their natural-scale complex-power factor.

For every concrete nontrivial zeta zero, the critical-strip condition gives
`0 < rho.re < 1`.  Mathlib's complex-power norm formula then proves
`abs ((X : Complex) ^ rho) <= max 1 X`, and this sharpens to `<= X` when
`1 <= X`.

The remaining multiplicity and denominator are isolated in one complex factor.
Its exact finite supremum gives a new TS266 uniform bound with the scale factor
visible.  No Riemann Hypothesis, numerical first-zero height, multiplicity
estimate, denominator estimate, zero-counting theorem, explicit formula,
Gallagher estimate, or Goldbach statement is used or proved.
-/

namespace TS268
namespace Goldbach

/-- Natural-scale complex powers are bounded by `max 1 X` in the strip. -/
theorem naturalScaleComplexPower_abs_le_max_one
    (X : Nat)
    (rho : Complex)
    (hZero : TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet rho) :
    Complex.abs ((X : Complex) ^ rho) <= max 1 (X : Real) := by
  have hStrip := TS264.Goldbach.concreteZero_in_critical_strip hZero
  change norm ((X : Complex) ^ rho) <= max 1 (X : Real)
  by_cases hX : X = 0
  case pos =>
    subst X
    rw [Complex.norm_natCast_cpow_of_re_ne_zero 0 hStrip.1.ne']
    simpa using Real.zero_rpow_le_one rho.re
  case neg =>
    have hXPos : 0 < X := Nat.pos_of_ne_zero hX
    rw [Complex.norm_natCast_cpow_of_pos hXPos rho]
    have hBase : (1 : Real) <= (X : Real) := by
      exact_mod_cast hXPos
    have hPow :=
      Real.rpow_le_rpow_of_exponent_le hBase hStrip.2.le
    rw [Real.rpow_one] at hPow
    exact hPow.trans (le_max_right 1 (X : Real))

/-- At scales at least one, the natural-scale complex power is at most `X`. -/
theorem naturalScaleComplexPower_abs_le
    (X : Nat)
    (rho : Complex)
    (hX : 1 <= X)
    (hZero : TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet rho) :
    Complex.abs ((X : Complex) ^ rho) <= (X : Real) := by
  have hStrip := TS264.Goldbach.concreteZero_in_critical_strip hZero
  have hXPos : 0 < X := Nat.zero_lt_of_lt hX
  change norm ((X : Complex) ^ rho) <= (X : Real)
  rw [Complex.norm_natCast_cpow_of_pos hXPos rho]
  have hBase : (1 : Real) <= (X : Real) := by
    exact_mod_cast hX
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hBase hStrip.2.le

/-- The multiplicity and Mellin-denominator factor left after scale removal. -/
noncomputable def concreteMultiplicityDenominatorFactor
    (rho : Complex) :
    Complex :=
  (TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho :
      Complex) /
    (rho * (rho + 1))

/-- Exact factorization of the TS266 weighted spectral term. -/
theorem concreteFiniteHeightZeroTerm_eq_scale_mul_factor
    (X : Nat)
    (rho : Complex) :
    TS266.Goldbach.concreteFiniteHeightZeroTerm X rho =
      (X : Complex) ^ rho * concreteMultiplicityDenominatorFactor rho := by
  unfold TS266.Goldbach.concreteFiniteHeightZeroTerm
    TS257.Goldbach.triangleSplineZeroSpectralSummand
    concreteMultiplicityDenominatorFactor
  ring

/-- Absolute-value factorization of the weighted spectral term. -/
theorem concreteFiniteHeightZeroTerm_abs_eq_scale_mul_factor
    (X : Nat)
    (rho : Complex) :
    Complex.abs (TS266.Goldbach.concreteFiniteHeightZeroTerm X rho) =
      Complex.abs ((X : Complex) ^ rho) *
        Complex.abs (concreteMultiplicityDenominatorFactor rho) := by
  rw [concreteFiniteHeightZeroTerm_eq_scale_mul_factor]
  exact map_mul Complex.abs ((X : Complex) ^ rho)
    (concreteMultiplicityDenominatorFactor rho)

/-- Nonnegative magnitude of the multiplicity-denominator factor. -/
noncomputable def concreteMultiplicityDenominatorMagnitude
    (rho : Complex) :
    NNReal :=
  Real.toNNReal (Complex.abs (concreteMultiplicityDenominatorFactor rho))

/-- Exact finite supremum of the residual factor below the TS265 height. -/
noncomputable def concreteFiniteHeightExactMultiplicityDenominatorBoundNNReal
    (X : Nat) :
    NNReal :=
  Finset.sup
    (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X)
    concreteMultiplicityDenominatorMagnitude

/-- Real-valued form of the exact finite residual-factor supremum. -/
noncomputable def concreteFiniteHeightExactMultiplicityDenominatorBound
    (X : Nat) :
    Real :=
  concreteFiniteHeightExactMultiplicityDenominatorBoundNNReal X

/-- The exact residual-factor supremum is nonnegative. -/
theorem concreteFiniteHeightExactMultiplicityDenominatorBound_nonnegative
    (X : Nat) :
    0 <= concreteFiniteHeightExactMultiplicityDenominatorBound X := by
  unfold concreteFiniteHeightExactMultiplicityDenominatorBound
  exact NNReal.coe_nonneg _

/-- Every selected residual factor is bounded by its exact finite supremum. -/
theorem concreteMultiplicityDenominatorFactor_abs_le_exactBound
    (X : Nat)
    (rho : Complex)
    (hRho : Membership.mem
      (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X) rho) :
    Complex.abs (concreteMultiplicityDenominatorFactor rho) <=
      concreteFiniteHeightExactMultiplicityDenominatorBound X := by
  unfold concreteFiniteHeightExactMultiplicityDenominatorBound
  rw [show
    Complex.abs (concreteMultiplicityDenominatorFactor rho) =
        (concreteMultiplicityDenominatorMagnitude rho : Real) by
      unfold concreteMultiplicityDenominatorMagnitude
      symm
      exact Real.coe_toNNReal _ (Complex.abs.nonneg _)]
  exact NNReal.coe_le_coe.mpr (Finset.le_sup hRho)

/-- Scale-visible uniform bound for the complete weighted term. -/
noncomputable def naturalScaleUniformTermBound
    (X : Nat) :
    Real :=
  max 1 (X : Real) *
    concreteFiniteHeightExactMultiplicityDenominatorBound X

/-- The scale-visible uniform term bound is nonnegative. -/
theorem naturalScaleUniformTermBound_nonnegative
    (X : Nat) :
    0 <= naturalScaleUniformTermBound X :=
  mul_nonneg
    (zero_le_one.trans (le_max_left 1 (X : Real)))
    (concreteFiniteHeightExactMultiplicityDenominatorBound_nonnegative X)

/-- Every selected weighted term is bounded by the scale-visible bound. -/
theorem concreteFiniteHeightZeroTerm_abs_le_naturalScaleUniformTermBound
    (X : Nat)
    (rho : Complex)
    (hRho : Membership.mem
      (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X) rho) :
    Complex.abs (TS266.Goldbach.concreteFiniteHeightZeroTerm X rho) <=
      naturalScaleUniformTermBound X := by
  have hZero :=
    (TS265.Goldbach.mem_concreteFiniteHeightTruncation_iff X rho).mp hRho |>.1
  rw [concreteFiniteHeightZeroTerm_abs_eq_scale_mul_factor]
  exact mul_le_mul
    (naturalScaleComplexPower_abs_le_max_one X rho hZero)
    (concreteMultiplicityDenominatorFactor_abs_le_exactBound X rho hRho)
    (Complex.abs.nonneg _)
    (zero_le_one.trans (le_max_left 1 (X : Real)))

/-- The scale-visible function fills the TS266 uniform-term input. -/
theorem naturalScaleUniformTermBound_statement :
    TS266.Goldbach.ConcreteFiniteHeightZeroUniformTermBoundStatement
      naturalScaleUniformTermBound :=
  And.intro
    naturalScaleUniformTermBound_nonnegative
    concreteFiniteHeightZeroTerm_abs_le_naturalScaleUniformTermBound

/-- The least TS267 bound is below the scale-visible analytic factorization. -/
theorem exactUniformTermBound_le_naturalScaleUniformTermBound
    (X : Nat) :
    TS267.Goldbach.concreteFiniteHeightExactUniformTermBound X <=
      naturalScaleUniformTermBound X :=
  TS267.Goldbach.concreteFiniteHeightExactUniformTermBound_le_of_uniformBound
    naturalScaleUniformTermBound
    naturalScaleUniformTermBound_statement
    X

/-- At scale at least one, `max 1 X` in the visible bound equals `X`. -/
theorem naturalScaleUniformTermBound_eq_linear
    (X : Nat)
    (hX : 1 <= X) :
    naturalScaleUniformTermBound X =
      (X : Real) * concreteFiniteHeightExactMultiplicityDenominatorBound X := by
  unfold naturalScaleUniformTermBound
  rw [max_eq_right]
  exact_mod_cast hX

/-- Linear-scale comparison for the least exact TS267 uniform bound. -/
theorem exactUniformTermBound_le_linearScaleResidualBound
    (X : Nat)
    (hX : 1 <= X) :
    TS267.Goldbach.concreteFiniteHeightExactUniformTermBound X <=
      (X : Real) *
        concreteFiniteHeightExactMultiplicityDenominatorBound X := by
  exact
    (exactUniformTermBound_le_naturalScaleUniformTermBound X).trans_eq
      (naturalScaleUniformTermBound_eq_linear X hX)

/-- Contribution bound using exact count and the visible scale factor. -/
theorem concreteFiniteHeightZeroContribution_abs_le_exactCount_mul_naturalScale
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      TS267.Goldbach.concreteFiniteHeightExactCountBound X *
        naturalScaleUniformTermBound X :=
  TS266.Goldbach.concreteFiniteHeightZeroContribution_abs_le_count_mul_term
    naturalScaleUniformTermBound
    TS267.Goldbach.concreteFiniteHeightExactCountBound
    naturalScaleUniformTermBound_statement
    TS267.Goldbach.concreteFiniteHeightExactCountBound_statement
    X

/-- Linear-scale contribution bound at every natural scale at least one. -/
theorem concreteFiniteHeightZeroContribution_abs_le_exactCount_mul_linearScale
    (X : Nat)
    (hX : 1 <= X) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      TS267.Goldbach.concreteFiniteHeightExactCountBound X *
        ((X : Real) *
          concreteFiniteHeightExactMultiplicityDenominatorBound X) := by
  exact
    (concreteFiniteHeightZeroContribution_abs_le_exactCount_mul_naturalScale X).trans_eq
      (congrArg
        (fun y : Real =>
          TS267.Goldbach.concreteFiniteHeightExactCountBound X * y)
        (naturalScaleUniformTermBound_eq_linear X hX))

/-- Any future counting estimate combines with the linear scale factor. -/
theorem concreteFiniteHeightZeroContribution_abs_le_count_mul_linearScale
    (countBound : Nat -> Real)
    (hCount :
      TS266.Goldbach.ConcreteFiniteHeightZeroCountingBoundStatement countBound)
    (X : Nat)
    (hX : 1 <= X) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      countBound X *
        ((X : Real) *
          concreteFiniteHeightExactMultiplicityDenominatorBound X) := by
  exact
    (TS266.Goldbach.concreteFiniteHeightZeroContribution_abs_le_count_mul_term
        naturalScaleUniformTermBound
        countBound
        naturalScaleUniformTermBound_statement
        hCount
        X).trans_eq
      (congrArg
        (fun y : Real => countBound X * y)
        (naturalScaleUniformTermBound_eq_linear X hX))

/-- Ledger recording the natural-scale complex-power extraction. -/
structure NaturalScaleComplexPowerBoundLedger where
  ts267_exact_uniform_bound :
    TS267.Goldbach.ExactFiniteUniformSpectralTermBoundLedger

  natural_scale_power_bound :
    forall (X : Nat) (rho : Complex),
      TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet rho ->
        Complex.abs ((X : Complex) ^ rho) <= max 1 (X : Real)

  multiplicity_denominator_factor :
    Complex -> Complex

  multiplicity_denominator_factor_eq :
    multiplicity_denominator_factor = concreteMultiplicityDenominatorFactor

  exact_residual_factor_bound :
    Nat -> Real

  exact_residual_factor_bound_eq :
    exact_residual_factor_bound =
      concreteFiniteHeightExactMultiplicityDenominatorBound

  scale_visible_uniform_bound :
    Nat -> Real

  scale_visible_uniform_bound_eq :
    scale_visible_uniform_bound = naturalScaleUniformTermBound

  scale_visible_uniform_bound_supplies_ts266 :
    TS266.Goldbach.ConcreteFiniteHeightZeroUniformTermBoundStatement
      scale_visible_uniform_bound

  linear_scale_contribution_bound :
    forall X : Nat,
      1 <= X ->
        abs
            (TS257.Goldbach.triangleSplineZeroContributionFunction
              TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
              TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
          TS267.Goldbach.concreteFiniteHeightExactCountBound X *
            ((X : Real) * exact_residual_factor_bound X)

  effective_multiplicity_bound_not_proved : True
  effective_denominator_lower_bound_not_proved : True
  closed_form_residual_factor_bound_not_proved : True
  effective_zero_counting_bound_not_proved : True
  zero_density_theorem_not_proved : True
  global_zero_summability_not_proved : True
  contour_shift_not_proved : True
  explicit_formula_identity_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS268 natural-scale extraction ledger. -/
noncomputable def naturalScaleComplexPowerBoundLedger :
    NaturalScaleComplexPowerBoundLedger where
  ts267_exact_uniform_bound :=
    TS267.Goldbach.exactFiniteUniformSpectralTermBoundLedger
  natural_scale_power_bound :=
    naturalScaleComplexPower_abs_le_max_one
  multiplicity_denominator_factor :=
    concreteMultiplicityDenominatorFactor
  multiplicity_denominator_factor_eq :=
    rfl
  exact_residual_factor_bound :=
    concreteFiniteHeightExactMultiplicityDenominatorBound
  exact_residual_factor_bound_eq :=
    rfl
  scale_visible_uniform_bound :=
    naturalScaleUniformTermBound
  scale_visible_uniform_bound_eq :=
    rfl
  scale_visible_uniform_bound_supplies_ts266 :=
    naturalScaleUniformTermBound_statement
  linear_scale_contribution_bound :=
    concreteFiniteHeightZeroContribution_abs_le_exactCount_mul_linearScale
  effective_multiplicity_bound_not_proved := True.intro
  effective_denominator_lower_bound_not_proved := True.intro
  closed_form_residual_factor_bound_not_proved := True.intro
  effective_zero_counting_bound_not_proved := True.intro
  zero_density_theorem_not_proved := True.intro
  global_zero_summability_not_proved := True.intro
  contour_shift_not_proved := True.intro
  explicit_formula_identity_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS268. -/
def NaturalScaleComplexPowerBoundTarget : Prop :=
  Nonempty NaturalScaleComplexPowerBoundLedger

/-- TS268 target: the natural scale factor is extracted and bounded. -/
theorem naturalScaleComplexPowerBoundTarget :
    NaturalScaleComplexPowerBoundTarget :=
  Nonempty.intro naturalScaleComplexPowerBoundLedger

end Goldbach
end TS268
