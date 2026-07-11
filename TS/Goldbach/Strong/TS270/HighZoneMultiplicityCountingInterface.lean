import Mathlib.Tactic
import TS.Goldbach.Strong.TS269.ImaginarySquareDenominatorBound

/-!
# TS270 - High-Zone Multiplicity Counting Interface

TS269 bounded the concrete zero contribution by an exact low-zone mass plus
a high-zone quadratic envelope.  The high envelope is weighted by the actual
analytic multiplicities, so plain `Finset.card` is not the correct counting
object.

This sprint defines exact multiplicity counts and proves that the high weighted
residual mass is bounded by the high multiplicity count.  It then packages a
generic upper bound for that count and transports any such bound to the real
TS255 zero contribution.

No simplicity of zeros, effective zero-counting estimate, zero-density theorem,
global summability, explicit formula, Gallagher estimate, or Goldbach statement
is used or proved.
-/

namespace TS270
namespace Goldbach

/-- Exact multiplicity count for concrete zeros below an arbitrary height. -/
noncomputable def concreteMultiplicityCountUpToHeight
    (T : Real) :
    Nat :=
  Finset.sum
    (TS265.Goldbach.zerosUpToHeight T)
    (fun rho =>
      TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho)

/-- Exact multiplicity count in the TS269 high zone at natural scale. -/
noncomputable def concreteHighImaginaryMultiplicityCount
    (X : Nat) :
    Nat :=
  Finset.sum
    (TS269.Goldbach.concreteHighImaginaryZeroSelection X)
    (fun rho =>
      TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho)

/-- The high-zone count is bounded by the full count up to height `X`. -/
theorem concreteHighImaginaryMultiplicityCount_le_countUpToHeight
    (X : Nat) :
    concreteHighImaginaryMultiplicityCount X <=
      concreteMultiplicityCountUpToHeight (X : Real) := by
  unfold concreteHighImaginaryMultiplicityCount
    concreteMultiplicityCountUpToHeight
  apply Finset.sum_le_sum_of_subset_of_nonneg
  case h =>
    intro rho hRho
    have hFull :=
      (TS269.Goldbach.mem_concreteHighImaginaryZeroSelection_iff X rho).mp
        hRho |>.1
    exact hFull
  case hf =>
    intro rho _ _
    exact Nat.zero_le _

/-- High-zone residual mass after removing the natural scale factor. -/
noncomputable def concreteHighImaginaryWeightedResidualMass
    (X : Nat) :
    Real :=
  Finset.sum
    (TS269.Goldbach.concreteHighImaginaryZeroSelection X)
    TS269.Goldbach.highImaginaryResidualEnvelope

/-- The high quadratic envelope is exactly scale times residual mass. -/
theorem concreteHighImaginaryQuadraticEnvelopeMass_eq_scale_mul_residualMass
    (X : Nat) :
    TS269.Goldbach.concreteHighImaginaryQuadraticEnvelopeMass X =
      max 1 (X : Real) * concreteHighImaginaryWeightedResidualMass X := by
  unfold TS269.Goldbach.concreteHighImaginaryQuadraticEnvelopeMass
    concreteHighImaginaryWeightedResidualMass
  exact
    (Finset.mul_sum
      (TS269.Goldbach.concreteHighImaginaryZeroSelection X)
      TS269.Goldbach.highImaginaryResidualEnvelope
      (max 1 (X : Real))).symm

/-- The high residual mass is nonnegative. -/
theorem concreteHighImaginaryWeightedResidualMass_nonnegative
    (X : Nat) :
    0 <= concreteHighImaginaryWeightedResidualMass X := by
  unfold concreteHighImaginaryWeightedResidualMass
  exact Finset.sum_nonneg fun rho _ =>
    TS269.Goldbach.highImaginaryResidualEnvelope_nonnegative rho

/-- Each high residual envelope is at most its multiplicity. -/
theorem highImaginaryResidualEnvelope_le_multiplicity
    (rho : Complex)
    (hHigh : 1 <= abs rho.im) :
    TS269.Goldbach.highImaginaryResidualEnvelope rho <=
      (TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho :
        Real) := by
  unfold TS269.Goldbach.highImaginaryResidualEnvelope
  apply div_le_self
  case ha =>
    exact Nat.cast_nonneg _
  case hb =>
    have hProduct :
        0 <= (abs rho.im - 1) * (abs rho.im + 1) :=
      mul_nonneg
        (sub_nonneg.mpr hHigh)
        (add_nonneg (abs_nonneg rho.im) zero_le_one)
    nlinarith

/-- Unconditional weighted-mass bound by exact high multiplicity count. -/
theorem concreteHighImaginaryWeightedResidualMass_le_multiplicityCount
    (X : Nat) :
    concreteHighImaginaryWeightedResidualMass X <=
      (concreteHighImaginaryMultiplicityCount X : Real) := by
  unfold concreteHighImaginaryWeightedResidualMass
    concreteHighImaginaryMultiplicityCount
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro rho hRho
  have hHigh :=
    (TS269.Goldbach.mem_concreteHighImaginaryZeroSelection_iff X rho).mp hRho |>.2
  exact highImaginaryResidualEnvelope_le_multiplicity rho hHigh

/-- A future effective upper bound for the exact high multiplicity count. -/
structure HighImaginaryMultiplicityCountingBoundContract
    (countBound : Nat -> Real) : Prop where
  countBound_nonnegative :
    forall X : Nat, 0 <= countBound X

  multiplicity_count_le :
    forall X : Nat,
      (concreteHighImaginaryMultiplicityCount X : Real) <= countBound X

/-- A global multiplicity-counting bound below every real height. -/
structure GlobalMultiplicityCountingBoundContract
    (countBound : Real -> Real) : Prop where
  countBound_nonnegative :
    forall T : Real, 0 <= countBound T

  multiplicity_count_le :
    forall T : Real,
      (concreteMultiplicityCountUpToHeight T : Real) <= countBound T

/-- The exact count itself satisfies the counting contract. -/
theorem exactHighImaginaryMultiplicityCountingBoundContract :
    HighImaginaryMultiplicityCountingBoundContract
      (fun X => (concreteHighImaginaryMultiplicityCount X : Real)) where
  countBound_nonnegative := fun _ => Nat.cast_nonneg _
  multiplicity_count_le := fun _ => le_rfl

/-- Every global multiplicity-counting bound supplies the high-zone contract. -/
theorem highImaginaryMultiplicityCountingBoundContract_of_global
    (countBound : Real -> Real)
    (hGlobal : GlobalMultiplicityCountingBoundContract countBound) :
    HighImaginaryMultiplicityCountingBoundContract
      (fun X => countBound (X : Real)) where
  countBound_nonnegative := fun X =>
    hGlobal.countBound_nonnegative (X : Real)
  multiplicity_count_le := fun X => by
    have hHighReal :
        (concreteHighImaginaryMultiplicityCount X : Real) <=
          (concreteMultiplicityCountUpToHeight (X : Real) : Real) := by
      exact_mod_cast
        concreteHighImaginaryMultiplicityCount_le_countUpToHeight X
    exact hHighReal.trans (hGlobal.multiplicity_count_le (X : Real))

/-- Any multiplicity-counting bound controls the high residual mass. -/
theorem concreteHighImaginaryWeightedResidualMass_le_countBound
    (countBound : Nat -> Real)
    (hCount : HighImaginaryMultiplicityCountingBoundContract countBound)
    (X : Nat) :
    concreteHighImaginaryWeightedResidualMass X <= countBound X :=
  (concreteHighImaginaryWeightedResidualMass_le_multiplicityCount X).trans
    (hCount.multiplicity_count_le X)

/-- Any multiplicity-counting bound controls the high quadratic mass. -/
theorem concreteHighImaginaryQuadraticEnvelopeMass_le_scale_mul_countBound
    (countBound : Nat -> Real)
    (hCount : HighImaginaryMultiplicityCountingBoundContract countBound)
    (X : Nat) :
    TS269.Goldbach.concreteHighImaginaryQuadraticEnvelopeMass X <=
      max 1 (X : Real) * countBound X := by
  rw [concreteHighImaginaryQuadraticEnvelopeMass_eq_scale_mul_residualMass]
  exact mul_le_mul_of_nonneg_left
    (concreteHighImaginaryWeightedResidualMass_le_countBound countBound hCount X)
    (zero_le_one.trans (le_max_left 1 (X : Real)))

/-- Final low-exact plus high-count bound for the real zero contribution. -/
theorem concreteFiniteHeightZeroContribution_abs_le_low_add_scale_mul_countBound
    (countBound : Nat -> Real)
    (hCount : HighImaginaryMultiplicityCountingBoundContract countBound)
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      TS269.Goldbach.concreteLowImaginaryWeightedNormMass X +
        max 1 (X : Real) * countBound X :=
  (TS269.Goldbach.concreteFiniteHeightZeroContribution_abs_le_low_add_highQuadratic X).trans
    (add_le_add_left
      (concreteHighImaginaryQuadraticEnvelopeMass_le_scale_mul_countBound
        countBound hCount X) _)

/-- A global height-counting bound controls the real zero contribution. -/
theorem concreteFiniteHeightZeroContribution_abs_le_of_globalMultiplicityCount
    (countBound : Real -> Real)
    (hGlobal : GlobalMultiplicityCountingBoundContract countBound)
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      TS269.Goldbach.concreteLowImaginaryWeightedNormMass X +
        max 1 (X : Real) * countBound (X : Real) :=
  concreteFiniteHeightZeroContribution_abs_le_low_add_scale_mul_countBound
    (fun Y => countBound (Y : Real))
    (highImaginaryMultiplicityCountingBoundContract_of_global
      countBound hGlobal)
    X

/-- At scale at least one, the natural factor is exactly `X`. -/
theorem concreteFiniteHeightZeroContribution_abs_le_low_add_natScale_mul_countBound
    (countBound : Nat -> Real)
    (hCount : HighImaginaryMultiplicityCountingBoundContract countBound)
    (X : Nat)
    (hX : 1 <= X) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      TS269.Goldbach.concreteLowImaginaryWeightedNormMass X +
        (X : Real) * countBound X := by
  have hOneReal : (1 : Real) <= (X : Real) := by
    exact_mod_cast hX
  simpa [max_eq_right hOneReal] using
    concreteFiniteHeightZeroContribution_abs_le_low_add_scale_mul_countBound
      countBound hCount X

/-- Exact-count specialization, requiring no analytic estimate. -/
theorem concreteFiniteHeightZeroContribution_abs_le_low_add_scale_mul_exactMultiplicityCount
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      TS269.Goldbach.concreteLowImaginaryWeightedNormMass X +
        max 1 (X : Real) *
          (concreteHighImaginaryMultiplicityCount X : Real) :=
  concreteFiniteHeightZeroContribution_abs_le_low_add_scale_mul_countBound
    (fun Y => (concreteHighImaginaryMultiplicityCount Y : Real))
    exactHighImaginaryMultiplicityCountingBoundContract
    X

/-- Ledger recording the TS270 multiplicity-counting interface. -/
structure HighZoneMultiplicityCountingInterfaceLedger where
  ts269_imaginary_square :
    TS269.Goldbach.ImaginarySquareDenominatorBoundLedger

  exact_multiplicity_count_up_to_height :
    Real -> Nat

  exact_high_multiplicity_count :
    Nat -> Nat

  high_weighted_mass_le_exact_count :
    forall X : Nat,
      concreteHighImaginaryWeightedResidualMass X <=
        (exact_high_multiplicity_count X : Real)

  generic_count_bound_transport :
    forall (countBound : Nat -> Real),
      HighImaginaryMultiplicityCountingBoundContract countBound ->
        forall X : Nat,
          abs
              (TS257.Goldbach.triangleSplineZeroContributionFunction
                TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
                TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
            TS269.Goldbach.concreteLowImaginaryWeightedNormMass X +
              max 1 (X : Real) * countBound X

  global_count_bound_transport :
    forall (countBound : Real -> Real),
      GlobalMultiplicityCountingBoundContract countBound ->
        forall X : Nat,
          abs
              (TS257.Goldbach.triangleSplineZeroContributionFunction
                TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
                TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
            TS269.Goldbach.concreteLowImaginaryWeightedNormMass X +
              max 1 (X : Real) * countBound (X : Real)

  low_zone_exclusion_not_proved : True
  effective_multiplicity_count_not_proved : True
  zero_counting_asymptotic_not_proved : True
  zero_density_theorem_not_proved : True
  global_weighted_zero_summability_not_proved : True
  explicit_formula_identity_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS270 multiplicity-counting ledger. -/
noncomputable def highZoneMultiplicityCountingInterfaceLedger :
    HighZoneMultiplicityCountingInterfaceLedger where
  ts269_imaginary_square :=
    TS269.Goldbach.imaginarySquareDenominatorBoundLedger
  exact_multiplicity_count_up_to_height :=
    concreteMultiplicityCountUpToHeight
  exact_high_multiplicity_count :=
    concreteHighImaginaryMultiplicityCount
  high_weighted_mass_le_exact_count :=
    concreteHighImaginaryWeightedResidualMass_le_multiplicityCount
  generic_count_bound_transport :=
    concreteFiniteHeightZeroContribution_abs_le_low_add_scale_mul_countBound
  global_count_bound_transport :=
    concreteFiniteHeightZeroContribution_abs_le_of_globalMultiplicityCount
  low_zone_exclusion_not_proved := True.intro
  effective_multiplicity_count_not_proved := True.intro
  zero_counting_asymptotic_not_proved := True.intro
  zero_density_theorem_not_proved := True.intro
  global_weighted_zero_summability_not_proved := True.intro
  explicit_formula_identity_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS270. -/
def HighZoneMultiplicityCountingInterfaceTarget : Prop :=
  Nonempty HighZoneMultiplicityCountingInterfaceLedger

/-- TS270 target: exact and generic multiplicity counting are connected. -/
theorem highZoneMultiplicityCountingInterfaceTarget :
    HighZoneMultiplicityCountingInterfaceTarget :=
  Nonempty.intro highZoneMultiplicityCountingInterfaceLedger

end Goldbach
end TS270
