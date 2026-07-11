import Mathlib.Tactic
import TS.Goldbach.Strong.TS272.HighZoneIntegerShellCover

/-!
# TS273 - Log-Linear Multiplicity Counting Reduction

TS272 transports every TS270 global multiplicity-counting bound to the full
finite zero contribution while retaining reciprocal-square Abel damping.  This
sprint gives the first analytically meaningful shape for that missing input:

`N_mult(T) <= C * T * log (T + 2)` for `T >= 1`.

The bound is extended safely to every real height by replacing `T` with
`max T 1`.  Monotonicity of the exact multiplicity count handles heights below
one, so no low-zero exclusion is assumed.  A second interface isolates the
future Jensen-disk route without claiming that the locked Mathlib revision
already contains Jensen's formula or a concrete Riemann xi function.

No counting estimate is proved here.  No Riemann Hypothesis, zero-density
theorem, infinite convergence, explicit formula, residual bound, Gallagher
estimate, OTSA bridge, or Goldbach statement is used or proved.
-/

namespace TS273
namespace Goldbach

/-- Global log-linear envelope, safely frozen at height one below the cutoff. -/
noncomputable def logLinearMultiplicityCountEnvelope
    (C T : Real) :
    Real :=
  C * max T 1 * Real.log (max T 1 + 2)

/-- The log-linear envelope is nonnegative for every real height. -/
theorem logLinearMultiplicityCountEnvelope_nonnegative
    (C : Real)
    (hC : 0 <= C)
    (T : Real) :
    0 <= logLinearMultiplicityCountEnvelope C T := by
  have hMax : 1 <= max T 1 := le_max_right T 1
  have hMaxNonnegative : 0 <= max T 1 := zero_le_one.trans hMax
  have hLogArgument : 1 <= max T 1 + 2 := by
    linarith
  unfold logLinearMultiplicityCountEnvelope
  exact mul_nonneg
    (mul_nonneg hC hMaxNonnegative)
    (Real.log_nonneg hLogArgument)

/-- The exact multiplicity-counting function is monotone in height. -/
theorem concreteMultiplicityCountUpToHeight_monotone
    {A B : Real}
    (hAB : A <= B) :
    TS270.Goldbach.concreteMultiplicityCountUpToHeight A <=
      TS270.Goldbach.concreteMultiplicityCountUpToHeight B := by
  unfold TS270.Goldbach.concreteMultiplicityCountUpToHeight
  apply Finset.sum_le_sum_of_subset_of_nonneg
  case h =>
    exact TS271.Goldbach.zerosUpToHeight_subset hAB
  case hf =>
    intro rho _ _
    exact Nat.zero_le _

/-- The analytically relevant counting estimate above height one. -/
structure LargeHeightLogLinearMultiplicityCountEstimate where
  C : Real

  C_nonnegative :
    0 <= C

  multiplicity_count_le :
    forall T : Real,
      1 <= T ->
        (TS270.Goldbach.concreteMultiplicityCountUpToHeight T : Real) <=
          C * T * Real.log (T + 2)

/-- A future disk-counting route, designed for a Jensen inequality backport. -/
structure JensenDiskMultiplicityCountingInput where
  C : Real

  C_nonnegative :
    0 <= C

  diskMultiplicityCount :
    Real -> Nat

  height_count_le_disk :
    forall T : Real,
      1 <= T ->
        (TS270.Goldbach.concreteMultiplicityCountUpToHeight T : Real) <=
          (diskMultiplicityCount (T + 2) : Real)

  disk_count_le_logLinear :
    forall R : Real,
      3 <= R ->
        (diskMultiplicityCount R : Real) <=
          C * (R - 2) * Real.log R

/-- A Jensen-disk input supplies the large-height log-linear estimate. -/
noncomputable def largeHeightLogLinearEstimate_of_jensenDiskInput
    (J : JensenDiskMultiplicityCountingInput) :
    LargeHeightLogLinearMultiplicityCountEstimate where
  C := J.C
  C_nonnegative := J.C_nonnegative
  multiplicity_count_le := by
    intro T hT
    have hRadius : 3 <= T + 2 := by
      linarith
    calc
      (TS270.Goldbach.concreteMultiplicityCountUpToHeight T : Real) <=
          (J.diskMultiplicityCount (T + 2) : Real) :=
        J.height_count_le_disk T hT
      _ <= J.C * ((T + 2) - 2) * Real.log (T + 2) :=
        J.disk_count_le_logLinear (T + 2) hRadius
      _ = J.C * T * Real.log (T + 2) := by
        ring

/-- Extend a large-height estimate to the full TS270 global contract. -/
theorem largeHeightLogLinearEstimate_implies_globalContract
    (H : LargeHeightLogLinearMultiplicityCountEstimate) :
    TS270.Goldbach.GlobalMultiplicityCountingBoundContract
      (logLinearMultiplicityCountEnvelope H.C) where
  countBound_nonnegative :=
    logLinearMultiplicityCountEnvelope_nonnegative H.C H.C_nonnegative
  multiplicity_count_le := by
    intro T
    by_cases hT : 1 <= T
    case pos =>
      simpa [logLinearMultiplicityCountEnvelope, max_eq_left hT] using
        H.multiplicity_count_le T hT
    case neg =>
      have hTle : T <= 1 := le_of_not_ge hT
      have hMonoNat := concreteMultiplicityCountUpToHeight_monotone hTle
      have hMonoReal :
          (TS270.Goldbach.concreteMultiplicityCountUpToHeight T : Real) <=
            (TS270.Goldbach.concreteMultiplicityCountUpToHeight 1 : Real) := by
        exact_mod_cast hMonoNat
      have hAtOne := H.multiplicity_count_le 1 le_rfl
      simpa [logLinearMultiplicityCountEnvelope, max_eq_right hTle] using
        hMonoReal.trans hAtOne

/-- Log-linear specialization of the TS272 amortized integer-shell bound. -/
noncomputable def logLinearAmortizedMultiplicityCountBound
    (H : LargeHeightLogLinearMultiplicityCountEstimate)
    (X : Nat) :
    Real :=
  TS272.Goldbach.shiftedIntegerAmortizedCountBound
    (logLinearMultiplicityCountEnvelope H.C)
    X

/-- Full finite zero-contribution bound under the large-height estimate. -/
theorem concreteFiniteHeightZeroContribution_abs_le_of_largeHeightLogLinear
    (H : LargeHeightLogLinearMultiplicityCountEstimate)
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      TS269.Goldbach.concreteLowImaginaryWeightedNormMass X +
        max 1 (X : Real) *
          (logLinearMultiplicityCountEnvelope H.C 1 +
            logLinearAmortizedMultiplicityCountBound H X) := by
  exact
    TS272.Goldbach.concreteFiniteHeightZeroContribution_abs_le_low_add_globalCountAmortized
      (logLinearMultiplicityCountEnvelope H.C)
      (largeHeightLogLinearEstimate_implies_globalContract H)
      X

/-- Jensen-disk specialization of the TS272 full finite zero bound. -/
theorem concreteFiniteHeightZeroContribution_abs_le_of_jensenDiskInput
    (J : JensenDiskMultiplicityCountingInput)
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      TS269.Goldbach.concreteLowImaginaryWeightedNormMass X +
        max 1 (X : Real) *
          (logLinearMultiplicityCountEnvelope J.C 1 +
            logLinearAmortizedMultiplicityCountBound
              (largeHeightLogLinearEstimate_of_jensenDiskInput J) X) := by
  exact concreteFiniteHeightZeroContribution_abs_le_of_largeHeightLogLinear
    (largeHeightLogLinearEstimate_of_jensenDiskInput J)
    X

/-- Ledger recording the TS273 log-linear counting reduction. -/
structure LogLinearMultiplicityCountingReductionLedger where
  ts272_integer_shell_cover :
    TS272.Goldbach.HighZoneIntegerShellCoverLedger

  count_monotonicity :
    forall (A B : Real),
      A <= B ->
        TS270.Goldbach.concreteMultiplicityCountUpToHeight A <=
          TS270.Goldbach.concreteMultiplicityCountUpToHeight B

  jensen_disk_to_large_height :
    JensenDiskMultiplicityCountingInput ->
      LargeHeightLogLinearMultiplicityCountEstimate

  large_height_to_global_contract :
    forall H : LargeHeightLogLinearMultiplicityCountEstimate,
      TS270.Goldbach.GlobalMultiplicityCountingBoundContract
        (logLinearMultiplicityCountEnvelope H.C)

  large_height_to_full_zero_bound :
    forall (H : LargeHeightLogLinearMultiplicityCountEstimate) (X : Nat),
      abs
          (TS257.Goldbach.triangleSplineZeroContributionFunction
            TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
            TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
        TS269.Goldbach.concreteLowImaginaryWeightedNormMass X +
          max 1 (X : Real) *
            (logLinearMultiplicityCountEnvelope H.C 1 +
              logLinearAmortizedMultiplicityCountBound H X)

  locked_mathlib_jensen_backport_not_proved : True
  riemann_xi_not_constructed : True
  xi_entire_not_proved : True
  xi_divisor_identification_not_proved : True
  circle_growth_bound_not_proved : True
  effective_log_linear_constant_not_proved : True
  infinite_shell_convergence_not_proved : True
  global_weighted_zero_summability_not_proved : True
  explicit_formula_identity_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS273 log-linear counting ledger. -/
noncomputable def logLinearMultiplicityCountingReductionLedger :
    LogLinearMultiplicityCountingReductionLedger where
  ts272_integer_shell_cover :=
    TS272.Goldbach.highZoneIntegerShellCoverLedger
  count_monotonicity :=
    fun _ _ hAB => concreteMultiplicityCountUpToHeight_monotone hAB
  jensen_disk_to_large_height :=
    largeHeightLogLinearEstimate_of_jensenDiskInput
  large_height_to_global_contract :=
    largeHeightLogLinearEstimate_implies_globalContract
  large_height_to_full_zero_bound :=
    concreteFiniteHeightZeroContribution_abs_le_of_largeHeightLogLinear
  locked_mathlib_jensen_backport_not_proved := True.intro
  riemann_xi_not_constructed := True.intro
  xi_entire_not_proved := True.intro
  xi_divisor_identification_not_proved := True.intro
  circle_growth_bound_not_proved := True.intro
  effective_log_linear_constant_not_proved := True.intro
  infinite_shell_convergence_not_proved := True.intro
  global_weighted_zero_summability_not_proved := True.intro
  explicit_formula_identity_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS273. -/
def LogLinearMultiplicityCountingReductionTarget : Prop :=
  Nonempty LogLinearMultiplicityCountingReductionLedger

/-- TS273 target: global counting is reduced to a log-linear estimate. -/
theorem logLinearMultiplicityCountingReductionTarget :
    LogLinearMultiplicityCountingReductionTarget :=
  Nonempty.intro logLinearMultiplicityCountingReductionLedger

end Goldbach
end TS273
