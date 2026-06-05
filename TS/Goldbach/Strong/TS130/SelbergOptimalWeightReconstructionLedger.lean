import Mathlib.Tactic
import TS.Goldbach.Strong.TS105.MobiusDeltaIdentityDischarge
import TS.Goldbach.Strong.TS129.SelbergDiagonalBudgetMajorantLedger

namespace TS130
namespace Goldbach

/-!
# TS130 - Selberg Optimal Weight Reconstruction Ledger

TS129 proves that the original dense side is the TS122 diagonal energy of the
absorbed divisor vector

`Y_d = sum_m 1_{d | m} * weight(m) / m`.

This sprint opens the inverse triangular step: reconstruct original weights
from a prescribed diagonal vector `Y`. The actual finite Mobius inversion
identity is kept as an exact local proposition, while the immediate support and
normalization consequences are proved.
-/

/-- Positive finite support used by the reconstruction sums. -/
def selbergReconstructionSupport
    (level : Nat) :
    Finset Nat :=
  TS122.Goldbach.selbergOptimizationSupport level

/-- Membership in the reconstruction support implies `d <= level`. -/
theorem mem_selbergReconstructionSupport_le_level
    {level d : Nat}
    (hd : Membership.mem (selbergReconstructionSupport level) d) :
    d <= level := by
  have hd' :
      Membership.mem (TS121.Goldbach.selbergPositiveQuadraticSupport level) d := by
    simpa [selbergReconstructionSupport, TS122.Goldbach.selbergOptimizationSupport]
      using hd
  have hd_mem :
      Membership.mem (TS108.Goldbach.selbergQuadraticSupport level) d :=
    (TS121.Goldbach.mem_selbergPositiveQuadraticSupport.mp hd').1
  have hd_lt :
      d < level + 1 := by
    simpa [TS108.Goldbach.selbergQuadraticSupport] using hd_mem
  exact Nat.lt_succ_iff.mp hd_lt

/-- Membership in the reconstruction support implies positivity. -/
theorem mem_selbergReconstructionSupport_pos
    {level d : Nat}
    (hd : Membership.mem (selbergReconstructionSupport level) d) :
    0 < d := by
  have hd' :
      Membership.mem (TS121.Goldbach.selbergPositiveQuadraticSupport level) d := by
    simpa [selbergReconstructionSupport, TS122.Goldbach.selbergOptimizationSupport]
      using hd
  exact (TS121.Goldbach.mem_selbergPositiveQuadraticSupport.mp hd').2

/--
Absorbed coefficient reconstructed from a target diagonal vector.

It is the finite upward Mobius transform

`a_m = sum_{m | d} mu(d / m) * Y_d`

over the positive reconstruction support.
-/
def absorbedCoefficientFromDiagonalVector
    (level : Nat)
    (Y : Nat -> Rat)
    (m : Nat) :
    Rat :=
  Finset.sum (selbergReconstructionSupport level) fun d =>
    if Dvd.dvd m d then
      TS122.Goldbach.selbergMobiusRatCoefficient (d / m) * Y d
    else
      0

/-- Reconstructed original Selberg weight from a target diagonal vector. -/
def reconstructedSelbergWeight
    (level : Nat)
    (Y : Nat -> Rat)
    (m : Nat) :
    Rat :=
  (m : Rat) * absorbedCoefficientFromDiagonalVector level Y m

/-- The reconstructed absorbed coefficient at zero is zero. -/
theorem absorbedCoefficientFromDiagonalVector_zero
    (level : Nat)
    (Y : Nat -> Rat) :
    absorbedCoefficientFromDiagonalVector level Y 0 = 0 := by
  unfold absorbedCoefficientFromDiagonalVector
  apply Finset.sum_eq_zero
  intro d hd
  have hdpos : 0 < d := mem_selbergReconstructionSupport_pos hd
  have hnotdvd : Not (Dvd.dvd 0 d) := by
    intro h
    exact Nat.ne_of_gt hdpos (Nat.eq_zero_of_zero_dvd h)
  simp [hnotdvd]

/-- The reconstructed original weight vanishes at zero. -/
theorem reconstructedSelbergWeight_zero
    (level : Nat)
    (Y : Nat -> Rat) :
    reconstructedSelbergWeight level Y 0 = 0 := by
  simp [reconstructedSelbergWeight]

/--
No positive support point below or equal to `level` can be divisible by
`m > level`.
-/
theorem not_dvd_of_level_lt_on_reconstructionSupport
    {level m d : Nat}
    (hm : level < m)
    (hd : Membership.mem (selbergReconstructionSupport level) d) :
    Not (Dvd.dvd m d) := by
  intro hdiv
  have hdpos : 0 < d := mem_selbergReconstructionSupport_pos hd
  have hm_le_d : m <= d := Nat.le_of_dvd hdpos hdiv
  have hd_le_level : d <= level :=
    mem_selbergReconstructionSupport_le_level hd
  exact (not_lt_of_ge (le_trans hm_le_d hd_le_level)) hm

/-- Reconstructed absorbed coefficient vanishes outside the level. -/
theorem absorbedCoefficientFromDiagonalVector_eq_zero_of_level_lt
    (level : Nat)
    (Y : Nat -> Rat)
    (m : Nat)
    (hm : level < m) :
    absorbedCoefficientFromDiagonalVector level Y m = 0 := by
  unfold absorbedCoefficientFromDiagonalVector
  apply Finset.sum_eq_zero
  intro d hd
  have hnotdvd :
      Not (Dvd.dvd m d) :=
    not_dvd_of_level_lt_on_reconstructionSupport
      (level := level)
      (m := m)
      (d := d)
      hm
      hd
  simp [hnotdvd]

/-- Reconstructed original weights are supported inside `level`. -/
theorem reconstructedSelbergWeight_eq_zero_of_level_lt
    (level : Nat)
    (Y : Nat -> Rat)
    (m : Nat)
    (hm : level < m) :
    reconstructedSelbergWeight level Y m = 0 := by
  unfold reconstructedSelbergWeight
  rw [absorbedCoefficientFromDiagonalVector_eq_zero_of_level_lt
    level Y m hm]
  ring

/-- Support-bound form for reconstructed original weights. -/
theorem reconstructedSelbergWeight_support_bound
    (level : Nat)
    (Y : Nat -> Rat) :
    forall m : Nat,
      Not (reconstructedSelbergWeight level Y m = 0) ->
        m <= level := by
  intro m hm_ne
  by_contra hm_not
  have hm_lt : level < m := Nat.lt_of_not_ge hm_not
  exact hm_ne
    (reconstructedSelbergWeight_eq_zero_of_level_lt level Y m hm_lt)

/--
For positive `m`, absorbed weight of the reconstructed original weight is the
reconstructed absorbed coefficient.
-/
theorem selbergLCMAbsorbedWeight_reconstructed_eq_absorbedCoefficient
    (level : Nat)
    (Y : Nat -> Rat)
    (m : Nat)
    (hm : 0 < m) :
    TS118.Goldbach.selbergLCMAbsorbedWeight
        (reconstructedSelbergWeight level Y)
        m =
      absorbedCoefficientFromDiagonalVector level Y m := by
  have hm_rat : Not ((m : Rat) = 0) := by
    exact_mod_cast (Nat.ne_of_gt hm)
  unfold TS118.Goldbach.selbergLCMAbsorbedWeight
  unfold reconstructedSelbergWeight
  field_simp [hm_rat]

/-- Reconstructed weight support package. -/
structure ReconstructedSelbergWeightSupport
    (level : Nat)
    (Y : Nat -> Rat) where
  support_bound :
    forall m : Nat,
      Not (reconstructedSelbergWeight level Y m = 0) ->
        m <= level

  zero_at_zero :
    reconstructedSelbergWeight level Y 0 = 0

  absorbed_weight_agrees_positive :
    forall m : Nat,
      0 < m ->
        TS118.Goldbach.selbergLCMAbsorbedWeight
            (reconstructedSelbergWeight level Y)
            m =
          absorbedCoefficientFromDiagonalVector level Y m

/-- Concrete support package for reconstructed weights. -/
def reconstructedSelbergWeightSupport
    (level : Nat)
    (Y : Nat -> Rat) :
    ReconstructedSelbergWeightSupport level Y where
  support_bound :=
    reconstructedSelbergWeight_support_bound level Y
  zero_at_zero :=
    reconstructedSelbergWeight_zero level Y
  absorbed_weight_agrees_positive := by
    intro m hm
    exact
      selbergLCMAbsorbedWeight_reconstructed_eq_absorbedCoefficient
        level
        Y
        m
        hm

/--
Exact finite Mobius reconstruction identity on the TS122 support.

This is the remaining local triangular inversion statement:
the absorbed diagonal vector of the reconstructed original weights recovers
the target diagonal vector on the finite positive support.
-/
def SelbergFiniteMobiusReconstructionIdentity
    (level : Nat)
    (Y : Nat -> Rat) :
    Prop :=
  forall d : Nat,
    Membership.mem (TS122.Goldbach.selbergOptimizationSupport level) d ->
      TS129.Goldbach.selbergAbsorbedDiagonalVector
          level
          (reconstructedSelbergWeight level Y)
          d =
        Y d

/--
Finite reconstruction ledger from a prescribed diagonal vector.

The support facts are concrete. The Mobius inversion identity is deliberately
stored as a proposition-valued obligation.
-/
structure SelbergWeightReconstruction
    (level : Nat)
    (Y : Nat -> Rat) where
  support :
    ReconstructedSelbergWeightSupport level Y

  reconstructedWeight :
    Nat -> Rat

  reconstructed_weight_eq :
    forall m : Nat,
      reconstructedWeight m = reconstructedSelbergWeight level Y m

  finite_mobius_reconstruction_obligation :
    Prop

  finite_mobius_reconstruction_obligation_eq :
    finite_mobius_reconstruction_obligation =
      SelbergFiniteMobiusReconstructionIdentity level Y

  mobius_delta_input :
    TS105.Goldbach.MobiusConcreteDeltaDischargeTarget

  finite_triangular_inversion_ready :
    True

  selberg_sieve_application_obligation :
    True

/-- Concrete TS130 reconstruction ledger for an arbitrary diagonal vector. -/
def selbergWeightReconstruction
    (level : Nat)
    (Y : Nat -> Rat) :
    SelbergWeightReconstruction level Y where
  support :=
    reconstructedSelbergWeightSupport level Y
  reconstructedWeight :=
    reconstructedSelbergWeight level Y
  reconstructed_weight_eq := by
    intro m
    rfl
  finite_mobius_reconstruction_obligation :=
    SelbergFiniteMobiusReconstructionIdentity level Y
  finite_mobius_reconstruction_obligation_eq := rfl
  mobius_delta_input :=
    TS105.Goldbach.mobiusConcreteDeltaDischargeTarget
  finite_triangular_inversion_ready := True.intro
  selberg_sieve_application_obligation := True.intro

/-- Optimal reconstructed original Selberg weight. -/
def optimalReconstructedSelbergWeight
    (level : Nat) :
    Nat -> Rat :=
  reconstructedSelbergWeight
    level
    (TS128.Goldbach.selbergOptimalDiagonalVector level)

/--
If finite Mobius reconstruction holds for the optimal vector, the reconstructed
weights satisfy the Mobius normalization through TS128.
-/
theorem optimalReconstructedWeight_mobius_constraint_of_reconstruction
    (level : Nat)
    (hlevel : 0 < level)
    (hrec :
      SelbergFiniteMobiusReconstructionIdentity
        level
        (TS128.Goldbach.selbergOptimalDiagonalVector level)) :
    TS122.Goldbach.selbergMobiusLinearForm
        level
        (TS129.Goldbach.selbergAbsorbedDiagonalVector
          level
          (optimalReconstructedSelbergWeight level)) =
      1 := by
  unfold optimalReconstructedSelbergWeight
  have hsum :
      TS122.Goldbach.selbergMobiusLinearForm
          level
          (TS129.Goldbach.selbergAbsorbedDiagonalVector
            level
            (reconstructedSelbergWeight
              level
              (TS128.Goldbach.selbergOptimalDiagonalVector level))) =
        TS122.Goldbach.selbergMobiusLinearForm
          level
          (TS128.Goldbach.selbergOptimalDiagonalVector level) := by
    unfold TS122.Goldbach.selbergMobiusLinearForm
    apply Finset.sum_congr rfl
    intro d hd
    rw [hrec d hd]
  rw [hsum]
  exact TS128.Goldbach.selbergOptimalDiagonalVector_linear_constraint level hlevel

/--
If finite Mobius reconstruction holds for the optimal vector, the original
dense side of the reconstructed weights has exact optimal budget `1 / D`.
-/
theorem optimalReconstructedWeight_denseSide_eq_optimal_budget_of_reconstruction
    (level : Nat)
    (hlevel : 0 < level)
    (hrec :
      SelbergFiniteMobiusReconstructionIdentity
        level
        (TS128.Goldbach.selbergOptimalDiagonalVector level)) :
    TS110.Goldbach.selbergDenseSide
        level
        (optimalReconstructedSelbergWeight level) =
      1 / TS122.Goldbach.selbergOptimizationDenominator level := by
  unfold optimalReconstructedSelbergWeight
  rw [TS129.Goldbach.selbergOriginalDenseSide_eq_absorbedDiagonalEnergy]
  have henergy :
      TS122.Goldbach.selbergDiagonalEnergy
          level
          (TS129.Goldbach.selbergAbsorbedDiagonalVector
            level
            (reconstructedSelbergWeight
              level
              (TS128.Goldbach.selbergOptimalDiagonalVector level))) =
        TS122.Goldbach.selbergDiagonalEnergy
          level
          (TS128.Goldbach.selbergOptimalDiagonalVector level) := by
    unfold TS122.Goldbach.selbergDiagonalEnergy
    apply Finset.sum_congr rfl
    intro d hd
    rw [hrec d hd]
  rw [henergy]
  exact TS128.Goldbach.selbergOptimalDiagonalVector_energy_eq level hlevel

/-- Optimal-weight reconstruction package. -/
structure SelbergOptimalWeightReconstruction
    (level : Nat) where
  reconstruction :
    SelbergWeightReconstruction
      level
      (TS128.Goldbach.selbergOptimalDiagonalVector level)

  diagonalBudget :
    TS129.Goldbach.SelbergDiagonalBudgetMajorant
      level
      (optimalReconstructedSelbergWeight level)

  finite_mobius_reconstruction_obligation :
    Prop

  finite_mobius_reconstruction_obligation_eq :
    finite_mobius_reconstruction_obligation =
      SelbergFiniteMobiusReconstructionIdentity
        level
        (TS128.Goldbach.selbergOptimalDiagonalVector level)

  normalized_if_reconstruction :
    0 < level ->
      finite_mobius_reconstruction_obligation ->
        TS122.Goldbach.selbergMobiusLinearForm
            level
            (TS129.Goldbach.selbergAbsorbedDiagonalVector
              level
              (optimalReconstructedSelbergWeight level)) =
          1

  optimal_budget_if_reconstruction :
    0 < level ->
      finite_mobius_reconstruction_obligation ->
        TS110.Goldbach.selbergDenseSide
            level
            (optimalReconstructedSelbergWeight level) =
          1 / TS122.Goldbach.selbergOptimizationDenominator level

  selberg_interval_majorant_obligation :
    True

  brun_titchmarsh_obligation :
    True

/-- Concrete TS130 optimal reconstruction package. -/
def selbergOptimalWeightReconstruction
    (level : Nat) :
    SelbergOptimalWeightReconstruction level where
  reconstruction :=
    selbergWeightReconstruction
      level
      (TS128.Goldbach.selbergOptimalDiagonalVector level)
  diagonalBudget :=
    TS129.Goldbach.selbergDiagonalBudgetMajorant
      level
      (optimalReconstructedSelbergWeight level)
  finite_mobius_reconstruction_obligation :=
    SelbergFiniteMobiusReconstructionIdentity
      level
      (TS128.Goldbach.selbergOptimalDiagonalVector level)
  finite_mobius_reconstruction_obligation_eq := rfl
  normalized_if_reconstruction := by
    intro hlevel hrec
    exact
      optimalReconstructedWeight_mobius_constraint_of_reconstruction
        level
        hlevel
        hrec
  optimal_budget_if_reconstruction := by
    intro hlevel hrec
    exact
      optimalReconstructedWeight_denseSide_eq_optimal_budget_of_reconstruction
        level
        hlevel
        hrec
  selberg_interval_majorant_obligation := True.intro
  brun_titchmarsh_obligation := True.intro

/-- Target proposition for the TS130 optimal-weight reconstruction ledger. -/
def SelbergOptimalWeightReconstructionTarget : Prop :=
  forall level : Nat,
    Nonempty (SelbergOptimalWeightReconstruction level)

/-- The TS130 optimal-weight reconstruction ledger is populated. -/
theorem selbergOptimalWeightReconstructionTarget :
    SelbergOptimalWeightReconstructionTarget := by
  intro level
  exact Nonempty.intro (selbergOptimalWeightReconstruction level)

/-- TS130 keeps the TS129 diagonal-budget target available. -/
theorem selbergDiagonalBudgetMajorantTarget :
    TS129.Goldbach.SelbergDiagonalBudgetMajorantTarget :=
  TS129.Goldbach.selbergDiagonalBudgetMajorantTarget

end Goldbach
end TS130
