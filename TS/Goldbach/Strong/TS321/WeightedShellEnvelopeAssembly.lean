import Mathlib.Tactic
import TS.Goldbach.Strong.TS320.UniformDiscreteKusminLandauBound

namespace TS321
namespace Goldbach

noncomputable section

/-!
# TS321: weighted shell envelope assembly

This module partitions the exact finite TS317 pair envelope into the close
regime and disjoint unit gap shells.  It keeps separate the unweighted
coefficient mass in a shell and the same mass carrying the TS317 gap-decay
weight.  On shell `(k,k+1]`, `k >= 1`, the latter is at most `1/k` times the
former.

The shell index is `Nat.ceil gap - 1`; this convention handles integral gaps
and gives the exact half-open intervals required by the estimate.  The module
then packages local coefficient-mass bounds into the existing TS317 global
envelope contract.

No local zero-density estimate, pair-correlation hypothesis, minimal zero
spacing, rational half-budget, RH, OTSA, or Goldbach conclusion is introduced.
-/

abbrev ConcreteNontrivialZero := TS292.Goldbach.ConcreteNontrivialZero

/-- Product of the exact TS316 coefficient magnitudes; multiplicities are
already included in both factors. -/
noncomputable def zeroPairCoefficientMass
    (rho sigma : ConcreteNontrivialZero) : Real :=
  TS316.Goldbach.zeroCoefficientMagnitude rho *
    TS316.Goldbach.zeroCoefficientMagnitude sigma

/-! ## Exact close and shell masses -/

/-- Coefficient mass of pairs whose ordinate gap is at most one. -/
noncomputable def weightedNearPairCoefficientMass (T : Nat) : Real :=
  Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
    Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho) (fun sigma =>
      if TS317.Goldbach.zeroOrdinateGap rho sigma <= 1 then
        zeroPairCoefficientMass rho sigma
      else 0))

/-- Coefficient mass in the half-open gap shell `(k,k+1]`. -/
noncomputable def weightedGapShellCoefficientMass
    (T k : Nat) : Real :=
  Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
    Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho) (fun sigma =>
      let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
      if (k : Real) < gap /\ gap <= (k : Real) + 1 then
        zeroPairCoefficientMass rho sigma
      else 0))

/-- Gap-weighted envelope mass in the half-open shell `(k,k+1]`. -/
noncomputable def weightedGapShellEnvelopeMass
    (T k : Nat) : Real :=
  Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
    Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho) (fun sigma =>
      let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
      if (k : Real) < gap /\ gap <= (k : Real) + 1 then
        zeroPairCoefficientMass rho sigma *
          TS317.Goldbach.ordinateGapDecayWeight rho sigma
      else 0))

/-- Canonical shell index for a real gap greater than one. -/
noncomputable def gapShellIndex (gap : Real) : Nat :=
  Nat.ceil gap - 1

theorem gapShellIndex_spec
    {gap : Real} (hGap : 1 < gap) :
    (gapShellIndex gap : Real) < gap /\
      gap <= (gapShellIndex gap : Real) + 1 := by
  have hCeilTwo : 2 <= Nat.ceil gap := by
    rw [Nat.add_one_le_ceil_iff]
    norm_num
    exact hGap
  have hCeilPos : 0 < Nat.ceil gap := by omega
  have hIndexSucc : gapShellIndex gap + 1 = Nat.ceil gap := by
    unfold gapShellIndex
    omega
  constructor
  case left =>
    rw [<- Nat.lt_ceil]
    omega
  case right =>
    rw [<- Nat.cast_one, <- Nat.cast_add, hIndexSucc]
    exact Nat.le_ceil gap

theorem gapShellIndex_mem
    {gap : Real} {T : Nat} (hGap : 1 < gap)
    (hGapUpper : gap <= 2 * (T : Real)) :
    Membership.mem (Finset.Ico 1 (2 * T)) (gapShellIndex gap) := by
  rw [Finset.mem_Ico]
  have hCeilTwo : 2 <= Nat.ceil gap := by
    rw [Nat.add_one_le_ceil_iff]
    norm_num
    exact hGap
  have hCeilUpper : Nat.ceil gap <= 2 * T := by
    rw [Nat.ceil_le]
    exact_mod_cast hGapUpper
  unfold gapShellIndex
  omega

theorem gapShellIndex_unique
    {gap : Real} {k : Nat}
    (hkLower : (k : Real) < gap)
    (hkUpper : gap <= (k : Real) + 1) :
    k = gapShellIndex gap := by
  have hGapPos : 0 < gap :=
    lt_of_le_of_lt (Nat.cast_nonneg k) hkLower
  have hCeilPos : 0 < Nat.ceil gap := Nat.ceil_pos.mpr hGapPos
  have hkLtCeil : k < Nat.ceil gap := Nat.lt_ceil.mpr hkLower
  have hCeilLe : Nat.ceil gap <= k + 1 := by
    rw [Nat.ceil_le]
    exact_mod_cast hkUpper
  unfold gapShellIndex
  omega

theorem zeroOrdinateGap_le_two_mul_height
    (T : Nat) (rho sigma : ConcreteNontrivialZero)
    (hRho : Membership.mem (TS315.Goldbach.truncatedZeroSet T) rho)
    (hSigma : Membership.mem
      ((TS315.Goldbach.truncatedZeroSet T).erase rho) sigma) :
    TS317.Goldbach.zeroOrdinateGap rho sigma <= 2 * (T : Real) := by
  simpa [TS317.Goldbach.zeroOrdinateGap,
    TS318.Goldbach.offDiagonalFrequency] using
      TS318.Goldbach.offDiagonalFrequency_abs_le_two_mul_height
        T rho sigma hRho hSigma

theorem ordinateGapDecayWeight_eq_one_of_le_one
    (rho sigma : ConcreteNontrivialZero)
    (hGap : TS317.Goldbach.zeroOrdinateGap rho sigma <= 1) :
    TS317.Goldbach.ordinateGapDecayWeight rho sigma = 1 := by
  unfold TS317.Goldbach.ordinateGapDecayWeight
  rw [max_eq_left hGap]
  norm_num

theorem pairEnvelopeTerm_eq_near_add_shells
    (T : Nat) (rho sigma : ConcreteNontrivialZero)
    (hRho : Membership.mem (TS315.Goldbach.truncatedZeroSet T) rho)
    (hSigma : Membership.mem
      ((TS315.Goldbach.truncatedZeroSet T).erase rho) sigma) :
    zeroPairCoefficientMass rho sigma *
        TS317.Goldbach.ordinateGapDecayWeight rho sigma =
      (if TS317.Goldbach.zeroOrdinateGap rho sigma <= 1 then
        zeroPairCoefficientMass rho sigma
      else 0) +
        Finset.sum (Finset.Ico 1 (2 * T)) (fun k =>
          let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
          if (k : Real) < gap /\ gap <= (k : Real) + 1 then
            zeroPairCoefficientMass rho sigma *
              TS317.Goldbach.ordinateGapDecayWeight rho sigma
          else 0) := by
  let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
  by_cases hNear : gap <= 1
  case pos =>
    have hWeight :
        TS317.Goldbach.ordinateGapDecayWeight rho sigma = 1 :=
      ordinateGapDecayWeight_eq_one_of_le_one rho sigma hNear
    have hShellsZero :
        Finset.sum (Finset.Ico 1 (2 * T)) (fun k =>
          if (k : Real) < gap /\ gap <= (k : Real) + 1 then
            zeroPairCoefficientMass rho sigma *
              TS317.Goldbach.ordinateGapDecayWeight rho sigma
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg]
      intro hShell
      have hkOne : (1 : Real) <= (k : Real) := by
        exact_mod_cast (Finset.mem_Ico.mp hk).1
      linarith
    dsimp [gap] at hNear hShellsZero
    rw [if_pos hNear, hShellsZero, add_zero, hWeight, mul_one]
  case neg =>
    have hFar : 1 < gap := lt_of_not_ge hNear
    have hGapUpper : gap <= 2 * (T : Real) :=
      zeroOrdinateGap_le_two_mul_height T rho sigma hRho hSigma
    have hIndexMem :
        Membership.mem (Finset.Ico 1 (2 * T)) (gapShellIndex gap) :=
      gapShellIndex_mem hFar hGapUpper
    have hIndexSpec := gapShellIndex_spec hFar
    have hShellSum :
        Finset.sum (Finset.Ico 1 (2 * T)) (fun k =>
          if (k : Real) < gap /\ gap <= (k : Real) + 1 then
            zeroPairCoefficientMass rho sigma *
              TS317.Goldbach.ordinateGapDecayWeight rho sigma
          else 0) =
        zeroPairCoefficientMass rho sigma *
          TS317.Goldbach.ordinateGapDecayWeight rho sigma := by
      rw [Finset.sum_eq_single (gapShellIndex gap)]
      next =>
        rw [if_pos hIndexSpec]
      next =>
        intro k hk hkNe
        rw [if_neg]
        intro hkSpec
        exact hkNe (gapShellIndex_unique hkSpec.1 hkSpec.2)
      next =>
        exact fun hNotMem => (hNotMem hIndexMem).elim
    dsimp [gap] at hNear hShellSum
    rw [if_neg hNear, zero_add, hShellSum]

/-! ## Global finite partition -/

/-- Exact partition of the complete TS317 envelope into its close mass and
the weighted unit shells `1 <= k < 2*T`. -/
theorem weightedClosePairEnvelope_eq_near_add_envelopeShells
    (T : Nat) :
    TS317.Goldbach.weightedClosePairEnvelope T =
      weightedNearPairCoefficientMass T +
        Finset.sum (Finset.Ico 1 (2 * T)) (fun k =>
          weightedGapShellEnvelopeMass T k) := by
  let zeros := TS315.Goldbach.truncatedZeroSet T
  let shells := Finset.Ico 1 (2 * T)
  change
    Finset.sum zeros (fun rho =>
        Finset.sum (zeros.erase rho) (fun sigma =>
          zeroPairCoefficientMass rho sigma *
            TS317.Goldbach.ordinateGapDecayWeight rho sigma)) =
      Finset.sum zeros (fun rho =>
          Finset.sum (zeros.erase rho) (fun sigma =>
            if TS317.Goldbach.zeroOrdinateGap rho sigma <= 1 then
              zeroPairCoefficientMass rho sigma
            else 0)) +
        Finset.sum shells (fun k =>
          Finset.sum zeros (fun rho =>
            Finset.sum (zeros.erase rho) (fun sigma =>
              let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
              if (k : Real) < gap /\ gap <= (k : Real) + 1 then
                zeroPairCoefficientMass rho sigma *
                  TS317.Goldbach.ordinateGapDecayWeight rho sigma
              else 0)))
  calc
    Finset.sum zeros (fun rho =>
        Finset.sum (zeros.erase rho) (fun sigma =>
          zeroPairCoefficientMass rho sigma *
            TS317.Goldbach.ordinateGapDecayWeight rho sigma)) =
      Finset.sum zeros (fun rho =>
        Finset.sum (zeros.erase rho) (fun sigma =>
          (if TS317.Goldbach.zeroOrdinateGap rho sigma <= 1 then
            zeroPairCoefficientMass rho sigma
          else 0) +
            Finset.sum shells (fun k =>
              let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
              if (k : Real) < gap /\ gap <= (k : Real) + 1 then
                zeroPairCoefficientMass rho sigma *
                  TS317.Goldbach.ordinateGapDecayWeight rho sigma
              else 0))) := by
        apply Finset.sum_congr rfl
        intro rho hRho
        apply Finset.sum_congr rfl
        intro sigma hSigma
        exact pairEnvelopeTerm_eq_near_add_shells T rho sigma hRho hSigma
    _ = Finset.sum zeros (fun rho =>
          Finset.sum (zeros.erase rho) (fun sigma =>
            if TS317.Goldbach.zeroOrdinateGap rho sigma <= 1 then
              zeroPairCoefficientMass rho sigma
            else 0)) +
        Finset.sum zeros (fun rho =>
          Finset.sum (zeros.erase rho) (fun sigma =>
            Finset.sum shells (fun k =>
              let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
              if (k : Real) < gap /\ gap <= (k : Real) + 1 then
                zeroPairCoefficientMass rho sigma *
                  TS317.Goldbach.ordinateGapDecayWeight rho sigma
              else 0))) := by
        simp_rw [Finset.sum_add_distrib]
    _ = Finset.sum zeros (fun rho =>
          Finset.sum (zeros.erase rho) (fun sigma =>
            if TS317.Goldbach.zeroOrdinateGap rho sigma <= 1 then
              zeroPairCoefficientMass rho sigma
            else 0)) +
        Finset.sum shells (fun k =>
          Finset.sum zeros (fun rho =>
            Finset.sum (zeros.erase rho) (fun sigma =>
              let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
              if (k : Real) < gap /\ gap <= (k : Real) + 1 then
                zeroPairCoefficientMass rho sigma *
                  TS317.Goldbach.ordinateGapDecayWeight rho sigma
              else 0))) := by
        congr 1
        calc
          Finset.sum zeros (fun rho =>
              Finset.sum (zeros.erase rho) (fun sigma =>
                Finset.sum shells (fun k =>
                  let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
                  if (k : Real) < gap /\ gap <= (k : Real) + 1 then
                    zeroPairCoefficientMass rho sigma *
                      TS317.Goldbach.ordinateGapDecayWeight rho sigma
                  else 0))) =
            Finset.sum zeros (fun rho =>
              Finset.sum shells (fun k =>
                Finset.sum (zeros.erase rho) (fun sigma =>
                  let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
                  if (k : Real) < gap /\ gap <= (k : Real) + 1 then
                    zeroPairCoefficientMass rho sigma *
                      TS317.Goldbach.ordinateGapDecayWeight rho sigma
                  else 0))) := by
              apply Finset.sum_congr rfl
              intro rho _
              exact Finset.sum_comm
          _ = Finset.sum shells (fun k =>
              Finset.sum zeros (fun rho =>
                Finset.sum (zeros.erase rho) (fun sigma =>
                  let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
                  if (k : Real) < gap /\ gap <= (k : Real) + 1 then
                    zeroPairCoefficientMass rho sigma *
                      TS317.Goldbach.ordinateGapDecayWeight rho sigma
                  else 0))) := Finset.sum_comm

theorem zeroPairCoefficientMass_nonnegative
    (rho sigma : ConcreteNontrivialZero) :
    0 <= zeroPairCoefficientMass rho sigma := by
  unfold zeroPairCoefficientMass
  exact mul_nonneg
    (TS316.Goldbach.zeroCoefficientMagnitude_nonnegative rho)
    (TS316.Goldbach.zeroCoefficientMagnitude_nonnegative sigma)

theorem weightedNearPairCoefficientMass_nonnegative (T : Nat) :
    0 <= weightedNearPairCoefficientMass T := by
  unfold weightedNearPairCoefficientMass
  apply Finset.sum_nonneg
  intro rho _
  apply Finset.sum_nonneg
  intro sigma _
  dsimp only
  split
  case isTrue => exact zeroPairCoefficientMass_nonnegative rho sigma
  case isFalse => exact le_rfl

theorem weightedGapShellCoefficientMass_nonnegative (T k : Nat) :
    0 <= weightedGapShellCoefficientMass T k := by
  unfold weightedGapShellCoefficientMass
  apply Finset.sum_nonneg
  intro rho _
  apply Finset.sum_nonneg
  intro sigma _
  dsimp only
  split
  case isTrue => exact zeroPairCoefficientMass_nonnegative rho sigma
  case isFalse => exact le_rfl

theorem weightedGapShellEnvelopeMass_nonnegative (T k : Nat) :
    0 <= weightedGapShellEnvelopeMass T k := by
  unfold weightedGapShellEnvelopeMass
  apply Finset.sum_nonneg
  intro rho _
  apply Finset.sum_nonneg
  intro sigma _
  dsimp only
  split
  case isTrue =>
    exact mul_nonneg
      (zeroPairCoefficientMass_nonnegative rho sigma)
      (TS317.Goldbach.ordinateGapDecayWeight_nonnegative rho sigma)
  case isFalse => exact le_rfl

theorem ordinateGapDecayWeight_le_one_div_nat
    (rho sigma : ConcreteNontrivialZero) (k : Nat) (hk : 1 <= k)
    (hShell : (k : Real) < TS317.Goldbach.zeroOrdinateGap rho sigma) :
    TS317.Goldbach.ordinateGapDecayWeight rho sigma <= 1 / (k : Real) := by
  have hkRealPos : (0 : Real) < (k : Real) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hOneGap : (1 : Real) <= TS317.Goldbach.zeroOrdinateGap rho sigma := by
    have hkRealOne : (1 : Real) <= (k : Real) := by exact_mod_cast hk
    exact hkRealOne.trans hShell.le
  unfold TS317.Goldbach.ordinateGapDecayWeight
  rw [max_eq_right hOneGap]
  exact one_div_le_one_div_of_le hkRealPos hShell.le

/-- On shell `(k,k+1]`, the exact weighted contribution is bounded by `1/k`
times the corresponding coefficient mass. -/
theorem weightedGapShellEnvelopeMass_le_one_div_mul_coefficientMass
    (T k : Nat) (hk : 1 <= k) :
    weightedGapShellEnvelopeMass T k <=
      (1 / (k : Real)) * weightedGapShellCoefficientMass T k := by
  unfold weightedGapShellEnvelopeMass weightedGapShellCoefficientMass
  calc
    Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
        Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho) (fun sigma =>
          let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
          if (k : Real) < gap /\ gap <= (k : Real) + 1 then
            zeroPairCoefficientMass rho sigma *
              TS317.Goldbach.ordinateGapDecayWeight rho sigma
          else 0)) <=
      Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
        Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho) (fun sigma =>
          (1 / (k : Real)) *
            (let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
             if (k : Real) < gap /\ gap <= (k : Real) + 1 then
               zeroPairCoefficientMass rho sigma
             else 0))) := by
        apply Finset.sum_le_sum
        intro rho _
        apply Finset.sum_le_sum
        intro sigma _
        dsimp only
        by_cases hShell :
            (k : Real) < TS317.Goldbach.zeroOrdinateGap rho sigma /\
              TS317.Goldbach.zeroOrdinateGap rho sigma <= (k : Real) + 1
        case pos =>
          rw [if_pos hShell, if_pos hShell]
          rw [mul_comm (1 / (k : Real))]
          exact mul_le_mul_of_nonneg_left
            (ordinateGapDecayWeight_le_one_div_nat rho sigma k hk hShell.1)
            (zeroPairCoefficientMass_nonnegative rho sigma)
        case neg => simp [hShell]
    _ = (1 / (k : Real)) *
        Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
          Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho) (fun sigma =>
            let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
            if (k : Real) < gap /\ gap <= (k : Real) + 1 then
              zeroPairCoefficientMass rho sigma
            else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho _
      rw [Finset.mul_sum]

/-- Global shell assembly with the correct upper weights `1/k`. -/
theorem weightedClosePairEnvelope_le_coefficientShellAssembly
    (T : Nat) :
    TS317.Goldbach.weightedClosePairEnvelope T <=
      weightedNearPairCoefficientMass T +
        Finset.sum (Finset.Ico 1 (2 * T)) (fun k =>
          (1 / (k : Real)) * weightedGapShellCoefficientMass T k) := by
  rw [weightedClosePairEnvelope_eq_near_add_envelopeShells T]
  gcongr with k hk
  exact weightedGapShellEnvelopeMass_le_one_div_mul_coefficientMass
    T k (Finset.mem_Ico.mp hk).1

/-! ## Local contracts and global adapter -/

def WeightedNearPairMassBoundStatement
    (T : Nat) (majorant : Real) : Prop :=
  0 <= majorant /\
    weightedNearPairCoefficientMass T <= majorant

def WeightedPairShellCoefficientMassBoundStatement
    (T k : Nat) (majorant : Real) : Prop :=
  0 <= majorant /\
    weightedGapShellCoefficientMass T k <= majorant

/-- Convert certified local coefficient-mass majorants into the canonical
TS317 weighted envelope contract. -/
theorem weightedClosePairEnvelopeBound_of_local_coefficient_bounds
    (T : Nat) (nearMajorant : Real) (shellMajorant : Nat -> Real)
    (hNear : WeightedNearPairMassBoundStatement T nearMajorant)
    (hShell : forall k, Membership.mem (Finset.Ico 1 (2 * T)) k ->
      WeightedPairShellCoefficientMassBoundStatement T k
        (shellMajorant k)) :
    TS317.Goldbach.WeightedClosePairEnvelopeBoundStatement T
      (nearMajorant + Finset.sum (Finset.Ico 1 (2 * T)) (fun k =>
        (1 / (k : Real)) * shellMajorant k)) := by
  constructor
  case left =>
    exact add_nonneg hNear.1 (Finset.sum_nonneg (fun k hk =>
      mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg k))
        (hShell k hk).1))
  case right =>
    calc
      TS317.Goldbach.weightedClosePairEnvelope T <=
          weightedNearPairCoefficientMass T +
            Finset.sum (Finset.Ico 1 (2 * T)) (fun k =>
              (1 / (k : Real)) *
                weightedGapShellCoefficientMass T k) :=
        weightedClosePairEnvelope_le_coefficientShellAssembly T
      _ <= nearMajorant +
          Finset.sum (Finset.Ico 1 (2 * T)) (fun k =>
            (1 / (k : Real)) * shellMajorant k) := by
        apply add_le_add hNear.2
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left (hShell k hk).2
          (one_div_nonneg.mpr (Nat.cast_nonneg k))

/-- Re-export the unconditional coarse global TS317 bound. -/
theorem weightedClosePairEnvelopeBound_coarse (T : Nat) :
    TS317.Goldbach.WeightedClosePairEnvelopeBoundStatement T
      (TS316.Goldbach.globalLinearSpectralMass ^ 2) :=
  TS317.Goldbach.weightedClosePairEnvelopeBound_coarse T

/-- Local close/shell certificates prepared for numerical work downstream. -/
structure WeightedLocalShellBoundData (T : Nat) where
  nearMajorant : Real
  shellMajorant : Nat -> Real
  near_bound : WeightedNearPairMassBoundStatement T nearMajorant
  shell_bounds : forall k, Membership.mem (Finset.Ico 1 (2 * T)) k ->
    WeightedPairShellCoefficientMassBoundStatement T k (shellMajorant k)

noncomputable def WeightedLocalShellBoundData.totalMajorant
    {T : Nat} (D : WeightedLocalShellBoundData T) : Real :=
  D.nearMajorant + Finset.sum (Finset.Ico 1 (2 * T)) (fun k =>
    (1 / (k : Real)) * D.shellMajorant k)

theorem WeightedLocalShellBoundData.toEnvelopeBound
    {T : Nat} (D : WeightedLocalShellBoundData T) :
    TS317.Goldbach.WeightedClosePairEnvelopeBoundStatement T
      D.totalMajorant := by
  exact weightedClosePairEnvelopeBound_of_local_coefficient_bounds
    T D.nearMajorant D.shellMajorant D.near_bound D.shell_bounds

structure TS321Ledger where
  exact_near_shell_partition_proved : True
  shell_coefficient_and_envelope_masses_separated : True
  one_over_k_shell_bound_proved : True
  local_weighted_contracts_defined : True
  local_bound_data_facade_defined : True
  local_to_global_adapter_proved : True
  coarse_uniform_bound_routed : True
  effective_near_pair_smallness_not_proved : True
  effective_shell_smallness_not_proved : True
  rational_half_budget_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def ts321Ledger : TS321Ledger where
  exact_near_shell_partition_proved := True.intro
  shell_coefficient_and_envelope_masses_separated := True.intro
  one_over_k_shell_bound_proved := True.intro
  local_weighted_contracts_defined := True.intro
  local_bound_data_facade_defined := True.intro
  local_to_global_adapter_proved := True.intro
  coarse_uniform_bound_routed := True.intro
  effective_near_pair_smallness_not_proved := True.intro
  effective_shell_smallness_not_proved := True.intro
  rational_half_budget_not_proved := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end

end Goldbach
end TS321
