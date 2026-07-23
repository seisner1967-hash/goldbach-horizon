import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic
import TS.Goldbach.Strong.TS298.RightLineCutoffAndHorizontalIntegration

/-!
# TS299 - Finite-Grid Strong Height and Reciprocal-Load Bound

This module replaces the arbitrary finite-avoidance height from TS296 by a
quantitative finite-grid selection.  If `M` is the nearby multiplicity mass,
the grid has `K = 4 * (M + 1)` midpoints in `(T,T+1)`.  Each zero height
forbids at most one midpoint at distance below `1/(4K)`, so at least half of
the grid remains admissible.

A discrete harmonic estimate bounds the truncated reciprocal kernel for each
zero by `8 * K * H_K`.  Averaging over the admissible points then constructs a
single height with reciprocal load at most `16 * M * H_K`.  TS290 turns `M`
into a closed log-linear envelope, yielding explicit closed functions for
both the separation and the load.

The construction is finite and unconditional.  It does not estimate the
local logarithm sphere bound, the completion correction, the fixed left
side, exceptional residues, Perron inversion, the meromorphic residue
theorem, the infinite explicit formula, Gallagher, OTSA, or Goldbach.
-/

noncomputable section

namespace TS299
namespace Goldbach

open scoped BigOperators

noncomputable def realHarmonic (K : Nat) : Real :=
  Finset.sum (Finset.range K) (fun n => 1 / ((n + 1 : Nat) : Real))

theorem realHarmonic_eq_cast_harmonic (K : Nat) :
    realHarmonic K = (harmonic K : Real) := by
  unfold realHarmonic harmonic
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

theorem realHarmonic_nonnegative (K : Nat) :
    0 <= realHarmonic K := by
  unfold realHarmonic
  exact Finset.sum_nonneg fun n _ => by positivity

theorem realHarmonic_mono {K L : Nat} (hKL : K <= L) :
    realHarmonic K <= realHarmonic L := by
  unfold realHarmonic
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono hKL)
    (fun n _ _ => by positivity)

theorem realHarmonic_le_one_add_log (K : Nat) :
    realHarmonic K <= 1 + Real.log K := by
  rw [realHarmonic_eq_cast_harmonic]
  exact harmonic_le_one_add_log K

theorem sum_range_inv_dist_add_one_le_two_harmonic
    (K j : Nat) :
    Finset.sum (Finset.range K)
        (fun k => 1 / ((Nat.dist k j + 1 : Nat) : Real)) <=
      2 * realHarmonic K := by
  by_cases hj : j < K
  case pos =>
    rw [(Finset.sum_range_add_sum_Ico
      (fun k => 1 / ((Nat.dist k j + 1 : Nat) : Real))
      (show j + 1 <= K by omega)).symm]
    have hLeft :
        Finset.sum (Finset.range (j + 1))
            (fun k => 1 / ((Nat.dist k j + 1 : Nat) : Real)) =
          realHarmonic (j + 1) := by
      unfold realHarmonic
      have hReflect := Finset.sum_range_reflect
        (fun n : Nat => 1 / ((n + 1 : Nat) : Real)) (j + 1)
      calc
        Finset.sum (Finset.range (j + 1))
            (fun k => 1 / ((Nat.dist k j + 1 : Nat) : Real)) =
            Finset.sum (Finset.range (j + 1))
              (fun k => 1 / ((j - k + 1 : Nat) : Real)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Nat.dist_eq_sub_of_le]
          simp only [Finset.mem_range] at hk
          omega
        _ = Finset.sum (Finset.range (j + 1))
              (fun n => 1 / ((n + 1 : Nat) : Real)) := by
          simpa using hReflect
    have hRight :
        Finset.sum (Finset.Ico (j + 1) K)
            (fun k => 1 / ((Nat.dist k j + 1 : Nat) : Real)) <=
          realHarmonic (K - (j + 1)) := by
      have hUpper : K - (j + 1) + (j + 1) = K := by omega
      have hShift := Finset.sum_Ico_add_right_sub_eq
        (f := fun n : Nat => 1 / ((n + 1 : Nat) : Real))
        0 (K - (j + 1)) (j + 1)
      simp only [zero_add] at hShift
      rw [hUpper] at hShift
      calc
        Finset.sum (Finset.Ico (j + 1) K)
            (fun k => 1 / ((Nat.dist k j + 1 : Nat) : Real)) <=
            Finset.sum (Finset.Ico (j + 1) K)
              (fun k => 1 / ((k - (j + 1) + 1 : Nat) : Real)) := by
          apply Finset.sum_le_sum
          intro k hk
          simp only [Finset.mem_Ico] at hk
          rw [Nat.dist_eq_sub_of_le_right (by omega)]
          apply one_div_le_one_div_of_le (by positivity)
          norm_cast
          omega
        _ = Finset.sum (Finset.Ico 0 (K - (j + 1)))
              (fun n => 1 / ((n + 1 : Nat) : Real)) := hShift
        _ = realHarmonic (K - (j + 1)) := by
          unfold realHarmonic
          simp
    have hLeftMono := realHarmonic_mono (show j + 1 <= K by omega)
    have hRightMono := realHarmonic_mono (show K - (j + 1) <= K by omega)
    linarith
  case neg =>
    have hjK : K <= j := by omega
    have hPointwise :
        forall k : Nat, Membership.mem (Finset.range K) k ->
          1 / ((Nat.dist k j + 1 : Nat) : Real) <=
            1 / ((K - k : Nat) : Real) := by
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [Nat.dist_eq_sub_of_le (show k <= j by omega)]
      have hPos : (0 : Real) < (K - k : Nat) := by
        exact_mod_cast Nat.sub_pos_of_lt hk
      apply one_div_le_one_div_of_le hPos
      norm_cast
      omega
    calc
      Finset.sum (Finset.range K)
          (fun k => 1 / ((Nat.dist k j + 1 : Nat) : Real)) <=
          Finset.sum (Finset.range K)
            (fun k => 1 / ((K - k : Nat) : Real)) := by
        exact Finset.sum_le_sum hPointwise
      _ = realHarmonic K := by
        unfold realHarmonic
        have hReflect := Finset.sum_range_reflect
          (fun n : Nat => 1 / ((n + 1 : Nat) : Real)) K
        calc
          Finset.sum (Finset.range K)
              (fun k => 1 / ((K - k : Nat) : Real)) =
              Finset.sum (Finset.range K)
                (fun k => 1 / ((K - 1 - k + 1 : Nat) : Real)) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_range] at hk
            congr 3
            omega
          _ = Finset.sum (Finset.range K)
                (fun n => 1 / ((n + 1 : Nat) : Real)) := hReflect
      _ <= 2 * realHarmonic K := by
        linarith [realHarmonic_nonnegative K]

noncomputable def gridPoint (T : Real) (K k : Nat) : Real :=
  T + ((2 * k + 1 : Nat) : Real) / (2 * (K : Real))

noncomputable def gridDelta (K : Nat) : Real :=
  1 / (4 * (K : Real))

noncomputable def truncatedGridKernel
    (T : Real) (K : Nat) (a : Real) (k : Nat) : Real :=
  1 / max (gridDelta K) |gridPoint T K k - a|

theorem gridDelta_pos {K : Nat} (hK : 0 < K) :
    0 < gridDelta K := by
  unfold gridDelta
  positivity

theorem gridPoint_sub_base_pos
    (T : Real) {K k : Nat} (hK : 0 < K) :
    0 < gridPoint T K k - T := by
  unfold gridPoint
  simp only [add_sub_cancel_left]
  positivity

theorem gridPoint_sub_base_lt_one
    (T : Real) {K k : Nat} (hK : 0 < K) (hk : k < K) :
    gridPoint T K k - T < 1 := by
  unfold gridPoint
  simp only [add_sub_cancel_left]
  rw [div_lt_one (by positivity : (0 : Real) < 2 * (K : Real))]
  norm_cast
  omega

theorem gridPoint_mem_Ioo
    (T : Real) {K k : Nat} (hK : 0 < K) (hk : k < K) :
    Set.Mem (Set.Ioo T (T + 1)) (gridPoint T K k) := by
  exact And.intro
    (by linarith [gridPoint_sub_base_pos T (k := k) hK])
    (by linarith [gridPoint_sub_base_lt_one T (k := k) hK hk])

theorem gridPoint_sub_gridPoint
    (T : Real) {K k l : Nat} (hK : 0 < K) :
    gridPoint T K l - gridPoint T K k =
      ((l : Real) - k) / K := by
  unfold gridPoint
  have hK0 : Ne (K : Real) 0 := by positivity
  field_simp
  ring

theorem truncatedGridKernel_nonnegative
    (T : Real) (K : Nat) (a : Real) (k : Nat) :
    0 <= truncatedGridKernel T K a k := by
  unfold truncatedGridKernel
  positivity

theorem interior_grid_denominator_lower_bound
    (T a : Real) {K k : Nat} (hK : 0 < K)
    (hTa : T < a) (haT : a < T + 1) :
    ((Nat.dist k (Nat.floor ((K : Real) * (a - T))) + 1 : Nat) : Real) /
        (4 * (K : Real)) <=
      max (gridDelta K) |gridPoint T K k - a| := by
  let c : Real := (K : Real) * (a - T)
  let j : Nat := Nat.floor c
  have hKR : (0 : Real) < K := by exact_mod_cast hK
  have hc0 : 0 <= c := by
    dsimp [c]
    exact mul_nonneg (le_of_lt hKR) (le_of_lt (sub_pos.mpr hTa))
  have hcK : c < (K : Real) := by
    dsimp [c]
    nlinarith
  have hjc : (j : Real) <= c := by
    dsimp [j]
    exact Nat.floor_le hc0
  have hcj : c < (j : Real) + 1 := by
    dsimp [j]
    exact_mod_cast Nat.lt_floor_add_one c
  change (((Nat.dist k j + 1 : Nat) : Real) / (4 * (K : Real))) <=
    max (gridDelta K) |gridPoint T K k - a|
  by_cases hkj : k = j
  case pos =>
    subst k
    simp only [Nat.dist_self, zero_add, Nat.cast_one]
    exact le_max_of_le_left (le_rfl : gridDelta K <= gridDelta K)
  case neg =>
    apply le_trans ?_ (le_max_right _ _)
    rcases lt_or_gt_of_ne hkj with hlt | hgt
    case inl =>
      have hkjR : (k : Real) + 1 <= (j : Real) := by
        exact_mod_cast (show k + 1 <= j by omega)
      rw [abs_sub_comm]
      apply le_trans ?_ (le_abs_self (a - gridPoint T K k))
      calc
        (((Nat.dist k j + 1 : Nat) : Real) / (4 * (K : Real))) =
            ((((Nat.dist k j + 1 : Nat) : Real) / 4) / (K : Real)) := by ring
        _ <= (c - (k : Real) - 1 / 2) / (K : Real) := by
          apply (div_le_div_iff_of_pos_right hKR).2
          rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hlt)]
          rw [Nat.cast_add, Nat.cast_sub (Nat.le_of_lt hlt), Nat.cast_one]
          nlinarith
        _ = a - gridPoint T K k := by
          dsimp [c, gridPoint]
          field_simp
          ring
    case inr =>
      have hjkR : (j : Real) + 1 <= (k : Real) := by
        exact_mod_cast (show j + 1 <= k by omega)
      apply le_trans ?_ (le_abs_self (gridPoint T K k - a))
      calc
        (((Nat.dist k j + 1 : Nat) : Real) / (4 * (K : Real))) =
            ((((Nat.dist k j + 1 : Nat) : Real) / 4) / (K : Real)) := by ring
        _ <= ((k : Real) + 1 / 2 - c) / (K : Real) := by
          apply (div_le_div_iff_of_pos_right hKR).2
          rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_lt hgt)]
          rw [Nat.cast_add, Nat.cast_sub (Nat.le_of_lt hgt), Nat.cast_one]
          nlinarith
        _ = gridPoint T K k - a := by
          dsimp [c, gridPoint]
          field_simp
          ring

theorem truncatedGridKernel_le_of_denominator_lower_bound
    (T a : Real) {K k d : Nat} (hK : 0 < K) (hd : 0 < d)
    (hLower : ((d : Real) / (4 * (K : Real))) <=
      max (gridDelta K) |gridPoint T K k - a|) :
    truncatedGridKernel T K a k <= 4 * (K : Real) / d := by
  unfold truncatedGridKernel
  calc
    1 / max (gridDelta K) |gridPoint T K k - a| <=
        1 / ((d : Real) / (4 * (K : Real))) := by
      exact one_div_le_one_div_of_le (by positivity) hLower
    _ = 4 * (K : Real) / d := by
      field_simp

theorem left_grid_denominator_lower_bound
    (T a : Real) {K k : Nat} (hK : 0 < K) (ha : a <= T) :
    (((k + 1 : Nat) : Real) / (4 * (K : Real))) <=
      max (gridDelta K) |gridPoint T K k - a| := by
  have hKR : (0 : Real) < K := by exact_mod_cast hK
  apply le_trans ?_ (le_max_right _ _)
  apply le_trans ?_ (le_abs_self (gridPoint T K k - a))
  calc
    (((k + 1 : Nat) : Real) / (4 * (K : Real))) =
        ((((k + 1 : Nat) : Real) / 4) / (K : Real)) := by ring
    _ <= ((K : Real) * (gridPoint T K k - a)) / (K : Real) := by
      apply (div_le_div_iff_of_pos_right hKR).2
      have hnonneg : 0 <= (K : Real) * (T - a) :=
        mul_nonneg (le_of_lt hKR) (sub_nonneg.mpr ha)
      have hid :
          (K : Real) * (gridPoint T K k - a) =
            (K : Real) * (T - a) + ((2 * k + 1 : Nat) : Real) / 2 := by
        dsimp [gridPoint]
        field_simp
        ring
      rw [hid]
      push_cast
      have hk0 : (0 : Real) <= k := by positivity
      nlinarith
    _ = gridPoint T K k - a := by
      field_simp

theorem right_grid_denominator_lower_bound
    (T a : Real) {K k : Nat} (hK : 0 < K) (hk : k < K)
    (ha : T + 1 <= a) :
    (((K - k : Nat) : Real) / (4 * (K : Real))) <=
      max (gridDelta K) |gridPoint T K k - a| := by
  have hKR : (0 : Real) < K := by exact_mod_cast hK
  have hKk : 0 < K - k := Nat.sub_pos_of_lt hk
  rw [abs_sub_comm]
  apply le_trans ?_ (le_max_right _ _)
  apply le_trans ?_ (le_abs_self (a - gridPoint T K k))
  calc
    (((K - k : Nat) : Real) / (4 * (K : Real))) =
        ((((K - k : Nat) : Real) / 4) / (K : Real)) := by ring
    _ <= ((K : Real) * (a - gridPoint T K k)) / (K : Real) := by
      apply (div_le_div_iff_of_pos_right hKR).2
      rw [Nat.cast_sub (Nat.le_of_lt hk)]
      have hnonneg : 0 <= (K : Real) * (a - (T + 1)) :=
        mul_nonneg (le_of_lt hKR) (sub_nonneg.mpr ha)
      have hid :
          (K : Real) * (a - gridPoint T K k) =
            (K : Real) * (a - (T + 1)) +
              ((K : Real) - k) - 1 / 2 := by
        dsimp [gridPoint]
        field_simp
        ring
      rw [hid]
      have hgap : (k : Real) + 1 <= (K : Real) := by exact_mod_cast hk
      nlinarith
    _ = a - gridPoint T K k := by
      field_simp

theorem truncatedGridKernel_sum_le
    (T a : Real) {K : Nat} (hK : 0 < K) :
    Finset.sum (Finset.range K) (truncatedGridKernel T K a) <=
      8 * (K : Real) * realHarmonic K := by
  have hFactor : 0 <= 4 * (K : Real) := by positivity
  by_cases haLeft : a <= T
  case pos =>
    calc
      Finset.sum (Finset.range K) (truncatedGridKernel T K a) <=
          Finset.sum (Finset.range K)
            (fun k => 4 * (K : Real) / ((Nat.dist k 0 + 1 : Nat) : Real)) := by
        apply Finset.sum_le_sum
        intro k hk
        apply truncatedGridKernel_le_of_denominator_lower_bound T a hK
          (show 0 < Nat.dist k 0 + 1 by omega)
        have hDist : Nat.dist k 0 + 1 = k + 1 := by
          rw [Nat.dist_eq_sub_of_le_right (Nat.zero_le k)]
          omega
        simpa [hDist] using left_grid_denominator_lower_bound T a (k := k) hK haLeft
      _ = 4 * (K : Real) * Finset.sum (Finset.range K)
            (fun k => 1 / ((Nat.dist k 0 + 1 : Nat) : Real)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ <= 4 * (K : Real) * (2 * realHarmonic K) := by
        exact mul_le_mul_of_nonneg_left
          (sum_range_inv_dist_add_one_le_two_harmonic K 0) hFactor
      _ = 8 * (K : Real) * realHarmonic K := by ring
  case neg =>
    by_cases haRight : T + 1 <= a
    case pos =>
      let j := K - 1
      calc
        Finset.sum (Finset.range K) (truncatedGridKernel T K a) <=
            Finset.sum (Finset.range K)
              (fun k => 4 * (K : Real) / ((Nat.dist k j + 1 : Nat) : Real)) := by
          apply Finset.sum_le_sum
          intro k hk
          simp only [Finset.mem_range] at hk
          apply truncatedGridKernel_le_of_denominator_lower_bound T a hK
            (show 0 < Nat.dist k j + 1 by omega)
          have hDen := right_grid_denominator_lower_bound T a hK hk haRight
          have hDist : Nat.dist k j + 1 = K - k := by
            dsimp [j]
            have hle : k <= K - 1 := by omega
            rw [Nat.dist_eq_sub_of_le hle]
            omega
          simpa [hDist] using hDen
        _ = 4 * (K : Real) * Finset.sum (Finset.range K)
              (fun k => 1 / ((Nat.dist k j + 1 : Nat) : Real)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ <= 4 * (K : Real) * (2 * realHarmonic K) := by
          exact mul_le_mul_of_nonneg_left
            (sum_range_inv_dist_add_one_le_two_harmonic K j) hFactor
        _ = 8 * (K : Real) * realHarmonic K := by ring
    case neg =>
      have hTa : T < a := lt_of_not_ge haLeft
      have haT : a < T + 1 := lt_of_not_ge haRight
      let j := Nat.floor ((K : Real) * (a - T))
      calc
        Finset.sum (Finset.range K) (truncatedGridKernel T K a) <=
            Finset.sum (Finset.range K)
              (fun k => 4 * (K : Real) / ((Nat.dist k j + 1 : Nat) : Real)) := by
          apply Finset.sum_le_sum
          intro k hk
          apply truncatedGridKernel_le_of_denominator_lower_bound T a hK
            (show 0 < Nat.dist k j + 1 by omega)
          simpa [j] using
            interior_grid_denominator_lower_bound T a (K := K) (k := k) hK hTa haT
        _ = 4 * (K : Real) * Finset.sum (Finset.range K)
              (fun k => 1 / ((Nat.dist k j + 1 : Nat) : Real)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ <= 4 * (K : Real) * (2 * realHarmonic K) := by
          exact mul_le_mul_of_nonneg_left
            (sum_range_inv_dist_add_one_le_two_harmonic K j) hFactor
        _ = 8 * (K : Real) * realHarmonic K := by ring

noncomputable def nearbyZeroMultiplicityNatMass (T : Nat) : Nat :=
  Finset.sum (TS295.Goldbach.nearbyConcreteZeros T)
    TS295.Goldbach.concreteZeroMultiplicity

noncomputable def finiteGridSize (T : Nat) : Nat :=
  4 * (nearbyZeroMultiplicityNatMass T + 1)

theorem finiteGridSize_pos (T : Nat) : 0 < finiteGridSize T := by
  unfold finiteGridSize
  omega

theorem concreteZeroMultiplicity_pos
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    0 < TS295.Goldbach.concreteZeroMultiplicity rho := by
  simpa [TS295.Goldbach.concreteZeroMultiplicity,
    TS264.Goldbach.concreteRiemannZetaZeroFamilyContract] using
    TS264.Goldbach.concreteRiemannZetaMultiplicity_positive rho.property

theorem nearbyConcreteZeros_card_le_natMass (T : Nat) :
    (TS295.Goldbach.nearbyConcreteZeros T).card <=
      nearbyZeroMultiplicityNatMass T := by
  unfold nearbyZeroMultiplicityNatMass
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro rho hRho
  exact concreteZeroMultiplicity_pos rho

theorem nearbyZeroMultiplicityMass_eq_natMass_cast (T : Nat) :
    TS295.Goldbach.nearbyZeroMultiplicityMass T =
      (nearbyZeroMultiplicityNatMass T : Real) := by
  unfold TS295.Goldbach.nearbyZeroMultiplicityMass
    nearbyZeroMultiplicityNatMass
  exact_mod_cast rfl

theorem one_div_gridSize_le_gridPoint_dist
    (T : Real) {K k l : Nat} (hK : 0 < K)
    (hkl : Ne k l) :
    1 / (K : Real) <= |gridPoint T K k - gridPoint T K l| := by
  have hKR : (0 : Real) < K := by exact_mod_cast hK
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  case inl =>
    have hklR : (k : Real) < (l : Real) := by exact_mod_cast hlt
    have hPos : 0 < ((l : Real) - k) / K := div_pos (sub_pos.mpr hklR) hKR
    rw [abs_sub_comm, gridPoint_sub_gridPoint T hK, abs_of_pos hPos]
    apply (div_le_div_iff_of_pos_right hKR).2
    have hStep : (k : Real) + 1 <= (l : Real) := by
      exact_mod_cast (show k + 1 <= l by omega)
    linarith
  case inr =>
    have hlkR : (l : Real) < (k : Real) := by exact_mod_cast hgt
    have hPos : 0 < ((k : Real) - l) / K := div_pos (sub_pos.mpr hlkR) hKR
    rw [gridPoint_sub_gridPoint T hK, abs_of_pos hPos]
    apply (div_le_div_iff_of_pos_right hKR).2
    have hStep : (l : Real) + 1 <= (k : Real) := by
      exact_mod_cast (show l + 1 <= k by omega)
    linarith

noncomputable def forbiddenGridIndices
    (T : Nat)
    (rho : TS292.Goldbach.ConcreteNontrivialZero) : Finset Nat :=
  Finset.filter
    (fun k =>
      TS295.Goldbach.symmetricZeroHeightGap
          (gridPoint (T : Real) (finiteGridSize T) k) rho <
        gridDelta (finiteGridSize T))
    (Finset.range (finiteGridSize T))

theorem forbiddenGridIndices_card_le_one
    (T : Nat)
    (rho : TS292.Goldbach.ConcreteNontrivialZero) :
    (forbiddenGridIndices T rho).card <= 1 := by
  rw [Finset.card_le_one_iff]
  intro k l hk hl
  simp only [forbiddenGridIndices, Finset.mem_filter,
    Finset.mem_range] at hk hl
  by_contra hkl
  have hSpacing := one_div_gridSize_le_gridPoint_dist (T : Real)
    (finiteGridSize_pos T) hkl
  have hTriangle :
      |gridPoint (T : Real) (finiteGridSize T) k -
          gridPoint (T : Real) (finiteGridSize T) l| <=
        TS295.Goldbach.symmetricZeroHeightGap
            (gridPoint (T : Real) (finiteGridSize T) k) rho +
          TS295.Goldbach.symmetricZeroHeightGap
            (gridPoint (T : Real) (finiteGridSize T) l) rho := by
    have h := abs_sub_le
      (gridPoint (T : Real) (finiteGridSize T) k)
      (_root_.abs rho.1.im)
      (gridPoint (T : Real) (finiteGridSize T) l)
    simpa [TS295.Goldbach.symmetricZeroHeightGap, abs_sub_comm] using h
  have hDelta :
      2 * gridDelta (finiteGridSize T) =
        1 / (2 * (finiteGridSize T : Real)) := by
    unfold gridDelta
    field_simp
    ring
  have hKR : (0 : Real) < finiteGridSize T := by
    exact_mod_cast finiteGridSize_pos T
  have hTooClose :
      |gridPoint (T : Real) (finiteGridSize T) k -
          gridPoint (T : Real) (finiteGridSize T) l| <
        1 / (2 * (finiteGridSize T : Real)) := by
    rw [<- hDelta]
    have hAdd := add_lt_add hk.2 hl.2
    nlinarith [hTriangle, hAdd]
  have hHalf :
      1 / (2 * (finiteGridSize T : Real)) <
        1 / (finiteGridSize T : Real) := by
    apply one_div_lt_one_div_of_lt hKR
    linarith
  linarith

noncomputable def badGridIndices (T : Nat) : Finset Nat :=
  (TS295.Goldbach.nearbyConcreteZeros T).biUnion
    (forbiddenGridIndices T)

noncomputable def goodGridIndices (T : Nat) : Finset Nat :=
  Finset.range (finiteGridSize T) \ badGridIndices T

theorem badGridIndices_subset_range (T : Nat) :
    badGridIndices T <= Finset.range (finiteGridSize T) := by
  intro k hk
  rw [badGridIndices, Finset.mem_biUnion] at hk
  let rho := Classical.choose hk
  have hSpec := Classical.choose_spec hk
  exact (Finset.mem_filter.mp hSpec.2).1

theorem badGridIndices_card_le_natMass (T : Nat) :
    (badGridIndices T).card <= nearbyZeroMultiplicityNatMass T := by
  calc
    (badGridIndices T).card <=
        Finset.sum (TS295.Goldbach.nearbyConcreteZeros T)
          (fun rho => (forbiddenGridIndices T rho).card) :=
      Finset.card_biUnion_le
    _ <= Finset.sum (TS295.Goldbach.nearbyConcreteZeros T)
          (fun _ => 1) := by
      apply Finset.sum_le_sum
      intro rho hRho
      exact forbiddenGridIndices_card_le_one T rho
    _ = (TS295.Goldbach.nearbyConcreteZeros T).card := by simp
    _ <= nearbyZeroMultiplicityNatMass T :=
      nearbyConcreteZeros_card_le_natMass T

theorem goodGridIndices_card_add_bad (T : Nat) :
    (goodGridIndices T).card + (badGridIndices T).card = finiteGridSize T := by
  unfold goodGridIndices
  rw [Finset.card_sdiff (badGridIndices_subset_range T)]
  rw [Finset.card_range]
  have hBadRange := Finset.card_le_card (badGridIndices_subset_range T)
  rw [Finset.card_range] at hBadRange
  omega

theorem finiteGridSize_le_two_mul_good_card (T : Nat) :
    finiteGridSize T <= 2 * (goodGridIndices T).card := by
  have hBad := badGridIndices_card_le_natMass T
  have hCard := goodGridIndices_card_add_bad T
  unfold finiteGridSize at hCard
  unfold finiteGridSize
  omega

theorem goodGridIndices_nonempty (T : Nat) :
    (goodGridIndices T).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hEmpty
  have hSize := finiteGridSize_le_two_mul_good_card T
  simp [hEmpty, finiteGridSize] at hSize

noncomputable def finiteGridReciprocalLoad (T k : Nat) : Real :=
  TS295.Goldbach.reciprocalZeroLoad T
    (gridPoint (T : Real) (finiteGridSize T) k)

theorem goodGridIndex_gap_lower_bound
    (T : Nat) {k : Nat}
    (hk : Membership.mem (goodGridIndices T) k)
    (rho : TS292.Goldbach.ConcreteNontrivialZero)
    (hRho : Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho) :
    gridDelta (finiteGridSize T) <=
      TS295.Goldbach.symmetricZeroHeightGap
        (gridPoint (T : Real) (finiteGridSize T) k) rho := by
  unfold goodGridIndices at hk
  have hkNotBad := (Finset.mem_sdiff.mp hk).2
  apply le_of_not_gt
  intro hGap
  apply hkNotBad
  rw [badGridIndices, Finset.mem_biUnion]
  refine Exists.intro rho (And.intro hRho ?_)
  exact Finset.mem_filter.mpr (And.intro (Finset.mem_sdiff.mp hk).1 hGap)

theorem reciprocal_term_eq_truncatedGridKernel
    (T : Nat) {k : Nat}
    (hk : Membership.mem (goodGridIndices T) k)
    (rho : TS292.Goldbach.ConcreteNontrivialZero)
    (hRho : Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho) :
    (TS295.Goldbach.concreteZeroMultiplicity rho : Real) /
        TS295.Goldbach.symmetricZeroHeightGap
          (gridPoint (T : Real) (finiteGridSize T) k) rho =
      (TS295.Goldbach.concreteZeroMultiplicity rho : Real) *
        truncatedGridKernel (T : Real) (finiteGridSize T)
          (_root_.abs rho.1.im) k := by
  have hGap := goodGridIndex_gap_lower_bound T hk rho hRho
  unfold TS295.Goldbach.symmetricZeroHeightGap at hGap
  unfold truncatedGridKernel TS295.Goldbach.symmetricZeroHeightGap
  rw [max_eq_right hGap]
  ring

theorem goodGrid_load_sum_le
    (T : Nat) :
    Finset.sum (goodGridIndices T) (finiteGridReciprocalLoad T) <=
      (nearbyZeroMultiplicityNatMass T : Real) *
        (8 * (finiteGridSize T : Real) *
          realHarmonic (finiteGridSize T)) := by
  let Z := TS295.Goldbach.nearbyConcreteZeros T
  let G := goodGridIndices T
  let K := finiteGridSize T
  calc
    Finset.sum G (finiteGridReciprocalLoad T) =
        Finset.sum Z (fun rho =>
          Finset.sum G (fun k =>
            (TS295.Goldbach.concreteZeroMultiplicity rho : Real) /
              TS295.Goldbach.symmetricZeroHeightGap
                (gridPoint (T : Real) K k) rho)) := by
      dsimp [G, Z, K]
      unfold finiteGridReciprocalLoad TS295.Goldbach.reciprocalZeroLoad
      rw [Finset.sum_comm]
    _ = Finset.sum Z (fun rho =>
          Finset.sum G (fun k =>
            (TS295.Goldbach.concreteZeroMultiplicity rho : Real) *
              truncatedGridKernel (T : Real) K
                (_root_.abs rho.1.im) k)) := by
      apply Finset.sum_congr rfl
      intro rho hRho
      apply Finset.sum_congr rfl
      intro k hk
      exact reciprocal_term_eq_truncatedGridKernel T hk rho hRho
    _ <= Finset.sum Z (fun rho =>
          Finset.sum (Finset.range K) (fun k =>
            (TS295.Goldbach.concreteZeroMultiplicity rho : Real) *
              truncatedGridKernel (T : Real) K
                (_root_.abs rho.1.im) k)) := by
      apply Finset.sum_le_sum
      intro rho hRho
      refine Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_
      intro k hkRange hkNotGood
      exact mul_nonneg (Nat.cast_nonneg _)
        (truncatedGridKernel_nonnegative _ _ _ _)
    _ <= Finset.sum Z (fun rho =>
          (TS295.Goldbach.concreteZeroMultiplicity rho : Real) *
            (8 * (K : Real) * realHarmonic K)) := by
      apply Finset.sum_le_sum
      intro rho hRho
      rw [<- Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (truncatedGridKernel_sum_le (T : Real) (_root_.abs rho.1.im)
          (finiteGridSize_pos T))
        (Nat.cast_nonneg _)
    _ = (nearbyZeroMultiplicityNatMass T : Real) *
          (8 * (finiteGridSize T : Real) *
            realHarmonic (finiteGridSize T)) := by
      dsimp [Z, K]
      rw [<- Finset.sum_mul]
      congr 1
      unfold nearbyZeroMultiplicityNatMass
      exact_mod_cast rfl

theorem goodGrid_load_sum_le_card_mul_envelope
    (T : Nat) :
    Finset.sum (goodGridIndices T) (finiteGridReciprocalLoad T) <=
      ((goodGridIndices T).card : Real) *
        (16 * (nearbyZeroMultiplicityNatMass T : Real) *
          realHarmonic (finiteGridSize T)) := by
  have hSum := goodGrid_load_sum_le T
  have hCard :
      (finiteGridSize T : Real) <=
        2 * ((goodGridIndices T).card : Real) := by
    exact_mod_cast finiteGridSize_le_two_mul_good_card T
  have hCoeff :
      0 <= 8 * (nearbyZeroMultiplicityNatMass T : Real) *
        realHarmonic (finiteGridSize T) := by
    exact mul_nonneg
      (mul_nonneg (by positivity) (Nat.cast_nonneg _))
      (realHarmonic_nonnegative _)
  calc
    Finset.sum (goodGridIndices T) (finiteGridReciprocalLoad T) <=
        (8 * (nearbyZeroMultiplicityNatMass T : Real) *
          realHarmonic (finiteGridSize T)) * (finiteGridSize T : Real) := by
      calc
        _ <= (nearbyZeroMultiplicityNatMass T : Real) *
            (8 * (finiteGridSize T : Real) *
              realHarmonic (finiteGridSize T)) := hSum
        _ = _ := by ring
    _ <= (8 * (nearbyZeroMultiplicityNatMass T : Real) *
          realHarmonic (finiteGridSize T)) *
        (2 * ((goodGridIndices T).card : Real)) :=
      mul_le_mul_of_nonneg_left hCard hCoeff
    _ = ((goodGridIndices T).card : Real) *
        (16 * (nearbyZeroMultiplicityNatMass T : Real) *
          realHarmonic (finiteGridSize T)) := by ring

theorem exists_goodGridIndex_load_le_envelope
    (T : Nat) :
    Exists fun k : Nat =>
      Membership.mem (goodGridIndices T) k /\
        finiteGridReciprocalLoad T k <=
          16 * (nearbyZeroMultiplicityNatMass T : Real) *
            realHarmonic (finiteGridSize T) := by
  let B : Real :=
    16 * (nearbyZeroMultiplicityNatMass T : Real) *
      realHarmonic (finiteGridSize T)
  by_contra hNone
  push_neg at hNone
  have hStrict :
      ((goodGridIndices T).card : Real) * B <
        Finset.sum (goodGridIndices T) (finiteGridReciprocalLoad T) := by
    calc
      ((goodGridIndices T).card : Real) * B =
          Finset.sum (goodGridIndices T) (fun _ => B) := by simp
      _ < Finset.sum (goodGridIndices T) (finiteGridReciprocalLoad T) :=
        Finset.sum_lt_sum_of_nonempty (goodGridIndices_nonempty T) hNone
  have hUpper := goodGrid_load_sum_le_card_mul_envelope T
  dsimp [B] at hStrict
  linarith

noncomputable def finiteGridStrongIndex (T : Nat) : Nat :=
  Classical.choose (exists_goodGridIndex_load_le_envelope T)

noncomputable def finiteGridStrongTau (T : Nat) : Real :=
  gridPoint (T : Real) (finiteGridSize T) (finiteGridStrongIndex T)

noncomputable def finiteGridStrongDelta (T : Nat) : Real :=
  gridDelta (finiteGridSize T)

noncomputable def finiteGridStrongLoadEnvelope (T : Nat) : Real :=
  16 * (nearbyZeroMultiplicityNatMass T : Real) *
    realHarmonic (finiteGridSize T)

theorem finiteGridStrongIndex_mem_good (T : Nat) :
    Membership.mem (goodGridIndices T) (finiteGridStrongIndex T) :=
  (Classical.choose_spec (exists_goodGridIndex_load_le_envelope T)).1

theorem finiteGridStrongLoad_le (T : Nat) :
    TS295.Goldbach.reciprocalZeroLoad T (finiteGridStrongTau T) <=
      finiteGridStrongLoadEnvelope T := by
  exact (Classical.choose_spec (exists_goodGridIndex_load_le_envelope T)).2

theorem finiteGridStrongIndex_lt_size (T : Nat) :
    finiteGridStrongIndex T < finiteGridSize T := by
  have hMem := finiteGridStrongIndex_mem_good T
  exact (Finset.mem_sdiff.mp hMem).1 |> Finset.mem_range.mp

theorem finiteGridStrongTau_mem_Ioo (T : Nat) :
    Set.Mem (Set.Ioo (T : Real) ((T : Real) + 1))
      (finiteGridStrongTau T) := by
  exact gridPoint_mem_Ioo (T : Real) (finiteGridSize_pos T)
    (finiteGridStrongIndex_lt_size T)

theorem finiteGridStrongDelta_pos (T : Nat) :
    0 < finiteGridStrongDelta T :=
  gridDelta_pos (finiteGridSize_pos T)

theorem finiteGridStrongDelta_le_gap
    (T : Nat)
    (rho : TS292.Goldbach.ConcreteNontrivialZero)
    (hRho : Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho) :
    finiteGridStrongDelta T <=
      TS295.Goldbach.symmetricZeroHeightGap (finiteGridStrongTau T) rho :=
  goodGridIndex_gap_lower_bound T (finiteGridStrongIndex_mem_good T) rho hRho

theorem finiteGridStrongTau_gt (T : Nat) :
    (T : Real) < finiteGridStrongTau T :=
  (finiteGridStrongTau_mem_Ioo T).1

theorem finiteGridStrongTau_lt (T : Nat) :
    finiteGridStrongTau T < (T : Real) + 1 :=
  (finiteGridStrongTau_mem_Ioo T).2

theorem finiteGridStrongTau_pos {T : Nat} (hT : 1 <= T) :
    0 < finiteGridStrongTau T := by
  have hTR : (0 : Real) < T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  exact hTR.trans (finiteGridStrongTau_gt T)

theorem finiteGridStrong_gap_ne_zero
    (T : Nat)
    (rho : TS292.Goldbach.ConcreteNontrivialZero)
    (hRho : Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho) :
    Not
      (TS295.Goldbach.symmetricZeroHeightGap
        (finiteGridStrongTau T) rho = 0) := by
  exact ne_of_gt ((finiteGridStrongDelta_pos T).trans_le
    (finiteGridStrongDelta_le_gap T rho hRho))

theorem riemannZeta_ne_zero_on_finiteGridStrong_top
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigmaLeft : TS294.Goldbach.fixedPerronLeft <= sigma)
    (hSigmaRight : sigma <= TS294.Goldbach.fixedPerronRight) :
    Not
      (riemannZeta
        ((sigma : Complex) + (finiteGridStrongTau T : Complex) * Complex.I) = 0) := by
  intro hZero
  let s : Complex :=
    (sigma : Complex) + (finiteGridStrongTau T : Complex) * Complex.I
  have hConcrete :
      TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet s := by
    exact TS296.Goldbach.zeta_zero_in_fixed_strip_is_concrete
      (by simpa [s] using hSigmaLeft)
      (by simpa [s] using hSigmaRight)
      (by simp [s, ne_of_gt (finiteGridStrongTau_pos hT)])
      hZero
  let rho : TS292.Goldbach.ConcreteNontrivialZero :=
    Subtype.mk s hConcrete
  have hHeight : _root_.abs rho.1.im <= (T : Real) + 2 := by
    dsimp [rho, s]
    simp [abs_of_pos (finiteGridStrongTau_pos hT)]
    linarith [finiteGridStrongTau_lt T]
  have hRho :
      Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho := by
    apply
      (TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff
        (T + 2) rho).mpr
    exact hHeight.trans_eq (by push_cast; ring)
  apply finiteGridStrong_gap_ne_zero T rho hRho
  simp [TS295.Goldbach.symmetricZeroHeightGap, rho, s,
    abs_of_pos (finiteGridStrongTau_pos hT)]

theorem riemannZeta_ne_zero_on_finiteGridStrong_bottom
    (T : Nat)
    (hT : 1 <= T)
    (sigma : Real)
    (hSigmaLeft : TS294.Goldbach.fixedPerronLeft <= sigma)
    (hSigmaRight : sigma <= TS294.Goldbach.fixedPerronRight) :
    Not
      (riemannZeta
        ((sigma : Complex) - (finiteGridStrongTau T : Complex) * Complex.I) = 0) := by
  intro hZero
  let s : Complex :=
    (sigma : Complex) - (finiteGridStrongTau T : Complex) * Complex.I
  have hConcrete :
      TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet s := by
    exact TS296.Goldbach.zeta_zero_in_fixed_strip_is_concrete
      (by simpa [s] using hSigmaLeft)
      (by simpa [s] using hSigmaRight)
      (by simp [s, ne_of_gt (finiteGridStrongTau_pos hT)])
      hZero
  let rho : TS292.Goldbach.ConcreteNontrivialZero :=
    Subtype.mk s hConcrete
  have hHeight : _root_.abs rho.1.im <= (T : Real) + 2 := by
    dsimp [rho, s]
    simp [abs_of_pos (finiteGridStrongTau_pos hT)]
    linarith [finiteGridStrongTau_lt T]
  have hRho :
      Membership.mem (TS295.Goldbach.nearbyConcreteZeros T) rho := by
    apply
      (TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff
        (T + 2) rho).mpr
    exact hHeight.trans_eq (by push_cast; ring)
  apply finiteGridStrong_gap_ne_zero T rho hRho
  simp [TS295.Goldbach.symmetricZeroHeightGap, rho, s,
    abs_of_pos (finiteGridStrongTau_pos hT)]

noncomputable def finiteGridStrongPerronContourData
    (T : Nat)
    (hT : 1 <= T) :
    TS294.Goldbach.QuantitativelyCleanPerronContourData T where
  left := TS294.Goldbach.fixedPerronLeft
  right := TS294.Goldbach.fixedPerronRight
  tau := finiteGridStrongTau T
  left_lt_neg_one := TS294.Goldbach.fixedPerronLeft_lt_neg_one
  one_lt_right := TS294.Goldbach.one_lt_fixedPerronRight
  tau_pos := finiteGridStrongTau_pos hT
  height_ge := (finiteGridStrongTau_gt T).le
  height_le := (finiteGridStrongTau_lt T).le
  zeta_nonzero_on_bottom := by
    intro sigma hLeft hRight
    exact riemannZeta_ne_zero_on_finiteGridStrong_bottom
      T hT sigma hLeft hRight
  zeta_nonzero_on_top := by
    intro sigma hLeft hRight
    exact riemannZeta_ne_zero_on_finiteGridStrong_top
      T hT sigma hLeft hRight
  zeta_nonzero_on_left := by
    intro t hBottom hTop
    exact TS296.Goldbach.riemannZeta_ne_zero_on_fixed_left t
  left_eq_fixed := rfl
  right_eq_fixed := rfl
  zeroSeparation := finiteGridStrongDelta T
  zeroSeparation_pos := finiteGridStrongDelta_pos T
  separated_from_nearby_zeros := by
    intro rho hRho
    apply finiteGridStrongDelta_le_gap T rho
    apply
      (TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff
        (T + 2) rho).mpr
    exact hRho.trans_eq (by push_cast; ring)

theorem finiteGridStrongCleanPerronContourExistence :
    TS295.Goldbach.StrongCleanPerronContourExistenceStatement
      finiteGridStrongDelta finiteGridStrongLoadEnvelope := by
  intro T hT
  exact Exists.intro (finiteGridStrongPerronContourData T hT)
    (And.intro le_rfl (finiteGridStrongLoad_le T))

theorem nearbyZeroMultiplicityNatMass_eq_globalCount (T : Nat) :
    nearbyZeroMultiplicityNatMass T =
      TS270.Goldbach.concreteMultiplicityCountUpToHeight
        ((T + 2 : Nat) : Real) := by
  unfold nearbyZeroMultiplicityNatMass TS295.Goldbach.nearbyConcreteZeros
    TS292.Goldbach.concreteZerosUpToHeightSubtype
    TS270.Goldbach.concreteMultiplicityCountUpToHeight
  refine Finset.sum_bij
    (fun rho _ => rho.1) ?_ ?_ ?_ ?_
  next =>
    intro rho hRho
    exact Finset.mem_preimage.mp hRho
  next =>
    intro rhoOne hOne rhoTwo hTwo hEq
    exact Subtype.ext hEq
  next =>
    intro rho hRho
    have hZero :=
      (TS265.Goldbach.mem_zerosUpToHeight_iff
        ((T + 2 : Nat) : Real) rho).mp hRho |>.1
    let rhoSub : TS292.Goldbach.ConcreteNontrivialZero :=
      Subtype.mk rho hZero
    refine Exists.intro rhoSub (Exists.intro ?_ rfl)
    exact Finset.mem_preimage.mpr hRho
  next =>
    intro rho hRho
    simp [TS295.Goldbach.concreteZeroMultiplicity]

noncomputable def finiteGridMultiplicityEnvelope (T : Nat) : Real :=
  TS290.Goldbach.xiGlobalLogLinearConstant * ((T : Real) + 2) *
    Real.log ((T : Real) + 4)

noncomputable def finiteGridClosedLoadEnvelope (T : Nat) : Real :=
  16 * finiteGridMultiplicityEnvelope T *
    (1 + Real.log (4 * (finiteGridMultiplicityEnvelope T + 1)))

theorem nearbyZeroMultiplicityNatMass_le_envelope
    (T : Nat) (hT : 1 <= T) :
    (nearbyZeroMultiplicityNatMass T : Real) <=
      finiteGridMultiplicityEnvelope T := by
  rw [nearbyZeroMultiplicityNatMass_eq_globalCount]
  unfold finiteGridMultiplicityEnvelope
  convert TS290.Goldbach.concreteMultiplicityCountUpToHeight_le_logLinear
    (((T + 2 : Nat) : Real))
      (by exact_mod_cast (show 1 <= T + 2 by omega)) using 1
  all_goals (push_cast; ring)

theorem finiteGridMultiplicityEnvelope_nonnegative
    (T : Nat) (hT : 1 <= T) :
    0 <= finiteGridMultiplicityEnvelope T := by
  unfold finiteGridMultiplicityEnvelope
  exact mul_nonneg
    (mul_nonneg TS290.Goldbach.xiGlobalLogLinearConstant_nonnegative
      (by positivity))
    (Real.log_nonneg (by linarith : (1 : Real) <= (T : Real) + 4))

theorem finiteGridStrongLoadEnvelope_le_closed
    (T : Nat) (hT : 1 <= T) :
    finiteGridStrongLoadEnvelope T <= finiteGridClosedLoadEnvelope T := by
  let M : Real := nearbyZeroMultiplicityNatMass T
  let A : Real := finiteGridMultiplicityEnvelope T
  let K : Nat := finiteGridSize T
  have hMA : M <= A := nearbyZeroMultiplicityNatMass_le_envelope T hT
  have hM0 : 0 <= M := by dsimp [M]; positivity
  have hA0 : 0 <= A := finiteGridMultiplicityEnvelope_nonnegative T hT
  have hKpos : (0 : Real) < K := by
    exact_mod_cast finiteGridSize_pos T
  have hKBound : (K : Real) <= 4 * (A + 1) := by
    dsimp [K, M, A, finiteGridSize]
    push_cast
    nlinarith
  have hLogK : Real.log K <= Real.log (4 * (A + 1)) := by
    exact Real.log_le_log hKpos hKBound
  have hHarmonic :
      realHarmonic K <= 1 + Real.log (4 * (A + 1)) := by
    exact (realHarmonic_le_one_add_log K).trans (add_le_add_left hLogK 1)
  have hLogTarget0 : 0 <= 1 + Real.log (4 * (A + 1)) := by
    have hFour : (1 : Real) <= 4 * (A + 1) := by nlinarith
    exact add_nonneg zero_le_one (Real.log_nonneg hFour)
  unfold finiteGridStrongLoadEnvelope finiteGridClosedLoadEnvelope
  dsimp [M, A, K] at hMA hA0 hHarmonic hLogTarget0
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hMA (by norm_num))
    hHarmonic
    (realHarmonic_nonnegative _)
    (mul_nonneg (by norm_num) hA0)

theorem finiteGridStrongLoad_le_closed
    (T : Nat) (hT : 1 <= T) :
    TS295.Goldbach.reciprocalZeroLoad T (finiteGridStrongTau T) <=
      finiteGridClosedLoadEnvelope T :=
  (finiteGridStrongLoad_le T).trans
    (finiteGridStrongLoadEnvelope_le_closed T hT)

noncomputable def finiteGridClosedDelta (T : Nat) : Real :=
  1 / (16 * (finiteGridMultiplicityEnvelope T + 1))

theorem finiteGridClosedDelta_pos
    (T : Nat) (hT : 1 <= T) :
    0 < finiteGridClosedDelta T := by
  unfold finiteGridClosedDelta
  have hA := finiteGridMultiplicityEnvelope_nonnegative T hT
  positivity

theorem finiteGridClosedDelta_le_strongDelta
    (T : Nat) (hT : 1 <= T) :
    finiteGridClosedDelta T <= finiteGridStrongDelta T := by
  have hMass := nearbyZeroMultiplicityNatMass_le_envelope T hT
  have hKpos : (0 : Real) < finiteGridSize T := by
    exact_mod_cast finiteGridSize_pos T
  unfold finiteGridClosedDelta finiteGridStrongDelta gridDelta
  exact one_div_le_one_div_of_le (by positivity) (by
    unfold finiteGridSize
    push_cast
    nlinarith)

theorem finiteGridClosedStrongPerronContourExistence :
    TS295.Goldbach.StrongCleanPerronContourExistenceStatement
      finiteGridClosedDelta finiteGridClosedLoadEnvelope := by
  intro T hT
  exact Exists.intro (finiteGridStrongPerronContourData T hT)
    (And.intro
      (finiteGridClosedDelta_le_strongDelta T hT)
      (finiteGridStrongLoad_le_closed T hT))

structure FiniteGridStrongHeightLedger where
  harmonic_grid_kernel_bound_proved : True
  finite_bad_grid_count_proved : True
  admissible_grid_nonempty_proved : True
  reciprocal_load_averaging_proved : True
  quantitative_clean_contour_constructed : True
  exact_load_bound_proved : True
  ts290_closed_load_envelope_proved : True
  ts290_closed_separation_envelope_proved : True
  logarithm_sphere_rate_not_proved : True
  completion_correction_rate_not_proved : True
  left_boundary_not_estimated : True
  exceptional_inventory_not_completed : True
  perron_inversion_not_proved : True
  meromorphic_residue_theorem_not_proved : True
  infinite_explicit_formula_not_proved : True
  gallagher_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def finiteGridStrongHeightLedger : FiniteGridStrongHeightLedger :=
  { harmonic_grid_kernel_bound_proved := True.intro
    finite_bad_grid_count_proved := True.intro
    admissible_grid_nonempty_proved := True.intro
    reciprocal_load_averaging_proved := True.intro
    quantitative_clean_contour_constructed := True.intro
    exact_load_bound_proved := True.intro
    ts290_closed_load_envelope_proved := True.intro
    ts290_closed_separation_envelope_proved := True.intro
    logarithm_sphere_rate_not_proved := True.intro
    completion_correction_rate_not_proved := True.intro
    left_boundary_not_estimated := True.intro
    exceptional_inventory_not_completed := True.intro
    perron_inversion_not_proved := True.intro
    meromorphic_residue_theorem_not_proved := True.intro
    infinite_explicit_formula_not_proved := True.intro
    gallagher_not_proved := True.intro
    otsa_not_proved := True.intro
    goldbach_not_claimed := True.intro }
end Goldbach
end TS299
