import Mathlib.Tactic
import TS.Goldbach.Strong.TS271.HeightShellPartialSummation

/-!
# TS272 - High-Zone Integer Shell Cover

TS271 proved exact generic shells and finite partial summation but deliberately
left the complete TS269 high-zone cover open.  This sprint uses the shifted
integer chain `height n = n + 1`.  At natural truncation height `X`, the strict
interior `1 < abs rho.im <= X` is exactly represented by the shells
`(1,2], ..., (X-1,X]`, while the boundary `abs rho.im = 1` remains a separate
finite object.

The high residual mass is decomposed exactly into boundary multiplicity and
the TS271 shell mass sum.  Every TS270 global multiplicity-counting bound is
then transported through the integer Abel estimate to the full real zero
contribution.

No effective zero count, zero-density theorem, infinite convergence, explicit
formula, residual bound, Gallagher estimate, OTSA bridge, or Goldbach statement
is used or proved.
-/

namespace TS272
namespace Goldbach

/-- Shifted integer heights `1, 2, 3, ...`. -/
noncomputable def shiftedIntegerHeight
    (n : Nat) :
    Real :=
  (n + 1 : Nat)

/-- The shifted integer chain is positive and monotone. -/
theorem shiftedIntegerHeight_positiveMonotone :
    TS271.Goldbach.PositiveMonotoneHeightChain shiftedIntegerHeight where
  positive := by
    intro n
    change (0 : Real) < ((n + 1 : Nat) : Real)
    exact_mod_cast Nat.zero_lt_succ n
  monotone := by
    intro m n hmn
    change ((m + 1 : Nat) : Real) <= ((n + 1 : Nat) : Real)
    exact_mod_cast Nat.add_le_add_right hmn 1

/-- Consecutive half-open shells are disjoint. -/
theorem consecutiveHeightShell_disjoint
    {A B C : Real} :
    Disjoint
      (TS271.Goldbach.concreteHeightShell A B)
      (TS271.Goldbach.concreteHeightShell B C) := by
  apply Finset.disjoint_left.mpr
  intro rho hAB hBC
  have hLeft :=
    (TS271.Goldbach.mem_concreteHeightShell_iff A B rho).mp hAB
  have hRight :=
    (TS271.Goldbach.mem_concreteHeightShell_iff B C rho).mp hBC
  linarith

/-- A shell across an intermediate height is the union of consecutive shells. -/
theorem concreteHeightShell_eq_union
    {A B C : Real}
    (hAB : A <= B)
    (hBC : B <= C) :
    TS271.Goldbach.concreteHeightShell A C =
      Union.union
        (TS271.Goldbach.concreteHeightShell A B)
        (TS271.Goldbach.concreteHeightShell B C) := by
  ext rho
  constructor
  case mp =>
    intro hAC
    have hData :=
      (TS271.Goldbach.mem_concreteHeightShell_iff A C rho).mp hAC
    by_cases hAtB : abs rho.im <= B
    case pos =>
      apply Finset.mem_union_left
      exact (TS271.Goldbach.mem_concreteHeightShell_iff A B rho).mpr
        (And.intro hData.1 (And.intro hData.2.1 hAtB))
    case neg =>
      apply Finset.mem_union_right
      exact (TS271.Goldbach.mem_concreteHeightShell_iff B C rho).mpr
        (And.intro hData.1
          (And.intro (lt_of_not_ge hAtB) hData.2.2))
  case mpr =>
    intro hUnion
    rcases Finset.mem_union.mp hUnion with hLeft | hRight
    case inl =>
      have hData :=
        (TS271.Goldbach.mem_concreteHeightShell_iff A B rho).mp hLeft
      exact (TS271.Goldbach.mem_concreteHeightShell_iff A C rho).mpr
        (And.intro hData.1
          (And.intro hData.2.1 (hData.2.2.trans hBC)))
    case inr =>
      have hData :=
        (TS271.Goldbach.mem_concreteHeightShell_iff B C rho).mp hRight
      exact (TS271.Goldbach.mem_concreteHeightShell_iff A C rho).mpr
        (And.intro hData.1
          (And.intro (lt_of_le_of_lt hAB hData.2.1) hData.2.2))

/-- A reversed or degenerate shell is empty. -/
theorem concreteHeightShell_eq_empty_of_le
    {A B : Real}
    (hBA : B <= A) :
    TS271.Goldbach.concreteHeightShell A B = {} := by
  unfold TS271.Goldbach.concreteHeightShell
  exact Finset.sdiff_eq_empty_iff_subset.mpr
    (TS271.Goldbach.zerosUpToHeight_subset hBA)

/-- Reciprocal-square shell mass is additive across an intermediate height. -/
theorem concreteHeightShellReciprocalSquareMass_add
    {A B C : Real}
    (hAB : A <= B)
    (hBC : B <= C) :
    TS271.Goldbach.concreteHeightShellReciprocalSquareMass A C =
      TS271.Goldbach.concreteHeightShellReciprocalSquareMass A B +
        TS271.Goldbach.concreteHeightShellReciprocalSquareMass B C := by
  unfold TS271.Goldbach.concreteHeightShellReciprocalSquareMass
  rw [concreteHeightShell_eq_union hAB hBC]
  exact Finset.sum_union
    (f := TS269.Goldbach.highImaginaryResidualEnvelope)
    consecutiveHeightShell_disjoint

/-- Integer shell masses telescope exactly from one to `K+1`. -/
theorem shiftedIntegerShellMassSum_telescope
    (K : Nat) :
    TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
        shiftedIntegerHeight K =
      TS271.Goldbach.concreteHeightShellReciprocalSquareMass
        1 (K + 1 : Nat) := by
  induction K with
  | zero =>
    unfold TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
      TS271.Goldbach.concreteHeightShellReciprocalSquareMass
    simp [TS271.Goldbach.concreteHeightShell,
      shiftedIntegerHeight]
  | succ K hK =>
    unfold TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum at hK
    unfold TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
    rw [Finset.sum_range_succ, hK]
    have hAdd := concreteHeightShellReciprocalSquareMass_add
      (A := (1 : Real))
      (B := (K + 1 : Nat))
      (C := (K + 2 : Nat))
      (by norm_num)
      (by norm_num)
    convert hAdd.symm using 1

/-- The `X-1` integer shells terminate exactly at natural height `X`. -/
theorem shiftedIntegerShellMassSum_eq_interiorMass
    (X : Nat) :
    TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
        shiftedIntegerHeight (X - 1) =
      TS271.Goldbach.concreteHeightShellReciprocalSquareMass 1 (X : Real) := by
  cases X with
  | zero =>
    have hEmpty :
        TS271.Goldbach.concreteHeightShell (1 : Real) 0 = {} :=
      concreteHeightShell_eq_empty_of_le (by norm_num)
    unfold TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
      TS271.Goldbach.concreteHeightShellReciprocalSquareMass
    simp [hEmpty]
  | succ X =>
    simpa using shiftedIntegerShellMassSum_telescope X

/-- Exact selected zeros on the boundary `abs rho.im = 1`. -/
noncomputable def concreteHeightOneBoundarySelection
    (X : Nat) :
    Finset Complex :=
  (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X).filter
    (fun rho => abs rho.im = 1)

/-- Membership characterization for the height-one boundary. -/
theorem mem_concreteHeightOneBoundarySelection_iff
    (X : Nat)
    (rho : Complex) :
    Membership.mem (concreteHeightOneBoundarySelection X) rho <->
      Membership.mem
          (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X) rho /\
        abs rho.im = 1 := by
  simp [concreteHeightOneBoundarySelection]

/-- Exact reciprocal-square residual mass on the height-one boundary. -/
noncomputable def concreteHeightOneBoundaryMass
    (X : Nat) :
    Real :=
  Finset.sum
    (concreteHeightOneBoundarySelection X)
    TS269.Goldbach.highImaginaryResidualEnvelope

/-- Exact multiplicity count on the height-one boundary. -/
noncomputable def concreteHeightOneBoundaryMultiplicityCount
    (X : Nat) :
    Nat :=
  Finset.sum
    (concreteHeightOneBoundarySelection X)
    (fun rho =>
      TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho)

/-- On the boundary, reciprocal-square mass equals multiplicity exactly. -/
theorem concreteHeightOneBoundaryMass_eq_multiplicityCount
    (X : Nat) :
    concreteHeightOneBoundaryMass X =
      (concreteHeightOneBoundaryMultiplicityCount X : Real) := by
  unfold concreteHeightOneBoundaryMass
    concreteHeightOneBoundaryMultiplicityCount
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro rho hRho
  have hOne :=
    (mem_concreteHeightOneBoundarySelection_iff X rho).mp hRho |>.2
  unfold TS269.Goldbach.highImaginaryResidualEnvelope
  rw [hOne]
  norm_num

/-- Boundary zeros are contained in the concrete selection up to height one. -/
theorem concreteHeightOneBoundarySelection_subset_zerosUpToHeightOne
    (X : Nat) :
    concreteHeightOneBoundarySelection X <=
      TS265.Goldbach.zerosUpToHeight 1 := by
  intro rho hRho
  have hBoundary :=
    (mem_concreteHeightOneBoundarySelection_iff X rho).mp hRho
  have hZero :=
    (TS265.Goldbach.mem_concreteFiniteHeightTruncation_iff X rho).mp
      hBoundary.1 |>.1
  exact (TS265.Goldbach.mem_zerosUpToHeight_iff 1 rho).mpr
    (And.intro hZero (le_of_eq hBoundary.2))

/-- Boundary multiplicity is bounded by the global count at height one. -/
theorem concreteHeightOneBoundaryMultiplicityCount_le_countAtOne
    (X : Nat) :
    concreteHeightOneBoundaryMultiplicityCount X <=
      TS270.Goldbach.concreteMultiplicityCountUpToHeight 1 := by
  unfold concreteHeightOneBoundaryMultiplicityCount
    TS270.Goldbach.concreteMultiplicityCountUpToHeight
  apply Finset.sum_le_sum_of_subset_of_nonneg
  case h =>
    exact concreteHeightOneBoundarySelection_subset_zerosUpToHeightOne X
  case hf =>
    intro rho _ _
    exact Nat.zero_le _

/-- The boundary is disjoint from the strict shell `(1,X]`. -/
theorem concreteHeightOneBoundary_disjoint_interiorShell
    (X : Nat) :
    Disjoint
      (concreteHeightOneBoundarySelection X)
      (TS271.Goldbach.concreteHeightShell 1 (X : Real)) := by
  apply Finset.disjoint_left.mpr
  intro rho hBoundary hInterior
  have hOne :=
    (mem_concreteHeightOneBoundarySelection_iff X rho).mp hBoundary |>.2
  have hStrict :=
    (TS271.Goldbach.mem_concreteHeightShell_iff 1 (X : Real) rho).mp
      hInterior |>.2.1
  linarith

/-- Exact high-zone partition into boundary and strict interior shell. -/
theorem concreteHighImaginaryZeroSelection_eq_boundary_union_interior
    (X : Nat) :
    TS269.Goldbach.concreteHighImaginaryZeroSelection X =
      Union.union
        (concreteHeightOneBoundarySelection X)
        (TS271.Goldbach.concreteHeightShell 1 (X : Real)) := by
  ext rho
  constructor
  case mp =>
    intro hHigh
    have hHighData :=
      (TS269.Goldbach.mem_concreteHighImaginaryZeroSelection_iff X rho).mp
        hHigh
    have hTrunc :=
      (TS265.Goldbach.mem_concreteFiniteHeightTruncation_iff X rho).mp
        hHighData.1
    rcases eq_or_lt_of_le hHighData.2 with hEq | hLt
    case inl =>
      apply Finset.mem_union_left
      exact (mem_concreteHeightOneBoundarySelection_iff X rho).mpr
        (And.intro hHighData.1 hEq.symm)
    case inr =>
      apply Finset.mem_union_right
      exact (TS271.Goldbach.mem_concreteHeightShell_iff 1 (X : Real) rho).mpr
        (And.intro hTrunc.1 (And.intro hLt hTrunc.2))
  case mpr =>
    intro hUnion
    rcases Finset.mem_union.mp hUnion with hBoundary | hInterior
    case inl =>
      have hData :=
        (mem_concreteHeightOneBoundarySelection_iff X rho).mp hBoundary
      exact (TS269.Goldbach.mem_concreteHighImaginaryZeroSelection_iff X rho).mpr
        (And.intro hData.1 (le_of_eq hData.2.symm))
    case inr =>
      have hData :=
        (TS271.Goldbach.mem_concreteHeightShell_iff 1 (X : Real) rho).mp
          hInterior
      have hTrunc :
          Membership.mem
            (TS265.Goldbach.concreteFiniteHeightTruncationData.zeros X) rho :=
        (TS265.Goldbach.mem_concreteFiniteHeightTruncation_iff X rho).mpr
          (And.intro hData.1 hData.2.2)
      exact (TS269.Goldbach.mem_concreteHighImaginaryZeroSelection_iff X rho).mpr
        (And.intro hTrunc (le_of_lt hData.2.1))

/-- Exact high residual mass splits into boundary and strict interior. -/
theorem concreteHighImaginaryWeightedResidualMass_eq_boundary_add_interior
    (X : Nat) :
    TS270.Goldbach.concreteHighImaginaryWeightedResidualMass X =
      concreteHeightOneBoundaryMass X +
        TS271.Goldbach.concreteHeightShellReciprocalSquareMass 1 (X : Real) := by
  unfold TS270.Goldbach.concreteHighImaginaryWeightedResidualMass
    concreteHeightOneBoundaryMass
    TS271.Goldbach.concreteHeightShellReciprocalSquareMass
  rw [concreteHighImaginaryZeroSelection_eq_boundary_union_interior X]
  exact Finset.sum_union
    (f := TS269.Goldbach.highImaginaryResidualEnvelope)
    (concreteHeightOneBoundary_disjoint_interiorShell X)

/-- Exact high residual mass expressed through boundary and integer shells. -/
theorem concreteHighImaginaryWeightedResidualMass_eq_boundary_add_integerShells
    (X : Nat) :
    TS270.Goldbach.concreteHighImaginaryWeightedResidualMass X =
      (concreteHeightOneBoundaryMultiplicityCount X : Real) +
        TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
          shiftedIntegerHeight (X - 1) := by
  rw [concreteHighImaginaryWeightedResidualMass_eq_boundary_add_interior X]
  rw [concreteHeightOneBoundaryMass_eq_multiplicityCount X]
  rw [shiftedIntegerShellMassSum_eq_interiorMass X]

/-- Exact high quadratic mass through boundary and integer shell masses. -/
theorem concreteHighImaginaryQuadraticEnvelopeMass_eq_boundary_add_integerShells
    (X : Nat) :
    TS269.Goldbach.concreteHighImaginaryQuadraticEnvelopeMass X =
      max 1 (X : Real) *
        ((concreteHeightOneBoundaryMultiplicityCount X : Real) +
          TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
            shiftedIntegerHeight (X - 1)) := by
  rw [TS270.Goldbach.concreteHighImaginaryQuadraticEnvelopeMass_eq_scale_mul_residualMass]
  rw [concreteHighImaginaryWeightedResidualMass_eq_boundary_add_integerShells]

/-- Finite amortized counting expression for the shifted integer chain. -/
noncomputable def shiftedIntegerAmortizedCountBound
    (countBound : Real -> Real)
    (X : Nat) :
    Real :=
  countBound (shiftedIntegerHeight (X - 1)) *
      TS271.Goldbach.reciprocalSquareHeightWeight
        shiftedIntegerHeight (X - 1) +
    Finset.sum (Finset.range (X - 1))
      (fun n =>
        countBound (shiftedIntegerHeight (n + 1)) *
          (TS271.Goldbach.reciprocalSquareHeightWeight shiftedIntegerHeight n -
            TS271.Goldbach.reciprocalSquareHeightWeight
              shiftedIntegerHeight (n + 1)))

/-- TS271 bounds the integer shell mass by the amortized count expression. -/
theorem shiftedIntegerShellMassSum_le_amortizedCountBound
    (countBound : Real -> Real)
    (hCount : TS270.Goldbach.GlobalMultiplicityCountingBoundContract countBound)
    (X : Nat) :
    TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
        shiftedIntegerHeight (X - 1) <=
      shiftedIntegerAmortizedCountBound countBound X := by
  unfold shiftedIntegerAmortizedCountBound
  exact TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum_le_of_globalCount
      shiftedIntegerHeight
      shiftedIntegerHeight_positiveMonotone
      countBound
      hCount
      (X - 1)

/-- Every global count bound controls boundary multiplicity at height one. -/
theorem concreteHeightOneBoundaryMultiplicityCount_le_globalCount
    (countBound : Real -> Real)
    (hCount : TS270.Goldbach.GlobalMultiplicityCountingBoundContract countBound)
    (X : Nat) :
    (concreteHeightOneBoundaryMultiplicityCount X : Real) <= countBound 1 := by
  have hBoundaryReal :
      (concreteHeightOneBoundaryMultiplicityCount X : Real) <=
        (TS270.Goldbach.concreteMultiplicityCountUpToHeight 1 : Real) := by
    exact_mod_cast concreteHeightOneBoundaryMultiplicityCount_le_countAtOne X
  exact hBoundaryReal.trans (hCount.multiplicity_count_le 1)

/-- The high residual mass is bounded by boundary plus amortized shell count. -/
theorem concreteHighImaginaryWeightedResidualMass_le_globalCountAmortized
    (countBound : Real -> Real)
    (hCount : TS270.Goldbach.GlobalMultiplicityCountingBoundContract countBound)
    (X : Nat) :
    TS270.Goldbach.concreteHighImaginaryWeightedResidualMass X <=
      countBound 1 + shiftedIntegerAmortizedCountBound countBound X := by
  rw [concreteHighImaginaryWeightedResidualMass_eq_boundary_add_integerShells]
  exact add_le_add
    (concreteHeightOneBoundaryMultiplicityCount_le_globalCount countBound hCount X)
    (shiftedIntegerShellMassSum_le_amortizedCountBound countBound hCount X)

/-- High quadratic mass bound preserving the integer-shell Abel damping. -/
theorem concreteHighImaginaryQuadraticEnvelopeMass_le_globalCountAmortized
    (countBound : Real -> Real)
    (hCount : TS270.Goldbach.GlobalMultiplicityCountingBoundContract countBound)
    (X : Nat) :
    TS269.Goldbach.concreteHighImaginaryQuadraticEnvelopeMass X <=
      max 1 (X : Real) *
        (countBound 1 + shiftedIntegerAmortizedCountBound countBound X) := by
  rw [TS270.Goldbach.concreteHighImaginaryQuadraticEnvelopeMass_eq_scale_mul_residualMass]
  exact mul_le_mul_of_nonneg_left
    (concreteHighImaginaryWeightedResidualMass_le_globalCountAmortized
      countBound hCount X)
    (zero_le_one.trans (le_max_left 1 (X : Real)))

/-- Full real zero-contribution bound with exact low mass and damped high mass. -/
theorem concreteFiniteHeightZeroContribution_abs_le_low_add_globalCountAmortized
    (countBound : Real -> Real)
    (hCount : TS270.Goldbach.GlobalMultiplicityCountingBoundContract countBound)
    (X : Nat) :
    abs
        (TS257.Goldbach.triangleSplineZeroContributionFunction
          TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
          TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
      TS269.Goldbach.concreteLowImaginaryWeightedNormMass X +
        max 1 (X : Real) *
          (countBound 1 + shiftedIntegerAmortizedCountBound countBound X) :=
  (TS269.Goldbach.concreteFiniteHeightZeroContribution_abs_le_low_add_highQuadratic X).trans
    (add_le_add_left
      (concreteHighImaginaryQuadraticEnvelopeMass_le_globalCountAmortized
        countBound hCount X) _)

/-- Ledger recording the exact integer-shell high-zone cover. -/
structure HighZoneIntegerShellCoverLedger where
  ts271_partial_summation :
    TS271.Goldbach.HeightShellPartialSummationLedger

  shifted_integer_chain :
    TS271.Goldbach.PositiveMonotoneHeightChain shiftedIntegerHeight

  boundary_selection :
    Nat -> Finset Complex

  boundary_multiplicity_count :
    Nat -> Nat

  high_zone_partition :
    forall X : Nat,
      TS269.Goldbach.concreteHighImaginaryZeroSelection X =
        Union.union
          (boundary_selection X)
          (TS271.Goldbach.concreteHeightShell 1 (X : Real))

  integer_shell_telescope :
    forall X : Nat,
      TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
          shiftedIntegerHeight (X - 1) =
        TS271.Goldbach.concreteHeightShellReciprocalSquareMass 1 (X : Real)

  high_mass_factorization :
    forall X : Nat,
      TS270.Goldbach.concreteHighImaginaryWeightedResidualMass X =
        (boundary_multiplicity_count X : Real) +
          TS271.Goldbach.concreteHeightShellReciprocalSquareMassSum
            shiftedIntegerHeight (X - 1)

  global_count_to_full_zero_bound :
    forall (countBound : Real -> Real),
      TS270.Goldbach.GlobalMultiplicityCountingBoundContract countBound ->
        forall X : Nat,
          abs
              (TS257.Goldbach.triangleSplineZeroContributionFunction
                TS264.Goldbach.concreteRiemannZetaZeroFamilyContract
                TS265.Goldbach.concreteFiniteHeightTruncationData X) <=
            TS269.Goldbach.concreteLowImaginaryWeightedNormMass X +
              max 1 (X : Real) *
                (countBound 1 + shiftedIntegerAmortizedCountBound countBound X)

  effective_multiplicity_count_not_proved : True
  zero_counting_asymptotic_not_proved : True
  infinite_shell_convergence_not_proved : True
  global_weighted_zero_summability_not_proved : True
  explicit_formula_identity_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS272 integer-shell cover ledger. -/
noncomputable def highZoneIntegerShellCoverLedger :
    HighZoneIntegerShellCoverLedger where
  ts271_partial_summation :=
    TS271.Goldbach.heightShellPartialSummationLedger
  shifted_integer_chain :=
    shiftedIntegerHeight_positiveMonotone
  boundary_selection :=
    concreteHeightOneBoundarySelection
  boundary_multiplicity_count :=
    concreteHeightOneBoundaryMultiplicityCount
  high_zone_partition :=
    concreteHighImaginaryZeroSelection_eq_boundary_union_interior
  integer_shell_telescope :=
    shiftedIntegerShellMassSum_eq_interiorMass
  high_mass_factorization :=
    concreteHighImaginaryWeightedResidualMass_eq_boundary_add_integerShells
  global_count_to_full_zero_bound :=
    concreteFiniteHeightZeroContribution_abs_le_low_add_globalCountAmortized
  effective_multiplicity_count_not_proved := True.intro
  zero_counting_asymptotic_not_proved := True.intro
  infinite_shell_convergence_not_proved := True.intro
  global_weighted_zero_summability_not_proved := True.intro
  explicit_formula_identity_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS272. -/
def HighZoneIntegerShellCoverTarget : Prop :=
  Nonempty HighZoneIntegerShellCoverLedger

/-- TS272 target: integer shells exactly cover and bound the high zone. -/
theorem highZoneIntegerShellCoverTarget :
    HighZoneIntegerShellCoverTarget :=
  Nonempty.intro highZoneIntegerShellCoverLedger

end Goldbach
end TS272
