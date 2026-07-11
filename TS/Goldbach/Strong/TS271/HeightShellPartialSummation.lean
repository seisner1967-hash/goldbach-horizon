import Mathlib.Tactic
import TS.Goldbach.Strong.TS270.HighZoneMultiplicityCountingInterface

/-!
# TS271 - Height-Shell Partial Summation

TS270 connected the high residual mass to multiplicity counting, but its crude
bound discarded the quadratic decay from TS269.  This sprint introduces exact
finite shells `(A, B]`, proves their multiplicity increments, bounds each shell
by its lower-height reciprocal square, and proves a reusable finite Abel
summation identity.

For every positive monotone height chain, any future global multiplicity-count
bound is transported to an amortized finite shell estimate.  No particular
chain is claimed to cover the complete TS269 high selection; that endpoint and
boundary bookkeeping remains explicit future work.

No effective zero count, zero-density theorem, infinite convergence, explicit
formula, residual bound, Gallagher estimate, or Goldbach statement is used or
proved.
-/

namespace TS271
namespace Goldbach

/-- Exact shell `(A, B]` formed from the concrete finite-height selections. -/
noncomputable def concreteHeightShell
    (A B : Real) :
    Finset Complex :=
  TS265.Goldbach.zerosUpToHeight B \ TS265.Goldbach.zerosUpToHeight A

/-- Membership characterization for the exact half-open height shell. -/
theorem mem_concreteHeightShell_iff
    (A B : Real)
    (rho : Complex) :
    Membership.mem (concreteHeightShell A B) rho <->
      TS264.Goldbach.concreteNontrivialRiemannZetaZeroSet rho /\
        A < abs rho.im /\
          abs rho.im <= B := by
  constructor
  case mp =>
    intro hRho
    have hDiff := Finset.mem_sdiff.mp hRho
    have hB :=
      (TS265.Goldbach.mem_zerosUpToHeight_iff B rho).mp hDiff.1
    have hLower : A < abs rho.im := by
      by_contra hNotLower
      have hAtA : abs rho.im <= A := le_of_not_gt hNotLower
      exact hDiff.2
        ((TS265.Goldbach.mem_zerosUpToHeight_iff A rho).mpr
          (And.intro hB.1 hAtA))
    exact And.intro hB.1 (And.intro hLower hB.2)
  case mpr =>
    intro hRho
    apply Finset.mem_sdiff.mpr
    constructor
    case left =>
      exact (TS265.Goldbach.mem_zerosUpToHeight_iff B rho).mpr
        (And.intro hRho.1 hRho.2.2)
    case right =>
      intro hAtA
      have hA :=
        (TS265.Goldbach.mem_zerosUpToHeight_iff A rho).mp hAtA
      exact (not_le_of_gt hRho.2.1) hA.2

/-- Concrete finite-height zero selections are monotone in the height. -/
theorem zerosUpToHeight_subset
    {A B : Real}
    (hAB : A <= B) :
    TS265.Goldbach.zerosUpToHeight A <=
      TS265.Goldbach.zerosUpToHeight B := by
  intro rho hRho
  have hData :=
    (TS265.Goldbach.mem_zerosUpToHeight_iff A rho).mp hRho
  exact (TS265.Goldbach.mem_zerosUpToHeight_iff B rho).mpr
    (And.intro hData.1 (hData.2.trans hAB))

/-- Exact analytic multiplicity count in the shell `(A, B]`. -/
noncomputable def concreteHeightShellMultiplicityCount
    (A B : Real) :
    Nat :=
  Finset.sum
    (concreteHeightShell A B)
    (fun rho =>
      TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho)

/-- The total count at `B` is the count at `A` plus the shell increment. -/
theorem concreteMultiplicityCountUpToHeight_eq_add_shellCount
    {A B : Real}
    (hAB : A <= B) :
    TS270.Goldbach.concreteMultiplicityCountUpToHeight B =
      TS270.Goldbach.concreteMultiplicityCountUpToHeight A +
        concreteHeightShellMultiplicityCount A B := by
  unfold TS270.Goldbach.concreteMultiplicityCountUpToHeight
    concreteHeightShellMultiplicityCount concreteHeightShell
  have hSum := Finset.sum_sdiff
    (f := fun rho =>
      TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho)
    (zerosUpToHeight_subset hAB)
  simpa [add_comm] using hSum.symm

/-- Real form of the exact shell-count increment. -/
theorem concreteHeightShellMultiplicityCount_cast_eq_sub
    {A B : Real}
    (hAB : A <= B) :
    (concreteHeightShellMultiplicityCount A B : Real) =
      (TS270.Goldbach.concreteMultiplicityCountUpToHeight B : Real) -
        (TS270.Goldbach.concreteMultiplicityCountUpToHeight A : Real) := by
  have hCount := concreteMultiplicityCountUpToHeight_eq_add_shellCount hAB
  have hCountReal :
      (TS270.Goldbach.concreteMultiplicityCountUpToHeight B : Real) =
        (TS270.Goldbach.concreteMultiplicityCountUpToHeight A : Real) +
          (concreteHeightShellMultiplicityCount A B : Real) := by
    exact_mod_cast hCount
  linarith

/-- Exact reciprocal-square residual mass in one height shell. -/
noncomputable def concreteHeightShellReciprocalSquareMass
    (A B : Real) :
    Real :=
  Finset.sum
    (concreteHeightShell A B)
    TS269.Goldbach.highImaginaryResidualEnvelope

/-- One shell term is bounded using the shell's positive lower height. -/
theorem highImaginaryResidualEnvelope_le_count_div_lower_sq
    {A B : Real}
    (hA : 0 < A)
    (rho : Complex)
    (hRho : Membership.mem (concreteHeightShell A B) rho) :
    TS269.Goldbach.highImaginaryResidualEnvelope rho <=
      (TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho :
        Real) / A ^ 2 := by
  have hLower := (mem_concreteHeightShell_iff A B rho).mp hRho |>.2.1
  have hAle : A <= abs rho.im := le_of_lt hLower
  have hA0 : 0 <= A := le_of_lt hA
  have hIm0 : 0 <= abs rho.im := abs_nonneg rho.im
  have hSq : A ^ 2 <= abs rho.im ^ 2 := by
    have hProduct :
        0 <= (abs rho.im - A) * (abs rho.im + A) :=
      mul_nonneg
        (sub_nonneg.mpr hAle)
        (add_nonneg hIm0 hA0)
    nlinarith
  unfold TS269.Goldbach.highImaginaryResidualEnvelope
  exact div_le_div_of_nonneg_left
    (Nat.cast_nonneg _)
    (pow_pos hA 2)
    hSq

/-- The shell residual mass is bounded by shell count divided by `A^2`. -/
theorem concreteHeightShellReciprocalSquareMass_le_count_div_sq
    {A B : Real}
    (hA : 0 < A) :
    concreteHeightShellReciprocalSquareMass A B <=
      (concreteHeightShellMultiplicityCount A B : Real) / A ^ 2 := by
  unfold concreteHeightShellReciprocalSquareMass
  calc
    Finset.sum
          (concreteHeightShell A B)
          TS269.Goldbach.highImaginaryResidualEnvelope <=
        Finset.sum
          (concreteHeightShell A B)
          (fun rho =>
            (TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity
              rho : Real) / A ^ 2) := by
      apply Finset.sum_le_sum
      intro rho hRho
      exact highImaginaryResidualEnvelope_le_count_div_lower_sq hA rho hRho
    _ = (concreteHeightShellMultiplicityCount A B : Real) / A ^ 2 := by
      unfold concreteHeightShellMultiplicityCount
      rw [Nat.cast_sum]
      exact
        (Finset.sum_div
          (concreteHeightShell A B)
          (fun rho =>
            (TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity
              rho : Real))
          (A ^ 2)).symm

/-- Finite Abel summation for arbitrary real sequences. -/
theorem finitePartialSummationIdentity
    (N weight : Nat -> Real)
    (K : Nat) :
    Finset.sum (Finset.range K)
        (fun n => (N (n + 1) - N n) * weight n) =
      N K * weight K - N 0 * weight 0 +
        Finset.sum (Finset.range K)
          (fun n => N (n + 1) * (weight n - weight (n + 1))) := by
  induction K with
  | zero =>
    simp
  | succ K hK =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hK]
    ring

/-- A nonnegative decreasing weight converts count bounds into Abel bounds. -/
theorem finitePartialSummationBound
    (N countBound weight : Nat -> Real)
    (hNNonnegative : forall n : Nat, 0 <= N n)
    (hCount : forall n : Nat, N n <= countBound n)
    (hWeightNonnegative : forall n : Nat, 0 <= weight n)
    (hWeightAntitone : Antitone weight)
    (K : Nat) :
    Finset.sum (Finset.range K)
        (fun n => (N (n + 1) - N n) * weight n) <=
      countBound K * weight K +
        Finset.sum (Finset.range K)
          (fun n =>
            countBound (n + 1) * (weight n - weight (n + 1))) := by
  rw [finitePartialSummationIdentity]
  have hInitial : 0 <= N 0 * weight 0 :=
    mul_nonneg (hNNonnegative 0) (hWeightNonnegative 0)
  calc
    N K * weight K - N 0 * weight 0 +
          Finset.sum (Finset.range K)
            (fun n => N (n + 1) * (weight n - weight (n + 1))) <=
        N K * weight K +
          Finset.sum (Finset.range K)
            (fun n => N (n + 1) * (weight n - weight (n + 1))) := by
      linarith
    _ <= countBound K * weight K +
          Finset.sum (Finset.range K)
            (fun n =>
              countBound (n + 1) * (weight n - weight (n + 1))) := by
      apply add_le_add
      next =>
        exact mul_le_mul_of_nonneg_right (hCount K) (hWeightNonnegative K)
      next =>
        apply Finset.sum_le_sum
        intro n _
        exact mul_le_mul_of_nonneg_right
          (hCount (n + 1))
          (sub_nonneg.mpr (hWeightAntitone (Nat.le_succ n)))

/-- Positive monotone threshold data for finite height shells. -/
structure PositiveMonotoneHeightChain
    (height : Nat -> Real) : Prop where
  positive :
    forall n : Nat, 0 < height n

  monotone :
    Monotone height

/-- Reciprocal-square weights attached to a height chain. -/
noncomputable def reciprocalSquareHeightWeight
    (height : Nat -> Real)
    (n : Nat) :
    Real :=
  1 / height n ^ 2

/-- Reciprocal-square height weights are nonnegative. -/
theorem reciprocalSquareHeightWeight_nonnegative
    (height : Nat -> Real)
    (n : Nat) :
    0 <= reciprocalSquareHeightWeight height n := by
  unfold reciprocalSquareHeightWeight
  exact one_div_nonneg.mpr (sq_nonneg (height n))

/-- Positive monotone heights produce decreasing reciprocal-square weights. -/
theorem reciprocalSquareHeightWeight_antitone
    (height : Nat -> Real)
    (hHeight : PositiveMonotoneHeightChain height) :
    Antitone (reciprocalSquareHeightWeight height) := by
  intro m n hmn
  have hmnHeight : height m <= height n := hHeight.monotone hmn
  have hm0 : 0 <= height m := le_of_lt (hHeight.positive m)
  have hn0 : 0 <= height n := le_of_lt (hHeight.positive n)
  have hSq : height m ^ 2 <= height n ^ 2 := by
    have hProduct :
        0 <= (height n - height m) * (height n + height m) :=
      mul_nonneg
        (sub_nonneg.mpr hmnHeight)
        (add_nonneg hn0 hm0)
    nlinarith
  unfold reciprocalSquareHeightWeight
  exact one_div_le_one_div_of_le (pow_pos (hHeight.positive m) 2) hSq

/-- Sum of exact reciprocal-square masses along a finite height chain. -/
noncomputable def concreteHeightShellReciprocalSquareMassSum
    (height : Nat -> Real)
    (K : Nat) :
    Real :=
  Finset.sum (Finset.range K)
    (fun n =>
      concreteHeightShellReciprocalSquareMass (height n) (height (n + 1)))

/-- Sum of shell multiplicity increments against reciprocal-square weights. -/
noncomputable def concreteHeightShellMultiplicityWeightedSum
    (height : Nat -> Real)
    (K : Nat) :
    Real :=
  Finset.sum (Finset.range K)
    (fun n =>
      (concreteHeightShellMultiplicityCount (height n) (height (n + 1)) :
          Real) * reciprocalSquareHeightWeight height n)

/-- Local shell bounds sum along every positive height chain. -/
theorem concreteHeightShellReciprocalSquareMassSum_le_weightedCountSum
    (height : Nat -> Real)
    (hHeight : PositiveMonotoneHeightChain height)
    (K : Nat) :
    concreteHeightShellReciprocalSquareMassSum height K <=
      concreteHeightShellMultiplicityWeightedSum height K := by
  unfold concreteHeightShellReciprocalSquareMassSum
    concreteHeightShellMultiplicityWeightedSum reciprocalSquareHeightWeight
  apply Finset.sum_le_sum
  intro n _
  simpa [div_eq_mul_inv, mul_comm] using
    concreteHeightShellReciprocalSquareMass_le_count_div_sq
      (hHeight.positive n)

/-- Shell increments equal differences of cumulative counts along the chain. -/
theorem concreteHeightShellMultiplicityWeightedSum_eq_countDifferences
    (height : Nat -> Real)
    (hHeight : PositiveMonotoneHeightChain height)
    (K : Nat) :
    concreteHeightShellMultiplicityWeightedSum height K =
      Finset.sum (Finset.range K)
        (fun n =>
          ((TS270.Goldbach.concreteMultiplicityCountUpToHeight
                (height (n + 1)) : Real) -
            (TS270.Goldbach.concreteMultiplicityCountUpToHeight
                (height n) : Real)) *
              reciprocalSquareHeightWeight height n) := by
  unfold concreteHeightShellMultiplicityWeightedSum
  apply Finset.sum_congr rfl
  intro n _
  rw [concreteHeightShellMultiplicityCount_cast_eq_sub
    (hHeight.monotone (Nat.le_succ n))]

/-- Exact finite Abel identity for concrete multiplicity counts. -/
theorem concreteMultiplicityCountFinitePartialSummation
    (height : Nat -> Real)
    (hHeight : PositiveMonotoneHeightChain height)
    (K : Nat) :
    concreteHeightShellMultiplicityWeightedSum height K =
      (TS270.Goldbach.concreteMultiplicityCountUpToHeight (height K) : Real) *
          reciprocalSquareHeightWeight height K -
        (TS270.Goldbach.concreteMultiplicityCountUpToHeight (height 0) : Real) *
          reciprocalSquareHeightWeight height 0 +
        Finset.sum (Finset.range K)
          (fun n =>
            (TS270.Goldbach.concreteMultiplicityCountUpToHeight
                (height (n + 1)) : Real) *
              (reciprocalSquareHeightWeight height n -
                reciprocalSquareHeightWeight height (n + 1))) := by
  rw [concreteHeightShellMultiplicityWeightedSum_eq_countDifferences
    height hHeight K]
  exact finitePartialSummationIdentity
    (fun n =>
      (TS270.Goldbach.concreteMultiplicityCountUpToHeight (height n) : Real))
    (reciprocalSquareHeightWeight height)
    K

/-- A global count bound yields an amortized finite shell estimate. -/
theorem concreteHeightShellReciprocalSquareMassSum_le_of_globalCount
    (height : Nat -> Real)
    (hHeight : PositiveMonotoneHeightChain height)
    (countBound : Real -> Real)
    (hCount : TS270.Goldbach.GlobalMultiplicityCountingBoundContract countBound)
    (K : Nat) :
    concreteHeightShellReciprocalSquareMassSum height K <=
      countBound (height K) * reciprocalSquareHeightWeight height K +
        Finset.sum (Finset.range K)
          (fun n =>
            countBound (height (n + 1)) *
              (reciprocalSquareHeightWeight height n -
                reciprocalSquareHeightWeight height (n + 1))) := by
  apply le_trans
    (concreteHeightShellReciprocalSquareMassSum_le_weightedCountSum
      height hHeight K)
  rw [concreteHeightShellMultiplicityWeightedSum_eq_countDifferences
    height hHeight K]
  exact finitePartialSummationBound
    (fun n =>
      (TS270.Goldbach.concreteMultiplicityCountUpToHeight (height n) : Real))
    (fun n => countBound (height n))
    (reciprocalSquareHeightWeight height)
    (fun _ => Nat.cast_nonneg _)
    (fun n => hCount.multiplicity_count_le (height n))
    (reciprocalSquareHeightWeight_nonnegative height)
    (reciprocalSquareHeightWeight_antitone height hHeight)
    K

/-- Ledger recording exact shells and finite partial summation. -/
structure HeightShellPartialSummationLedger where
  ts270_multiplicity_counting :
    TS270.Goldbach.HighZoneMultiplicityCountingInterfaceLedger

  exact_shell :
    Real -> Real -> Finset Complex

  exact_shell_count :
    Real -> Real -> Nat

  shell_count_increment :
    forall (A B : Real),
      A <= B ->
        TS270.Goldbach.concreteMultiplicityCountUpToHeight B =
          TS270.Goldbach.concreteMultiplicityCountUpToHeight A +
            exact_shell_count A B

  finite_partial_summation :
    forall (N weight : Nat -> Real) (K : Nat),
      Finset.sum (Finset.range K)
          (fun n => (N (n + 1) - N n) * weight n) =
        N K * weight K - N 0 * weight 0 +
          Finset.sum (Finset.range K)
            (fun n => N (n + 1) * (weight n - weight (n + 1)))

  global_count_to_amortized_shell_bound :
    forall
      (height : Nat -> Real)
      (_hHeight : PositiveMonotoneHeightChain height)
      (countBound : Real -> Real),
      TS270.Goldbach.GlobalMultiplicityCountingBoundContract countBound ->
        forall K : Nat,
          concreteHeightShellReciprocalSquareMassSum height K <=
            countBound (height K) * reciprocalSquareHeightWeight height K +
              Finset.sum (Finset.range K)
                (fun n =>
                  countBound (height (n + 1)) *
                    (reciprocalSquareHeightWeight height n -
                      reciprocalSquareHeightWeight height (n + 1)))

  concrete_shell_cover_of_high_zone_not_proved : True
  boundary_at_one_not_assembled : True
  effective_multiplicity_count_not_proved : True
  zero_counting_asymptotic_not_proved : True
  infinite_shell_convergence_not_proved : True
  global_weighted_zero_summability_not_proved : True
  explicit_formula_identity_not_proved : True
  residual_bound_not_proved : True
  gallagher_not_proved : True
  goldbach_not_claimed : True

/-- Concrete TS271 height-shell partial-summation ledger. -/
noncomputable def heightShellPartialSummationLedger :
    HeightShellPartialSummationLedger where
  ts270_multiplicity_counting :=
    TS270.Goldbach.highZoneMultiplicityCountingInterfaceLedger
  exact_shell :=
    concreteHeightShell
  exact_shell_count :=
    concreteHeightShellMultiplicityCount
  shell_count_increment :=
    fun _ _ hAB => concreteMultiplicityCountUpToHeight_eq_add_shellCount hAB
  finite_partial_summation :=
    finitePartialSummationIdentity
  global_count_to_amortized_shell_bound :=
    concreteHeightShellReciprocalSquareMassSum_le_of_globalCount
  concrete_shell_cover_of_high_zone_not_proved := True.intro
  boundary_at_one_not_assembled := True.intro
  effective_multiplicity_count_not_proved := True.intro
  zero_counting_asymptotic_not_proved := True.intro
  infinite_shell_convergence_not_proved := True.intro
  global_weighted_zero_summability_not_proved := True.intro
  explicit_formula_identity_not_proved := True.intro
  residual_bound_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS271. -/
def HeightShellPartialSummationTarget : Prop :=
  Nonempty HeightShellPartialSummationLedger

/-- TS271 target: exact finite shells retain quadratic decay under counting. -/
theorem heightShellPartialSummationTarget :
    HeightShellPartialSummationTarget :=
  Nonempty.intro heightShellPartialSummationLedger

end Goldbach
end TS271
