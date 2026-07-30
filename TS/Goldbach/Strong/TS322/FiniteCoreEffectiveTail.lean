import Mathlib.Tactic
import TS.Goldbach.Strong.TS321.WeightedShellEnvelopeAssembly

namespace TS322
namespace Goldbach

noncomputable section

/-!
# TS322: finite core and effective coefficient tail

This module separates the exact finite TS321 shell core from the part of the
TS317 pair envelope involving coefficients above a chosen height.  The only
asymptotic input is the effective TS292 coefficient tail at arithmetic scale
one.  All bounds remain real-valued: no rational certificate or TS181
half-budget is constructed here.
-/

abbrev ConcreteNontrivialZero := TS292.Goldbach.ConcreteNontrivialZero

/-! ## Exact linear coefficient tail -/

/-- Exact subtype of concrete zeros outside the height-`H` truncation. -/
abbrev CoefficientTailIndex (H : Nat) :=
  {rho : ConcreteNontrivialZero //
    Not (Membership.mem (TS315.Goldbach.truncatedZeroSet H) rho)}

/-- Exact linear mass of coefficients outside the height-`H` truncation. -/
noncomputable def linearCoefficientTailMass (H : Nat) : Real :=
  tsum (fun rho : CoefficientTailIndex H =>
    TS316.Goldbach.zeroCoefficientMagnitude rho.1)

/-- Linear coefficient mass retained in the finite height-`H` core. -/
noncomputable def finiteLinearCoefficientMass (H : Nat) : Real :=
  Finset.sum (TS315.Goldbach.truncatedZeroSet H)
    TS316.Goldbach.zeroCoefficientMagnitude

theorem linearCoefficientTailMass_summable (H : Nat) :
    Summable (fun rho : CoefficientTailIndex H =>
      TS316.Goldbach.zeroCoefficientMagnitude rho.1) := by
  simpa [CoefficientTailIndex, Function.comp_def] using
    TS316.Goldbach.zeroCoefficientMagnitude_summable.subtype
      {rho : ConcreteNontrivialZero |
        Not (Membership.mem (TS315.Goldbach.truncatedZeroSet H) rho)}

theorem linearCoefficientTailMass_nonnegative (H : Nat) :
    0 <= linearCoefficientTailMass H := by
  unfold linearCoefficientTailMass
  exact tsum_nonneg (fun rho =>
    TS316.Goldbach.zeroCoefficientMagnitude_nonnegative rho.1)

theorem finiteLinearCoefficientMass_nonnegative (H : Nat) :
    0 <= finiteLinearCoefficientMass H := by
  unfold finiteLinearCoefficientMass
  exact Finset.sum_nonneg (fun rho _ =>
    TS316.Goldbach.zeroCoefficientMagnitude_nonnegative rho)

/-- TS292 gives the exact coefficient tail a uniform explicit real bound. -/
theorem linearCoefficientTailMass_le_effective
    (H : Nat) (hH : 1 <= H) :
    linearCoefficientTailMass H <=
      TS292.Goldbach.infiniteZeroResidualTailConstant *
        TS292.Goldbach.logarithmicTailRate H := by
  have hSummable := linearCoefficientTailMass_summable H
  apply tsum_le_of_sum_le hSummable
  intro s
  have hTail :=
    TS292.Goldbach.finiteInfiniteZeroSpectralTail_norm_sum_le 1 H hH s
  simpa [CoefficientTailIndex, TS315.Goldbach.truncatedZeroSet,
    TS316.Goldbach.zeroCoefficientMagnitude] using hTail

/-- The finite coefficient core and its exact complement partition the mass. -/
theorem finiteLinearCoefficientMass_add_tail
    (H : Nat) :
    finiteLinearCoefficientMass H + linearCoefficientTailMass H =
      TS316.Goldbach.globalLinearSpectralMass := by
  simpa [finiteLinearCoefficientMass, linearCoefficientTailMass,
    CoefficientTailIndex, TS315.Goldbach.truncatedZeroSet,
    TS316.Goldbach.globalLinearSpectralMass] using
      sum_add_tsum_subtype_compl
        TS316.Goldbach.zeroCoefficientMagnitude_summable
        (TS315.Goldbach.truncatedZeroSet H)

theorem finiteLinearCoefficientMass_le_global (H : Nat) :
    finiteLinearCoefficientMass H <=
      TS316.Goldbach.globalLinearSpectralMass := by
  rw [<- finiteLinearCoefficientMass_add_tail H]
  exact le_add_of_nonneg_right (linearCoefficientTailMass_nonnegative H)

theorem linearCoefficientTailMass_le_global (H : Nat) :
    linearCoefficientTailMass H <=
      TS316.Goldbach.globalLinearSpectralMass := by
  rw [<- finiteLinearCoefficientMass_add_tail H]
  exact le_add_of_nonneg_left (finiteLinearCoefficientMass_nonnegative H)

theorem finiteLinearCoefficientMass_tendsto_global :
    Filter.Tendsto finiteLinearCoefficientMass Filter.atTop
      (nhds TS316.Goldbach.globalLinearSpectralMass) := by
  simpa [finiteLinearCoefficientMass, TS315.Goldbach.truncatedZeroSet,
    TS316.Goldbach.globalLinearSpectralMass] using
      TS316.Goldbach.zeroCoefficientMagnitude_summable.hasSum.comp
        TS292.Goldbach.concreteZerosUpToHeightSubtype_tendsto_atTop

theorem linearCoefficientTailMass_eq_global_sub_finite
    (H : Nat) :
    linearCoefficientTailMass H =
      TS316.Goldbach.globalLinearSpectralMass -
        finiteLinearCoefficientMass H := by
  linarith [finiteLinearCoefficientMass_add_tail H]

theorem linearCoefficientTailMass_tendsto_zero :
    Filter.Tendsto linearCoefficientTailMass Filter.atTop (nhds 0) := by
  have hSub :
      Filter.Tendsto
        (fun H => TS316.Goldbach.globalLinearSpectralMass -
          finiteLinearCoefficientMass H)
        Filter.atTop (nhds
          (TS316.Goldbach.globalLinearSpectralMass -
            TS316.Goldbach.globalLinearSpectralMass)) :=
    tendsto_const_nhds.sub finiteLinearCoefficientMass_tendsto_global
  simpa only [sub_self] using
    hSub.congr' (Filter.Eventually.of_forall fun H =>
      (linearCoefficientTailMass_eq_global_sub_finite H).symm)

/-! ## Finite TS321 core -/

/-- Exact finite TS321 coefficient-shell majorant at height `H`. -/
noncomputable def finiteWeightedLocalCore (H : Nat) : Real :=
  TS321.Goldbach.weightedNearPairCoefficientMass H +
    Finset.sum (Finset.Ico 1 (2 * H)) (fun k =>
      (1 / (k : Real)) *
        TS321.Goldbach.weightedGapShellCoefficientMass H k)

theorem finiteWeightedLocalCore_nonnegative (H : Nat) :
    0 <= finiteWeightedLocalCore H := by
  unfold finiteWeightedLocalCore
  exact add_nonneg
    (TS321.Goldbach.weightedNearPairCoefficientMass_nonnegative H)
    (Finset.sum_nonneg fun k _ =>
      mul_nonneg (by positivity)
        (TS321.Goldbach.weightedGapShellCoefficientMass_nonnegative H k))

/-- The exact TS317 envelope at height `H` is controlled by the finite core. -/
theorem weightedClosePairEnvelope_le_finiteWeightedLocalCore (H : Nat) :
    TS317.Goldbach.weightedClosePairEnvelope H <=
      finiteWeightedLocalCore H := by
  exact TS321.Goldbach.weightedClosePairEnvelope_le_coefficientShellAssembly H

/-! ## Ordered-pair representation and truncation monotonicity -/

/-- Ordered off-diagonal pairs in the concrete height truncation. -/
noncomputable def orderedOffDiagonalZeroPairs (T : Nat) :
    Finset (Prod ConcreteNontrivialZero ConcreteNontrivialZero) :=
  Finset.filter (fun pair => Not (pair.1 = pair.2))
    ((TS315.Goldbach.truncatedZeroSet T).product
      (TS315.Goldbach.truncatedZeroSet T))

/-- The exact nonnegative TS317 envelope summand attached to an ordered pair. -/
noncomputable def orderedPairEnvelopeTerm
    (pair : Prod ConcreteNontrivialZero ConcreteNontrivialZero) : Real :=
  TS321.Goldbach.zeroPairCoefficientMass pair.1 pair.2 *
    TS317.Goldbach.ordinateGapDecayWeight pair.1 pair.2

theorem orderedPairEnvelopeTerm_nonnegative
    (pair : Prod ConcreteNontrivialZero ConcreteNontrivialZero) :
    0 <= orderedPairEnvelopeTerm pair := by
  unfold orderedPairEnvelopeTerm
  exact mul_nonneg
    (TS321.Goldbach.zeroPairCoefficientMass_nonnegative pair.1 pair.2)
    (TS317.Goldbach.ordinateGapDecayWeight_nonnegative pair.1 pair.2)

theorem weightedClosePairEnvelope_eq_orderedPairSum (T : Nat) :
    TS317.Goldbach.weightedClosePairEnvelope T =
      Finset.sum (orderedOffDiagonalZeroPairs T) orderedPairEnvelopeTerm := by
  classical
  unfold TS317.Goldbach.weightedClosePairEnvelope
    orderedOffDiagonalZeroPairs orderedPairEnvelopeTerm
    TS321.Goldbach.zeroPairCoefficientMass
  rw [Finset.sum_filter]
  calc
    Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
        Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho)
          (fun sigma =>
            TS316.Goldbach.zeroCoefficientMagnitude rho *
                TS316.Goldbach.zeroCoefficientMagnitude sigma *
              TS317.Goldbach.ordinateGapDecayWeight rho sigma)) =
      Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun rho =>
        Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun sigma =>
          if Not (rho = sigma) then
            TS316.Goldbach.zeroCoefficientMagnitude rho *
                TS316.Goldbach.zeroCoefficientMagnitude sigma *
              TS317.Goldbach.ordinateGapDecayWeight rho sigma
          else 0)) := by
      apply Finset.sum_congr rfl
      intro rho hRho
      symm
      calc
        Finset.sum (TS315.Goldbach.truncatedZeroSet T) (fun sigma =>
            if Not (rho = sigma) then
              TS316.Goldbach.zeroCoefficientMagnitude rho *
                  TS316.Goldbach.zeroCoefficientMagnitude sigma *
                TS317.Goldbach.ordinateGapDecayWeight rho sigma
            else 0) =
          Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho)
            (fun sigma =>
              if Not (rho = sigma) then
                TS316.Goldbach.zeroCoefficientMagnitude rho *
                    TS316.Goldbach.zeroCoefficientMagnitude sigma *
                  TS317.Goldbach.ordinateGapDecayWeight rho sigma
              else 0) := by
          symm
          apply Finset.sum_erase
          simp
        _ = Finset.sum ((TS315.Goldbach.truncatedZeroSet T).erase rho)
            (fun sigma =>
              TS316.Goldbach.zeroCoefficientMagnitude rho *
                  TS316.Goldbach.zeroCoefficientMagnitude sigma *
                TS317.Goldbach.ordinateGapDecayWeight rho sigma) := by
          apply Finset.sum_congr rfl
          intro sigma hSigma
          have hNe : Not (rho = sigma) := by
            exact ne_comm.mp (Finset.ne_of_mem_erase hSigma)
          rw [if_pos hNe]
    _ = Finset.sum
        ((TS315.Goldbach.truncatedZeroSet T).product
          (TS315.Goldbach.truncatedZeroSet T))
        (fun pair =>
          if Not (pair.1 = pair.2) then
            TS316.Goldbach.zeroCoefficientMagnitude pair.1 *
                TS316.Goldbach.zeroCoefficientMagnitude pair.2 *
              TS317.Goldbach.ordinateGapDecayWeight pair.1 pair.2
          else 0) := by
      symm
      exact Finset.sum_product _ _ _

theorem truncatedZeroSet_mono
    {H T : Nat} (hHT : H <= T) :
    TS315.Goldbach.truncatedZeroSet H <=
      TS315.Goldbach.truncatedZeroSet T := by
  intro rho hRho
  unfold TS315.Goldbach.truncatedZeroSet at hRho
  unfold TS315.Goldbach.truncatedZeroSet
  apply (TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff T rho).mpr
  exact
    ((TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff H rho).mp hRho).trans
      (by exact_mod_cast hHT)

theorem orderedOffDiagonalZeroPairs_mono
    {H T : Nat} (hHT : H <= T) :
    orderedOffDiagonalZeroPairs H <= orderedOffDiagonalZeroPairs T := by
  intro pair hPair
  change Membership.mem
    (Finset.filter (fun pair => Not (pair.1 = pair.2))
      ((TS315.Goldbach.truncatedZeroSet H).product
        (TS315.Goldbach.truncatedZeroSet H))) pair at hPair
  have hPairData := Finset.mem_filter.mp hPair
  have hCoordinates := Finset.mem_product.mp hPairData.1
  change Membership.mem
    (Finset.filter (fun pair => Not (pair.1 = pair.2))
      ((TS315.Goldbach.truncatedZeroSet T).product
        (TS315.Goldbach.truncatedZeroSet T))) pair
  apply Finset.mem_filter.mpr
  exact And.intro
    (Finset.mem_product.mpr (And.intro
      (truncatedZeroSet_mono hHT hCoordinates.1)
      (truncatedZeroSet_mono hHT hCoordinates.2)))
    hPairData.2

/-- Exact new-pair contribution between heights `H` and `T`. -/
noncomputable def weightedPairIncrement (T H : Nat) : Real :=
  Finset.sum
    (orderedOffDiagonalZeroPairs T \ orderedOffDiagonalZeroPairs H)
    orderedPairEnvelopeTerm

theorem weightedPairIncrement_nonnegative (T H : Nat) :
    0 <= weightedPairIncrement T H := by
  unfold weightedPairIncrement
  exact Finset.sum_nonneg (fun pair _ =>
    orderedPairEnvelopeTerm_nonnegative pair)

theorem weightedClosePairEnvelope_eq_coreEnvelope_add_increment
    (T H : Nat) (hHT : H <= T) :
    TS317.Goldbach.weightedClosePairEnvelope T =
      TS317.Goldbach.weightedClosePairEnvelope H +
        weightedPairIncrement T H := by
  rw [weightedClosePairEnvelope_eq_orderedPairSum,
    weightedClosePairEnvelope_eq_orderedPairSum]
  have hSplit := Finset.sum_sdiff (orderedOffDiagonalZeroPairs_mono hHT)
    (f := orderedPairEnvelopeTerm)
  unfold weightedPairIncrement
  linarith

/-! ## Uniform control of the new ordered pairs -/

/-- Finite coefficient mass added between heights `H` and `T`. -/
noncomputable def finiteCoefficientTailMass (T H : Nat) : Real :=
  Finset.sum
    (TS315.Goldbach.truncatedZeroSet T \
      TS315.Goldbach.truncatedZeroSet H)
    TS316.Goldbach.zeroCoefficientMagnitude

theorem finiteCoefficientTailMass_nonnegative (T H : Nat) :
    0 <= finiteCoefficientTailMass T H := by
  unfold finiteCoefficientTailMass
  exact Finset.sum_nonneg (fun rho _ =>
    TS316.Goldbach.zeroCoefficientMagnitude_nonnegative rho)

theorem finiteCoefficientTailMass_add_core
    (T H : Nat) (hHT : H <= T) :
    finiteCoefficientTailMass T H + finiteLinearCoefficientMass H =
      finiteLinearCoefficientMass T := by
  simpa [finiteCoefficientTailMass, finiteLinearCoefficientMass] using
    Finset.sum_sdiff (truncatedZeroSet_mono hHT)
      (f := TS316.Goldbach.zeroCoefficientMagnitude)

theorem finiteCoefficientTailMass_le_linearTail
    (T H : Nat) (hHT : H <= T) :
    finiteCoefficientTailMass T H <= linearCoefficientTailMass H := by
  have hFinite := finiteLinearCoefficientMass_le_global T
  have hPartition := finiteCoefficientTailMass_add_core T H hHT
  have hGlobal := finiteLinearCoefficientMass_add_tail H
  linarith

/-- Product of exact coefficient magnitudes on an ordered pair. -/
noncomputable def orderedPairCoefficientTerm
    (pair : Prod ConcreteNontrivialZero ConcreteNontrivialZero) : Real :=
  TS321.Goldbach.zeroPairCoefficientMass pair.1 pair.2

theorem orderedPairCoefficientTerm_nonnegative
    (pair : Prod ConcreteNontrivialZero ConcreteNontrivialZero) :
    0 <= orderedPairCoefficientTerm pair := by
  exact TS321.Goldbach.zeroPairCoefficientMass_nonnegative pair.1 pair.2

theorem orderedPairEnvelopeTerm_le_coefficient
    (pair : Prod ConcreteNontrivialZero ConcreteNontrivialZero) :
    orderedPairEnvelopeTerm pair <= orderedPairCoefficientTerm pair := by
  unfold orderedPairEnvelopeTerm orderedPairCoefficientTerm
  exact mul_le_of_le_one_right
    (TS321.Goldbach.zeroPairCoefficientMass_nonnegative pair.1 pair.2)
    (TS317.Goldbach.ordinateGapDecayWeight_le_one pair.1 pair.2)

/-- New pairs whose first coordinate lies above the finite core. -/
noncomputable def leftTailPairRectangle (T H : Nat) :
    Finset (Prod ConcreteNontrivialZero ConcreteNontrivialZero) :=
  (TS315.Goldbach.truncatedZeroSet T \
      TS315.Goldbach.truncatedZeroSet H).product
    (TS315.Goldbach.truncatedZeroSet T)

/-- New pairs whose second coordinate lies above the finite core. -/
noncomputable def rightTailPairRectangle (T H : Nat) :
    Finset (Prod ConcreteNontrivialZero ConcreteNontrivialZero) :=
  (TS315.Goldbach.truncatedZeroSet T).product
    (TS315.Goldbach.truncatedZeroSet T \
      TS315.Goldbach.truncatedZeroSet H)

/-- New pairs whose first coordinate lies in the coefficient tail. -/
noncomputable def firstTailIncrementPairs (T H : Nat) :
    Finset (Prod ConcreteNontrivialZero ConcreteNontrivialZero) :=
  Finset.filter
    (fun pair => Not (Membership.mem
      (TS315.Goldbach.truncatedZeroSet H) pair.1))
    (orderedOffDiagonalZeroPairs T \ orderedOffDiagonalZeroPairs H)

/-- New pairs whose first coordinate remains in the finite core. -/
noncomputable def firstCoreIncrementPairs (T H : Nat) :
    Finset (Prod ConcreteNontrivialZero ConcreteNontrivialZero) :=
  Finset.filter
    (fun pair => Membership.mem
      (TS315.Goldbach.truncatedZeroSet H) pair.1)
    (orderedOffDiagonalZeroPairs T \ orderedOffDiagonalZeroPairs H)

theorem weightedPairIncrement_eq_firstTail_add_firstCore
    (T H : Nat) :
    weightedPairIncrement T H =
      Finset.sum (firstTailIncrementPairs T H) orderedPairEnvelopeTerm +
        Finset.sum (firstCoreIncrementPairs T H) orderedPairEnvelopeTerm := by
  unfold weightedPairIncrement firstTailIncrementPairs
    firstCoreIncrementPairs
  have hSplit := Finset.sum_filter_add_sum_filter_not
    (orderedOffDiagonalZeroPairs T \ orderedOffDiagonalZeroPairs H)
    (fun pair => Membership.mem
      (TS315.Goldbach.truncatedZeroSet H) pair.1)
    orderedPairEnvelopeTerm
  linarith

theorem firstTailIncrementPairs_subset_leftRectangle
    (T H : Nat) :
    firstTailIncrementPairs T H <= leftTailPairRectangle T H := by
  intro pair hPair
  have hFiltered := Finset.mem_filter.mp hPair
  have hPairData := Finset.mem_sdiff.mp hFiltered.1
  have hTotal := Finset.mem_filter.mp hPairData.1
  have hCoordinates := Finset.mem_product.mp hTotal.1
  unfold leftTailPairRectangle
  exact Finset.mem_product.mpr (And.intro
    (Finset.mem_sdiff.mpr (And.intro hCoordinates.1 hFiltered.2))
    hCoordinates.2)

theorem firstCoreIncrementPairs_subset_rightRectangle
    (T H : Nat) :
    firstCoreIncrementPairs T H <= rightTailPairRectangle T H := by
  intro pair hPair
  have hFiltered := Finset.mem_filter.mp hPair
  have hPairData := Finset.mem_sdiff.mp hFiltered.1
  have hTotal := Finset.mem_filter.mp hPairData.1
  have hCoordinates := Finset.mem_product.mp hTotal.1
  have hSecond : Not (Membership.mem
      (TS315.Goldbach.truncatedZeroSet H) pair.2) := by
    intro hSecond
    apply hPairData.2
    apply Finset.mem_filter.mpr
    exact And.intro
      (Finset.mem_product.mpr (And.intro hFiltered.2 hSecond))
      hTotal.2
  unfold rightTailPairRectangle
  exact Finset.mem_product.mpr (And.intro hCoordinates.1
    (Finset.mem_sdiff.mpr (And.intro hCoordinates.2 hSecond)))

theorem leftTailPairRectangle_coefficient_sum
    (T H : Nat) :
    Finset.sum (leftTailPairRectangle T H) orderedPairCoefficientTerm =
      finiteCoefficientTailMass T H * finiteLinearCoefficientMass T := by
  unfold leftTailPairRectangle orderedPairCoefficientTerm
    TS321.Goldbach.zeroPairCoefficientMass finiteCoefficientTailMass
    finiteLinearCoefficientMass
  calc
    Finset.sum
        ((TS315.Goldbach.truncatedZeroSet T \
            TS315.Goldbach.truncatedZeroSet H).product
          (TS315.Goldbach.truncatedZeroSet T))
        (fun pair =>
          TS316.Goldbach.zeroCoefficientMagnitude pair.1 *
            TS316.Goldbach.zeroCoefficientMagnitude pair.2) =
      Finset.sum
          (TS315.Goldbach.truncatedZeroSet T \
            TS315.Goldbach.truncatedZeroSet H)
          (fun rho => Finset.sum (TS315.Goldbach.truncatedZeroSet T)
            (fun sigma =>
              TS316.Goldbach.zeroCoefficientMagnitude rho *
                TS316.Goldbach.zeroCoefficientMagnitude sigma)) :=
      Finset.sum_product _ _ _
    _ = Finset.sum
          (TS315.Goldbach.truncatedZeroSet T \
            TS315.Goldbach.truncatedZeroSet H)
          TS316.Goldbach.zeroCoefficientMagnitude *
        Finset.sum (TS315.Goldbach.truncatedZeroSet T)
          TS316.Goldbach.zeroCoefficientMagnitude := by
      symm
      exact Finset.sum_mul_sum _ _ _ _

theorem rightTailPairRectangle_coefficient_sum
    (T H : Nat) :
    Finset.sum (rightTailPairRectangle T H) orderedPairCoefficientTerm =
      finiteLinearCoefficientMass T * finiteCoefficientTailMass T H := by
  unfold rightTailPairRectangle orderedPairCoefficientTerm
    TS321.Goldbach.zeroPairCoefficientMass finiteCoefficientTailMass
    finiteLinearCoefficientMass
  calc
    Finset.sum
        ((TS315.Goldbach.truncatedZeroSet T).product
          (TS315.Goldbach.truncatedZeroSet T \
            TS315.Goldbach.truncatedZeroSet H))
        (fun pair =>
          TS316.Goldbach.zeroCoefficientMagnitude pair.1 *
            TS316.Goldbach.zeroCoefficientMagnitude pair.2) =
      Finset.sum (TS315.Goldbach.truncatedZeroSet T)
          (fun rho => Finset.sum
            (TS315.Goldbach.truncatedZeroSet T \
              TS315.Goldbach.truncatedZeroSet H)
            (fun sigma =>
              TS316.Goldbach.zeroCoefficientMagnitude rho *
                TS316.Goldbach.zeroCoefficientMagnitude sigma)) :=
      Finset.sum_product _ _ _
    _ = Finset.sum (TS315.Goldbach.truncatedZeroSet T)
          TS316.Goldbach.zeroCoefficientMagnitude *
        Finset.sum
          (TS315.Goldbach.truncatedZeroSet T \
            TS315.Goldbach.truncatedZeroSet H)
          TS316.Goldbach.zeroCoefficientMagnitude := by
      symm
      exact Finset.sum_mul_sum _ _ _ _

theorem weightedPairIncrement_le_finiteMasses
    (T H : Nat) :
    weightedPairIncrement T H <=
      2 * finiteLinearCoefficientMass T * finiteCoefficientTailMass T H := by
  rw [weightedPairIncrement_eq_firstTail_add_firstCore]
  calc
    Finset.sum (firstTailIncrementPairs T H) orderedPairEnvelopeTerm +
        Finset.sum (firstCoreIncrementPairs T H) orderedPairEnvelopeTerm <=
      Finset.sum (firstTailIncrementPairs T H) orderedPairCoefficientTerm +
        Finset.sum (firstCoreIncrementPairs T H)
          orderedPairCoefficientTerm := by
      apply add_le_add
      next =>
        apply Finset.sum_le_sum
        intro pair hPair
        exact orderedPairEnvelopeTerm_le_coefficient pair
      next =>
        apply Finset.sum_le_sum
        intro pair hPair
        exact orderedPairEnvelopeTerm_le_coefficient pair
    _ <= Finset.sum (leftTailPairRectangle T H) orderedPairCoefficientTerm +
        Finset.sum (rightTailPairRectangle T H)
          orderedPairCoefficientTerm := by
      exact add_le_add
        (Finset.sum_le_sum_of_subset_of_nonneg
          (firstTailIncrementPairs_subset_leftRectangle T H)
          (fun pair _ _ => orderedPairCoefficientTerm_nonnegative pair))
        (Finset.sum_le_sum_of_subset_of_nonneg
          (firstCoreIncrementPairs_subset_rightRectangle T H)
          (fun pair _ _ => orderedPairCoefficientTerm_nonnegative pair))
    _ = finiteCoefficientTailMass T H * finiteLinearCoefficientMass T +
        finiteLinearCoefficientMass T * finiteCoefficientTailMass T H := by
      rw [leftTailPairRectangle_coefficient_sum,
        rightTailPairRectangle_coefficient_sum]
    _ = 2 * finiteLinearCoefficientMass T * finiteCoefficientTailMass T H := by
      ring

/-- Real effective error used by the robust uniform TS322 theorem. -/
noncomputable def effectiveWeightedTailError (H : Nat) : Real :=
  2 * TS316.Goldbach.globalLinearSpectralMass *
    linearCoefficientTailMass H

theorem effectiveWeightedTailError_nonnegative (H : Nat) :
    0 <= effectiveWeightedTailError H := by
  unfold effectiveWeightedTailError
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      TS316.Goldbach.globalLinearSpectralMass_nonnegative)
    (linearCoefficientTailMass_nonnegative H)

theorem effectiveWeightedTailError_le_explicit
    (H : Nat) (hH : 1 <= H) :
    effectiveWeightedTailError H <=
      2 * TS316.Goldbach.globalLinearSpectralMass *
        (TS292.Goldbach.infiniteZeroResidualTailConstant *
          TS292.Goldbach.logarithmicTailRate H) := by
  unfold effectiveWeightedTailError
  exact mul_le_mul_of_nonneg_left
    (linearCoefficientTailMass_le_effective H hH)
    (mul_nonneg (by norm_num)
      TS316.Goldbach.globalLinearSpectralMass_nonnegative)

theorem effectiveWeightedTailError_tendsto_zero :
    Filter.Tendsto effectiveWeightedTailError Filter.atTop (nhds 0) := by
  have h := linearCoefficientTailMass_tendsto_zero.const_mul
    (2 * TS316.Goldbach.globalLinearSpectralMass)
  simpa [effectiveWeightedTailError] using h

theorem weightedPairIncrement_le_effectiveTail
    (T H : Nat) (hHT : H <= T) :
    weightedPairIncrement T H <= effectiveWeightedTailError H := by
  have hIncrement := weightedPairIncrement_le_finiteMasses T H
  have hFinite := finiteLinearCoefficientMass_le_global T
  have hTail := finiteCoefficientTailMass_le_linearTail T H hHT
  have hFiniteNonneg := finiteLinearCoefficientMass_nonnegative T
  have hTailFiniteNonneg := finiteCoefficientTailMass_nonnegative T H
  have hGlobalNonneg := TS316.Goldbach.globalLinearSpectralMass_nonnegative
  have hTailNonneg := linearCoefficientTailMass_nonnegative H
  unfold effectiveWeightedTailError
  calc
    weightedPairIncrement T H <=
        2 * finiteLinearCoefficientMass T * finiteCoefficientTailMass T H :=
      hIncrement
    _ <= 2 * TS316.Goldbach.globalLinearSpectralMass *
        linearCoefficientTailMass H := by
      nlinarith [mul_nonneg
        (sub_nonneg.mpr hFinite) hTailFiniteNonneg,
        mul_nonneg hGlobalNonneg (sub_nonneg.mpr hTail)]

/-- Uniform real approximation of every higher envelope by the finite core. -/
theorem weightedClosePairEnvelope_le_core_add_effectiveTail
    (T H : Nat) (hHT : H <= T) :
    TS317.Goldbach.weightedClosePairEnvelope T <=
      finiteWeightedLocalCore H + effectiveWeightedTailError H := by
  rw [weightedClosePairEnvelope_eq_coreEnvelope_add_increment T H hHT]
  exact add_le_add
    (weightedClosePairEnvelope_le_finiteWeightedLocalCore H)
    (weightedPairIncrement_le_effectiveTail T H hHT)

/-- The core-plus-tail estimate inhabits the canonical TS317 real contract. -/
theorem weightedClosePairEnvelopeBound_of_core_tail
    (T H : Nat) (hHT : H <= T) :
    TS317.Goldbach.WeightedClosePairEnvelopeBoundStatement T
      (finiteWeightedLocalCore H + effectiveWeightedTailError H) := by
  exact And.intro
    (add_nonneg (finiteWeightedLocalCore_nonnegative H)
      (effectiveWeightedTailError_nonnegative H))
    (weightedClosePairEnvelope_le_core_add_effectiveTail T H hHT)

/-- Canonical real-valued TS322 package at a chosen finite core height. -/
structure FiniteCoreEffectiveTailData (H : Nat) where
  coreMajorant : Real
  tailError : Real
  coreMajorant_eq : coreMajorant = finiteWeightedLocalCore H
  tailError_eq : tailError = effectiveWeightedTailError H
  coreMajorant_nonnegative : 0 <= coreMajorant
  tailError_nonnegative : 0 <= tailError
  envelope_bounds : forall T, H <= T ->
    TS317.Goldbach.weightedClosePairEnvelope T <=
      coreMajorant + tailError
  explicit_tail_bound : 1 <= H ->
    tailError <=
      2 * TS316.Goldbach.globalLinearSpectralMass *
        (TS292.Goldbach.infiniteZeroResidualTailConstant *
          TS292.Goldbach.logarithmicTailRate H)

noncomputable def finiteCoreEffectiveTailData (H : Nat) :
    FiniteCoreEffectiveTailData H where
  coreMajorant := finiteWeightedLocalCore H
  tailError := effectiveWeightedTailError H
  coreMajorant_eq := rfl
  tailError_eq := rfl
  coreMajorant_nonnegative := finiteWeightedLocalCore_nonnegative H
  tailError_nonnegative := effectiveWeightedTailError_nonnegative H
  envelope_bounds := fun T hHT =>
    weightedClosePairEnvelope_le_core_add_effectiveTail T H hHT
  explicit_tail_bound := fun hH =>
    effectiveWeightedTailError_le_explicit H hH

/-! ## Fail-closed ledger -/

structure TS322Ledger where
  exact_linear_tail_defined : True
  ts292_effective_tail_bound_routed : True
  finite_plus_tail_mass_identity_proved : True
  linear_tail_tends_to_zero : True
  finite_ts321_core_defined : True
  ordered_pair_representation_proved : True
  exact_core_increment_partition_proved : True
  two_tail_rectangles_bound_increment : True
  effective_tail_tends_to_zero : True
  uniform_core_plus_tail_bound_proved : True
  ts317_real_contract_routed : True
  canonical_real_data_constructed : True
  rationalization_deferred_to_ts323 : True
  rational_half_budget_not_proved : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def ts322Ledger : TS322Ledger where
  exact_linear_tail_defined := True.intro
  ts292_effective_tail_bound_routed := True.intro
  finite_plus_tail_mass_identity_proved := True.intro
  linear_tail_tends_to_zero := True.intro
  finite_ts321_core_defined := True.intro
  ordered_pair_representation_proved := True.intro
  exact_core_increment_partition_proved := True.intro
  two_tail_rectangles_bound_increment := True.intro
  effective_tail_tends_to_zero := True.intro
  uniform_core_plus_tail_bound_proved := True.intro
  ts317_real_contract_routed := True.intro
  canonical_real_data_constructed := True.intro
  rationalization_deferred_to_ts323 := True.intro
  rational_half_budget_not_proved := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end

end Goldbach
end TS322
