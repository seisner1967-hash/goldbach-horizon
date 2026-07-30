import Mathlib.Tactic
import Mathlib.Data.Rat.Floor
import TS.Goldbach.Strong.TS322.FiniteCoreEffectiveTail

namespace TS324
namespace Goldbach

noncomputable section

/-!
# TS324: certified zero-cover semantics

This module defines a flat rational payload for certified boxes containing
concrete nontrivial zeta zeros.  The payload itself is untrusted and carries no
proofs.  Its semantic certificate separately states coverage of the finite
height truncation and a valid upper bound for the total TS316 coefficient mass
inside every box.

The finite TS322 core is rewritten exactly as a weighted ordered-pair sum.  A
lower bound for the ordinate gap between two rational boxes then gives the
largest compatible core weight.  Summing the products of the certified box
masses yields a non-circular rational majorant for the complete finite core.

Overlapping boxes are sound: they only overcount covered zeros.  Disjointness
is therefore a numerical-quality condition for a later checker, not an
assumption of the semantic theorem proved here.
-/

abbrev ConcreteNontrivialZero := TS292.Goldbach.ConcreteNontrivialZero

/-! ## Untrusted rational payload -/

/-- Closed rational interval.  Validity is checked separately. -/
structure RationalInterval where
  lower : Rat
  upper : Rat
deriving DecidableEq

/-- Flat payload for one certified zero box. -/
structure ZeroBoxPayload where
  realPart : RationalInterval
  imagPart : RationalInterval
  /-- Reserved for the analytic multiplicity certificate in TS326. -/
  multiplicityUpper : Nat
  coefficientMassUpper : Rat
deriving DecidableEq

/-- Untrusted flat array of zero boxes. -/
structure ZeroCoverPayload where
  boxes : Array ZeroBoxPayload
deriving DecidableEq

/-- Purely rational well-formedness conditions. -/
structure PayloadWellFormed (data : ZeroCoverPayload) : Prop where
  realIntervalsValid : forall i : Fin data.boxes.size,
    data.boxes[i].realPart.lower <= data.boxes[i].realPart.upper
  imagIntervalsValid : forall i : Fin data.boxes.size,
    data.boxes[i].imagPart.lower <= data.boxes[i].imagPart.upper
  coefficientMassesNonnegative : forall i : Fin data.boxes.size,
    0 <= data.boxes[i].coefficientMassUpper

/-! ## Stepwise core weights -/

/-- Exact stepwise weight attached to the TS322 finite shell core. -/
noncomputable def corePairWeight (gap : Real) : Real :=
  if gap <= 1 then 1
  else 1 / (TS321.Goldbach.gapShellIndex gap : Real)

/-- Rational shell index matching `TS321.Goldbach.gapShellIndex`. -/
def rationalGapShellIndex (gap : Rat) : Nat :=
  Nat.ceil gap - 1

/-- Computable rational version of the exact core weight. -/
def rationalCorePairWeight (gap : Rat) : Rat :=
  if gap <= 1 then 1
  else 1 / (rationalGapShellIndex gap : Rat)

/-- Distance between two closed rational intervals. -/
def intervalDistance (I J : RationalInterval) : Rat :=
  max 0 (max (J.lower - I.upper) (I.lower - J.upper))

theorem gapShellIndex_positive
    {gap : Real} (hGap : 1 < gap) :
    0 < TS321.Goldbach.gapShellIndex gap := by
  have hCeilTwo : 2 <= Nat.ceil gap := by
    rw [Nat.add_one_le_ceil_iff]
    norm_num
    exact hGap
  unfold TS321.Goldbach.gapShellIndex
  omega

theorem gapShellIndex_mono
    {a b : Real} (hab : a <= b) :
    TS321.Goldbach.gapShellIndex a <=
      TS321.Goldbach.gapShellIndex b := by
  have hCeil : Nat.ceil a <= Nat.ceil b := Nat.ceil_mono hab
  unfold TS321.Goldbach.gapShellIndex
  omega

theorem corePairWeight_nonnegative (gap : Real) :
    0 <= corePairWeight gap := by
  unfold corePairWeight
  split
  case isTrue => norm_num
  case isFalse hGap =>
    have hIndex : 0 < TS321.Goldbach.gapShellIndex gap :=
      gapShellIndex_positive (lt_of_not_ge hGap)
    positivity

theorem corePairWeight_antitone : Antitone corePairWeight := by
  intro a b hab
  by_cases hb : b <= 1
  case pos =>
    have ha : a <= 1 := hab.trans hb
    simp [corePairWeight, ha, hb]
  case neg =>
    by_cases ha : a <= 1
    case pos =>
      simp only [corePairWeight]
      rw [if_pos ha, if_neg hb]
      have hIndex : 0 < TS321.Goldbach.gapShellIndex b :=
        gapShellIndex_positive (lt_of_not_ge hb)
      have hOne : (1 : Real) <=
          (TS321.Goldbach.gapShellIndex b : Real) := by
        exact_mod_cast hIndex
      simpa using one_div_le_one_div_of_le zero_lt_one hOne
    case neg =>
      simp only [corePairWeight]
      rw [if_neg ha, if_neg hb]
      have hIndexA : 0 < TS321.Goldbach.gapShellIndex a :=
        gapShellIndex_positive (lt_of_not_ge ha)
      have hIndexMono : TS321.Goldbach.gapShellIndex a <=
          TS321.Goldbach.gapShellIndex b := gapShellIndex_mono hab
      exact one_div_le_one_div_of_le
        (by exact_mod_cast hIndexA) (by exact_mod_cast hIndexMono)

theorem natCeil_rat_cast (q : Rat) :
    Nat.ceil (q : Real) = Nat.ceil q := by
  apply le_antisymm
  next =>
    rw [Nat.ceil_le]
    exact_mod_cast Nat.le_ceil q
  next =>
    rw [Nat.ceil_le]
    exact_mod_cast Nat.le_ceil (q : Real)

theorem rationalGapShellIndex_cast (q : Rat) :
    TS321.Goldbach.gapShellIndex (q : Real) =
      rationalGapShellIndex q := by
  unfold TS321.Goldbach.gapShellIndex rationalGapShellIndex
  rw [natCeil_rat_cast]

theorem rationalCorePairWeight_cast (q : Rat) :
    (rationalCorePairWeight q : Real) = corePairWeight (q : Real) := by
  by_cases hq : q <= 1
  case pos =>
    have hqReal : (q : Real) <= 1 := by exact_mod_cast hq
    simp [rationalCorePairWeight, corePairWeight, hq, hqReal]
  case neg =>
    have hqReal : Not ((q : Real) <= 1) := by exact_mod_cast hq
    simp [rationalCorePairWeight, corePairWeight, hq, hqReal,
      rationalGapShellIndex_cast]

theorem rationalCorePairWeight_nonnegative (q : Rat) :
    0 <= rationalCorePairWeight q := by
  have hReal := corePairWeight_nonnegative (q : Real)
  rw [<- rationalCorePairWeight_cast q] at hReal
  exact_mod_cast hReal

theorem rationalCorePairWeight_compat
    (gapRat : Rat) (gapReal : Real)
    (hLower : (gapRat : Real) <= gapReal) :
    corePairWeight gapReal <= (rationalCorePairWeight gapRat : Real) := by
  rw [rationalCorePairWeight_cast]
  exact corePairWeight_antitone hLower

/-! ## Exact finite-core pair representation -/

theorem pairCoreTerm_eq_near_add_shells
    (H : Nat) (rho sigma : ConcreteNontrivialZero)
    (hRho : Membership.mem (TS315.Goldbach.truncatedZeroSet H) rho)
    (hSigma : Membership.mem
      ((TS315.Goldbach.truncatedZeroSet H).erase rho) sigma) :
    TS321.Goldbach.zeroPairCoefficientMass rho sigma *
        corePairWeight (TS317.Goldbach.zeroOrdinateGap rho sigma) =
      (if TS317.Goldbach.zeroOrdinateGap rho sigma <= 1 then
        TS321.Goldbach.zeroPairCoefficientMass rho sigma
      else 0) +
        Finset.sum (Finset.Ico 1 (2 * H)) (fun k =>
          let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
          if (k : Real) < gap /\ gap <= (k : Real) + 1 then
            (1 / (k : Real)) *
              TS321.Goldbach.zeroPairCoefficientMass rho sigma
          else 0) := by
  let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
  by_cases hNear : gap <= 1
  case pos =>
    have hShellsZero :
        Finset.sum (Finset.Ico 1 (2 * H)) (fun k =>
          if (k : Real) < gap /\ gap <= (k : Real) + 1 then
            (1 / (k : Real)) *
              TS321.Goldbach.zeroPairCoefficientMass rho sigma
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg]
      intro hShell
      have hkOne : (1 : Real) <= (k : Real) := by
        exact_mod_cast (Finset.mem_Ico.mp hk).1
      linarith
    dsimp [gap] at hNear hShellsZero
    have hShellsZero' :
        Finset.sum (Finset.Ico 1 (2 * H)) (fun k =>
          if (k : Real) < TS317.Goldbach.zeroOrdinateGap rho sigma /\
              TS317.Goldbach.zeroOrdinateGap rho sigma <= (k : Real) + 1 then
            (1 / (k : Real)) *
              TS321.Goldbach.zeroPairCoefficientMass rho sigma
          else 0) = 0 := by
      simpa only [one_div] using hShellsZero
    rw [corePairWeight, if_pos hNear, if_pos hNear, hShellsZero',
      add_zero, mul_one]
  case neg =>
    have hFar : 1 < gap := lt_of_not_ge hNear
    have hGapUpper : gap <= 2 * (H : Real) :=
      TS321.Goldbach.zeroOrdinateGap_le_two_mul_height
        H rho sigma hRho hSigma
    have hIndexMem : Membership.mem (Finset.Ico 1 (2 * H))
        (TS321.Goldbach.gapShellIndex gap) :=
      TS321.Goldbach.gapShellIndex_mem hFar hGapUpper
    have hIndexSpec := TS321.Goldbach.gapShellIndex_spec hFar
    have hShellSum :
        Finset.sum (Finset.Ico 1 (2 * H)) (fun k =>
          if (k : Real) < gap /\ gap <= (k : Real) + 1 then
            (1 / (k : Real)) *
              TS321.Goldbach.zeroPairCoefficientMass rho sigma
          else 0) =
        (1 / (TS321.Goldbach.gapShellIndex gap : Real)) *
          TS321.Goldbach.zeroPairCoefficientMass rho sigma := by
      rw [Finset.sum_eq_single (TS321.Goldbach.gapShellIndex gap)]
      next => rw [if_pos hIndexSpec]
      next =>
        intro k hk hkNe
        rw [if_neg]
        intro hkSpec
        exact hkNe (TS321.Goldbach.gapShellIndex_unique
          hkSpec.1 hkSpec.2)
      next => exact fun hNotMem => (hNotMem hIndexMem).elim
    dsimp [gap] at hNear hShellSum
    rw [if_neg hNear, zero_add, hShellSum]
    simp [corePairWeight, hNear, mul_comm]

theorem finiteWeightedLocalCore_eq_weightedPairSum (H : Nat) :
    TS322.Goldbach.finiteWeightedLocalCore H =
      Finset.sum (TS315.Goldbach.truncatedZeroSet H) (fun rho =>
        Finset.sum ((TS315.Goldbach.truncatedZeroSet H).erase rho)
          (fun sigma =>
            TS321.Goldbach.zeroPairCoefficientMass rho sigma *
              corePairWeight
                (TS317.Goldbach.zeroOrdinateGap rho sigma))) := by
  let zeros := TS315.Goldbach.truncatedZeroSet H
  let shells := Finset.Ico 1 (2 * H)
  change
    Finset.sum zeros (fun rho =>
        Finset.sum (zeros.erase rho) (fun sigma =>
          if TS317.Goldbach.zeroOrdinateGap rho sigma <= 1 then
            TS321.Goldbach.zeroPairCoefficientMass rho sigma
          else 0)) +
      Finset.sum shells (fun k =>
        (1 / (k : Real)) *
          Finset.sum zeros (fun rho =>
            Finset.sum (zeros.erase rho) (fun sigma =>
              let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
              if (k : Real) < gap /\ gap <= (k : Real) + 1 then
                TS321.Goldbach.zeroPairCoefficientMass rho sigma
              else 0))) =
    Finset.sum zeros (fun rho =>
      Finset.sum (zeros.erase rho) (fun sigma =>
        TS321.Goldbach.zeroPairCoefficientMass rho sigma *
          corePairWeight (TS317.Goldbach.zeroOrdinateGap rho sigma)))
  symm
  calc
    Finset.sum zeros (fun rho =>
        Finset.sum (zeros.erase rho) (fun sigma =>
          TS321.Goldbach.zeroPairCoefficientMass rho sigma *
            corePairWeight (TS317.Goldbach.zeroOrdinateGap rho sigma))) =
      Finset.sum zeros (fun rho =>
        Finset.sum (zeros.erase rho) (fun sigma =>
          (if TS317.Goldbach.zeroOrdinateGap rho sigma <= 1 then
            TS321.Goldbach.zeroPairCoefficientMass rho sigma
          else 0) +
            Finset.sum shells (fun k =>
              let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
              if (k : Real) < gap /\ gap <= (k : Real) + 1 then
                (1 / (k : Real)) *
                  TS321.Goldbach.zeroPairCoefficientMass rho sigma
              else 0))) := by
        apply Finset.sum_congr rfl
        intro rho hRho
        apply Finset.sum_congr rfl
        intro sigma hSigma
        exact pairCoreTerm_eq_near_add_shells H rho sigma hRho hSigma
    _ = Finset.sum zeros (fun rho =>
          Finset.sum (zeros.erase rho) (fun sigma =>
            if TS317.Goldbach.zeroOrdinateGap rho sigma <= 1 then
              TS321.Goldbach.zeroPairCoefficientMass rho sigma
            else 0)) +
        Finset.sum zeros (fun rho =>
          Finset.sum (zeros.erase rho) (fun sigma =>
            Finset.sum shells (fun k =>
              let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
              if (k : Real) < gap /\ gap <= (k : Real) + 1 then
                (1 / (k : Real)) *
                  TS321.Goldbach.zeroPairCoefficientMass rho sigma
              else 0))) := by
        simp_rw [Finset.sum_add_distrib]
    _ = Finset.sum zeros (fun rho =>
          Finset.sum (zeros.erase rho) (fun sigma =>
            if TS317.Goldbach.zeroOrdinateGap rho sigma <= 1 then
              TS321.Goldbach.zeroPairCoefficientMass rho sigma
            else 0)) +
        Finset.sum shells (fun k =>
          Finset.sum zeros (fun rho =>
            Finset.sum (zeros.erase rho) (fun sigma =>
              let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
              if (k : Real) < gap /\ gap <= (k : Real) + 1 then
                (1 / (k : Real)) *
                  TS321.Goldbach.zeroPairCoefficientMass rho sigma
              else 0))) := by
        congr 1
        calc
          Finset.sum zeros (fun rho =>
              Finset.sum (zeros.erase rho) (fun sigma =>
                Finset.sum shells (fun k =>
                  let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
                  if (k : Real) < gap /\ gap <= (k : Real) + 1 then
                    (1 / (k : Real)) *
                      TS321.Goldbach.zeroPairCoefficientMass rho sigma
                  else 0))) =
            Finset.sum zeros (fun rho =>
              Finset.sum shells (fun k =>
                Finset.sum (zeros.erase rho) (fun sigma =>
                  let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
                  if (k : Real) < gap /\ gap <= (k : Real) + 1 then
                    (1 / (k : Real)) *
                      TS321.Goldbach.zeroPairCoefficientMass rho sigma
                  else 0))) := by
              apply Finset.sum_congr rfl
              intro rho _
              exact Finset.sum_comm
          _ = Finset.sum shells (fun k =>
              Finset.sum zeros (fun rho =>
                Finset.sum (zeros.erase rho) (fun sigma =>
                  let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
                  if (k : Real) < gap /\ gap <= (k : Real) + 1 then
                    (1 / (k : Real)) *
                      TS321.Goldbach.zeroPairCoefficientMass rho sigma
                  else 0))) := Finset.sum_comm
    _ = Finset.sum zeros (fun rho =>
          Finset.sum (zeros.erase rho) (fun sigma =>
            if TS317.Goldbach.zeroOrdinateGap rho sigma <= 1 then
              TS321.Goldbach.zeroPairCoefficientMass rho sigma
            else 0)) +
        Finset.sum shells (fun k =>
          (1 / (k : Real)) *
            Finset.sum zeros (fun rho =>
              Finset.sum (zeros.erase rho) (fun sigma =>
                let gap := TS317.Goldbach.zeroOrdinateGap rho sigma
                if (k : Real) < gap /\ gap <= (k : Real) + 1 then
                  TS321.Goldbach.zeroPairCoefficientMass rho sigma
                else 0))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro rho _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro sigma _
        dsimp only
        split <;> simp_all

/-! ## Semantic zero cover -/

/-- A concrete zero lies in a closed rational box. -/
noncomputable def zeroLiesInBox
    (rho : ConcreteNontrivialZero) (box : ZeroBoxPayload) : Prop :=
  (box.realPart.lower : Real) <= rho.1.re /\
    rho.1.re <= (box.realPart.upper : Real) /\
    (box.imagPart.lower : Real) <= rho.1.im /\
    rho.1.im <= (box.imagPart.upper : Real)

/-- Contribution of one zero to one box. -/
noncomputable def boxCoefficientTerm
    (rho : ConcreteNontrivialZero) (box : ZeroBoxPayload) : Real :=
  by
    classical
    exact if zeroLiesInBox rho box then
      TS316.Goldbach.zeroCoefficientMagnitude rho
    else 0

/-- Exact coefficient mass in one box at height `H`. -/
noncomputable def boxCoefficientMass
    (H : Nat) (box : ZeroBoxPayload) : Real :=
  Finset.sum (TS315.Goldbach.truncatedZeroSet H) (fun rho =>
    boxCoefficientTerm rho box)

/-- Analytic semantics of an externally supplied finite zero cover. -/
structure CertifiedTruncatedZeroCover
    (H : Nat) (data : ZeroCoverPayload) : Prop where
  covers : forall rho,
    Membership.mem (TS315.Goldbach.truncatedZeroSet H) rho ->
      exists i : Fin data.boxes.size,
        zeroLiesInBox rho data.boxes[i]
  coefficientMassValid : forall i : Fin data.boxes.size,
    boxCoefficientMass H data.boxes[i] <=
      (data.boxes[i].coefficientMassUpper : Real)

theorem boxCoefficientTerm_nonnegative
    (rho : ConcreteNontrivialZero) (box : ZeroBoxPayload) :
    0 <= boxCoefficientTerm rho box := by
  unfold boxCoefficientTerm
  split
  case isTrue =>
    exact TS316.Goldbach.zeroCoefficientMagnitude_nonnegative rho
  case isFalse => exact le_rfl

theorem boxCoefficientMass_nonnegative
    (H : Nat) (box : ZeroBoxPayload) :
    0 <= boxCoefficientMass H box := by
  unfold boxCoefficientMass
  exact Finset.sum_nonneg fun rho _ =>
    boxCoefficientTerm_nonnegative rho box

theorem intervalDistance_nonnegative (I J : RationalInterval) :
    0 <= intervalDistance I J := by
  unfold intervalDistance
  exact le_max_left _ _

theorem intervalDistance_cast_le_gap
    (rho sigma : ConcreteNontrivialZero) (boxI boxJ : ZeroBoxPayload)
    (hRho : zeroLiesInBox rho boxI)
    (hSigma : zeroLiesInBox sigma boxJ) :
    (intervalDistance boxI.imagPart boxJ.imagPart : Real) <=
      TS317.Goldbach.zeroOrdinateGap rho sigma := by
  have hRhoLower := hRho.2.2.1
  have hRhoUpper := hRho.2.2.2
  have hSigmaLower := hSigma.2.2.1
  have hSigmaUpper := hSigma.2.2.2
  simp only [intervalDistance, Rat.cast_max, Rat.cast_zero, Rat.cast_sub]
  unfold TS317.Goldbach.zeroOrdinateGap
  apply max_le
  next => exact abs_nonneg _
  next =>
    apply max_le
    next =>
      calc
        (boxJ.imagPart.lower : Real) - boxI.imagPart.upper <=
            sigma.1.im - rho.1.im := sub_le_sub hSigmaLower hRhoUpper
        _ <= abs (rho.1.im - sigma.1.im) := by
          nlinarith [neg_le_abs (rho.1.im - sigma.1.im)]
    next =>
      calc
        (boxI.imagPart.lower : Real) - boxJ.imagPart.upper <=
            rho.1.im - sigma.1.im := sub_le_sub hRhoLower hSigmaUpper
        _ <= abs (rho.1.im - sigma.1.im) := le_abs_self _

/-- Largest core weight compatible with two ordinate boxes. -/
def maximalCompatibleCoreWeight
    (boxI boxJ : ZeroBoxPayload) : Rat :=
  rationalCorePairWeight
    (intervalDistance boxI.imagPart boxJ.imagPart)

theorem actualCoreWeight_le_maximalCompatibleCoreWeight
    (rho sigma : ConcreteNontrivialZero) (boxI boxJ : ZeroBoxPayload)
    (hRho : zeroLiesInBox rho boxI)
    (hSigma : zeroLiesInBox sigma boxJ) :
    corePairWeight (TS317.Goldbach.zeroOrdinateGap rho sigma) <=
      (maximalCompatibleCoreWeight boxI boxJ : Real) := by
  unfold maximalCompatibleCoreWeight
  exact rationalCorePairWeight_compat _ _
    (intervalDistance_cast_le_gap rho sigma boxI boxJ hRho hSigma)

theorem maximalCompatibleCoreWeight_nonnegative
    (boxI boxJ : ZeroBoxPayload) :
    0 <= maximalCompatibleCoreWeight boxI boxJ := by
  unfold maximalCompatibleCoreWeight
  exact rationalCorePairWeight_nonnegative _

/-! ## Computable rational box majorant -/

/-- Ordered double sum of certified box masses at the largest compatible
core weight.  This definition is executable rational arithmetic. -/
def computedCoreMajorant (data : ZeroCoverPayload) : Rat :=
  Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
    Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
      data.boxes[i].coefficientMassUpper *
        data.boxes[j].coefficientMassUpper *
          maximalCompatibleCoreWeight data.boxes[i] data.boxes[j]))

theorem computedCoreMajorant_nonnegative
    {data : ZeroCoverPayload} (hData : PayloadWellFormed data) :
    0 <= computedCoreMajorant data := by
  unfold computedCoreMajorant
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg
    (mul_nonneg (hData.coefficientMassesNonnegative i)
      (hData.coefficientMassesNonnegative j))
    (maximalCompatibleCoreWeight_nonnegative data.boxes[i] data.boxes[j])

/-! ## Direct positive overcount by boxes -/

/-- Contribution assigned to one ordered pair of boxes. -/
noncomputable def boxCoveredPairTerm
    (data : ZeroCoverPayload) (i j : Fin data.boxes.size)
    (rho sigma : ConcreteNontrivialZero) : Real :=
  boxCoefficientTerm rho data.boxes[i] *
    boxCoefficientTerm sigma data.boxes[j] *
      (maximalCompatibleCoreWeight data.boxes[i] data.boxes[j] : Real)

theorem boxCoveredPairTerm_nonnegative
    (data : ZeroCoverPayload) (i j : Fin data.boxes.size)
    (rho sigma : ConcreteNontrivialZero) :
    0 <= boxCoveredPairTerm data i j rho sigma := by
  unfold boxCoveredPairTerm
  exact mul_nonneg
    (mul_nonneg
      (boxCoefficientTerm_nonnegative rho data.boxes[i])
      (boxCoefficientTerm_nonnegative sigma data.boxes[j]))
    (by exact_mod_cast
      maximalCompatibleCoreWeight_nonnegative data.boxes[i] data.boxes[j])

theorem weightedPairTerm_le_boxOvercount
    {H : Nat} {data : ZeroCoverPayload}
    (C : CertifiedTruncatedZeroCover H data)
    (rho sigma : ConcreteNontrivialZero)
    (hRho : Membership.mem (TS315.Goldbach.truncatedZeroSet H) rho)
    (hSigma : Membership.mem (TS315.Goldbach.truncatedZeroSet H) sigma) :
    TS321.Goldbach.zeroPairCoefficientMass rho sigma *
        corePairWeight (TS317.Goldbach.zeroOrdinateGap rho sigma) <=
      Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
          boxCoveredPairTerm data i j rho sigma)) := by
  cases C.covers rho hRho with
  | intro i hRhoBox =>
      cases C.covers sigma hSigma with
      | intro j hSigmaBox =>
          have hSelected :
              TS321.Goldbach.zeroPairCoefficientMass rho sigma *
                  corePairWeight
                    (TS317.Goldbach.zeroOrdinateGap rho sigma) <=
                boxCoveredPairTerm data i j rho sigma := by
            unfold boxCoveredPairTerm boxCoefficientTerm
            rw [if_pos hRhoBox, if_pos hSigmaBox]
            unfold TS321.Goldbach.zeroPairCoefficientMass
            exact mul_le_mul_of_nonneg_left
              (actualCoreWeight_le_maximalCompatibleCoreWeight
                rho sigma data.boxes[i] data.boxes[j] hRhoBox hSigmaBox)
              (mul_nonneg
                (TS316.Goldbach.zeroCoefficientMagnitude_nonnegative rho)
                (TS316.Goldbach.zeroCoefficientMagnitude_nonnegative sigma))
          have hInner : boxCoveredPairTerm data i j rho sigma <=
              Finset.sum Finset.univ (fun j' : Fin data.boxes.size =>
                boxCoveredPairTerm data i j' rho sigma) := by
            exact Finset.single_le_sum
              (fun j' _ =>
                boxCoveredPairTerm_nonnegative data i j' rho sigma)
              (Finset.mem_univ j)
          have hOuter :
              Finset.sum Finset.univ (fun j' : Fin data.boxes.size =>
                  boxCoveredPairTerm data i j' rho sigma) <=
                Finset.sum Finset.univ (fun i' : Fin data.boxes.size =>
                  Finset.sum Finset.univ (fun j' : Fin data.boxes.size =>
                    boxCoveredPairTerm data i' j' rho sigma)) := by
            exact Finset.single_le_sum
              (fun i' _ => Finset.sum_nonneg fun j' _ =>
                boxCoveredPairTerm_nonnegative data i' j' rho sigma)
              (Finset.mem_univ i)
          exact hSelected.trans (hInner.trans hOuter)

theorem boxPairContribution_sum
    (H : Nat) (data : ZeroCoverPayload)
    (i j : Fin data.boxes.size) :
    Finset.sum (TS315.Goldbach.truncatedZeroSet H) (fun rho =>
        Finset.sum (TS315.Goldbach.truncatedZeroSet H) (fun sigma =>
          boxCoveredPairTerm data i j rho sigma)) =
      boxCoefficientMass H data.boxes[i] *
        boxCoefficientMass H data.boxes[j] *
          (maximalCompatibleCoreWeight data.boxes[i] data.boxes[j] : Real) := by
  let zeros := TS315.Goldbach.truncatedZeroSet H
  let weight : Real :=
    (maximalCompatibleCoreWeight data.boxes[i] data.boxes[j] : Real)
  change
    Finset.sum zeros (fun rho =>
      Finset.sum zeros (fun sigma =>
        boxCoefficientTerm rho data.boxes[i] *
          boxCoefficientTerm sigma data.boxes[j] * weight)) =
    Finset.sum zeros (fun rho => boxCoefficientTerm rho data.boxes[i]) *
      Finset.sum zeros (fun sigma => boxCoefficientTerm sigma data.boxes[j]) *
        weight
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro rho _
  rw [Finset.sum_mul]

theorem fullBoxOvercount_sum
    (H : Nat) (data : ZeroCoverPayload) :
    Finset.sum (TS315.Goldbach.truncatedZeroSet H) (fun rho =>
        Finset.sum (TS315.Goldbach.truncatedZeroSet H) (fun sigma =>
          Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
            Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
              boxCoveredPairTerm data i j rho sigma)))) =
      Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
          boxCoefficientMass H data.boxes[i] *
            boxCoefficientMass H data.boxes[j] *
              (maximalCompatibleCoreWeight data.boxes[i] data.boxes[j] : Real))) := by
  let zeros := TS315.Goldbach.truncatedZeroSet H
  calc
    Finset.sum zeros (fun rho =>
        Finset.sum zeros (fun sigma =>
          Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
            Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
              boxCoveredPairTerm data i j rho sigma)))) =
      Finset.sum zeros (fun rho =>
        Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
          Finset.sum zeros (fun sigma =>
            Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
              boxCoveredPairTerm data i j rho sigma)))) := by
        apply Finset.sum_congr rfl
        intro rho _
        exact Finset.sum_comm
    _ = Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        Finset.sum zeros (fun rho =>
          Finset.sum zeros (fun sigma =>
            Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
              boxCoveredPairTerm data i j rho sigma)))) := Finset.sum_comm
    _ = Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        Finset.sum zeros (fun rho =>
          Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
            Finset.sum zeros (fun sigma =>
              boxCoveredPairTerm data i j rho sigma)))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro rho _
        exact Finset.sum_comm
    _ = Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
          Finset.sum zeros (fun rho =>
            Finset.sum zeros (fun sigma =>
              boxCoveredPairTerm data i j rho sigma)))) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
    _ = Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
          boxCoefficientMass H data.boxes[i] *
            boxCoefficientMass H data.boxes[j] *
              (maximalCompatibleCoreWeight data.boxes[i] data.boxes[j] : Real))) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact boxPairContribution_sum H data i j

theorem boxMassProductSum_le_computedCoreMajorant
    {H : Nat} {data : ZeroCoverPayload}
    (hData : PayloadWellFormed data)
    (C : CertifiedTruncatedZeroCover H data) :
    Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
          boxCoefficientMass H data.boxes[i] *
            boxCoefficientMass H data.boxes[j] *
              (maximalCompatibleCoreWeight data.boxes[i] data.boxes[j] : Real))) <=
      (computedCoreMajorant data : Real) := by
  unfold computedCoreMajorant
  push_cast
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hMassProduct :
      boxCoefficientMass H data.boxes[i] *
          boxCoefficientMass H data.boxes[j] <=
        (data.boxes[i].coefficientMassUpper : Real) *
          data.boxes[j].coefficientMassUpper := by
    exact mul_le_mul (C.coefficientMassValid i) (C.coefficientMassValid j)
      (boxCoefficientMass_nonnegative H data.boxes[j])
      (by exact_mod_cast hData.coefficientMassesNonnegative i)
  exact mul_le_mul_of_nonneg_right hMassProduct
    (by exact_mod_cast
      maximalCompatibleCoreWeight_nonnegative data.boxes[i] data.boxes[j])

/-- A well-formed payload and a semantic zero cover give a non-circular
rational upper bound for the exact finite TS322 core. -/
theorem finiteWeightedLocalCore_le_computedCoreMajorant
    {H : Nat} {data : ZeroCoverPayload}
    (hData : PayloadWellFormed data)
    (C : CertifiedTruncatedZeroCover H data) :
    TS322.Goldbach.finiteWeightedLocalCore H <=
      (computedCoreMajorant data : Real) := by
  rw [finiteWeightedLocalCore_eq_weightedPairSum]
  let zeros := TS315.Goldbach.truncatedZeroSet H
  calc
    Finset.sum zeros (fun rho =>
        Finset.sum (zeros.erase rho) (fun sigma =>
          TS321.Goldbach.zeroPairCoefficientMass rho sigma *
            corePairWeight (TS317.Goldbach.zeroOrdinateGap rho sigma))) <=
      Finset.sum zeros (fun rho =>
        Finset.sum zeros (fun sigma =>
          Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
            Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
              boxCoveredPairTerm data i j rho sigma)))) := by
        apply Finset.sum_le_sum
        intro rho hRho
        calc
          Finset.sum (zeros.erase rho) (fun sigma =>
              TS321.Goldbach.zeroPairCoefficientMass rho sigma *
                corePairWeight
                  (TS317.Goldbach.zeroOrdinateGap rho sigma)) <=
            Finset.sum (zeros.erase rho) (fun sigma =>
              Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
                Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
                  boxCoveredPairTerm data i j rho sigma))) := by
              apply Finset.sum_le_sum
              intro sigma hSigma
              exact weightedPairTerm_le_boxOvercount C rho sigma hRho
                (Finset.mem_of_mem_erase hSigma)
          _ <= Finset.sum zeros (fun sigma =>
              Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
                Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
                  boxCoveredPairTerm data i j rho sigma))) := by
              exact Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.erase_subset rho zeros)
                (fun sigma _ _ =>
                  Finset.sum_nonneg fun i _ =>
                    Finset.sum_nonneg fun j _ =>
                      boxCoveredPairTerm_nonnegative data i j rho sigma)
    _ = Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
          boxCoefficientMass H data.boxes[i] *
            boxCoefficientMass H data.boxes[j] *
              (maximalCompatibleCoreWeight data.boxes[i] data.boxes[j] : Real))) :=
      fullBoxOvercount_sum H data
    _ <= (computedCoreMajorant data : Real) :=
      boxMassProductSum_le_computedCoreMajorant hData C

/-! ## Fail-closed ledger -/

structure TS324Ledger where
  proof_free_rational_payload_defined : True
  rational_payload_well_formedness_separated : True
  semantic_zero_cover_defined : True
  semantic_box_mass_certificate_retained : True
  exact_finite_core_pair_rewrite_proved : True
  stepwise_core_weight_antitone_proved : True
  rational_real_weight_compatibility_proved : True
  interval_distance_gap_lower_bound_proved : True
  ordered_box_overcount_proved : True
  computable_rational_core_majorant_defined : True
  noncircular_core_majorant_theorem_proved : True
  box_disjointness_not_required_for_soundness : True
  boolean_payload_checker_not_built : True
  analytic_zero_cover_not_constructed : True
  concrete_zero_dataset_not_imported : True
  ts323_certificate_not_inhabited : True
  unconditional_half_budget_not_claimed : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def ts324Ledger : TS324Ledger where
  proof_free_rational_payload_defined := True.intro
  rational_payload_well_formedness_separated := True.intro
  semantic_zero_cover_defined := True.intro
  semantic_box_mass_certificate_retained := True.intro
  exact_finite_core_pair_rewrite_proved := True.intro
  stepwise_core_weight_antitone_proved := True.intro
  rational_real_weight_compatibility_proved := True.intro
  interval_distance_gap_lower_bound_proved := True.intro
  ordered_box_overcount_proved := True.intro
  computable_rational_core_majorant_defined := True.intro
  noncircular_core_majorant_theorem_proved := True.intro
  box_disjointness_not_required_for_soundness := True.intro
  boolean_payload_checker_not_built := True.intro
  analytic_zero_cover_not_constructed := True.intro
  concrete_zero_dataset_not_imported := True.intro
  ts323_certificate_not_inhabited := True.intro
  unconditional_half_budget_not_claimed := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end

end Goldbach
end TS324
