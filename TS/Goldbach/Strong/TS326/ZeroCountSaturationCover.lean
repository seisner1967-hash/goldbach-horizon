import Mathlib.Tactic
import TS.Goldbach.Strong.TS325.ExecutablePayloadChecker

namespace TS326
namespace Goldbach

noncomputable section

/-!
# TS326: zero-count saturation cover

This module reduces the analytic TS324 zero-cover obligation to three
independent inputs: an exact global multiplicity count, local multiplicity
lower bounds in rational boxes, and saturation of those lower bounds.  Box
disjointness and positivity of concrete zero multiplicities then force the
boxes to cover every zero in the finite truncation.

The second half derives the TS324 coefficient-mass field algebraically.  A
positive rational lower bound for the absolute ordinate controls the Mellin
denominator, while `multiplicityUpper` is interpreted as an upper bound for
the total multiplicity in the box.  No zeta evaluator, global zero count,
local sign-change certificate, empirical payload, or half-budget certificate
is constructed here.
-/

abbrev ConcreteNontrivialZero := TS324.Goldbach.ConcreteNontrivialZero
abbrev RationalInterval := TS324.Goldbach.RationalInterval
abbrev ZeroBoxPayload := TS324.Goldbach.ZeroBoxPayload
abbrev ZeroCoverPayload := TS324.Goldbach.ZeroCoverPayload

/-! ## Exact multiplicity masses -/

/-- Concrete analytic multiplicity of a nontrivial zeta zero. -/
noncomputable def concreteZeroMultiplicity
    (rho : ConcreteNontrivialZero) : Nat :=
  TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity rho.1

theorem concreteZeroMultiplicity_positive
    (rho : ConcreteNontrivialZero) :
    0 < concreteZeroMultiplicity rho := by
  exact TS264.Goldbach.concreteRiemannZetaMultiplicity_positive rho.property

/-- Total multiplicity in the finite TS315 truncation. -/
noncomputable def truncatedMultiplicityMass (H : Nat) : Nat :=
  Finset.sum (TS315.Goldbach.truncatedZeroSet H) concreteZeroMultiplicity

/-- Multiplicity contribution of one zero to one rational box. -/
noncomputable def boxMultiplicityTerm
    (rho : ConcreteNontrivialZero) (box : ZeroBoxPayload) : Nat :=
  by
    classical
    exact if TS324.Goldbach.zeroLiesInBox rho box then
      concreteZeroMultiplicity rho
    else 0

/-- Total multiplicity of truncated zeros lying in one box. -/
noncomputable def boxMultiplicityMass
    (H : Nat) (box : ZeroBoxPayload) : Nat :=
  Finset.sum (TS315.Goldbach.truncatedZeroSet H) (fun rho =>
    boxMultiplicityTerm rho box)

/-! ## Independent global and local count certificates -/

/-- Exact global zero count, with multiplicity, at height `H`. -/
structure CertifiedGlobalZeroCount (H N : Nat) : Prop where
  countExact : truncatedMultiplicityMass H = N

/-- Certified lower counts for the boxes of one payload. -/
structure CertifiedLocalZeroCountLower
    (H : Nat) (data : ZeroCoverPayload)
    (localCount : Fin data.boxes.size -> Nat) : Prop where
  countLower : forall i,
    localCount i <= boxMultiplicityMass H data.boxes[i]

/--
Saturation data.  This structure deliberately contains neither TS324
coverage nor a coefficient-mass conclusion.

`multiplicityUpper` means the total multiplicity of all truncated zeros in
the box, not the largest multiplicity of one zero.
-/
structure CertifiedZeroCountSaturation
    (H : Nat) (data : ZeroCoverPayload) where
  N : Nat
  localCount : Fin data.boxes.size -> Nat
  global : CertifiedGlobalZeroCount H N
  localLower : CertifiedLocalZeroCountLower H data localCount
  boxesDisjointOnTruncation : forall
    (i j : Fin data.boxes.size), Not (i = j) ->
    forall rho : ConcreteNontrivialZero,
      Membership.mem (TS315.Goldbach.truncatedZeroSet H) rho ->
      TS324.Goldbach.zeroLiesInBox rho data.boxes[i] ->
      TS324.Goldbach.zeroLiesInBox rho data.boxes[j] -> False
  saturated : Finset.sum Finset.univ localCount = N
  localCountLeMultiplicityUpper : forall i,
    localCount i <= data.boxes[i].multiplicityUpper

namespace CertifiedZeroCountSaturation

variable {H : Nat} {data : ZeroCoverPayload}

theorem sum_boxMultiplicityTerm_le
    (S : CertifiedZeroCountSaturation H data)
    (rho : ConcreteNontrivialZero)
    (hRho : Membership.mem (TS315.Goldbach.truncatedZeroSet H) rho) :
    Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        boxMultiplicityTerm rho data.boxes[i]) <=
      concreteZeroMultiplicity rho := by
  classical
  by_cases hExists : exists i : Fin data.boxes.size,
      TS324.Goldbach.zeroLiesInBox rho data.boxes[i]
  case pos =>
    let i := hExists.choose
    have hi : TS324.Goldbach.zeroLiesInBox rho data.boxes[i] :=
      hExists.choose_spec
    have hEq :
        Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
            boxMultiplicityTerm rho data.boxes[j]) =
          concreteZeroMultiplicity rho := by
      calc
        Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
            boxMultiplicityTerm rho data.boxes[j]) =
            boxMultiplicityTerm rho data.boxes[i] := by
          apply Fintype.sum_eq_single i
          intro j hji
          have hNot :
              Not (TS324.Goldbach.zeroLiesInBox rho data.boxes[j]) := by
            intro hj
            exact CertifiedZeroCountSaturation.boxesDisjointOnTruncation
              S i j (Ne.symm hji)
              rho hRho hi hj
          unfold boxMultiplicityTerm
          split
          case isTrue hIn => exact (hNot hIn).elim
          case isFalse => rfl
        _ = concreteZeroMultiplicity rho := by
          unfold boxMultiplicityTerm
          split
          case isTrue => rfl
          case isFalse hNot => exact (hNot hi).elim
    exact hEq.le
  case neg =>
    have hNone : forall i : Fin data.boxes.size,
        Not (TS324.Goldbach.zeroLiesInBox rho data.boxes[i]) := by
      simpa only [not_exists] using hExists
    have hZero :
        Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
            boxMultiplicityTerm rho data.boxes[i]) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      unfold boxMultiplicityTerm
      split
      case isTrue hIn => exact (hNone i hIn).elim
      case isFalse => rfl
    rw [hZero]
    exact Nat.zero_le _

theorem sum_boxMultiplicityMass_le_total :
    CertifiedZeroCountSaturation H data ->
    Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        boxMultiplicityMass H data.boxes[i]) <=
      truncatedMultiplicityMass H := by
  intro S
  classical
  unfold boxMultiplicityMass truncatedMultiplicityMass
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun rho hRho =>
    sum_boxMultiplicityTerm_le S rho hRho

theorem sum_localCount_le_boxMultiplicityMass :
    forall S : CertifiedZeroCountSaturation H data,
    Finset.sum Finset.univ S.localCount <=
      Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        boxMultiplicityMass H data.boxes[i]) := by
  intro S
  exact Finset.sum_le_sum fun i _ => S.localLower.countLower i

theorem sum_localCount_eq_total :
    forall S : CertifiedZeroCountSaturation H data,
    Finset.sum Finset.univ S.localCount = truncatedMultiplicityMass H := by
  intro S
  calc
    Finset.sum Finset.univ S.localCount = S.N := S.saturated
    _ = truncatedMultiplicityMass H := S.global.countExact.symm

theorem sum_boxMultiplicityMass_eq_total :
    CertifiedZeroCountSaturation H data ->
    Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        boxMultiplicityMass H data.boxes[i]) =
      truncatedMultiplicityMass H := by
  intro S
  apply Nat.le_antisymm (sum_boxMultiplicityMass_le_total S)
  rw [<- sum_localCount_eq_total S]
  exact sum_localCount_le_boxMultiplicityMass S

theorem boxMultiplicityMass_eq_localCount
    (S : CertifiedZeroCountSaturation H data)
    (i : Fin data.boxes.size) :
    boxMultiplicityMass H data.boxes[i] = S.localCount i := by
  apply Nat.le_antisymm
  next =>
    by_contra hNot
    have hStrict : S.localCount i < boxMultiplicityMass H data.boxes[i] :=
      Nat.lt_of_not_ge hNot
    have hSumStrict :
        Finset.sum Finset.univ S.localCount <
          Finset.sum Finset.univ (fun j : Fin data.boxes.size =>
            boxMultiplicityMass H data.boxes[j]) :=
      Finset.sum_lt_sum
        (fun j _ => S.localLower.countLower j)
        (Exists.intro i (And.intro (Finset.mem_univ i) hStrict))
    rw [sum_localCount_eq_total S,
      sum_boxMultiplicityMass_eq_total S] at hSumStrict
    exact (Nat.lt_irrefl _ hSumStrict)
  next => exact S.localLower.countLower i

theorem boxMultiplicityMass_le_payloadUpper
    (S : CertifiedZeroCountSaturation H data)
    (i : Fin data.boxes.size) :
    boxMultiplicityMass H data.boxes[i] <=
      data.boxes[i].multiplicityUpper := by
  rw [boxMultiplicityMass_eq_localCount S i]
  exact S.localCountLeMultiplicityUpper i

theorem covers_of_countSaturation
    (S : CertifiedZeroCountSaturation H data) : forall rho,
    Membership.mem (TS315.Goldbach.truncatedZeroSet H) rho ->
      exists i : Fin data.boxes.size,
        TS324.Goldbach.zeroLiesInBox rho data.boxes[i] := by
  classical
  intro rho hRho
  by_contra hMissing
  have hNone : forall i : Fin data.boxes.size,
      Not (TS324.Goldbach.zeroLiesInBox rho data.boxes[i]) := by
    simpa only [not_exists] using hMissing
  have hStrictAt :
      Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
          boxMultiplicityTerm rho data.boxes[i]) <
        concreteZeroMultiplicity rho := by
    have hZero :
        Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
            boxMultiplicityTerm rho data.boxes[i]) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      unfold boxMultiplicityTerm
      split
      case isTrue hIn => exact (hNone i hIn).elim
      case isFalse => rfl
    rw [hZero]
    exact concreteZeroMultiplicity_positive rho
  have hSumStrict :
      Finset.sum (TS315.Goldbach.truncatedZeroSet H) (fun sigma =>
          Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
            boxMultiplicityTerm sigma data.boxes[i])) <
        truncatedMultiplicityMass H := by
    unfold truncatedMultiplicityMass
    exact Finset.sum_lt_sum
      (fun sigma hSigma => sum_boxMultiplicityTerm_le S sigma hSigma)
      (Exists.intro rho (And.intro hRho hStrictAt))
  have hFubini :
      Finset.sum (TS315.Goldbach.truncatedZeroSet H) (fun sigma =>
          Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
            boxMultiplicityTerm sigma data.boxes[i])) =
        Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
          boxMultiplicityMass H data.boxes[i]) := by
    unfold boxMultiplicityMass
    rw [Finset.sum_comm]
  rw [hFubini, sum_boxMultiplicityMass_eq_total S] at hSumStrict
  exact Nat.lt_irrefl _ hSumStrict

end CertifiedZeroCountSaturation

/-! ## Rational ordinate allocation -/

/-- Rational lower bound for the absolute value on a closed interval. -/
def intervalAbsLower (I : RationalInterval) : Rat :=
  max 0 (max I.lower (-I.upper))

theorem intervalAbsLower_nonnegative (I : RationalInterval) :
    0 <= intervalAbsLower I := by
  exact le_max_left _ _

theorem intervalAbsLower_cast_le_abs
    (I : RationalInterval) (y : Real)
    (hLower : (I.lower : Real) <= y)
    (hUpper : y <= (I.upper : Real)) :
    (intervalAbsLower I : Real) <= abs y := by
  rw [show (intervalAbsLower I : Real) =
      max 0 (max (I.lower : Real) (-(I.upper : Real))) by
    simp [intervalAbsLower, Rat.cast_max]]
  exact max_le
    (abs_nonneg y)
    (max_le
      (hLower.trans (le_abs_self y))
      ((neg_le_neg hUpper).trans (neg_le_abs y)))

/-- Purely rational allocation sufficient for every per-box coefficient mass. -/
structure CertifiedCoefficientMassAllocation
    (data : ZeroCoverPayload) : Prop where
  ordinateLowerPositive : forall i : Fin data.boxes.size,
    0 < intervalAbsLower data.boxes[i].imagPart
  allocated : forall i : Fin data.boxes.size,
    (data.boxes[i].multiplicityUpper : Rat) /
        intervalAbsLower data.boxes[i].imagPart ^ 2 <=
      data.boxes[i].coefficientMassUpper

theorem zeroCoefficientMagnitude_le_multiplicity_div_lower
    (rho : ConcreteNontrivialZero) (box : ZeroBoxPayload)
    (hIn : TS324.Goldbach.zeroLiesInBox rho box)
    (hLowerPositive : 0 < intervalAbsLower box.imagPart) :
    TS316.Goldbach.zeroCoefficientMagnitude rho <=
      (concreteZeroMultiplicity rho : Real) /
        (intervalAbsLower box.imagPart : Real) ^ 2 := by
  have hLower :
      (intervalAbsLower box.imagPart : Real) <= abs rho.1.im :=
    intervalAbsLower_cast_le_abs box.imagPart rho.1.im hIn.2.2.1 hIn.2.2.2
  have hLowerPositiveReal :
      (0 : Real) < (intervalAbsLower box.imagPart : Real) := by
    exact_mod_cast hLowerPositive
  have hLowerSqPositive :
      0 < (intervalAbsLower box.imagPart : Real) ^ 2 :=
    pow_pos hLowerPositiveReal 2
  have hLowerSqLeImSq :
      (intervalAbsLower box.imagPart : Real) ^ 2 <= abs rho.1.im ^ 2 := by
    nlinarith [abs_nonneg rho.1.im]
  have hLowerSqLeDenominator :
      (intervalAbsLower box.imagPart : Real) ^ 2 <=
        Complex.abs (rho.1 * (rho.1 + 1)) :=
    hLowerSqLeImSq.trans
      (TS269.Goldbach.spectralDenominator_abs_ge_im_sq rho.1)
  rw [TS316.Goldbach.zeroCoefficientMagnitude_eq_factor_abs]
  unfold TS268.Goldbach.concreteMultiplicityDenominatorFactor
    concreteZeroMultiplicity
  change
    norm
        (((TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity
            rho.1 : Nat) : Complex) / (rho.1 * (rho.1 + 1))) <=
      (TS264.Goldbach.concreteRiemannZetaZeroFamilyContract.multiplicity
          rho.1 : Real) /
        (intervalAbsLower box.imagPart : Real) ^ 2
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_left
    (Nat.cast_nonneg _)
    hLowerSqPositive
    hLowerSqLeDenominator

theorem boxCoefficientMass_le_multiplicity_div_lower
    (H : Nat) (box : ZeroBoxPayload)
    (hLowerPositive : 0 < intervalAbsLower box.imagPart) :
    TS324.Goldbach.boxCoefficientMass H box <=
      (boxMultiplicityMass H box : Real) /
        (intervalAbsLower box.imagPart : Real) ^ 2 := by
  classical
  unfold TS324.Goldbach.boxCoefficientMass boxMultiplicityMass
  calc
    Finset.sum (TS315.Goldbach.truncatedZeroSet H) (fun rho =>
        TS324.Goldbach.boxCoefficientTerm rho box) <=
      Finset.sum (TS315.Goldbach.truncatedZeroSet H) (fun rho =>
        (boxMultiplicityTerm rho box : Real) /
          (intervalAbsLower box.imagPart : Real) ^ 2) := by
      apply Finset.sum_le_sum
      intro rho _
      by_cases hIn : TS324.Goldbach.zeroLiesInBox rho box
      case pos =>
        simp only [TS324.Goldbach.boxCoefficientTerm, boxMultiplicityTerm,
          if_pos hIn, Nat.cast_ofNat]
        exact zeroCoefficientMagnitude_le_multiplicity_div_lower
          rho box hIn hLowerPositive
      case neg =>
        simp [TS324.Goldbach.boxCoefficientTerm, boxMultiplicityTerm, hIn]
    _ = (boxMultiplicityMass H box : Real) /
        (intervalAbsLower box.imagPart : Real) ^ 2 := by
      rw [<- Finset.sum_div]
      unfold boxMultiplicityMass
      push_cast
      rfl

theorem coefficientMassValid_of_countSaturation
    {H : Nat} {data : ZeroCoverPayload}
    (S : CertifiedZeroCountSaturation H data)
    (A : CertifiedCoefficientMassAllocation data)
    (i : Fin data.boxes.size) :
    TS324.Goldbach.boxCoefficientMass H data.boxes[i] <=
      (data.boxes[i].coefficientMassUpper : Real) := by
  let u : Rat := intervalAbsLower data.boxes[i].imagPart
  have hu : 0 < u := A.ordinateLowerPositive i
  have huReal : (0 : Real) < (u : Real) := by exact_mod_cast hu
  have hMultiplicity :=
    CertifiedZeroCountSaturation.boxMultiplicityMass_le_payloadUpper S i
  have hAllocation :
      ((data.boxes[i].multiplicityUpper : Rat) / u ^ 2 : Rat) <=
        data.boxes[i].coefficientMassUpper := A.allocated i
  calc
    TS324.Goldbach.boxCoefficientMass H data.boxes[i] <=
        (boxMultiplicityMass H data.boxes[i] : Real) / (u : Real) ^ 2 := by
      simpa [u] using
        boxCoefficientMass_le_multiplicity_div_lower
          H data.boxes[i] (A.ordinateLowerPositive i)
    _ <= (data.boxes[i].multiplicityUpper : Real) / (u : Real) ^ 2 := by
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast hMultiplicity)
        (sq_nonneg (u : Real))
    _ <= (data.boxes[i].coefficientMassUpper : Real) := by
      exact_mod_cast hAllocation

/-- Count saturation plus rational mass allocation constructs the TS324 cover. -/
theorem certifiedTruncatedZeroCover_of_countSaturation
    {H : Nat} {data : ZeroCoverPayload}
    (S : CertifiedZeroCountSaturation H data)
    (A : CertifiedCoefficientMassAllocation data) :
    TS324.Goldbach.CertifiedTruncatedZeroCover H data where
  covers := CertifiedZeroCountSaturation.covers_of_countSaturation S
  coefficientMassValid := coefficientMassValid_of_countSaturation S A

/-! ## Fail-closed ledger -/

structure TS326Ledger : Prop where
  globalCountSeparated : True
  localLowerCountsSeparated : True
  saturationContainsNoCoverage : True
  disjointSaturationForcesCoverage : True
  multiplicityPositivityUsed : True
  boxMultiplicityUpperDerived : True
  ordinateLowerBoundRational : True
  denominatorAllocationDerived : True
  ts324CoverConstructedConditionally : True
  zetaEvaluatorRemainsOpen : True
  globalCountCertificateRemainsOpen : True
  localCountCertificatesRemainOpen : True
  empiricalPayloadRemainsOpen : True
  halfBudgetRemainsOpen : True

noncomputable def zeroCountSaturationCoverLedger : TS326Ledger where
  globalCountSeparated := True.intro
  localLowerCountsSeparated := True.intro
  saturationContainsNoCoverage := True.intro
  disjointSaturationForcesCoverage := True.intro
  multiplicityPositivityUsed := True.intro
  boxMultiplicityUpperDerived := True.intro
  ordinateLowerBoundRational := True.intro
  denominatorAllocationDerived := True.intro
  ts324CoverConstructedConditionally := True.intro
  zetaEvaluatorRemainsOpen := True.intro
  globalCountCertificateRemainsOpen := True.intro
  localCountCertificatesRemainOpen := True.intro
  empiricalPayloadRemainsOpen := True.intro
  halfBudgetRemainsOpen := True.intro

end

end Goldbach
end TS326
