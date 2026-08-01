import Mathlib.Tactic
import TS.Goldbach.Strong.TS326.ZeroCountSaturationCover
import TS.Goldbach.Strong.TS327.PositiveSymmetryAdapter
import TS.Goldbach.Strong.TS328.ExecutableGroupedZeroPayload

namespace TS329
namespace Goldbach

noncomputable section

/-!
# TS329: positive-count saturation

This module transports explicit positive-ordinate counting certificates to the
symmetric payload constructed by TS328.  Conjugation and multiplicity
preservation come from TS327, while the executable rational conditions come
from TS328.

No positive count certificate is inhabited here.  In particular, this module
contains no empirical zero data, zeta evaluator, Turing method, trace-budget
certificate, TS181 adapter, ledger, or unconditional analytic claim.
-/

abbrev ZeroCoverPayload := TS324.Goldbach.ZeroCoverPayload
abbrev ZeroBoxPayload := TS324.Goldbach.ZeroBoxPayload
abbrev ConcreteNontrivialZero := TS324.Goldbach.ConcreteNontrivialZero

/-! ## Positive analytic certificates -/

/-- Exact positive-ordinate multiplicity count at height `H`. -/
structure CertifiedPositiveGlobalZeroCount
    (H Npos : Nat) : Prop where
  countExact : TS327.Goldbach.positiveMultiplicityMass H = Npos

/-- Certified lower multiplicity counts in the positive payload boxes. -/
structure CertifiedPositiveLocalZeroCountLower
    (H : Nat) (upper : ZeroCoverPayload)
    (localCount : Fin upper.boxes.size -> Nat) : Prop where
  localLower : forall i,
    localCount i <=
      TS327.Goldbach.positiveBoxMultiplicityMass H upper.boxes[i]

/-- Positive count data whose local lower bounds saturate the global count. -/
structure CertifiedPositiveCountSaturation
    (H : Nat) (upper : ZeroCoverPayload) where
  Npos : Nat
  localCount : Fin upper.boxes.size -> Nat
  global : CertifiedPositiveGlobalZeroCount H Npos
  localCertificate :
    CertifiedPositiveLocalZeroCountLower H upper localCount
  saturated : Finset.sum Finset.univ localCount = Npos
  localLe : forall i,
    localCount i <= upper.boxes[i].multiplicityUpper

/-! ## Positive-payload reflection -/

/-- Every box in the upper payload has strictly positive imaginary lower edge. -/
def PositiveImaginaryPayload (upper : ZeroCoverPayload) : Prop :=
  forall i : Fin upper.boxes.size,
    0 < upper.boxes[i].imagPart.lower

/-- Executable positivity check for all upper-payload imaginary intervals. -/
def checkPositiveImaginaryPayload (upper : ZeroCoverPayload) : Bool :=
  upper.boxes.all fun box => decide (0 < box.imagPart.lower)

theorem checkPositiveImaginaryPayload_iff (upper : ZeroCoverPayload) :
    checkPositiveImaginaryPayload upper = true <->
      PositiveImaginaryPayload upper := by
  constructor
  next =>
    intro hCheck
    have hAll := Array.all_eq_true.mp hCheck
    intro i
    simpa [checkPositiveImaginaryPayload] using hAll i
  next =>
    intro hPositive
    apply Array.all_eq_true.mpr
    intro i
    simpa [checkPositiveImaginaryPayload] using hPositive i

theorem zeroLiesInPositiveBox_im_pos
    {rho : ConcreteNontrivialZero} {box : ZeroBoxPayload}
    (hPositive : 0 < box.imagPart.lower)
    (hIn : TS324.Goldbach.zeroLiesInBox rho box) :
    0 < rho.1.im := by
  have hPositiveReal : (0 : Real) < (box.imagPart.lower : Real) := by
    exact_mod_cast hPositive
  linarith [hIn.2.2.1]

theorem zeroLiesInNegativeBox_im_neg
    {rho : ConcreteNontrivialZero} {box : ZeroBoxPayload}
    (hNegative : box.imagPart.upper < 0)
    (hIn : TS324.Goldbach.zeroLiesInBox rho box) :
    rho.1.im < 0 := by
  have hNegativeReal : (box.imagPart.upper : Real) < 0 := by
    exact_mod_cast hNegative
  linarith [hIn.2.2.2]

/-! ## Full-box and half-plane multiplicity masses -/

theorem boxMultiplicityMass_eq_positiveBoxMultiplicityMass
    (H : Nat) (box : ZeroBoxPayload)
    (hPositive : 0 < box.imagPart.lower) :
    TS326.Goldbach.boxMultiplicityMass H box =
      TS327.Goldbach.positiveBoxMultiplicityMass H box := by
  unfold TS326.Goldbach.boxMultiplicityMass
    TS327.Goldbach.positiveBoxMultiplicityMass
    TS327.Goldbach.positiveTruncatedZeros
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro rho hRho
  by_cases hIm : 0 < rho.1.im
  next => simp [hIm]
  next =>
    have hNotIn : Not (TS324.Goldbach.zeroLiesInBox rho box) := by
      intro hIn
      exact hIm (zeroLiesInPositiveBox_im_pos hPositive hIn)
    simp [hIm, TS326.Goldbach.boxMultiplicityTerm, hNotIn]

theorem boxMultiplicityMass_eq_negativeBoxMultiplicityMass
    (H : Nat) (box : ZeroBoxPayload)
    (hNegative : box.imagPart.upper < 0) :
    TS326.Goldbach.boxMultiplicityMass H box =
      TS327.Goldbach.negativeBoxMultiplicityMass H box := by
  unfold TS326.Goldbach.boxMultiplicityMass
    TS327.Goldbach.negativeBoxMultiplicityMass
    TS327.Goldbach.negativeTruncatedZeros
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro rho hRho
  by_cases hIm : rho.1.im < 0
  next => simp [hIm]
  next =>
    have hNotIn : Not (TS324.Goldbach.zeroLiesInBox rho box) := by
      intro hIn
      exact hIm (zeroLiesInNegativeBox_im_neg hNegative hIn)
    simp [hIm, TS326.Goldbach.boxMultiplicityTerm, hNotIn]

theorem mirroredBoxMultiplicityMass_eq_positive
    (H : Nat) (box : ZeroBoxPayload)
    (hPositive : 0 < box.imagPart.lower) :
    TS326.Goldbach.boxMultiplicityMass H (TS327.Goldbach.mirrorBox box) =
      TS327.Goldbach.positiveBoxMultiplicityMass H box := by
  have hNegative :
      (TS327.Goldbach.mirrorBox box).imagPart.upper < 0 := by
    simpa [TS327.Goldbach.mirrorBox, TS327.Goldbach.mirrorInterval] using
      (neg_lt_zero.mpr hPositive)
  calc
    TS326.Goldbach.boxMultiplicityMass H (TS327.Goldbach.mirrorBox box) =
        TS327.Goldbach.negativeBoxMultiplicityMass H
          (TS327.Goldbach.mirrorBox box) :=
      boxMultiplicityMass_eq_negativeBoxMultiplicityMass H
        (TS327.Goldbach.mirrorBox box) hNegative
    _ = TS327.Goldbach.positiveBoxMultiplicityMass H box :=
      (TS327.Goldbach.positiveBoxMultiplicityMass_eq_mirroredNegative
        H box).symm

/-! ## Symmetric payload indices -/

/-- Positive indices on the left and their mirrored copies on the right. -/
abbrev SymmetricIndex (upper : ZeroCoverPayload) :=
  Sum (Fin upper.boxes.size) (Fin upper.boxes.size)

theorem symmetricPayload_boxes_size (upper : ZeroCoverPayload) :
    (TS328.Goldbach.symmetricPayload upper).boxes.size =
      upper.boxes.size + upper.boxes.size := by
  simp [TS328.Goldbach.symmetricPayload]

/-- Canonical index equivalence for the appended symmetric payload. -/
def symmetricIndexEquiv (upper : ZeroCoverPayload) :
    Equiv (SymmetricIndex upper)
      (Fin (TS328.Goldbach.symmetricPayload upper).boxes.size) :=
  finSumFinEquiv.trans
    (Fin.castOrderIso (symmetricPayload_boxes_size upper).symm).toEquiv

theorem symmetricIndexEquiv_inl_val
    (upper : ZeroCoverPayload) (i : Fin upper.boxes.size) :
    (symmetricIndexEquiv upper (Sum.inl i)).val = i.val := by
  simp [symmetricIndexEquiv]

theorem symmetricIndexEquiv_inr_val
    (upper : ZeroCoverPayload) (i : Fin upper.boxes.size) :
    (symmetricIndexEquiv upper (Sum.inr i)).val =
      upper.boxes.size + i.val := by
  simp [symmetricIndexEquiv, Nat.add_comm]

theorem symmetricPayload_get_positive
    (upper : ZeroCoverPayload) (i : Fin upper.boxes.size) :
    (TS328.Goldbach.symmetricPayload upper).boxes[
        symmetricIndexEquiv upper (Sum.inl i)] = upper.boxes[i] := by
  change
    (upper.boxes ++ upper.boxes.map TS327.Goldbach.mirrorBox)[
        (symmetricIndexEquiv upper (Sum.inl i)).val] = upper.boxes[i.val]
  simpa only [symmetricIndexEquiv_inl_val] using
    (Array.getElem_append_left
      (as := upper.boxes)
      (bs := upper.boxes.map TS327.Goldbach.mirrorBox)
      (i := i.val) i.isLt)

theorem symmetricPayload_get_mirror
    (upper : ZeroCoverPayload) (i : Fin upper.boxes.size) :
    (TS328.Goldbach.symmetricPayload upper).boxes[
        symmetricIndexEquiv upper (Sum.inr i)] =
      TS327.Goldbach.mirrorBox upper.boxes[i] := by
  change
    (upper.boxes ++ upper.boxes.map TS327.Goldbach.mirrorBox)[
        (symmetricIndexEquiv upper (Sum.inr i)).val] =
      TS327.Goldbach.mirrorBox upper.boxes[i.val]
  simpa only [symmetricIndexEquiv_inr_val, Nat.add_sub_cancel_left,
      Array.getElem_map] using
    (Array.getElem_append_right
      (as := upper.boxes)
      (bs := upper.boxes.map TS327.Goldbach.mirrorBox)
      (i := upper.boxes.size + i.val)
      (Nat.le_add_right upper.boxes.size i.val))

/-- Duplicate each positive local count on its mirrored box. -/
def symmetricLocalCount
    {H : Nat} {upper : ZeroCoverPayload}
    (P : CertifiedPositiveCountSaturation H upper) :
    Fin (TS328.Goldbach.symmetricPayload upper).boxes.size -> Nat :=
  fun j => Sum.elim P.localCount P.localCount
    ((symmetricIndexEquiv upper).symm j)

theorem symmetricLocalCount_positive
    {H : Nat} {upper : ZeroCoverPayload}
    (P : CertifiedPositiveCountSaturation H upper)
    (i : Fin upper.boxes.size) :
    symmetricLocalCount P (symmetricIndexEquiv upper (Sum.inl i)) =
      P.localCount i := by
  simp [symmetricLocalCount]

theorem symmetricLocalCount_mirror
    {H : Nat} {upper : ZeroCoverPayload}
    (P : CertifiedPositiveCountSaturation H upper)
    (i : Fin upper.boxes.size) :
    symmetricLocalCount P (symmetricIndexEquiv upper (Sum.inr i)) =
      P.localCount i := by
  simp [symmetricLocalCount]

/-! ## Transport to TS326 certificates -/

theorem certifiedGlobalZeroCount_of_positive
    {H : Nat} {upper : ZeroCoverPayload}
    (hNoZero : TS327.Goldbach.NoZeroOrdinateInTruncation H)
    (P : CertifiedPositiveCountSaturation H upper) :
    TS326.Goldbach.CertifiedGlobalZeroCount H (2 * P.Npos) := by
  exact {
    countExact := by
      calc
        TS326.Goldbach.truncatedMultiplicityMass H =
            2 * TS327.Goldbach.positiveMultiplicityMass H :=
          TS327.Goldbach.truncatedMultiplicityMass_eq_twice_positive
            H hNoZero
        _ = 2 * P.Npos := by rw [P.global.countExact]
  }

theorem certifiedLocalZeroCountLower_of_positive
    {H : Nat} {upper : ZeroCoverPayload}
    (hPositive : PositiveImaginaryPayload upper)
    (P : CertifiedPositiveCountSaturation H upper) :
    TS326.Goldbach.CertifiedLocalZeroCountLower H
      (TS328.Goldbach.symmetricPayload upper) (symmetricLocalCount P) := by
  refine { countLower := ?_ }
  intro j
  let s := (symmetricIndexEquiv upper).symm j
  have hj : symmetricIndexEquiv upper s = j :=
    (symmetricIndexEquiv upper).apply_symm_apply j
  rw [<- hj]
  cases s with
  | inl i =>
      rw [symmetricLocalCount_positive, symmetricPayload_get_positive,
        boxMultiplicityMass_eq_positiveBoxMultiplicityMass H upper.boxes[i]
          (hPositive i)]
      exact P.localCertificate.localLower i
  | inr i =>
      rw [symmetricLocalCount_mirror, symmetricPayload_get_mirror,
        mirroredBoxMultiplicityMass_eq_positive H upper.boxes[i]
          (hPositive i)]
      exact P.localCertificate.localLower i

theorem symmetricLocalCount_sum
    {H : Nat} {upper : ZeroCoverPayload}
    (P : CertifiedPositiveCountSaturation H upper) :
    Finset.sum Finset.univ (symmetricLocalCount P) = 2 * P.Npos := by
  change Finset.sum Finset.univ
    (fun j : Fin (TS328.Goldbach.symmetricPayload upper).boxes.size =>
      symmetricLocalCount P j) = 2 * P.Npos
  rw [<- Equiv.sum_comp (symmetricIndexEquiv upper) (symmetricLocalCount P),
    Fintype.sum_sum_type]
  simp only [symmetricLocalCount_positive, symmetricLocalCount_mirror]
  rw [P.saturated]
  omega

theorem symmetricLocalCount_le_multiplicityUpper
    {H : Nat} {upper : ZeroCoverPayload}
    (P : CertifiedPositiveCountSaturation H upper) :
    forall j : Fin (TS328.Goldbach.symmetricPayload upper).boxes.size,
      symmetricLocalCount P j <=
        (TS328.Goldbach.symmetricPayload upper).boxes[j].multiplicityUpper := by
  intro j
  let s := (symmetricIndexEquiv upper).symm j
  have hj : symmetricIndexEquiv upper s = j :=
    (symmetricIndexEquiv upper).apply_symm_apply j
  rw [<- hj]
  cases s with
  | inl i =>
      rw [symmetricLocalCount_positive, symmetricPayload_get_positive]
      exact P.localLe i
  | inr i =>
      rw [symmetricLocalCount_mirror, symmetricPayload_get_mirror]
      simpa [TS327.Goldbach.mirrorBox] using P.localLe i

/-! ## Symmetric saturation and semantic cover -/

noncomputable def certifiedZeroCountSaturation_of_positive
    {H : Nat} {upper : ZeroCoverPayload}
    (hNoZero : TS327.Goldbach.NoZeroOrdinateInTruncation H)
    (hPositive : PositiveImaginaryPayload upper)
    (P : CertifiedPositiveCountSaturation H upper)
    (hGrouped : TS328.Goldbach.checkGroupedPayload
      (TS328.Goldbach.symmetricPayload upper) = true) :
    TS326.Goldbach.CertifiedZeroCountSaturation H
      (TS328.Goldbach.symmetricPayload upper) := by
  have hImagCheck : TS328.Goldbach.checkImagDisjoint
      (TS328.Goldbach.symmetricPayload upper) = true := by
    simp only [TS328.Goldbach.checkGroupedPayload, Bool.and_eq_true] at hGrouped
    exact hGrouped.2.2
  exact {
    N := 2 * P.Npos
    localCount := symmetricLocalCount P
    global := certifiedGlobalZeroCount_of_positive hNoZero P
    localLower := certifiedLocalZeroCountLower_of_positive hPositive P
    boxesDisjointOnTruncation := fun i j hNe rho hRho hI hJ =>
      TS328.Goldbach.zero_not_in_distinct_boxes_of_checkImagDisjoint
        hImagCheck i j hNe rho hI hJ
    saturated := symmetricLocalCount_sum P
    localCountLeMultiplicityUpper :=
      symmetricLocalCount_le_multiplicityUpper P
  }

theorem certifiedTruncatedZeroCover_of_positive
    {H : Nat} {upper : ZeroCoverPayload}
    (hNoZero : TS327.Goldbach.NoZeroOrdinateInTruncation H)
    (hPositive : PositiveImaginaryPayload upper)
    (P : CertifiedPositiveCountSaturation H upper)
    (hGrouped : TS328.Goldbach.checkGroupedPayload
      (TS328.Goldbach.symmetricPayload upper) = true) :
    TS324.Goldbach.CertifiedTruncatedZeroCover H
      (TS328.Goldbach.symmetricPayload upper) := by
  have hGroupedParts :=
    (TS328.Goldbach.checkGroupedPayload_iff
      (TS328.Goldbach.symmetricPayload upper)).mp hGrouped
  exact TS326.Goldbach.certifiedTruncatedZeroCover_of_countSaturation
    (certifiedZeroCountSaturation_of_positive
      hNoZero hPositive P hGrouped)
    hGroupedParts.2.1

end

end Goldbach
end TS329
