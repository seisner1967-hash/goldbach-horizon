import Mathlib.Tactic
import TS.Goldbach.Strong.TS264.ConcreteRiemannZetaZeroFamilyRealization
import TS.Goldbach.Strong.TS292.EffectiveInfiniteZeroTailConvergence
import TS.Goldbach.Strong.TS315.DiscreteSpectralCorrelationIdentity
import TS.Goldbach.Strong.TS324.CertifiedZeroCoverSemantics
import TS.Goldbach.Strong.TS326.ZeroCountSaturationCover

namespace TS327
namespace Goldbach

noncomputable section

/-!
# TS327: positive-to-symmetric zero adapter

This micro-sprint isolates the exact conjugation symmetry of the concrete
nontrivial zeta-zero subtype.  It proves the finite positive/negative
multiplicity transports needed by future empirical payloads.

The only additional analytic premise is the explicit absence of a truncated
zero with ordinate zero.  No payload, executable checker, trace-budget
certificate, ledger, or README claim is introduced here.
-/

abbrev ConcreteNontrivialZero := TS324.Goldbach.ConcreteNontrivialZero
abbrev RationalInterval := TS324.Goldbach.RationalInterval
abbrev ZeroBoxPayload := TS324.Goldbach.ZeroBoxPayload

/-! ## Rational box mirroring -/

/-- Mirror a closed rational interval across zero. -/
def mirrorInterval (I : RationalInterval) : RationalInterval where
  lower := -I.upper
  upper := -I.lower

theorem mirrorInterval_involutive (I : RationalInterval) :
    mirrorInterval (mirrorInterval I) = I := by
  cases I
  simp [mirrorInterval]

/-- Mirror one zero box across the real axis. -/
def mirrorBox (box : ZeroBoxPayload) : ZeroBoxPayload where
  realPart := box.realPart
  imagPart := mirrorInterval box.imagPart
  multiplicityUpper := box.multiplicityUpper
  coefficientMassUpper := box.coefficientMassUpper

theorem mirrorBox_involutive (box : ZeroBoxPayload) :
    mirrorBox (mirrorBox box) = box := by
  cases box
  simp [mirrorBox, mirrorInterval]

/-! ## Canonical conjugation on concrete zeros -/

/-- Complex conjugation preserves the concrete nontrivial-zero subtype. -/
noncomputable def conjugateZero
    (rho : ConcreteNontrivialZero) : ConcreteNontrivialZero :=
  Subtype.mk (star rho.1)
    (TS264.Goldbach.concreteNontrivialZero_conjugate_closed rho.property)

theorem conjugateZero_value (rho : ConcreteNontrivialZero) :
    (conjugateZero rho).1 = star rho.1 := rfl

theorem conjugateZero_involutive (rho : ConcreteNontrivialZero) :
    conjugateZero (conjugateZero rho) = rho := by
  apply Subtype.ext
  simp [conjugateZero]

theorem conjugateZero_injective : Function.Injective conjugateZero := by
  intro rho sigma h
  rw [<- conjugateZero_involutive rho, <- conjugateZero_involutive sigma, h]

theorem conjugateZero_mem_truncation_iff
    (H : Nat) (rho : ConcreteNontrivialZero) :
    Membership.mem (TS315.Goldbach.truncatedZeroSet H) (conjugateZero rho) <->
      Membership.mem (TS315.Goldbach.truncatedZeroSet H) rho := by
  rw [TS315.Goldbach.truncatedZeroSet,
    TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff,
    TS292.Goldbach.mem_concreteZerosUpToHeightSubtype_iff]
  simp [conjugateZero]

theorem zeroLiesInBox_conjugate_iff
    (rho : ConcreteNontrivialZero) (box : ZeroBoxPayload) :
    TS324.Goldbach.zeroLiesInBox (conjugateZero rho) (mirrorBox box) <->
      TS324.Goldbach.zeroLiesInBox rho box := by
  unfold TS324.Goldbach.zeroLiesInBox mirrorBox mirrorInterval
  simp only [conjugateZero_value, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Rat.cast_neg]
  constructor
  next =>
    intro h
    exact And.intro h.1
      (And.intro h.2.1 (And.intro (by linarith [h.2.2.2])
        (by linarith [h.2.2.1])))
  next =>
    intro h
    exact And.intro h.1
      (And.intro h.2.1 (And.intro (by linarith [h.2.2.2])
        (by linarith [h.2.2.1])))

theorem concreteZeroMultiplicity_conjugate
    (rho : ConcreteNontrivialZero) :
    TS326.Goldbach.concreteZeroMultiplicity (conjugateZero rho) =
      TS326.Goldbach.concreteZeroMultiplicity rho := by
  unfold TS326.Goldbach.concreteZeroMultiplicity
  simpa [conjugateZero,
    TS264.Goldbach.concreteRiemannZetaTS259Extension] using
      TS264.Goldbach.concreteRiemannZetaTS259Extension.multiplicity_conjugate
        rho.1 rho.property

/-! ## Positive and negative finite truncations -/

/-- Positive-ordinate part of the concrete finite truncation. -/
noncomputable def positiveTruncatedZeros
    (H : Nat) : Finset ConcreteNontrivialZero :=
  (TS315.Goldbach.truncatedZeroSet H).filter (fun rho => 0 < rho.1.im)

/-- Negative-ordinate part of the concrete finite truncation. -/
noncomputable def negativeTruncatedZeros
    (H : Nat) : Finset ConcreteNontrivialZero :=
  (TS315.Goldbach.truncatedZeroSet H).filter (fun rho => rho.1.im < 0)

/-- The explicit finite-height premise excluding real nontrivial zeros. -/
def NoZeroOrdinateInTruncation (H : Nat) : Prop :=
  forall rho,
    Membership.mem (TS315.Goldbach.truncatedZeroSet H) rho ->
      Not (rho.1.im = 0)

theorem positive_negative_disjoint (H : Nat) :
    Disjoint (positiveTruncatedZeros H) (negativeTruncatedZeros H) := by
  rw [Finset.disjoint_left]
  intro rho hPos hNeg
  simp only [positiveTruncatedZeros, negativeTruncatedZeros,
    Finset.mem_filter] at hPos hNeg
  linarith

theorem truncatedZeroSet_eq_positive_union_negative
    (H : Nat) (hNoZero : NoZeroOrdinateInTruncation H) :
    TS315.Goldbach.truncatedZeroSet H =
      Union.union (positiveTruncatedZeros H) (negativeTruncatedZeros H) := by
  ext rho
  constructor
  next =>
    intro hRho
    have hNe : Not (rho.1.im = 0) := hNoZero rho hRho
    exact (lt_or_gt_of_ne hNe).elim
      (fun hNeg => Finset.mem_union_right _
        (Finset.mem_filter.mpr (And.intro hRho hNeg)))
      (fun hPos => Finset.mem_union_left _
        (Finset.mem_filter.mpr (And.intro hRho hPos)))
  next =>
    intro hRho
    exact (Finset.mem_union.mp hRho).elim
      (fun hPos => (Finset.mem_filter.mp hPos).1)
      (fun hNeg => (Finset.mem_filter.mp hNeg).1)

theorem conjugateZero_mem_positive_iff_negative
    (H : Nat) (rho : ConcreteNontrivialZero) :
    Membership.mem (negativeTruncatedZeros H) (conjugateZero rho) <->
      Membership.mem (positiveTruncatedZeros H) rho := by
  simp only [positiveTruncatedZeros, negativeTruncatedZeros,
    Finset.mem_filter, conjugateZero_mem_truncation_iff,
    conjugateZero_value, Complex.star_def, Complex.conj_im]
  constructor
  next =>
    intro h
    exact And.intro h.1 (by linarith [h.2])
  next =>
    intro h
    exact And.intro h.1 (by linarith [h.2])

theorem conjugateZero_mem_negative_iff_positive
    (H : Nat) (rho : ConcreteNontrivialZero) :
    Membership.mem (positiveTruncatedZeros H) (conjugateZero rho) <->
      Membership.mem (negativeTruncatedZeros H) rho := by
  simp only [positiveTruncatedZeros, negativeTruncatedZeros,
    Finset.mem_filter, conjugateZero_mem_truncation_iff,
    conjugateZero_value, Complex.star_def, Complex.conj_im]
  constructor
  next =>
    intro h
    exact And.intro h.1 (by linarith [h.2])
  next =>
    intro h
    exact And.intro h.1 (by linarith [h.2])

/-! ## Multiplicity transports -/

/-- Multiplicity mass on the positive part of the truncation. -/
noncomputable def positiveMultiplicityMass (H : Nat) : Nat :=
  Finset.sum (positiveTruncatedZeros H)
    TS326.Goldbach.concreteZeroMultiplicity

/-- Multiplicity mass on the negative part of the truncation. -/
noncomputable def negativeMultiplicityMass (H : Nat) : Nat :=
  Finset.sum (negativeTruncatedZeros H)
    TS326.Goldbach.concreteZeroMultiplicity

theorem positiveMultiplicityMass_eq_negative (H : Nat) :
    positiveMultiplicityMass H = negativeMultiplicityMass H := by
  unfold positiveMultiplicityMass negativeMultiplicityMass
  refine Finset.sum_nbij' conjugateZero conjugateZero ?_ ?_ ?_ ?_ ?_
  next =>
    intro rho hRho
    exact (conjugateZero_mem_positive_iff_negative H rho).2 hRho
  next =>
    intro rho hRho
    exact (conjugateZero_mem_negative_iff_positive H rho).2 hRho
  next =>
    intro rho _
    exact conjugateZero_involutive rho
  next =>
    intro rho _
    exact conjugateZero_involutive rho
  next =>
    intro rho _
    exact (concreteZeroMultiplicity_conjugate rho).symm

/-- Positive multiplicity mass lying in one box. -/
noncomputable def positiveBoxMultiplicityMass
    (H : Nat) (box : ZeroBoxPayload) : Nat :=
  Finset.sum (positiveTruncatedZeros H) (fun rho =>
    TS326.Goldbach.boxMultiplicityTerm rho box)

/-- Negative multiplicity mass lying in one box. -/
noncomputable def negativeBoxMultiplicityMass
    (H : Nat) (box : ZeroBoxPayload) : Nat :=
  Finset.sum (negativeTruncatedZeros H) (fun rho =>
    TS326.Goldbach.boxMultiplicityTerm rho box)

theorem boxMultiplicityTerm_conjugate_mirror
    (rho : ConcreteNontrivialZero) (box : ZeroBoxPayload) :
    TS326.Goldbach.boxMultiplicityTerm (conjugateZero rho) (mirrorBox box) =
      TS326.Goldbach.boxMultiplicityTerm rho box := by
  classical
  by_cases hIn : TS324.Goldbach.zeroLiesInBox rho box
  case pos =>
    have hConj : TS324.Goldbach.zeroLiesInBox
        (conjugateZero rho) (mirrorBox box) :=
      (zeroLiesInBox_conjugate_iff rho box).2 hIn
    simp [TS326.Goldbach.boxMultiplicityTerm, hIn, hConj,
      concreteZeroMultiplicity_conjugate]
  case neg =>
    have hConj : Not (TS324.Goldbach.zeroLiesInBox
        (conjugateZero rho) (mirrorBox box)) := by
      intro h
      exact hIn ((zeroLiesInBox_conjugate_iff rho box).1 h)
    simp [TS326.Goldbach.boxMultiplicityTerm, hIn, hConj]

theorem positiveBoxMultiplicityMass_eq_mirroredNegative
    (H : Nat) (box : ZeroBoxPayload) :
    positiveBoxMultiplicityMass H box =
      negativeBoxMultiplicityMass H (mirrorBox box) := by
  unfold positiveBoxMultiplicityMass negativeBoxMultiplicityMass
  refine Finset.sum_nbij' conjugateZero conjugateZero ?_ ?_ ?_ ?_ ?_
  next =>
    intro rho hRho
    exact (conjugateZero_mem_positive_iff_negative H rho).2 hRho
  next =>
    intro rho hRho
    exact (conjugateZero_mem_negative_iff_positive H rho).2 hRho
  next =>
    intro rho _
    exact conjugateZero_involutive rho
  next =>
    intro rho _
    exact conjugateZero_involutive rho
  next =>
    intro rho _
    exact (boxMultiplicityTerm_conjugate_mirror rho box).symm

theorem truncatedMultiplicityMass_eq_twice_positive
    (H : Nat) (hNoZero : NoZeroOrdinateInTruncation H) :
    TS326.Goldbach.truncatedMultiplicityMass H =
      2 * positiveMultiplicityMass H := by
  unfold TS326.Goldbach.truncatedMultiplicityMass
  rw [truncatedZeroSet_eq_positive_union_negative H hNoZero,
    Finset.sum_union (positive_negative_disjoint H)]
  change positiveMultiplicityMass H + negativeMultiplicityMass H =
    2 * positiveMultiplicityMass H
  rw [<- positiveMultiplicityMass_eq_negative H]
  omega

end

end Goldbach
end TS327
