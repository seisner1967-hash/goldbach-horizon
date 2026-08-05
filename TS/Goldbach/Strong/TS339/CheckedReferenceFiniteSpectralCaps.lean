import Mathlib.Tactic
import TS.Goldbach.Strong.TS325.ExecutablePayloadChecker
import TS.Goldbach.Strong.TS333.AbstractShiftedSpectralMassAssembly
import TS.Goldbach.Strong.TS338.ConcreteZetaLedgerReferenceBudgetBridge

namespace TS339
namespace Goldbach

noncomputable section

/-!
# TS339: checked reference finite spectral caps

This module computes rational linear and quadratic coefficient-mass majorants
from an untrusted TS324 zero-cover payload. A Boolean checker verifies only
payload well-formedness and the two rational reference caps. An independently
supplied `CertifiedTruncatedZeroCover` then transfers those checks to the exact
finite spectral masses used by TS338.

No payload is instantiated here. Analytic coverage remains an explicit premise,
and no core saturation or trace-budget completion is constructed.
-/

/-! ## Executable rational majorants -/

/-- Sum of the declared linear coefficient-mass bounds. -/
def computedLinearCoefficientMajorant
    (data : TS324.Goldbach.ZeroCoverPayload) : Rat :=
  Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
    data.boxes[i].coefficientMassUpper)

/-- Sum of the squares of the declared coefficient-mass bounds. -/
def computedQuadraticCoefficientMajorant
    (data : TS324.Goldbach.ZeroCoverPayload) : Rat :=
  Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
    data.boxes[i].coefficientMassUpper ^ 2)

/-- Check payload structure and both rational reference caps. -/
def checkReferenceFiniteSpectralCaps
    (data : TS324.Goldbach.ZeroCoverPayload) : Bool :=
  TS325.Goldbach.checkPayloadWellFormed data &&
    decide (computedLinearCoefficientMajorant data <= (1 : Rat) / 20) &&
      decide (computedQuadraticCoefficientMajorant data <= (1 : Rat) / 10000)

theorem checkReferenceFiniteSpectralCaps_iff
    (data : TS324.Goldbach.ZeroCoverPayload) :
    checkReferenceFiniteSpectralCaps data = true <->
      TS324.Goldbach.PayloadWellFormed data /\
        computedLinearCoefficientMajorant data <= (1 : Rat) / 20 /\
          computedQuadraticCoefficientMajorant data <= (1 : Rat) / 10000 := by
  simp [checkReferenceFiniteSpectralCaps,
    TS325.Goldbach.checkPayloadWellFormed_iff, and_assoc]

/-! ## Linear overcounting -/

theorem zeroCoefficientMagnitude_le_boxTermSum
    {H : Nat} {data : TS324.Goldbach.ZeroCoverPayload}
    (C : TS324.Goldbach.CertifiedTruncatedZeroCover H data)
    (rho : TS324.Goldbach.ConcreteNontrivialZero)
    (hRho : Membership.mem (TS315.Goldbach.truncatedZeroSet H) rho) :
    TS316.Goldbach.zeroCoefficientMagnitude rho <=
      Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        TS324.Goldbach.boxCoefficientTerm rho data.boxes[i]) := by
  cases C.covers rho hRho with
  | intro i hBox =>
      have hSelected :
          TS324.Goldbach.boxCoefficientTerm rho data.boxes[i] =
            TS316.Goldbach.zeroCoefficientMagnitude rho := by
        unfold TS324.Goldbach.boxCoefficientTerm
        rw [if_pos hBox]
      rw [<- hSelected]
      exact Finset.single_le_sum
        (fun j _ =>
          TS324.Goldbach.boxCoefficientTerm_nonnegative rho data.boxes[j])
        (Finset.mem_univ i)

theorem finiteLinearCoefficientMass_le_computedMajorant
    {H : Nat} {data : TS324.Goldbach.ZeroCoverPayload}
    (C : TS324.Goldbach.CertifiedTruncatedZeroCover H data) :
    TS322.Goldbach.finiteLinearCoefficientMass H <=
      (computedLinearCoefficientMajorant data : Real) := by
  unfold TS322.Goldbach.finiteLinearCoefficientMass
  calc
    Finset.sum (TS315.Goldbach.truncatedZeroSet H)
        TS316.Goldbach.zeroCoefficientMagnitude <=
      Finset.sum (TS315.Goldbach.truncatedZeroSet H) (fun rho =>
        Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
          TS324.Goldbach.boxCoefficientTerm rho data.boxes[i])) := by
            apply Finset.sum_le_sum
            intro rho hRho
            exact zeroCoefficientMagnitude_le_boxTermSum C rho hRho
    _ = Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        TS324.Goldbach.boxCoefficientMass H data.boxes[i]) := by
          rw [Finset.sum_comm]
          rfl
    _ <= Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        (data.boxes[i].coefficientMassUpper : Real)) := by
          exact Finset.sum_le_sum (fun i _ => C.coefficientMassValid i)
    _ = (computedLinearCoefficientMajorant data : Real) := by
          unfold computedLinearCoefficientMajorant
          push_cast
          rfl

/-! ## Quadratic overcounting -/

/-- Exact quadratic coefficient mass contributed by one box. -/
noncomputable def boxQuadraticCoefficientMass
    (H : Nat) (box : TS324.Goldbach.ZeroBoxPayload) : Real :=
  Finset.sum (TS315.Goldbach.truncatedZeroSet H) (fun rho =>
    TS324.Goldbach.boxCoefficientTerm rho box ^ 2)

theorem boxQuadraticCoefficientMass_nonnegative
    (H : Nat) (box : TS324.Goldbach.ZeroBoxPayload) :
    0 <= boxQuadraticCoefficientMass H box := by
  unfold boxQuadraticCoefficientMass
  exact Finset.sum_nonneg (fun rho _ =>
    sq_nonneg (TS324.Goldbach.boxCoefficientTerm rho box))

theorem boxQuadraticCoefficientMass_le_linear_sq
    (H : Nat) (box : TS324.Goldbach.ZeroBoxPayload) :
    boxQuadraticCoefficientMass H box <=
      TS324.Goldbach.boxCoefficientMass H box ^ 2 := by
  let zeros := TS315.Goldbach.truncatedZeroSet H
  have hTermLe : forall rho, Membership.mem zeros rho ->
      TS324.Goldbach.boxCoefficientTerm rho box <=
        TS324.Goldbach.boxCoefficientMass H box := by
    intro rho hRho
    unfold TS324.Goldbach.boxCoefficientMass
    exact Finset.single_le_sum
      (fun sigma _ =>
        TS324.Goldbach.boxCoefficientTerm_nonnegative sigma box)
      hRho
  calc
    boxQuadraticCoefficientMass H box <=
      Finset.sum zeros (fun rho =>
        TS324.Goldbach.boxCoefficientMass H box *
          TS324.Goldbach.boxCoefficientTerm rho box) := by
            unfold boxQuadraticCoefficientMass
            apply Finset.sum_le_sum
            intro rho hRho
            have hNonneg :=
              TS324.Goldbach.boxCoefficientTerm_nonnegative rho box
            nlinarith [hTermLe rho hRho]
    _ = TS324.Goldbach.boxCoefficientMass H box *
        TS324.Goldbach.boxCoefficientMass H box := by
          rw [<- Finset.mul_sum]
          rfl
    _ = TS324.Goldbach.boxCoefficientMass H box ^ 2 := by ring

theorem zeroCoefficientMagnitude_sq_le_boxQuadraticTermSum
    {H : Nat} {data : TS324.Goldbach.ZeroCoverPayload}
    (C : TS324.Goldbach.CertifiedTruncatedZeroCover H data)
    (rho : TS324.Goldbach.ConcreteNontrivialZero)
    (hRho : Membership.mem (TS315.Goldbach.truncatedZeroSet H) rho) :
    TS316.Goldbach.zeroCoefficientMagnitude rho ^ 2 <=
      Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        TS324.Goldbach.boxCoefficientTerm rho data.boxes[i] ^ 2) := by
  cases C.covers rho hRho with
  | intro i hBox =>
      have hSelected :
          TS324.Goldbach.boxCoefficientTerm rho data.boxes[i] =
            TS316.Goldbach.zeroCoefficientMagnitude rho := by
        unfold TS324.Goldbach.boxCoefficientTerm
        rw [if_pos hBox]
      rw [<- hSelected]
      exact Finset.single_le_sum
        (fun j _ => sq_nonneg
          (TS324.Goldbach.boxCoefficientTerm rho data.boxes[j]))
        (Finset.mem_univ i)

theorem finiteQuadraticCoefficientMass_le_computedMajorant
    {H : Nat} {data : TS324.Goldbach.ZeroCoverPayload}
    (hData : TS324.Goldbach.PayloadWellFormed data)
    (C : TS324.Goldbach.CertifiedTruncatedZeroCover H data) :
    TS333.Goldbach.finiteQuadraticCoefficientMass H <=
      (computedQuadraticCoefficientMajorant data : Real) := by
  unfold TS333.Goldbach.finiteQuadraticCoefficientMass
  calc
    Finset.sum (TS315.Goldbach.truncatedZeroSet H) (fun rho =>
        TS316.Goldbach.zeroCoefficientMagnitude rho ^ 2) <=
      Finset.sum (TS315.Goldbach.truncatedZeroSet H) (fun rho =>
        Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
          TS324.Goldbach.boxCoefficientTerm rho data.boxes[i] ^ 2)) := by
            apply Finset.sum_le_sum
            intro rho hRho
            exact zeroCoefficientMagnitude_sq_le_boxQuadraticTermSum C rho hRho
    _ = Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        boxQuadraticCoefficientMass H data.boxes[i]) := by
          rw [Finset.sum_comm]
          rfl
    _ <= Finset.sum Finset.univ (fun i : Fin data.boxes.size =>
        (data.boxes[i].coefficientMassUpper : Real) ^ 2) := by
          apply Finset.sum_le_sum
          intro i _
          have hLocal :=
            boxQuadraticCoefficientMass_le_linear_sq H data.boxes[i]
          have hMass := C.coefficientMassValid i
          have hMassNonneg :=
            TS324.Goldbach.boxCoefficientMass_nonnegative H data.boxes[i]
          have hCapNonneg :
              0 <= (data.boxes[i].coefficientMassUpper : Real) := by
            exact_mod_cast hData.coefficientMassesNonnegative i
          have hSquares :
              TS324.Goldbach.boxCoefficientMass H data.boxes[i] ^ 2 <=
                (data.boxes[i].coefficientMassUpper : Real) ^ 2 := by
            nlinarith
          exact hLocal.trans hSquares
    _ = (computedQuadraticCoefficientMajorant data : Real) := by
          unfold computedQuadraticCoefficientMajorant
          push_cast
          rfl

/-! ## Reference caps and TS338 routing -/

structure ReferenceFiniteSpectralCaps : Prop where
  linear_cap :
    TS322.Goldbach.finiteLinearCoefficientMass 1132490 <=
      (((1 : Rat) / 20 : Rat) : Real)
  quadratic_cap :
    TS333.Goldbach.finiteQuadraticCoefficientMass 1132490 <=
      (((1 : Rat) / 10000 : Rat) : Real)

theorem referenceFiniteSpectralCaps_of_checkedCover
    {data : TS324.Goldbach.ZeroCoverPayload}
    (C : TS324.Goldbach.CertifiedTruncatedZeroCover 1132490 data)
    (hCheck : checkReferenceFiniteSpectralCaps data = true) :
    ReferenceFiniteSpectralCaps := by
  have hReflected :=
    (checkReferenceFiniteSpectralCaps_iff data).mp hCheck
  have hLinearCast :
      (computedLinearCoefficientMajorant data : Real) <=
        (((1 : Rat) / 20 : Rat) : Real) := by
    exact_mod_cast hReflected.2.1
  have hQuadraticCast :
      (computedQuadraticCoefficientMajorant data : Real) <=
        (((1 : Rat) / 10000 : Rat) : Real) := by
    exact_mod_cast hReflected.2.2
  exact {
    linear_cap :=
      (finiteLinearCoefficientMass_le_computedMajorant C).trans hLinearCast
    quadratic_cap :=
      (finiteQuadraticCoefficientMass_le_computedMajorant hReflected.1 C).trans
        hQuadraticCast
  }

/-- Route checked finite caps and an independent semantic cover into TS338. -/
noncomputable def concreteReferenceTraceBudgetTemplate_of_checkedCover
    {data : TS324.Goldbach.ZeroCoverPayload}
    (C : TS324.Goldbach.CertifiedTruncatedZeroCover 1132490 data)
    (hCheck : checkReferenceFiniteSpectralCaps data = true) :
    TS330.Goldbach.RationalTraceBudgetTemplate
      1132490 ((1 : Rat) / 7500) :=
  let caps := referenceFiniteSpectralCaps_of_checkedCover C hCheck
  TS338.Goldbach.concreteReferenceTraceBudgetTemplate
    caps.linear_cap caps.quadratic_cap

end

end Goldbach
end TS339
