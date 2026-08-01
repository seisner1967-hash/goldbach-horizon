import Mathlib.Tactic
import TS.Goldbach.Strong.TS332.ShiftedInfiniteZeroTailProvider

namespace TS333
namespace Goldbach

noncomputable section

/-!
# TS333: abstract shifted spectral-mass assembly

This module combines abstract finite linear and quadratic coefficient caps
with the shifted infinite-zero tail supplied by TS332.  The finite caps remain
explicit premises.  No zero payload, concrete cap, trace-budget template, or
half-budget claim is constructed here.
-/

/-! ## Exact quadratic core and tail -/

/-- Quadratic coefficient mass retained in the finite height-`H` core. -/
noncomputable def finiteQuadraticCoefficientMass (H : Nat) : Real :=
  Finset.sum (TS315.Goldbach.truncatedZeroSet H)
    (fun rho => TS316.Goldbach.zeroCoefficientMagnitude rho ^ 2)

/-- Quadratic coefficient mass outside the finite height-`H` core. -/
noncomputable def quadraticCoefficientTailMass (H : Nat) : Real :=
  tsum (fun rho : TS322.Goldbach.CoefficientTailIndex H =>
    TS316.Goldbach.zeroCoefficientMagnitude rho.1 ^ 2)

theorem finiteQuadraticCoefficientMass_nonnegative (H : Nat) :
    0 <= finiteQuadraticCoefficientMass H := by
  unfold finiteQuadraticCoefficientMass
  exact Finset.sum_nonneg (fun rho _ =>
    sq_nonneg (TS316.Goldbach.zeroCoefficientMagnitude rho))

theorem quadraticCoefficientTailMass_nonnegative (H : Nat) :
    0 <= quadraticCoefficientTailMass H := by
  unfold quadraticCoefficientTailMass
  exact tsum_nonneg (fun rho =>
    sq_nonneg (TS316.Goldbach.zeroCoefficientMagnitude rho.1))

theorem quadraticCoefficientTailMass_summable (H : Nat) :
    Summable (fun rho : TS322.Goldbach.CoefficientTailIndex H =>
      TS316.Goldbach.zeroCoefficientMagnitude rho.1 ^ 2) := by
  simpa [TS322.Goldbach.CoefficientTailIndex, Function.comp_def] using
    TS316.Goldbach.zeroCoefficientMagnitude_sq_summable.subtype
      {rho : TS316.Goldbach.ConcreteNontrivialZero |
        Not (Membership.mem (TS315.Goldbach.truncatedZeroSet H) rho)}

/-- The finite quadratic core and its exact complement partition the global
quadratic mass. -/
theorem finiteQuadraticCoefficientMass_add_tail (H : Nat) :
    finiteQuadraticCoefficientMass H + quadraticCoefficientTailMass H =
      TS316.Goldbach.globalQuadraticSpectralMass := by
  simpa [finiteQuadraticCoefficientMass, quadraticCoefficientTailMass,
    TS322.Goldbach.CoefficientTailIndex,
    TS315.Goldbach.truncatedZeroSet,
    TS316.Goldbach.globalQuadraticSpectralMass] using
      sum_add_tsum_subtype_compl
        TS316.Goldbach.zeroCoefficientMagnitude_sq_summable
        (TS315.Goldbach.truncatedZeroSet H)

/-- On the residual subtype, the quadratic mass is at most the square of the
linear mass. -/
theorem quadraticCoefficientTailMass_le_linear_sq (H : Nat) :
    quadraticCoefficientTailMass H <=
      TS322.Goldbach.linearCoefficientTailMass H ^ 2 := by
  let a : TS322.Goldbach.CoefficientTailIndex H -> Real :=
    fun rho => TS316.Goldbach.zeroCoefficientMagnitude rho.1
  have ha : Summable a := TS322.Goldbach.linearCoefficientTailMass_summable H
  have ha0 : forall rho, 0 <= a rho := fun rho =>
    TS316.Goldbach.zeroCoefficientMagnitude_nonnegative rho.1
  let S : Real := tsum a
  have hSq : Summable (fun rho => a rho ^ 2) :=
    TS316.Goldbach.summable_sq_of_summable_nonnegative a ha ha0
  have hPointwise : forall rho, a rho ^ 2 <= S * a rho := by
    intro rho
    have hLe : a rho <= S := by
      exact le_tsum ha rho (fun sigma hNe => ha0 sigma)
    nlinarith [ha0 rho]
  have hMajorant : Summable (fun rho => S * a rho) := ha.mul_left S
  unfold quadraticCoefficientTailMass TS322.Goldbach.linearCoefficientTailMass
  change tsum (fun rho => a rho ^ 2) <= tsum a ^ 2
  calc
    tsum (fun rho => a rho ^ 2) <= tsum (fun rho => S * a rho) :=
      tsum_le_tsum hPointwise hSq hMajorant
    _ = S * tsum a := ha.tsum_mul_left S
    _ = tsum a ^ 2 := by ring

/-! ## Assembly from arbitrary real caps -/

/-- A finite linear cap and a tail cap bound the global linear mass. -/
theorem globalLinearSpectralMass_le_of_finite_tailCaps
    {H : Nat} {L R : Real}
    (hL : TS322.Goldbach.finiteLinearCoefficientMass H <= L)
    (hR : TS322.Goldbach.linearCoefficientTailMass H <= R) :
    TS316.Goldbach.globalLinearSpectralMass <= L + R := by
  rw [<- TS322.Goldbach.finiteLinearCoefficientMass_add_tail H]
  exact add_le_add hL hR

/-- A finite quadratic cap and a linear tail cap bound the global quadratic
mass. -/
theorem globalQuadraticSpectralMass_le_of_finite_tailCaps
    {H : Nat} {Q R : Real}
    (hQ : finiteQuadraticCoefficientMass H <= Q)
    (hR : TS322.Goldbach.linearCoefficientTailMass H <= R) :
    TS316.Goldbach.globalQuadraticSpectralMass <= Q + R ^ 2 := by
  have hTailNonnegative := TS322.Goldbach.linearCoefficientTailMass_nonnegative H
  have hRNonnegative : 0 <= R := hTailNonnegative.trans hR
  have hTailSq :
      TS322.Goldbach.linearCoefficientTailMass H ^ 2 <= R ^ 2 := by
    nlinarith
  rw [<- finiteQuadraticCoefficientMass_add_tail H]
  exact add_le_add hQ
    ((quadraticCoefficientTailMass_le_linear_sq H).trans hTailSq)

/-- The TS322 weighted tail error is controlled by abstract finite and tail
linear caps. -/
theorem effectiveWeightedTailError_le_of_finite_tailCaps
    {H : Nat} {L R : Real}
    (hL : TS322.Goldbach.finiteLinearCoefficientMass H <= L)
    (hR : TS322.Goldbach.linearCoefficientTailMass H <= R) :
    TS322.Goldbach.effectiveWeightedTailError H <=
      2 * (L + R) * R := by
  have hGlobal := globalLinearSpectralMass_le_of_finite_tailCaps hL hR
  have hTailNonnegative := TS322.Goldbach.linearCoefficientTailMass_nonnegative H
  have hGlobalUpperNonnegative : 0 <= L + R :=
    TS316.Goldbach.globalLinearSpectralMass_nonnegative.trans hGlobal
  have hProduct :
      TS316.Goldbach.globalLinearSpectralMass *
          TS322.Goldbach.linearCoefficientTailMass H <=
        (L + R) * R :=
    mul_le_mul hGlobal hR hTailNonnegative hGlobalUpperNonnegative
  calc
    TS322.Goldbach.effectiveWeightedTailError H =
        2 * (TS316.Goldbach.globalLinearSpectralMass *
          TS322.Goldbach.linearCoefficientTailMass H) := by
      unfold TS322.Goldbach.effectiveWeightedTailError
      ring
    _ <= 2 * ((L + R) * R) :=
      mul_le_mul_of_nonneg_left hProduct (by norm_num)
    _ = 2 * (L + R) * R := by ring

/-- Four times the global quadratic mass is controlled by abstract finite and
tail caps. -/
theorem diagonalSpectralMass_le_of_finite_tailCaps
    {H : Nat} {Q R : Real}
    (hQ : finiteQuadraticCoefficientMass H <= Q)
    (hR : TS322.Goldbach.linearCoefficientTailMass H <= R) :
    4 * TS316.Goldbach.globalQuadraticSpectralMass <=
      4 * (Q + R ^ 2) := by
  exact mul_le_mul_of_nonneg_left
    (globalQuadraticSpectralMass_le_of_finite_tailCaps hQ hR)
    (by norm_num)

/-! ## Specialization to the shifted TS332 tail -/

/-- Analytic shifted residual majorant at height `H`. -/
noncomputable def shiftedResidualMajorant (H : Nat) : Real :=
  TS332.Goldbach.shiftedInfiniteZeroResidualTailConstant *
    TS292.Goldbach.logarithmicTailRate H

theorem shiftedResidualMajorant_nonnegative (H : Nat) :
    0 <= shiftedResidualMajorant H := by
  unfold shiftedResidualMajorant
  exact mul_nonneg
    TS332.Goldbach.shiftedInfiniteZeroResidualTailConstant_nonnegative
    (by
      unfold TS292.Goldbach.logarithmicTailRate
      exact div_nonneg
        (add_nonneg
          (Real.log_nonneg (by
            have hHNonnegative : (0 : Real) <= (H : Real) :=
              Nat.cast_nonneg H
            linarith))
          (by norm_num))
        (Nat.cast_nonneg H))

theorem linearCoefficientTailMass_le_shiftedResidualMajorant
    (H : Nat)
    (hH : 2 <= H) :
    TS322.Goldbach.linearCoefficientTailMass H <=
      shiftedResidualMajorant H := by
  simpa [shiftedResidualMajorant] using
    TS332.Goldbach.linearCoefficientTailMass_le_shifted H hH

theorem globalLinearSpectralMass_le_of_shifted_finiteCap
    {H : Nat} {L : Real}
    (hH : 2 <= H)
    (hL : TS322.Goldbach.finiteLinearCoefficientMass H <= L) :
    TS316.Goldbach.globalLinearSpectralMass <=
      L + shiftedResidualMajorant H :=
  globalLinearSpectralMass_le_of_finite_tailCaps hL
    (linearCoefficientTailMass_le_shiftedResidualMajorant H hH)

theorem globalQuadraticSpectralMass_le_of_shifted_finiteCap
    {H : Nat} {Q : Real}
    (hH : 2 <= H)
    (hQ : finiteQuadraticCoefficientMass H <= Q) :
    TS316.Goldbach.globalQuadraticSpectralMass <=
      Q + shiftedResidualMajorant H ^ 2 :=
  globalQuadraticSpectralMass_le_of_finite_tailCaps hQ
    (linearCoefficientTailMass_le_shiftedResidualMajorant H hH)

theorem effectiveWeightedTailError_le_of_shifted_finiteCap
    {H : Nat} {L : Real}
    (hH : 2 <= H)
    (hL : TS322.Goldbach.finiteLinearCoefficientMass H <= L) :
    TS322.Goldbach.effectiveWeightedTailError H <=
      2 * (L + shiftedResidualMajorant H) * shiftedResidualMajorant H :=
  effectiveWeightedTailError_le_of_finite_tailCaps hL
    (linearCoefficientTailMass_le_shiftedResidualMajorant H hH)

theorem diagonalSpectralMass_le_of_shifted_finiteCap
    {H : Nat} {Q : Real}
    (hH : 2 <= H)
    (hQ : finiteQuadraticCoefficientMass H <= Q) :
    4 * TS316.Goldbach.globalQuadraticSpectralMass <=
      4 * (Q + shiftedResidualMajorant H ^ 2) :=
  diagonalSpectralMass_le_of_finite_tailCaps hQ
    (linearCoefficientTailMass_le_shiftedResidualMajorant H hH)

/-! ## Abstract rational-cap interfaces -/

theorem effectiveWeightedTailError_le_of_rationalCaps
    {H : Nat} {L R : Rat}
    (hL : TS322.Goldbach.finiteLinearCoefficientMass H <= (L : Real))
    (hR : TS322.Goldbach.linearCoefficientTailMass H <= (R : Real)) :
    TS322.Goldbach.effectiveWeightedTailError H <=
      ((2 * (L + R) * R : Rat) : Real) := by
  simpa using effectiveWeightedTailError_le_of_finite_tailCaps hL hR

theorem diagonalSpectralMass_le_of_rationalCaps
    {H : Nat} {Q R : Rat}
    (hQ : finiteQuadraticCoefficientMass H <= (Q : Real))
    (hR : TS322.Goldbach.linearCoefficientTailMass H <= (R : Real)) :
    4 * TS316.Goldbach.globalQuadraticSpectralMass <=
      ((4 * (Q + R ^ 2) : Rat) : Real) := by
  simpa using diagonalSpectralMass_le_of_finite_tailCaps hQ hR

/-! ## Rational tail specialization at the reference height -/

theorem effectiveWeightedTailError_referenceHeight_le_of_rationalFiniteCap
    {L : Rat}
    (hL : TS322.Goldbach.finiteLinearCoefficientMass 1132490 <= (L : Real)) :
    TS322.Goldbach.effectiveWeightedTailError 1132490 <=
      ((2 * (L + 31140 / 2151731) * (31140 / 2151731) : Rat) : Real) := by
  apply effectiveWeightedTailError_le_of_rationalCaps hL
  simpa using TS332.Goldbach.linearCoefficientTailMass_referenceHeight_le

theorem diagonalSpectralMass_referenceHeight_le_of_rationalFiniteCap
    {Q : Rat}
    (hQ : finiteQuadraticCoefficientMass 1132490 <= (Q : Real)) :
    4 * TS316.Goldbach.globalQuadraticSpectralMass <=
      ((4 * (Q + (31140 / 2151731) ^ 2) : Rat) : Real) := by
  apply diagonalSpectralMass_le_of_rationalCaps hQ
  simpa using TS332.Goldbach.linearCoefficientTailMass_referenceHeight_le

end


end Goldbach
end TS333
