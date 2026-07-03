import Mathlib.Tactic
import TS.Goldbach.Strong.TS220.CosSquareIPPPrimitiveDerivativeBridge

namespace TS221
namespace Goldbach

open MeasureTheory

/-!
# TS221 - Cos-Square Finite Triple IPP Discharge

TS219 reformulated the triple integration-by-parts target as a finite cutoff
identity on `[eps, T]` plus boundary terms. TS220 proved the local derivative
identity for an explicit primitive `P`.

This sprint closes the finite compact part:

* it identifies `P(x)` with the sum of the three TS219 boundary terms;
* it proves `P(T) - P(eps)` equals `cosSquareTripleIPPBoundarySum eps T`;
* it applies the finite-interval FTC to prove
  `TS219.Goldbach.CosSquareFiniteTripleIPPStatement`.

No improper limit is taken in TS221. Boundary vanishing, the third-derivative
cutoff value, Dirichlet cutoff or Abel values, the canonical `sinc^4` value,
Plancherel evidence, and Goldbach remain open.
-/

/-- The TS220 primitive is exactly the sum of the three TS219 boundary terms. -/
theorem cosSquareIPPPrimitive_eq_boundaryTerms
    (x : Real) :
    TS220.Goldbach.cosSquareIPPPrimitive x =
      TS219.Goldbach.cosSquareTripleIPPBoundaryTerm1 x +
        TS219.Goldbach.cosSquareTripleIPPBoundaryTerm2 x +
          TS219.Goldbach.cosSquareTripleIPPBoundaryTerm3 x := by
  have h1 :
      (-(1 / 3 : Real)) *
          TS213.Goldbach.cosSquareRemainder x * x ^ (-3 : Int) =
        TS219.Goldbach.cosSquareTripleIPPBoundaryTerm1 x := by
    unfold TS219.Goldbach.cosSquareTripleIPPBoundaryTerm1
    simp [zpow_neg, zpow_natCast, div_eq_mul_inv]
    ac_rfl
  have h2 :
      (-(1 / 6 : Real)) *
          TS220.Goldbach.cosSquareFirstDerivativeModel x *
            x ^ (-2 : Int) =
        TS219.Goldbach.cosSquareTripleIPPBoundaryTerm2 x := by
    unfold TS220.Goldbach.cosSquareFirstDerivativeModel
    unfold TS219.Goldbach.cosSquareTripleIPPBoundaryTerm2
    simp [zpow_neg, zpow_natCast, div_eq_mul_inv]
    ring_nf
    exact
      congrArg
        (fun y : Real =>
          Real.cos x * Real.sin x * y * ((-1 / 3 : Real)) +
            Real.sin x * y * (1 / 3 : Real))
        (inv_pow x 2).symm
  have h3 :
      (-(1 / 6 : Real)) *
          TS220.Goldbach.cosSquareSecondDerivativeModel x *
            x ^ (-1 : Int) =
        TS219.Goldbach.cosSquareTripleIPPBoundaryTerm3 x := by
    unfold TS220.Goldbach.cosSquareSecondDerivativeModel
    unfold TS219.Goldbach.cosSquareTripleIPPBoundaryTerm3
    rw [Real.sin_sq]
    simp [zpow_neg, zpow_natCast, div_eq_mul_inv, inv_pow]
    ring
  unfold TS220.Goldbach.cosSquareIPPPrimitive
  rw [h1, h2, h3]

/-- The primitive jump is the TS219 boundary sum. -/
theorem cosSquareIPPPrimitive_jump_eq_boundarySum
    (eps T : Real) :
    TS220.Goldbach.cosSquareIPPPrimitive T -
        TS220.Goldbach.cosSquareIPPPrimitive eps =
      TS219.Goldbach.cosSquareTripleIPPBoundarySum eps T := by
  rw [cosSquareIPPPrimitive_eq_boundaryTerms T]
  rw [cosSquareIPPPrimitive_eq_boundaryTerms eps]
  unfold TS219.Goldbach.cosSquareTripleIPPBoundarySum
  unfold TS219.Goldbach.boundaryJump
  ring

/-- The finite triple IPP identity on `[eps, T]`. -/
theorem cosSquareFiniteTripleIPP :
    TS219.Goldbach.CosSquareFiniteTripleIPPStatement := by
  intro eps T heps hT
  let g : Real -> Real :=
    fun x =>
      TS213.Goldbach.cosSquareHaarKernel x -
        (1 / 6 : Real) * TS213.Goldbach.cosSquareThirdDerivativeKernel x
  have hderiv :
      forall x : Real,
        Set.Mem (Set.uIcc eps T) x ->
          HasDerivAt TS220.Goldbach.cosSquareIPPPrimitive (g x) x := by
    intro x hx
    have hx_left : eps <= x := by
      rcases Set.mem_uIcc.1 hx with h | h
      next =>
        exact h.1
      next =>
        linarith
    have hx0 : Ne x 0 := by
      linarith
    exact TS220.Goldbach.cosSquareIPPPrimitive_hasDerivAt x hx0
  have hcont_haar :
      ContinuousOn
        (fun x : Real => TS213.Goldbach.cosSquareHaarKernel x)
        (Set.uIcc eps T) := by
    intro x hx
    have hx_left : eps <= x := by
      rcases Set.mem_uIcc.1 hx with h | h
      next =>
        exact h.1
      next =>
        linarith
    have hx0 : Ne x 0 := by
      linarith
    unfold TS213.Goldbach.cosSquareHaarKernel
    unfold TS213.Goldbach.cosSquareRemainder
    exact
      ((by fun_prop :
        Continuous
          (fun y : Real => (1 - Real.cos y) ^ 2)).continuousWithinAt).div
        ((by fun_prop :
          Continuous
            (fun y : Real => y ^ 4)).continuousWithinAt)
        (pow_ne_zero 4 hx0)
  have hcont_third :
      ContinuousOn
        (fun x : Real => TS213.Goldbach.cosSquareThirdDerivativeKernel x)
        (Set.uIcc eps T) := by
    intro x hx
    have hx_left : eps <= x := by
      rcases Set.mem_uIcc.1 hx with h | h
      next =>
        exact h.1
      next =>
        linarith
    have hx0 : Ne x 0 := by
      linarith
    unfold TS213.Goldbach.cosSquareThirdDerivativeKernel
    exact
      ((by fun_prop :
        Continuous
          (fun y : Real =>
            -2 * Real.sin y + 4 * Real.sin (2 * y))).continuousWithinAt).div
        ((by fun_prop :
          Continuous
            (fun y : Real => y)).continuousWithinAt)
        hx0
  have hcont_g :
      ContinuousOn g (Set.uIcc eps T) := by
    unfold g
    exact hcont_haar.sub (continuousOn_const.mul hcont_third)
  have hint :
      IntervalIntegrable g volume eps T :=
    hcont_g.intervalIntegrable
  have hFTC :
      intervalIntegral g eps T volume =
        TS220.Goldbach.cosSquareIPPPrimitive T -
          TS220.Goldbach.cosSquareIPPPrimitive eps :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hjump :
      TS220.Goldbach.cosSquareIPPPrimitive T -
          TS220.Goldbach.cosSquareIPPPrimitive eps =
        TS219.Goldbach.cosSquareTripleIPPBoundarySum eps T :=
    cosSquareIPPPrimitive_jump_eq_boundarySum eps T
  have hsplit :
      intervalIntegral g eps T volume =
        intervalIntegral
          (fun x : Real => TS213.Goldbach.cosSquareHaarKernel x)
          eps
          T
          volume -
        (1 / 6 : Real) *
          intervalIntegral
            (fun x : Real => TS213.Goldbach.cosSquareThirdDerivativeKernel x)
            eps
            T
            volume := by
    unfold g
    rw [intervalIntegral.integral_sub hcont_haar.intervalIntegrable
      (continuousOn_const.mul hcont_third).intervalIntegrable]
    rw [intervalIntegral.integral_const_mul]
  rw [hsplit, hjump] at hFTC
  linarith

/-- Ledger recording the finite triple IPP discharge. -/
structure CosSquareFiniteTripleIPPDischargeLedger where
  ts220_derivative_bridge :
    TS220.Goldbach.CosSquareIPPPrimitiveDerivativeBridgeLedger

  primitive_boundary_terms :
    forall x : Real,
      TS220.Goldbach.cosSquareIPPPrimitive x =
        TS219.Goldbach.cosSquareTripleIPPBoundaryTerm1 x +
          TS219.Goldbach.cosSquareTripleIPPBoundaryTerm2 x +
            TS219.Goldbach.cosSquareTripleIPPBoundaryTerm3 x

  primitive_jump_boundary_sum :
    forall eps T : Real,
      TS220.Goldbach.cosSquareIPPPrimitive T -
          TS220.Goldbach.cosSquareIPPPrimitive eps =
        TS219.Goldbach.cosSquareTripleIPPBoundarySum eps T

  finite_triple_ipp :
    TS219.Goldbach.CosSquareFiniteTripleIPPStatement

  boundary_vanishing_not_proved :
    True

  third_derivative_cutoff_value_not_proved :
    True

  dirichlet_cutoff_not_proved :
    True

  canonical_sinc_fourth_value_not_proved :
    True

  plancherel_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS221 finite triple IPP discharge ledger. -/
noncomputable def cosSquareFiniteTripleIPPDischargeLedger :
    CosSquareFiniteTripleIPPDischargeLedger where
  ts220_derivative_bridge :=
    TS220.Goldbach.cosSquareIPPPrimitiveDerivativeBridgeLedger
  primitive_boundary_terms :=
    cosSquareIPPPrimitive_eq_boundaryTerms
  primitive_jump_boundary_sum :=
    cosSquareIPPPrimitive_jump_eq_boundarySum
  finite_triple_ipp :=
    cosSquareFiniteTripleIPP
  boundary_vanishing_not_proved :=
    True.intro
  third_derivative_cutoff_value_not_proved :=
    True.intro
  dirichlet_cutoff_not_proved :=
    True.intro
  canonical_sinc_fourth_value_not_proved :=
    True.intro
  plancherel_not_proved :=
    True.intro
  goldbach_not_claimed :=
    True.intro

/-- Target proposition for TS221. -/
def CosSquareFiniteTripleIPPDischargeTarget :
    Prop :=
  Nonempty CosSquareFiniteTripleIPPDischargeLedger

theorem cosSquareFiniteTripleIPPDischargeTarget :
    CosSquareFiniteTripleIPPDischargeTarget :=
  Nonempty.intro cosSquareFiniteTripleIPPDischargeLedger

end Goldbach
end TS221
