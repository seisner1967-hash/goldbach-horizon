import Mathlib.Tactic
import TS.Goldbach.Strong.TS221.CosSquareFiniteTripleIPPDischarge

namespace TS222
namespace Goldbach

open Filter

/-!
# TS222 - Cos-Square Boundary Vanishing Reduction Bridge

TS221 closed the finite compact triple-IPP identity.  The remaining boundary
task is an improper cutoff limit:

`boundarySum(eps, T) -> 0` as `(eps, T) -> (0+, +infty)`.

This sprint isolates the exact one-variable asymptotic obligations needed for
that statement.  Since TS221 proved

`P(T) - P(eps) = boundarySum eps T`,

it is enough to prove

* `P(T) -> 0` as `T -> +infty`;
* `P(eps) -> 0` as `eps -> 0+`.

TS222 proves this product-filter bridge.  It does not yet prove the two
one-variable asymptotic estimates themselves, the third-derivative cutoff
value, Dirichlet cutoff or Abel convergence, the canonical `sinc^4` value,
Plancherel evidence, or Goldbach.
-/

/-- The primitive boundary term tends to zero at `+infty`. -/
def CosSquareIPPPrimitiveAtTopVanishingStatement :
    Prop :=
  Tendsto
    TS220.Goldbach.cosSquareIPPPrimitive
    atTop
    (nhds (0 : Real))

/-- The primitive boundary term tends to zero as `x -> 0+`. -/
def CosSquareIPPPrimitiveZeroRightVanishingStatement :
    Prop :=
  Tendsto
    TS220.Goldbach.cosSquareIPPPrimitive
    (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
    (nhds (0 : Real))

/-- Evidence for the two one-variable boundary limits of the TS220 primitive. -/
structure CosSquareIPPPrimitiveBoundaryLimitEvidence where
  atTop_vanishing :
    CosSquareIPPPrimitiveAtTopVanishingStatement

  zero_right_vanishing :
    CosSquareIPPPrimitiveZeroRightVanishingStatement

/--
The two primitive limits imply the TS219 product-filter boundary vanishing
statement.
-/
theorem cosSquareBoundaryVanishing_of_primitiveLimits
    (evidence : CosSquareIPPPrimitiveBoundaryLimitEvidence) :
    TS219.Goldbach.CosSquareBoundaryVanishingStatement := by
  unfold TS219.Goldbach.CosSquareBoundaryVanishingStatement
  unfold TS219.Goldbach.cosSquareCutoffFilter
  have hT :
      Tendsto
        (fun p : Prod Real Real =>
          TS220.Goldbach.cosSquareIPPPrimitive p.2)
        (Filter.prod
          (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
          atTop)
        (nhds (0 : Real)) := by
    exact evidence.atTop_vanishing.comp tendsto_snd
  have heps :
      Tendsto
        (fun p : Prod Real Real =>
          TS220.Goldbach.cosSquareIPPPrimitive p.1)
        (Filter.prod
          (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
          atTop)
        (nhds (0 : Real)) := by
    exact evidence.zero_right_vanishing.comp tendsto_fst
  have hdiff :
      Tendsto
        (fun p : Prod Real Real =>
          TS220.Goldbach.cosSquareIPPPrimitive p.2 -
            TS220.Goldbach.cosSquareIPPPrimitive p.1)
        (Filter.prod
          (nhdsWithin (0 : Real) (Set.Ioi (0 : Real)))
          atTop)
        (nhds (0 : Real)) := by
    simpa using hT.sub heps
  exact
    hdiff.congr'
      (Eventually.of_forall
        (fun p : Prod Real Real =>
          TS221.Goldbach.cosSquareIPPPrimitive_jump_eq_boundarySum
            p.1
            p.2))

/-- Ledger recording the TS222 boundary-vanishing reduction. -/
structure CosSquareBoundaryVanishingReductionBridgeLedger where
  ts221_finite_ipp :
    TS221.Goldbach.CosSquareFiniteTripleIPPDischargeLedger

  primitive_atTop_vanishing_statement :
    Prop

  primitive_atTop_vanishing_statement_eq :
    primitive_atTop_vanishing_statement =
      CosSquareIPPPrimitiveAtTopVanishingStatement

  primitive_zero_right_vanishing_statement :
    Prop

  primitive_zero_right_vanishing_statement_eq :
    primitive_zero_right_vanishing_statement =
      CosSquareIPPPrimitiveZeroRightVanishingStatement

  boundary_vanishing_statement :
    Prop

  boundary_vanishing_statement_eq :
    boundary_vanishing_statement =
      TS219.Goldbach.CosSquareBoundaryVanishingStatement

  boundary_vanishing_of_primitive_limits :
    CosSquareIPPPrimitiveBoundaryLimitEvidence ->
      TS219.Goldbach.CosSquareBoundaryVanishingStatement

  atTop_asymptotic_not_proved :
    True

  zero_right_asymptotic_not_proved :
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

/-- Concrete TS222 boundary-vanishing reduction ledger. -/
noncomputable def cosSquareBoundaryVanishingReductionBridgeLedger :
    CosSquareBoundaryVanishingReductionBridgeLedger where
  ts221_finite_ipp :=
    TS221.Goldbach.cosSquareFiniteTripleIPPDischargeLedger
  primitive_atTop_vanishing_statement :=
    CosSquareIPPPrimitiveAtTopVanishingStatement
  primitive_atTop_vanishing_statement_eq := rfl
  primitive_zero_right_vanishing_statement :=
    CosSquareIPPPrimitiveZeroRightVanishingStatement
  primitive_zero_right_vanishing_statement_eq := rfl
  boundary_vanishing_statement :=
    TS219.Goldbach.CosSquareBoundaryVanishingStatement
  boundary_vanishing_statement_eq := rfl
  boundary_vanishing_of_primitive_limits :=
    cosSquareBoundaryVanishing_of_primitiveLimits
  atTop_asymptotic_not_proved := True.intro
  zero_right_asymptotic_not_proved := True.intro
  third_derivative_cutoff_value_not_proved := True.intro
  dirichlet_cutoff_not_proved := True.intro
  canonical_sinc_fourth_value_not_proved := True.intro
  plancherel_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS222. -/
def CosSquareBoundaryVanishingReductionBridgeTarget :
    Prop :=
  Nonempty CosSquareBoundaryVanishingReductionBridgeLedger

theorem cosSquareBoundaryVanishingReductionBridgeTarget :
    CosSquareBoundaryVanishingReductionBridgeTarget :=
  Nonempty.intro cosSquareBoundaryVanishingReductionBridgeLedger

end Goldbach
end TS222
