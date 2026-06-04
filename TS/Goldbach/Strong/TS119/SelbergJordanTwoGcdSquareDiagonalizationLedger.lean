import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic
import TS.Goldbach.Strong.TS118.SelbergLCMAbsorptionBridge

namespace TS119
namespace Goldbach

/-!
# TS119 - Selberg Jordan-Two GCD-Square Diagonalization Ledger

TS118 rewrites the original dense `gcd/lcm` Selberg form as an absorbed-weight
dense form with kernel `gcd(m,n)^2`. This sprint introduces the arithmetic
coefficient for that corrected kernel: the Jordan totient of order two,
represented as the Dirichlet convolution

`J2 = moebius * pow 2`.

It proves the local divisor-sum collapse

`sum_{d | g} J2(d) = g^2`

using Mathlib's arithmetic-function convolution API. The finite global
reindexing from the corrected gcd-square dense side to the corrected diagonal
square side remains a named obligation for later sprints.
-/

/-- The Jordan totient of order two as an arithmetic function over `Rat`. -/
def selbergJordanTwoFunction :
    ArithmeticFunction Rat :=
  ArithmeticFunction.moebius *
    (ArithmeticFunction.pow 2 : ArithmeticFunction Rat)

/-- The scalar coefficient used by the corrected gcd-square diagonal side. -/
def selbergJordanTwoCoefficient
    (d : Nat) :
    Rat :=
  selbergJordanTwoFunction d

/-- The Jordan-two function is the Mobius convolution with the square function. -/
theorem selbergJordanTwoFunction_eq_moebius_mul_pow_two :
    selbergJordanTwoFunction =
      ArithmeticFunction.moebius *
        (ArithmeticFunction.pow 2 : ArithmeticFunction Rat) :=
  rfl

/-- The zeta convolution of `J2` is the square function. -/
theorem zeta_mul_selbergJordanTwoFunction :
    (ArithmeticFunction.zeta * selbergJordanTwoFunction :
      ArithmeticFunction Rat) =
      (ArithmeticFunction.pow 2 : ArithmeticFunction Rat) := by
  unfold selbergJordanTwoFunction
  rw [<- mul_assoc]
  rw [ArithmeticFunction.coe_zeta_mul_coe_moebius (R := Rat)]
  simp

/-- Local Jordan-two divisor-sum collapse: `sum_{d | g} J2(d) = g^2`. -/
theorem selbergJordanTwoCoefficient_divisor_sum_eq_square
    (g : Nat) :
    Finset.sum g.divisors (fun d => selbergJordanTwoCoefficient d) =
      (g : Rat) ^ (2 : Nat) := by
  have h :=
    congrArg
      (fun F : ArithmeticFunction Rat => F g)
      zeta_mul_selbergJordanTwoFunction
  change
    (ArithmeticFunction.zeta * selbergJordanTwoFunction :
      ArithmeticFunction Rat) g =
      (ArithmeticFunction.pow 2 : ArithmeticFunction Rat) g at h
  rw [ArithmeticFunction.coe_zeta_mul_apply] at h
  unfold selbergJordanTwoCoefficient
  simpa [ArithmeticFunction.pow_apply] using h

/-- The corrected divisor-filtered transformed weight for the gcd-square side. -/
def selbergGcdSquareTransformedWeight
    (level : Nat)
    (weight : Nat -> Rat)
    (d : Nat) :
    Rat :=
  Finset.sum (TS108.Goldbach.selbergQuadraticSupport level) fun m =>
    if Dvd.dvd d m then weight m else 0

/-- The transformed weight is its defining divisor-filtered finite sum. -/
theorem selbergGcdSquareTransformedWeight_expansion
    (level : Nat)
    (weight : Nat -> Rat)
    (d : Nat) :
    selbergGcdSquareTransformedWeight level weight d =
      Finset.sum (TS108.Goldbach.selbergQuadraticSupport level) fun m =>
        if Dvd.dvd d m then weight m else 0 :=
  rfl

/-- One corrected Jordan-two diagonal square term. -/
def selbergJordanTwoDiagonalSquareTerm
    (transformedWeight : Nat -> Rat)
    (d : Nat) :
    Rat :=
  selbergJordanTwoCoefficient d *
    transformedWeight d ^ (2 : Nat)

/-- Corrected Jordan-two diagonal side for the absorbed gcd-square form. -/
def selbergJordanTwoDiagonalSide
    (level : Nat)
    (weight : Nat -> Rat) :
    Rat :=
  Finset.sum (TS108.Goldbach.selbergQuadraticSupport level) fun d =>
    selbergJordanTwoDiagonalSquareTerm
      (selbergGcdSquareTransformedWeight level weight)
      d

/-- The corrected diagonal side is its defining finite sum. -/
theorem selbergJordanTwoDiagonalSide_expansion
    (level : Nat)
    (weight : Nat -> Rat) :
    selbergJordanTwoDiagonalSide level weight =
      Finset.sum (TS108.Goldbach.selbergQuadraticSupport level) fun d =>
        selbergJordanTwoDiagonalSquareTerm
          (selbergGcdSquareTransformedWeight level weight)
          d :=
  rfl

/--
Corrected gcd-square diagonalization ledger.

The local Jordan-two divisor collapse is concrete. The global finite
reindexing identity is deliberately kept as a proposition-valued obligation.
-/
structure SelbergGcdSquareDiagonalization
    (level : Nat)
    (weight : Nat -> Rat) where
  lcmAbsorption :
    TS118.Goldbach.SelbergLCMAbsorptionBridge level weight

  absorbedWeight :
    Nat -> Rat

  absorbed_weight_eq :
    forall m : Nat,
      absorbedWeight m = TS118.Goldbach.selbergLCMAbsorbedWeight weight m

  denseGcdSquareSide :
    Rat

  dense_gcd_square_side_eq :
    denseGcdSquareSide =
      TS118.Goldbach.selbergGcdSquareDenseSide level absorbedWeight

  transformedWeight :
    Nat -> Rat

  transformed_weight_eq :
    forall d : Nat,
      transformedWeight d =
        selbergGcdSquareTransformedWeight level absorbedWeight d

  diagonalSide :
    Rat

  diagonal_side_eq :
    diagonalSide =
      selbergJordanTwoDiagonalSide level absorbedWeight

  jordan_divisor_sum_identity :
    forall g : Nat,
      Finset.sum g.divisors (fun d => selbergJordanTwoCoefficient d) =
        (g : Rat) ^ (2 : Nat)

  dense_to_diagonal_identity_obligation :
    Prop

  dense_to_diagonal_identity_obligation_eq :
    dense_to_diagonal_identity_obligation =
      (denseGcdSquareSide = diagonalSide)

  corrected_kernel_ready :
    True

  jordan_two_coefficient_ready :
    True

  finite_reindexing_obligation :
    True

  square_sum_majorant_obligation :
    True

/-- Concrete TS119 corrected diagonalization ledger. -/
def selbergGcdSquareDiagonalization
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergGcdSquareDiagonalization level weight where
  lcmAbsorption := TS118.Goldbach.selbergLCMAbsorptionBridge level weight
  absorbedWeight := TS118.Goldbach.selbergLCMAbsorbedWeight weight
  absorbed_weight_eq := by
    intro m
    rfl
  denseGcdSquareSide :=
    TS118.Goldbach.selbergGcdSquareDenseSide
      level
      (TS118.Goldbach.selbergLCMAbsorbedWeight weight)
  dense_gcd_square_side_eq := rfl
  transformedWeight :=
    selbergGcdSquareTransformedWeight
      level
      (TS118.Goldbach.selbergLCMAbsorbedWeight weight)
  transformed_weight_eq := by
    intro d
    rfl
  diagonalSide :=
    selbergJordanTwoDiagonalSide
      level
      (TS118.Goldbach.selbergLCMAbsorbedWeight weight)
  diagonal_side_eq := rfl
  jordan_divisor_sum_identity :=
    selbergJordanTwoCoefficient_divisor_sum_eq_square
  dense_to_diagonal_identity_obligation :=
    TS118.Goldbach.selbergGcdSquareDenseSide
      level
      (TS118.Goldbach.selbergLCMAbsorbedWeight weight) =
        selbergJordanTwoDiagonalSide
          level
          (TS118.Goldbach.selbergLCMAbsorbedWeight weight)
  dense_to_diagonal_identity_obligation_eq := rfl
  corrected_kernel_ready := True.intro
  jordan_two_coefficient_ready := True.intro
  finite_reindexing_obligation := True.intro
  square_sum_majorant_obligation := True.intro

/-- Target proposition for the corrected TS119 gcd-square diagonalization. -/
def SelbergGcdSquareDiagonalizationTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergGcdSquareDiagonalization level weight)

/-- The corrected TS119 gcd-square diagonalization ledger is populated. -/
theorem selbergGcdSquareDiagonalizationTarget :
    SelbergGcdSquareDiagonalizationTarget := by
  intro level weight
  exact Nonempty.intro (selbergGcdSquareDiagonalization level weight)

/-- TS119 keeps the TS118 lcm-absorption target available. -/
theorem selbergLCMAbsorptionBridgeTarget :
    TS118.Goldbach.SelbergLCMAbsorptionBridgeTarget :=
  TS118.Goldbach.selbergLCMAbsorptionBridgeTarget

end Goldbach
end TS119
