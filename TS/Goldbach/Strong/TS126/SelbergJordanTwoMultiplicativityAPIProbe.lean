import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import TS.Goldbach.Strong.TS125.SelbergJordanTwoPrimePowerPositivityProbe

namespace TS126
namespace Goldbach

/-!
# TS126 - Selberg Jordan-Two Multiplicativity API Probe

TS125 proves positivity of the corrected Selberg Jordan-two coefficient on
positive prime powers. This sprint opens the next arithmetic layer: the
Mathlib multiplicativity API for the same coefficient.

The concrete pieces proved here are:

* the arithmetic function `J2 = moebius * pow 2` is multiplicative over `Rat`;
* Mathlib's factorization theorem rewrites `J2(n)` as the product of the
  prime-power values `J2(p^k)` for `n != 0`;
* the TS125 prime-power positivity theorem is available in the normalized
  `0 < k` form needed by the factorization route.

The final product-positivity proof for all positive integers remains a named
local obligation for TS127.
-/

/-- The corrected Jordan-two arithmetic function is multiplicative over `Rat`. -/
theorem selbergJordanTwoFunction_isMultiplicative :
    TS119.Goldbach.selbergJordanTwoFunction.IsMultiplicative := by
  unfold TS119.Goldbach.selbergJordanTwoFunction
  exact
    ArithmeticFunction.isMultiplicative_moebius.intCast.mul
      (ArithmeticFunction.isMultiplicative_pow (k := 2)).natCast

/-- The scalar coefficient inherits multiplicativity from the arithmetic function. -/
theorem selbergJordanTwoCoefficient_mul_of_coprime
    {m n : Nat}
    (hmn : Nat.Coprime m n) :
    TS119.Goldbach.selbergJordanTwoCoefficient (m * n) =
      TS119.Goldbach.selbergJordanTwoCoefficient m *
        TS119.Goldbach.selbergJordanTwoCoefficient n := by
  unfold TS119.Goldbach.selbergJordanTwoCoefficient
  exact selbergJordanTwoFunction_isMultiplicative.map_mul_of_coprime hmn

/--
Mathlib factorization formula for the corrected Jordan-two coefficient.

This is the exact API bridge needed before multiplying the TS125 prime-power
positivity facts over the prime factorization of a positive integer.
-/
theorem selbergJordanTwoCoefficient_factorization
    {n : Nat}
    (hn : Not (n = 0)) :
    TS119.Goldbach.selbergJordanTwoCoefficient n =
      n.factorization.prod fun p k =>
        TS119.Goldbach.selbergJordanTwoCoefficient (p ^ k) := by
  unfold TS119.Goldbach.selbergJordanTwoCoefficient
  exact
    selbergJordanTwoFunction_isMultiplicative.multiplicative_factorization
      TS119.Goldbach.selbergJordanTwoFunction
      hn

/--
TS125 prime-power positivity in the exponent-positive shape naturally produced
by `Nat.factorization`.
-/
theorem selbergJordanTwoCoefficient_pos_of_prime_pow
    {p k : Nat}
    (hp : p.Prime)
    (hk : 0 < k) :
    0 < TS119.Goldbach.selbergJordanTwoCoefficient (p ^ k) := by
  cases k with
  | zero =>
      exact False.elim (Nat.lt_irrefl 0 hk)
  | succ k =>
      exact TS125.Goldbach.selbergJordanTwoCoefficient_pos_of_prime_pow_succ hp k

/--
Prime-power positivity input in the factorization form.

The exponent is arbitrary but required to be positive, matching the nonzero
entries of `n.factorization`.
-/
def SelbergJordanTwoPositiveOnPrimePowersFactorizationShape : Prop :=
  forall p k : Nat,
    p.Prime ->
      0 < k ->
        0 < TS119.Goldbach.selbergJordanTwoCoefficient (p ^ k)

/-- The TS125 prime-power positivity theorem supplies the factorization shape. -/
theorem selbergJordanTwoPositiveOnPrimePowersFactorizationShape :
    SelbergJordanTwoPositiveOnPrimePowersFactorizationShape := by
  intro p k hp hk
  exact selbergJordanTwoCoefficient_pos_of_prime_pow hp hk

/--
The exact remaining product-positivity route.

TS127 should prove this by combining `selbergJordanTwoCoefficient_factorization`
with `selbergJordanTwoCoefficient_pos_of_prime_pow` and the positivity of finite
products over `n.factorization`.
-/
def SelbergJordanTwoMultiplicativePositiveProductRoute : Prop :=
  TS124.Goldbach.SelbergJordanTwoPositiveOnPositiveNat

/-- Multiplicativity API probe package for the corrected Jordan-two coefficient. -/
structure SelbergJordanTwoMultiplicativityAPIProbe
    (level : Nat)
    (weight : Nat -> Rat) where
  primePowerPositivityProbe :
    TS125.Goldbach.SelbergJordanTwoPrimePowerPositivityProbe level weight

  jordan_two_multiplicative :
    TS119.Goldbach.selbergJordanTwoFunction.IsMultiplicative

  jordan_two_mul_of_coprime :
    forall m n : Nat,
      Nat.Coprime m n ->
        TS119.Goldbach.selbergJordanTwoCoefficient (m * n) =
          TS119.Goldbach.selbergJordanTwoCoefficient m *
            TS119.Goldbach.selbergJordanTwoCoefficient n

  jordan_two_factorization :
    forall n : Nat,
      Not (n = 0) ->
        TS119.Goldbach.selbergJordanTwoCoefficient n =
          n.factorization.prod fun p k =>
            TS119.Goldbach.selbergJordanTwoCoefficient (p ^ k)

  prime_power_positive_factorization_shape :
    SelbergJordanTwoPositiveOnPrimePowersFactorizationShape

  global_positive_nat_obligation :
    Prop

  global_positive_nat_obligation_eq :
    global_positive_nat_obligation =
      TS124.Goldbach.SelbergJordanTwoPositiveOnPositiveNat

  product_positivity_route_obligation :
    Prop

  product_positivity_route_obligation_eq :
    product_positivity_route_obligation =
      SelbergJordanTwoMultiplicativePositiveProductRoute

  optimal_vector_normalization_obligation :
    True

  selberg_sieve_bound_obligation :
    True

  brun_titchmarsh_obligation :
    True

/-- Concrete TS126 multiplicativity API probe package. -/
def selbergJordanTwoMultiplicativityAPIProbe
    (level : Nat)
    (weight : Nat -> Rat) :
    SelbergJordanTwoMultiplicativityAPIProbe level weight where
  primePowerPositivityProbe :=
    TS125.Goldbach.selbergJordanTwoPrimePowerPositivityProbe level weight
  jordan_two_multiplicative :=
    selbergJordanTwoFunction_isMultiplicative
  jordan_two_mul_of_coprime := by
    intro m n hmn
    exact selbergJordanTwoCoefficient_mul_of_coprime hmn
  jordan_two_factorization := by
    intro n hn
    exact selbergJordanTwoCoefficient_factorization hn
  prime_power_positive_factorization_shape :=
    selbergJordanTwoPositiveOnPrimePowersFactorizationShape
  global_positive_nat_obligation :=
    TS124.Goldbach.SelbergJordanTwoPositiveOnPositiveNat
  global_positive_nat_obligation_eq := rfl
  product_positivity_route_obligation :=
    SelbergJordanTwoMultiplicativePositiveProductRoute
  product_positivity_route_obligation_eq := rfl
  optimal_vector_normalization_obligation := True.intro
  selberg_sieve_bound_obligation := True.intro
  brun_titchmarsh_obligation := True.intro

/-- Target proposition for TS126 multiplicativity API probe. -/
def SelbergJordanTwoMultiplicativityAPIProbeTarget : Prop :=
  forall level : Nat,
    forall weight : Nat -> Rat,
      Nonempty (SelbergJordanTwoMultiplicativityAPIProbe level weight)

/-- The TS126 multiplicativity API probe package is populated. -/
theorem selbergJordanTwoMultiplicativityAPIProbeTarget :
    SelbergJordanTwoMultiplicativityAPIProbeTarget := by
  intro level weight
  exact Nonempty.intro
    (selbergJordanTwoMultiplicativityAPIProbe level weight)

/-- TS126 keeps the TS125 prime-power positivity probe target available. -/
theorem selbergJordanTwoPrimePowerPositivityProbeTarget :
    TS125.Goldbach.SelbergJordanTwoPrimePowerPositivityProbeTarget :=
  TS125.Goldbach.selbergJordanTwoPrimePowerPositivityProbeTarget

end Goldbach
end TS126
