import Mathlib.Tactic
import Mathlib.Data.Complex.ExponentialBounds
import TS.Goldbach.Strong.TS156.BrunTitchmarshThresholdEvaluation

namespace TS157
namespace Goldbach

set_option maxRecDepth 10000

/-!
# TS157 - Goldbach Scale Eventual Obstruction

TS156 proves that the current dependent Selberg/Brun-Titchmarsh comparison is
impossible at the Goldbach scale once two explicit finite inequalities hold.
This sprint supplies a single natural threshold guaranteeing both of them.

The deliberately coarse exponent is `3000`. Mathlib's certified bound on
`exp 1` gives

`exp 16 < 9,000,001 = 3000^2 + 1`.

If `2^3000 <= x`, then `3000 <= Nat.log 2 x`. The exponential condition in
TS156 follows immediately. The remaining scale condition follows from the
elementary inequality

`2 * n^2 <= 2^n` for `8 <= n`

together with `2^(Nat.log 2 x) <= x`.

Thus the TS156 obstruction holds for every `x >= 2^3000`, and no dependent
Selberg level selection can satisfy the TS150 comparison throughout that
tail. This is an impossibility result for the current pipeline; it does not
alter the Selberg denominator, the TS22 budget, or the finite-head obligation.
-/

/-- Coarse explicit exponent sufficient for the eventual obstruction. -/
def goldbachObstructionExponent : Nat := 3000

/-- Explicit natural threshold for the TS156 Goldbach obstruction regime. -/
def goldbachObstructionThreshold : Nat :=
  2 ^ goldbachObstructionExponent

/-- Certified numerical comparison used to dominate the real exponential. -/
theorem exp_sixteen_lt_nine_million_one :
    Real.exp 16 < (9000001 : Real) := by
  have hexp : Real.exp 16 = Real.exp 1 ^ (16 : Nat) := by
    exact (Real.exp_one_pow 16).symm
  rw [hexp]
  have he : Real.exp 1 < (68 : Real) / 25 := by
    exact Real.exp_one_lt_d9.trans (by norm_num)
  have hpow :
      Real.exp 1 ^ (16 : Nat) < ((68 : Real) / 25) ^ (16 : Nat) := by
    gcongr
  exact hpow.trans (by norm_num)

/-- Powers of two dominate twice the square beyond exponent eight. -/
theorem two_mul_sq_le_two_pow
    (n : Nat)
    (hn : 8 <= n) :
    2 * n ^ 2 <= 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hquad : (n + 1) ^ 2 <= 2 * n ^ 2 := by
        nlinarith
      calc
        2 * (n + 1) ^ 2 <= 2 * (2 * n ^ 2) :=
          Nat.mul_le_mul_left 2 hquad
        _ <= 2 * (2 ^ n) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

/-- The explicit obstruction threshold is positive. -/
theorem goldbachObstructionThreshold_pos :
    0 < goldbachObstructionThreshold := by
  unfold goldbachObstructionThreshold
  positivity

/-- The explicit obstruction threshold is above the TS15 large-X cutoff. -/
theorem sixteen_le_goldbachObstructionThreshold :
    16 <= goldbachObstructionThreshold := by
  calc
    16 = 2 ^ (4 : Nat) := by norm_num
    _ <= 2 ^ goldbachObstructionExponent := by
      exact Nat.pow_le_pow_right (by norm_num)
        (by simp [goldbachObstructionExponent])
    _ = goldbachObstructionThreshold := rfl

/-- Crossing the explicit threshold forces a binary logarithm of at least 3000. -/
theorem obstructionExponent_le_log
    {x : Nat}
    (hx : goldbachObstructionThreshold <= x) :
    goldbachObstructionExponent <= Nat.log 2 x := by
  apply Nat.le_log_of_pow_le (by norm_num)
  exact hx

/-- The explicit threshold supplies the TS15 large-X hypothesis. -/
theorem largeX_of_goldbachObstructionThreshold_le
    {x : Nat}
    (hx : goldbachObstructionThreshold <= x) :
    TS15.Goldbach.LargeX x := by
  unfold TS15.Goldbach.LargeX
  exact sixteen_le_goldbachObstructionThreshold.trans hx

/--
Every natural number beyond the explicit threshold lies in the finite TS156
obstruction regime.
-/
theorem goldbachThresholdObstructionRegime_of_threshold_le
    {x : Nat}
    (hx : goldbachObstructionThreshold <= x) :
    TS156.Goldbach.GoldbachThresholdObstructionRegime x := by
  have hxpos : Not (x = 0) := by
    exact Nat.ne_of_gt (goldbachObstructionThreshold_pos.trans_le hx)
  have hlogExponent :
      goldbachObstructionExponent <= Nat.log 2 x :=
    obstructionExponent_le_log hx
  have hlog : 3000 <= Nat.log 2 x := by
    simpa [goldbachObstructionExponent] using hlogExponent
  constructor
  case left =>
    simpa [TS156.Goldbach.goldbachScaleQ, pow_two] using
      ((two_mul_sq_le_two_pow (Nat.log 2 x) (by omega)).trans
        (Nat.pow_log_le_self 2 hxpos))
  case right =>
    have hsquareNat : 9000001 <= (Nat.log 2 x) ^ 2 + 1 := by
      nlinarith
    have hsquare :
        (9000001 : Real) <= (((Nat.log 2 x) ^ 2 + 1 : Nat) : Real) := by
      exact_mod_cast hsquareNat
    apply (exp_sixteen_lt_nine_million_one.le).trans
    simpa [TS156.Goldbach.goldbachScaleQ, pow_two] using hsquare

/-- The TS155 geometric obstruction holds throughout the explicit tail. -/
theorem geometricObstruction_of_goldbachObstructionThreshold_le
    {x : Nat}
    (hx : goldbachObstructionThreshold <= x) :
    TS155.Goldbach.SelbergBTGeometricObstruction
      x
      (TS156.Goldbach.goldbachScaleQ x) := by
  exact TS156.Goldbach.geometricObstruction_at_goldbachScale
    x
    (largeX_of_goldbachObstructionThreshold_le hx)
    (goldbachThresholdObstructionRegime_of_threshold_le hx)

/--
No dependent Selberg level selection can satisfy the TS150 comparison for any
`x` beyond the explicit threshold.
-/
theorem no_dependentRefinedComparison_of_goldbachObstructionThreshold_le
    (level : TS151.Goldbach.SelbergLevelSelection)
    {x : Nat}
    (hx : goldbachObstructionThreshold <= x) :
    Not (TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level) := by
  exact TS156.Goldbach.no_dependentRefinedComparison_at_goldbachScale
    level
    x
    (largeX_of_goldbachObstructionThreshold_le hx)
    (goldbachThresholdObstructionRegime_of_threshold_le hx)

/-- TS157 package recording the explicit eventual obstruction. -/
structure GoldbachScaleEventualObstruction where
  threshold : Nat

  threshold_eq :
    threshold = goldbachObstructionThreshold

  obstruction_regime :
    forall x : Nat,
      threshold <= x ->
        TS156.Goldbach.GoldbachThresholdObstructionRegime x

  no_dependent_comparison :
    forall level : TS151.Goldbach.SelbergLevelSelection,
      forall x : Nat,
        threshold <= x ->
          Not
            (TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level)

  denominator_or_budget_refactor_obligation :
    True

  cumulative_head_prime_count_obligation :
    True

/-- Concrete TS157 eventual-obstruction package. -/
def goldbachScaleEventualObstruction :
    GoldbachScaleEventualObstruction where
  threshold := goldbachObstructionThreshold
  threshold_eq := rfl
  obstruction_regime := by
    intro x hx
    exact goldbachThresholdObstructionRegime_of_threshold_le hx
  no_dependent_comparison := by
    intro level x hx
    exact no_dependentRefinedComparison_of_goldbachObstructionThreshold_le
      level hx
  denominator_or_budget_refactor_obligation := True.intro
  cumulative_head_prime_count_obligation := True.intro

/-- Target proposition for the TS157 eventual-obstruction sprint. -/
def GoldbachScaleEventualObstructionTarget : Prop :=
  Nonempty GoldbachScaleEventualObstruction

/-- The TS157 target is populated without external assumptions. -/
theorem goldbachScaleEventualObstructionTarget :
    GoldbachScaleEventualObstructionTarget :=
  Nonempty.intro goldbachScaleEventualObstruction

end Goldbach
end TS157
