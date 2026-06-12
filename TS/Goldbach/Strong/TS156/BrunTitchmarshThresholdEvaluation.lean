import Mathlib.Tactic
import TS.Goldbach.Strong.TS155.BrunTitchmarshThresholdObstructionGeometry

namespace TS156
namespace Goldbach

/-!
# TS156 - Brun-Titchmarsh Threshold Evaluation

TS155 rewrites the Selberg denominator obstruction as the natural inequality

`2 * brunTitchmarshCeilBudget x Q <= intervalScale x Q + 1`.

This sprint evaluates that inequality against the exact TS22 definition

`ceil (4 * intervalScale x Q / log (Q + 1))`.

The proof keeps the real logarithm and the natural ceiling visible. A simple
finite regime is enough: interval scale at least `2` and logarithmic
denominator at least `16`. Under those hypotheses the TS22 ceiling is less
than one quarter of the interval scale plus one, which forces the TS155
obstruction.

The final declarations specialize this criterion to the actual Goldbach scale
`Q = (Nat.log 2 x)^2`. No claim is made here that the finite regime holds for
all sufficiently large `x`; proving an explicit eventual threshold remains a
separate task.
-/

/-- The modulus scale required by the TS15/TS22 Goldbach route. -/
def goldbachScaleQ (x : Nat) : Nat :=
  Nat.log 2 x * Nat.log 2 x

/--
Finite sufficient conditions for the TS155 obstruction at the Goldbach scale.
-/
def GoldbachThresholdObstructionRegime (x : Nat) : Prop :=
  2 * goldbachScaleQ x <= x /\
    Real.exp 16 <= ((goldbachScaleQ x : Nat) : Real) + 1

/--
The exact TS22 ceiling is positive when the interval scale is at least two and
the real logarithmic denominator is at least sixteen.
-/
theorem brunTitchmarshCeilBudget_pos_of_log_sixteen
    (x Q : Nat)
    (hscale : 2 <= TS15.Goldbach.intervalScale x Q)
    (hlog : (16 : Real) <= Real.log ((Q : Real) + 1)) :
    0 < TS22.Goldbach.brunTitchmarshCeilBudget x Q := by
  have hlog_pos : (0 : Real) < Real.log ((Q : Real) + 1) := by
    linarith
  unfold TS22.Goldbach.brunTitchmarshCeilBudget
  apply Nat.ceil_pos.mpr
  positivity

/--
Under the finite logarithmic regime, twice the exact TS22 ceiling fits inside
the closed interval length.
-/
theorem twice_brunTitchmarshCeilBudget_le_interval_of_log_sixteen
    (x Q : Nat)
    (hscale : 2 <= TS15.Goldbach.intervalScale x Q)
    (hlog : (16 : Real) <= Real.log ((Q : Real) + 1)) :
    2 * TS22.Goldbach.brunTitchmarshCeilBudget x Q <=
      TS15.Goldbach.intervalScale x Q + 1 := by
  let h := TS15.Goldbach.intervalScale x Q
  let L := Real.log ((Q : Real) + 1)
  have hh : 2 <= h := hscale
  have hL : (16 : Real) <= L := hlog
  have hLpos : (0 : Real) < L := by linarith
  have hzpos : (0 : Real) < (4 : Real) * h / L := by
    positivity
  have hznonneg : (0 : Real) <= (4 : Real) * h / L := hzpos.le
  have hzle : (4 : Real) * h / L <= (h : Real) / 4 := by
    calc
      (4 : Real) * h / L <= (4 : Real) * h / 16 := by
        exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hL
      _ = (h : Real) / 4 := by ring
  have hceil :
      ((Nat.ceil ((4 : Real) * h / L) : Nat) : Real) <
        (h : Real) / 4 + 1 := by
    exact lt_of_lt_of_le
      (Nat.ceil_lt_add_one hznonneg)
      (by linarith)
  have htwo :
      ((2 * Nat.ceil ((4 : Real) * h / L) : Nat) : Real) <
        ((h + 1 : Nat) : Real) := by
    push_cast
    have hhreal : (2 : Real) <= h := by exact_mod_cast hh
    nlinarith
  unfold TS22.Goldbach.brunTitchmarshCeilBudget
  change 2 * Nat.ceil ((4 : Real) * h / L) <= h + 1
  exact Nat.le_of_lt (by exact_mod_cast htwo)

/-- The finite logarithmic regime triggers the exact TS155 obstruction. -/
theorem geometricObstruction_of_log_sixteen
    (x Q : Nat)
    (hscale : 2 <= TS15.Goldbach.intervalScale x Q)
    (hlog : (16 : Real) <= Real.log ((Q : Real) + 1)) :
    TS155.Goldbach.SelbergBTGeometricObstruction x Q := by
  exact And.intro
    (brunTitchmarshCeilBudget_pos_of_log_sixteen x Q hscale hlog)
    (twice_brunTitchmarshCeilBudget_le_interval_of_log_sixteen
      x Q hscale hlog)

/--
An exponential lower bound on `Q+1` is an equivalent Lean-friendly way to
supply the logarithmic hypothesis.
-/
theorem geometricObstruction_of_exp_sixteen_le
    (x Q : Nat)
    (hscale : 2 <= TS15.Goldbach.intervalScale x Q)
    (hexp : Real.exp 16 <= (Q : Real) + 1) :
    TS155.Goldbach.SelbergBTGeometricObstruction x Q := by
  have hqpos : (0 : Real) < (Q : Real) + 1 := by positivity
  have hlog : (16 : Real) <= Real.log ((Q : Real) + 1) :=
    (Real.le_log_iff_exp_le hqpos).2 hexp
  exact geometricObstruction_of_log_sixteen x Q hscale hlog

/-- Large-X data make the actual Goldbach modulus scale positive. -/
theorem goldbachScaleQ_pos
    (x : Nat)
    (hx : TS15.Goldbach.LargeX x) :
    0 < goldbachScaleQ x := by
  have hlog : 0 < Nat.log 2 x :=
    Nat.log_pos (by omega) (by
      unfold TS15.Goldbach.LargeX at hx
      omega)
  unfold goldbachScaleQ
  positivity

/--
The finite Goldbach obstruction regime implies interval scale at least two.
-/
theorem two_le_intervalScale_goldbachScaleQ
    (x : Nat)
    (hx : TS15.Goldbach.LargeX x)
    (hregime : GoldbachThresholdObstructionRegime x) :
    2 <= TS15.Goldbach.intervalScale x (goldbachScaleQ x) := by
  unfold TS15.Goldbach.intervalScale
  exact (Nat.le_div_iff_mul_le (goldbachScaleQ_pos x hx)).2 hregime.1

/--
The actual Goldbach scale is obstructed whenever its explicit finite regime
holds.
-/
theorem geometricObstruction_at_goldbachScale
    (x : Nat)
    (hx : TS15.Goldbach.LargeX x)
    (hregime : GoldbachThresholdObstructionRegime x) :
    TS155.Goldbach.SelbergBTGeometricObstruction x (goldbachScaleQ x) := by
  exact geometricObstruction_of_exp_sixteen_le
    x
    (goldbachScaleQ x)
    (two_le_intervalScale_goldbachScaleQ x hx hregime)
    hregime.2

/--
At every `x` in the finite obstruction regime, no dependent Selberg level
selection can satisfy the TS150 budget comparison.
-/
theorem no_dependentRefinedComparison_at_goldbachScale
    (level : TS151.Goldbach.SelbergLevelSelection)
    (x : Nat)
    (hx : TS15.Goldbach.LargeX x)
    (hregime : GoldbachThresholdObstructionRegime x) :
    Not (TS151.Goldbach.DependentRefinedSelbergBudgetScaleComparison level) := by
  exact TS155.Goldbach.no_dependentRefinedComparison_of_geometricObstruction
    level
    x
    (goldbachScaleQ x)
    hx
    rfl
    (geometricObstruction_at_goldbachScale x hx hregime)

/-- TS156 package exposing the evaluated finite obstruction regime. -/
structure BrunTitchmarshThresholdEvaluation where
  generic_obstruction :
    forall x Q : Nat,
      2 <= TS15.Goldbach.intervalScale x Q ->
        (16 : Real) <= Real.log ((Q : Real) + 1) ->
          TS155.Goldbach.SelbergBTGeometricObstruction x Q

  goldbach_scale_obstruction :
    forall x : Nat,
      TS15.Goldbach.LargeX x ->
        GoldbachThresholdObstructionRegime x ->
          TS155.Goldbach.SelbergBTGeometricObstruction x (goldbachScaleQ x)

  eventual_regime_obligation :
    True

  denominator_or_budget_refactor_obligation :
    True

/-- Concrete TS156 threshold-evaluation package. -/
def brunTitchmarshThresholdEvaluation :
    BrunTitchmarshThresholdEvaluation where
  generic_obstruction := geometricObstruction_of_log_sixteen
  goldbach_scale_obstruction := geometricObstruction_at_goldbachScale
  eventual_regime_obligation := True.intro
  denominator_or_budget_refactor_obligation := True.intro

/-- Target proposition for the TS156 threshold-evaluation sprint. -/
def BrunTitchmarshThresholdEvaluationTarget : Prop :=
  Nonempty BrunTitchmarshThresholdEvaluation

/-- The TS156 target is populated without external assumptions. -/
theorem brunTitchmarshThresholdEvaluationTarget :
    BrunTitchmarshThresholdEvaluationTarget :=
  Nonempty.intro brunTitchmarshThresholdEvaluation

end Goldbach
end TS156
