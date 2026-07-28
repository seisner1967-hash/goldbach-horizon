import Mathlib.Tactic
import TS.Goldbach.Strong.TS313.NormalizedTraceBudgetRationalPackagingBridge

namespace TS314
namespace Goldbach

noncomputable section

/-!
# Finite quadratic spectral moment and good-scale selection

This module keeps the truncated spectral trace complex, forms its finite
quadratic mean on the natural dyadic window `[X, 2X)`, selects a good natural
scale from a moment bound, and transfers the effective TS292 tail to the
pointwise TS313 interface.

No quadratic-moment estimate is proved here.  The named finite-moment
statement, together with the height-scale condition `4 * T <= X`, is the
analytic input reserved for TS315.
-/

/-! ## Dyadic natural window -/

/-- The half-open natural dyadic window `[X, 2X)`. -/
def dyadicWindow (X : Nat) : Finset Nat :=
  Finset.Ico X (2 * X)

@[simp]
theorem mem_dyadicWindow_iff
    {X x : Nat} :
    Membership.mem (dyadicWindow X) x <-> X <= x /\ x < 2 * X := by
  simp [dyadicWindow]

@[simp]
theorem dyadicWindow_card
    (X : Nat) :
    (dyadicWindow X).card = X := by
  simp only [dyadicWindow, Nat.card_Ico]
  omega

theorem dyadicWindow_nonempty
    (X : Nat)
    (hX : 0 < X) :
    (dyadicWindow X).Nonempty := by
  refine Exists.intro X ?_
  simp only [mem_dyadicWindow_iff]
  omega

theorem one_le_of_mem_dyadicWindow
    {X x : Nat}
    (hX : 0 < X)
    (hx : Membership.mem (dyadicWindow X) x) :
    1 <= x := by
  have hLower := (mem_dyadicWindow_iff.mp hx).1
  omega

/-! ## Complex truncated trace and its quadratic mean -/

/-- The normalized truncated spectral value, with its complex phase intact. -/
noncomputable def normalizedTruncatedSpectralValue
    (x T : Nat) : Complex :=
  (TS313.Goldbach.canonicalTraceNormalizationFactor x : Complex) *
    TS292.Goldbach.truncatedInfiniteZeroContribution x T

/-- The real size used in the finite quadratic moment. -/
noncomputable def normalizedTruncatedSpectralSize
    (x T : Nat) : Real :=
  norm (normalizedTruncatedSpectralValue x T)

theorem normalizedTruncatedSpectralSize_nonnegative
    (x T : Nat) :
    0 <= normalizedTruncatedSpectralSize x T :=
  norm_nonneg _

/-- The normalized infinite spectral value, used only for the tail bridge. -/
noncomputable def normalizedInfiniteSpectralValue
    (x : Nat) : Complex :=
  (TS313.Goldbach.canonicalTraceNormalizationFactor x : Complex) *
    TS292.Goldbach.infiniteZeroContribution x

theorem normalizedInfiniteSpectralValue_norm_eq
    (x : Nat) :
    norm (normalizedInfiniteSpectralValue x) =
      TS313.Goldbach.normalizedSpectralTrace x
        (TS313.Goldbach.canonicalTraceNormalizationFactor x) := by
  unfold normalizedInfiniteSpectralValue
    TS313.Goldbach.normalizedSpectralTrace
  rw [norm_mul]
  simp [abs_of_nonneg
    (TS313.Goldbach.canonicalTraceNormalizationFactor_nonnegative x)]

/-- Average squared normalized truncated size on `[X, 2X)`. -/
noncomputable def finiteQuadraticSpectralMoment
    (X T : Nat) : Real :=
  (Finset.sum (dyadicWindow X)
      (fun x => normalizedTruncatedSpectralSize x T ^ 2)) /
    ((dyadicWindow X).card : Real)

theorem finiteQuadraticSpectralMoment_nonnegative
    (X T : Nat) :
    0 <= finiteQuadraticSpectralMoment X T := by
  unfold finiteQuadraticSpectralMoment
  positivity

theorem finiteQuadraticSpectralMoment_eq_sum_div_scale
    (X T : Nat) :
    finiteQuadraticSpectralMoment X T =
      (Finset.sum (dyadicWindow X)
        (fun x => normalizedTruncatedSpectralSize x T ^ 2)) /
        (X : Real) := by
  simp [finiteQuadraticSpectralMoment]

/-! ## Pure finite good-scale selection -/

/-- A finite quadratic average below `q^2` contains a value at most `q`. -/
theorem exists_le_of_quadratic_average_le
    {alpha : Type*}
    [DecidableEq alpha]
    (s : Finset alpha)
    (hs : s.Nonempty)
    (f : alpha -> Real)
    {q : Real}
    (hq : 0 <= q)
    (hAverage :
      (Finset.sum s (fun i => f i ^ 2)) / (s.card : Real) <= q ^ 2) :
    exists i, Membership.mem s i /\ f i <= q := by
  by_contra hExists
  push_neg at hExists
  have hSquares : forall i, Membership.mem s i -> q ^ 2 < f i ^ 2 := by
    intro i hi
    have hStrict := hExists i hi
    nlinarith
  have hSumStrict :
      Finset.sum s (fun _i => q ^ 2) <
        Finset.sum s (fun i => f i ^ 2) :=
    Finset.sum_lt_sum_of_nonempty hs hSquares
  have hCardPositive : 0 < (s.card : Real) := by
    exact_mod_cast hs.card_pos
  have hAverageStrict :
      q ^ 2 <
        (Finset.sum s (fun i => f i ^ 2)) / (s.card : Real) := by
    calc
      q ^ 2 = (q ^ 2 * (s.card : Real)) / (s.card : Real) := by
        field_simp
      _ < (Finset.sum s (fun i => f i ^ 2)) / (s.card : Real) :=
        (div_lt_div_iff_of_pos_right hCardPositive).2
          (by simpa [mul_comm] using hSumStrict)
  exact (not_lt_of_ge hAverage) hAverageStrict

/-- A small dyadic quadratic moment selects a good natural scale. -/
theorem exists_good_scale_of_moment_le
    (X T : Nat)
    (hX : 0 < X)
    {q : Real}
    (hq : 0 <= q)
    (hMoment : finiteQuadraticSpectralMoment X T <= q ^ 2) :
    exists x, Membership.mem (dyadicWindow X) x /\
      normalizedTruncatedSpectralSize x T <= q := by
  exact exists_le_of_quadratic_average_le
    (dyadicWindow X)
    (dyadicWindow_nonempty X hX)
    (fun x => normalizedTruncatedSpectralSize x T)
    hq hMoment

/-! ## Effective normalized TS292 tail -/

/-- The TS292 zero tail after canonical normalization by `2 / x`. -/
noncomputable def normalizedSpectralTailEnvelope
    (T : Nat) : Real :=
  2 * TS292.Goldbach.infiniteZeroResidualTailConstant *
    TS292.Goldbach.logarithmicTailRate T

theorem normalizedSpectralTailEnvelope_nonnegative
    (T : Nat) :
    0 <= normalizedSpectralTailEnvelope T := by
  have hArgument : (1 : Real) <= (T : Real) + 2 := by
    have hTNonnegative : 0 <= (T : Real) := by positivity
    linarith
  have hLog : 0 <= Real.log ((T : Real) + 2) :=
    Real.log_nonneg hArgument
  have hRate : 0 <= TS292.Goldbach.logarithmicTailRate T := by
    unfold TS292.Goldbach.logarithmicTailRate
    exact div_nonneg (add_nonneg hLog zero_le_one) (by positivity)
  unfold normalizedSpectralTailEnvelope
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      TS292.Goldbach.infiniteZeroResidualTailConstant_nonnegative)
    hRate

theorem normalizedSpectralValue_sub_truncated_norm_le
    (x T : Nat)
    (hx : 1 <= x)
    (hT : 1 <= T) :
    norm
        (normalizedInfiniteSpectralValue x -
          normalizedTruncatedSpectralValue x T) <=
      normalizedSpectralTailEnvelope T := by
  have hTail :=
    TS292.Goldbach.infiniteZeroContribution_sub_truncated_norm_le
      x T hT
  have hMax : max 1 (x : Real) = (x : Real) := by
    apply max_eq_right
    exact_mod_cast hx
  rw [hMax] at hTail
  have hFactorNonnegative :
      0 <= TS313.Goldbach.canonicalTraceNormalizationFactor x :=
    TS313.Goldbach.canonicalTraceNormalizationFactor_nonnegative x
  have hxReal : Not ((x : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hx))
  calc
    norm
        (normalizedInfiniteSpectralValue x -
          normalizedTruncatedSpectralValue x T) =
        TS313.Goldbach.canonicalTraceNormalizationFactor x *
          norm
            (TS292.Goldbach.infiniteZeroContribution x -
              TS292.Goldbach.truncatedInfiniteZeroContribution x T) := by
      unfold normalizedInfiniteSpectralValue
        normalizedTruncatedSpectralValue
      rw [<- mul_sub, norm_mul]
      simp [abs_of_nonneg hFactorNonnegative]
    _ <= TS313.Goldbach.canonicalTraceNormalizationFactor x *
        ((x : Real) *
          (TS292.Goldbach.infiniteZeroResidualTailConstant *
            TS292.Goldbach.logarithmicTailRate T)) :=
      mul_le_mul_of_nonneg_left hTail hFactorNonnegative
    _ = normalizedSpectralTailEnvelope T := by
      unfold TS313.Goldbach.canonicalTraceNormalizationFactor
        normalizedSpectralTailEnvelope
      field_simp
      ring

/-- Reverse-triangle transfer between infinite and truncated normalized sizes. -/
theorem normalizedSpectralSize_sub_truncated_abs_le
    (x T : Nat)
    (hx : 1 <= x)
    (hT : 1 <= T) :
    abs
        (TS313.Goldbach.normalizedSpectralTrace x
            (TS313.Goldbach.canonicalTraceNormalizationFactor x) -
          normalizedTruncatedSpectralSize x T) <=
      normalizedSpectralTailEnvelope T := by
  rw [<- normalizedInfiniteSpectralValue_norm_eq]
  unfold normalizedTruncatedSpectralSize
  exact (abs_norm_sub_norm_le _ _).trans
    (normalizedSpectralValue_sub_truncated_norm_le x T hx hT)

theorem normalizedSpectralTrace_le_truncated_add_tail
    (x T : Nat)
    (hx : 1 <= x)
    (hT : 1 <= T) :
    TS313.Goldbach.normalizedSpectralTrace x
        (TS313.Goldbach.canonicalTraceNormalizationFactor x) <=
      normalizedTruncatedSpectralSize x T +
        normalizedSpectralTailEnvelope T := by
  have hAbs := normalizedSpectralSize_sub_truncated_abs_le x T hx hT
  have hOneSided :
      TS313.Goldbach.normalizedSpectralTrace x
          (TS313.Goldbach.canonicalTraceNormalizationFactor x) -
        normalizedTruncatedSpectralSize x T <=
      normalizedSpectralTailEnvelope T :=
    (le_abs_self _).trans hAbs
  linarith

/-! ## Real and rational outputs for TS313 -/

theorem exists_good_scale_real_spectral_bound
    (X T : Nat)
    (hX : 0 < X)
    (hT : 1 <= T)
    {qMoment qTail : Real}
    (hqMoment : 0 <= qMoment)
    (hMoment : finiteQuadraticSpectralMoment X T <= qMoment ^ 2)
    (hTail : normalizedSpectralTailEnvelope T <= qTail) :
    exists x, Membership.mem (dyadicWindow X) x /\
      TS313.Goldbach.normalizedSpectralTrace x
          (TS313.Goldbach.canonicalTraceNormalizationFactor x) <=
        qMoment + qTail := by
  let hGood := exists_good_scale_of_moment_le X T hX hqMoment hMoment
  let x := Classical.choose hGood
  have hxSpec := Classical.choose_spec hGood
  have hxWindow := hxSpec.1
  have hxMoment := hxSpec.2
  refine Exists.intro x (And.intro hxWindow ?_)
  have hxOne := one_le_of_mem_dyadicWindow hX hxWindow
  exact (normalizedSpectralTrace_le_truncated_add_tail x T hxOne hT).trans
    (add_le_add hxMoment hTail)

/--
Rationalized good-scale output.  TS316 will provide the rational tail and
residual majorants; TS314 only performs the certified conversion to TS313.
-/
theorem exists_good_scale_normalizedSpectralTraceBound
    (X T : Nat)
    (hX : 0 < X)
    (hT : 1 <= T)
    (qMoment tailMajorant : Rat)
    (hqMoment : 0 <= qMoment)
    (hMoment :
      finiteQuadraticSpectralMoment X T <= (qMoment : Real) ^ 2)
    (hTail :
      normalizedSpectralTailEnvelope T <= (tailMajorant : Real)) :
    exists x, Membership.mem (dyadicWindow X) x /\
      TS313.Goldbach.NormalizedSpectralTraceBoundStatement
        x
        (TS313.Goldbach.canonicalTraceNormalizationFactor x)
        (qMoment + tailMajorant) := by
  have hqMomentReal : 0 <= (qMoment : Real) := by
    exact_mod_cast hqMoment
  let hGood := exists_good_scale_real_spectral_bound
    X T hX hT hqMomentReal hMoment hTail
  let x := Classical.choose hGood
  have hxSpec := Classical.choose_spec hGood
  have hxWindow := hxSpec.1
  have hxBound := hxSpec.2
  refine Exists.intro x (And.intro hxWindow ?_)
  unfold TS313.Goldbach.NormalizedSpectralTraceBoundStatement
  simpa [x] using hxBound

/-! ## TS315-facing contract -/

/-- The exact finite quadratic moment estimate that TS315 must establish. -/
def FiniteQuadraticSpectralMomentBoundStatement
    (X T : Nat)
    (q : Real) : Prop :=
  finiteQuadraticSpectralMoment X T <= q ^ 2

/--
The structural package expected from TS315.  The compatibility `4 * T <= X`
prevents the discrete phase from entering an aliased frequency regime.
-/
structure FiniteQuadraticSpectralMomentEstimateData where
  scale : Nat
  scale_pos : 0 < scale
  height : Nat
  height_pos : 0 < height
  height_scale_compatible : 4 * height <= scale
  momentMajorant : Real
  momentMajorant_nonnegative : 0 <= momentMajorant
  moment_bound :
    FiniteQuadraticSpectralMomentBoundStatement
      scale height momentMajorant

/-- Audit ledger for the exact TS314 proof boundary. -/
structure TS314Ledger where
  half_open_dyadic_window_proved : True
  dyadic_window_cardinality_proved : True
  complex_truncated_trace_preserved : True
  finite_quadratic_moment_defined : True
  good_scale_selection_proved : True
  normalized_tail_transfer_proved : True
  rational_ts313_output_proved : True
  finite_moment_estimate_not_proved : True
  discrete_correlation_identity_deferred_to_ts315 : True
  weighted_close_pair_bound_deferred_to_ts315 : True
  normalized_budget_not_constructed : True
  rh_not_assumed : True
  otsa_not_proved : True
  goldbach_not_claimed : True

def ts314Ledger : TS314Ledger where
  half_open_dyadic_window_proved := True.intro
  dyadic_window_cardinality_proved := True.intro
  complex_truncated_trace_preserved := True.intro
  finite_quadratic_moment_defined := True.intro
  good_scale_selection_proved := True.intro
  normalized_tail_transfer_proved := True.intro
  rational_ts313_output_proved := True.intro
  finite_moment_estimate_not_proved := True.intro
  discrete_correlation_identity_deferred_to_ts315 := True.intro
  weighted_close_pair_bound_deferred_to_ts315 := True.intro
  normalized_budget_not_constructed := True.intro
  rh_not_assumed := True.intro
  otsa_not_proved := True.intro
  goldbach_not_claimed := True.intro

end

end Goldbach
end TS314
