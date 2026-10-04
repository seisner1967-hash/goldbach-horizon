import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-! SOURCE ONLY. The point is constructed from the rational log32 box,
nearest rounding with ties to even, then an integer clamp. Neither a log
enclosure nor a precision premise is supplied to the final theorem.
Native common-denominator, word/carry and catalogue realization remain separate. -/

noncomputable section
open scoped BigOperators

namespace GoldbachLogQuantization22

def gridScale : ℕ := 2 ^ 58

def logTerm (z : ℝ) (j : ℕ) : ℝ :=
  2 * (1 / ((2 * j + 1 : ℕ) : ℝ)) * z ^ (2 * j + 1)

def logPartial (z : ℝ) : ℝ := ∑ j ∈ Finset.range 32, logTerm z j

def logRemainder : ℝ := 9 / (4 * 65 * 3 ^ 65)

def logTermQ (z : ℚ) (j : ℕ) : ℚ :=
  2 * (1 / ((2 * j + 1 : ℕ) : ℚ)) * z ^ (2 * j + 1)

def logPartialQ (z : ℚ) : ℚ := ∑ j ∈ Finset.range 32, logTermQ z j

def reductionExponent (p : ℕ) : ℕ := Nat.log2 p

def reducedArg (p : ℕ) : ℚ :=
  ((p : ℚ) - 2 ^ reductionExponent p) / ((p : ℚ) + 2 ^ reductionExponent p)

def logLowerQ (p : ℕ) : ℚ :=
  (reductionExponent p : ℚ) * logPartialQ (1 / 3) + logPartialQ (reducedArg p)

def logWidthQ (p : ℕ) : ℚ :=
  ((reductionExponent p : ℚ) + 1) * 9 / (4 * 65 * 3 ^ 65)

def logMidpointQ (p : ℕ) : ℚ := logLowerQ p + logWidthQ p / 2

/-- Rational nearest rounding; the exact half case selects the even integer. -/
def nearestEven (x : ℚ) : ℤ :=
  let q : ℤ := Int.floor x
  let r : ℚ := x - q
  if r < 1 / 2 then q else
    if 1 / 2 < r then q + 1 else if Even q then q else q + 1

def clampInteger (cap z : ℤ) : ℤ := max 0 (min cap z)

def logPoint (p : ℕ) : ℤ :=
  clampInteger (32 * (gridScale : ℤ))
    (nearestEven ((gridScale : ℚ) * logMidpointQ p))

def quantizedLog (p : ℕ) : ℝ := (logPoint p : ℝ) / (gridScale : ℝ)

theorem gridScale_pos : 0 < gridScale := by norm_num [gridScale]

theorem logTerm_nonneg {z : ℝ} (hz : 0 ≤ z) (j : ℕ) : 0 ≤ logTerm z j := by
  unfold logTerm
  positivity

theorem logSeries {z : ℝ} (hz : |z| < 1) :
    HasSum (logTerm z) (Real.log (1 + z) - Real.log (1 - z)) := by
  simpa [logTerm, Nat.cast_add, Nat.cast_mul] using
    Real.hasSum_log_sub_log_of_abs_lt_one hz

theorem logTailSeries {z : ℝ} (hz : |z| < 1) :
    HasSum (fun j : ℕ => logTerm z (j + 32))
      (Real.log (1 + z) - Real.log (1 - z) - logPartial z) := by
  simpa only [logPartial] using (hasSum_nat_add_iff' 32).2 (logSeries hz)

theorem logTailTerm_bound {z : ℝ} (hz : 0 ≤ z) (hthird : z ≤ 1 / 3) (j : ℕ) :
    logTerm z (j + 32) ≤
      (2 / 65 * (1 / 3 : ℝ) ^ 65) * (1 / 9 : ℝ) ^ j := by
  have hd : (65 : ℝ) ≤ ((2 * (j + 32) + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 65 ≤ 2 * (j + 32) + 1 by omega)
  have he : 2 * (j + 32) + 1 = 65 + 2 * j := by omega
  calc
    logTerm z (j + 32) =
        (2 / ((2 * (j + 32) + 1 : ℕ) : ℝ)) * z ^ (2 * (j + 32) + 1) := by
      unfold logTerm
      ring
    _ ≤ (2 / 65) * (1 / 3 : ℝ) ^ (2 * (j + 32) + 1) := by
      gcongr
    _ = (2 / 65 * (1 / 3 : ℝ) ^ 65) * (1 / 9 : ℝ) ^ j := by
      rw [he, pow_add, pow_mul]
      norm_num <;> ring

theorem logRemainder_nonneg : 0 ≤ logRemainder := by
  norm_num [logRemainder]

/-- Both endpoints are obtained from the genuine logarithm series. -/
theorem logPartial_encloses {z : ℝ} (hz : 0 ≤ z) (hthird : z ≤ 1 / 3) :
    logPartial z ≤ Real.log (1 + z) - Real.log (1 - z) ∧
      Real.log (1 + z) - Real.log (1 - z) ≤ logPartial z + logRemainder := by
  have habs : |z| < 1 := by rw [abs_of_nonneg hz]; linarith
  have ht := logTailSeries habs
  have hn : 0 ≤ Real.log (1 + z) - Real.log (1 - z) - logPartial z :=
    hasSum_le (fun j => logTerm_nonneg hz (j + 32)) hasSum_zero ht
  have hg : HasSum
      (fun j : ℕ => (2 / 65 * (1 / 3 : ℝ) ^ 65) * (1 / 9 : ℝ) ^ j)
      logRemainder := by
    convert (hasSum_geometric_of_lt_one
      (by norm_num : 0 ≤ (1 / 9 : ℝ)) (by norm_num : (1 / 9 : ℝ) < 1)).mul_left
        (2 / 65 * (1 / 3 : ℝ) ^ 65) using 1 <;> norm_num [logRemainder]
  have hu := hasSum_le (logTailTerm_bound hz hthird) ht hg
  constructor <;> linarith

theorem logPartialQ_cast (z : ℚ) : (logPartialQ z : ℝ) = logPartial (z : ℝ) := by
  unfold logPartialQ logPartial logTermQ logTerm
  push_cast <;> rfl

theorem reductionExponent_bounds {p : ℕ} (hp : 2 ≤ p) (hN : p ≤ 100000000) :
    reductionExponent p ≤ 26 ∧
      2 ^ reductionExponent p ≤ p ∧ p < 2 ^ (reductionExponent p + 1) := by
  have hp0 : p ≠ 0 := by omega
  have h27 : p < 2 ^ 27 := hN.trans_lt (by norm_num)
  unfold reductionExponent
  rw [Nat.log2_eq_log_two]
  exact ⟨by have := Nat.log_lt_of_lt_pow hp0 h27; omega,
    Nat.pow_log_le_self 2 hp0, Nat.lt_pow_succ_log_self (by norm_num) p⟩

theorem reducedArg_bounds {p : ℕ} (hp : 2 ≤ p) (hN : p ≤ 100000000) :
    0 ≤ reducedArg p ∧ reducedArg p ≤ 1 / 3 := by
  obtain ⟨hk, hl, hu⟩ := reductionExponent_bounds hp hN
  have hlq : (2 : ℚ) ^ reductionExponent p ≤ (p : ℚ) := by exact_mod_cast hl
  have huq : (p : ℚ) < 2 * (2 : ℚ) ^ reductionExponent p := by
    have hc : (p : ℚ) < (2 : ℚ) ^ (reductionExponent p + 1) := by exact_mod_cast hu
    simpa only [pow_succ, mul_comm] using hc
  have hd : 0 < (p : ℚ) + (2 : ℚ) ^ reductionExponent p := by positivity
  unfold reducedArg
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlq) hd.le
  · rw [div_le_iff₀ hd]
    linarith

theorem log_reduction_identity {p : ℕ} (hp : 2 ≤ p) (hN : p ≤ 100000000) :
    Real.log (p : ℝ) = (reductionExponent p : ℝ) * Real.log 2 +
      (Real.log (1 + (reducedArg p : ℝ)) - Real.log (1 - (reducedArg p : ℝ))) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hd : 0 < (2 : ℝ) ^ reductionExponent p := by positivity
  have hden : 0 < (p : ℝ) + (2 : ℝ) ^ reductionExponent p := by positivity
  obtain ⟨hzq, hthirdq⟩ := reducedArg_bounds hp hN
  have hz : 0 ≤ (reducedArg p : ℝ) := by exact_mod_cast hzq
  have hthird : (reducedArg p : ℝ) ≤ 1 / 3 := by exact_mod_cast hthirdq
  have hplus : 0 < 1 + (reducedArg p : ℝ) := by linarith
  have hminus : 0 < 1 - (reducedArg p : ℝ) := by linarith
  have hzform : (reducedArg p : ℝ) =
      ((p : ℝ) - (2 : ℝ) ^ reductionExponent p) /
        ((p : ℝ) + (2 : ℝ) ^ reductionExponent p) := by
    unfold reducedArg
    push_cast <;> rfl
  have hr : (1 + (reducedArg p : ℝ)) / (1 - (reducedArg p : ℝ)) =
      (p : ℝ) / (2 : ℝ) ^ reductionExponent p := by
    have hm : 1 - (((p : ℝ) - (2 : ℝ) ^ reductionExponent p) /
        ((p : ℝ) + (2 : ℝ) ^ reductionExponent p)) ≠ 0 := by
      rw [← hzform]
      exact hminus.ne'
    rw [hzform]
    field_simp [hden.ne', hd.ne', hm] <;> ring
  rw [← Real.log_div hplus.ne' hminus.ne', hr,
    Real.log_div hpR.ne' hd.ne', Real.log_pow]
  ring

theorem logTwo_encloses :
    logPartial (1 / 3) ≤ Real.log 2 ∧
      Real.log 2 ≤ logPartial (1 / 3) + logRemainder := by
  have h := logPartial_encloses (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
  have he : Real.log (1 + (1 / 3 : ℝ)) - Real.log (1 - (1 / 3 : ℝ)) =
      Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  simpa only [he] using h

theorem logWidthQ_nonneg (p : ℕ) : 0 ≤ logWidthQ p := by
  unfold logWidthQ
  positivity

theorem log32_enclosure {p : ℕ} (hp : 2 ≤ p) (hN : p ≤ 100000000) :
    (logLowerQ p : ℝ) ≤ Real.log (p : ℝ) ∧
      Real.log (p : ℝ) ≤ (logLowerQ p : ℝ) + (logWidthQ p : ℝ) := by
  obtain ⟨hzq, hthirdq⟩ := reducedArg_bounds hp hN
  have hz : 0 ≤ (reducedArg p : ℝ) := by exact_mod_cast hzq
  have hthird : (reducedArg p : ℝ) ≤ 1 / 3 := by exact_mod_cast hthirdq
  obtain ⟨hzlo, hzhi⟩ := logPartial_encloses hz hthird
  obtain ⟨h2lo, h2hi⟩ := logTwo_encloses
  have hk : 0 ≤ (reductionExponent p : ℝ) := Nat.cast_nonneg _
  have hl := mul_le_mul_of_nonneg_left h2lo hk
  have hu := mul_le_mul_of_nonneg_left h2hi hk
  simp only [log_reduction_identity hp hN]
  unfold logLowerQ logWidthQ
  push_cast
  simp only [logPartialQ_cast]
  norm_num [logRemainder] at hu hzhi ⊢
  constructor <;> nlinarith

theorem log32_width_small {p : ℕ} (hp : 2 ≤ p) (hN : p ≤ 100000000) :
    (logWidthQ p : ℝ) ≤ 1 / (gridScale : ℝ) := by
  have hk := (reductionExponent_bounds hp hN).1
  have hkR : (reductionExponent p : ℝ) ≤ 26 := by exact_mod_cast hk
  unfold logWidthQ
  push_cast
  have hk1 : (reductionExponent p : ℝ) + 1 ≤ 27 := by linarith
  calc
    _ = ((reductionExponent p : ℝ) + 1) * logRemainder := by
      unfold logRemainder
      ring
    _ ≤ 27 * logRemainder :=
      mul_le_mul_of_nonneg_right hk1 logRemainder_nonneg
    _ ≤ 1 / (gridScale : ℝ) := by norm_num [gridScale, logRemainder]

theorem log32_midpoint_error {p : ℕ} (hp : 2 ≤ p) (hN : p ≤ 100000000) :
    |Real.log (p : ℝ) - (logMidpointQ p : ℝ)| ≤ (logWidthQ p : ℝ) / 2 := by
  obtain ⟨hl, hu⟩ := log32_enclosure hp hN
  have hw : 0 ≤ (logWidthQ p : ℝ) := by exact_mod_cast logWidthQ_nonneg p
  unfold logMidpointQ
  push_cast
  rw [abs_le]
  constructor <;> linarith

theorem nearestEven_error (x : ℚ) : |x - (nearestEven x : ℚ)| ≤ 1 / 2 := by
  have hl := Int.floor_le x
  have hu := Int.lt_floor_add_one x
  unfold nearestEven
  dsimp only
  split_ifs <;> rw [abs_le] <;> push_cast <;> constructor <;> linarith

theorem nearestEven_error_real (x : ℚ) :
    |(x : ℝ) - (nearestEven x : ℝ)| ≤ 1 / 2 := by
  exact_mod_cast nearestEven_error x

theorem clampInteger_bounds {cap : ℤ} (hcap : 0 ≤ cap) (z : ℤ) :
    0 ≤ clampInteger cap z ∧ clampInteger cap z ≤ cap := by
  unfold clampInteger
  exact ⟨le_max_left _ _, max_le hcap (min_le_left _ _)⟩

theorem clampInteger_distance {cap : ℤ} (hcap : 0 ≤ cap) {x : ℝ}
    (hx0 : 0 ≤ x) (hxcap : x ≤ (cap : ℝ)) (z : ℤ) :
    |x - (clampInteger cap z : ℝ)| ≤ |x - (z : ℝ)| := by
  have hcapR : 0 ≤ (cap : ℝ) := by exact_mod_cast hcap
  by_cases hz0 : z < 0
  · have hzcap : z ≤ cap := le_trans hz0.le hcap
    have hzR : (z : ℝ) < 0 := by exact_mod_cast hz0
    simp only [clampInteger, min_eq_right hzcap, max_eq_left hz0.le, Int.cast_zero,
      sub_zero, abs_of_nonneg hx0, abs_of_nonneg (by linarith : 0 ≤ x - (z : ℝ))]
    linarith
  · by_cases hzcap : cap < z
    · have hzR : (cap : ℝ) < (z : ℝ) := by exact_mod_cast hzcap
      simp only [clampInteger, min_eq_left hzcap.le, max_eq_right hcap,
        abs_of_nonpos (by linarith : x - (cap : ℝ) ≤ 0),
        abs_of_nonpos (by linarith : x - (z : ℝ) ≤ 0)]
      linarith
    · have h0z : 0 ≤ z := le_of_not_gt hz0
      have hzc : z ≤ cap := le_of_not_gt hzcap
      simp only [clampInteger, min_eq_right hzc, max_eq_right h0z, le_refl]

theorem true_log_bounds {p : ℕ} (hp : 2 ≤ p) (hN : p ≤ 100000000) :
    0 ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 32 := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hpow : (p : ℝ) ≤ (2 : ℝ) ^ 32 := by
    exact_mod_cast (hN.trans (by norm_num : 100000000 ≤ 2 ^ 32))
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  refine ⟨Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega)), ?_⟩
  calc
    Real.log (p : ℝ) ≤ Real.log ((2 : ℝ) ^ 32) := Real.log_le_log hpR hpow
    _ = 32 * Real.log 2 := by rw [Real.log_pow]; norm_num
    _ ≤ 32 := by linarith

theorem logPoint_bounds (p : ℕ) :
    0 ≤ logPoint p ∧ logPoint p ≤ 32 * (gridScale : ℤ) := by
  exact clampInteger_bounds (by positivity) _

/-- Precision is proved from the fixed log32 constructor, with no precision hypothesis. -/
theorem quantizedLog_precision {p : ℕ} (hp : 2 ≤ p) (hN : p ≤ 100000000) :
    |Real.log (p : ℝ) - quantizedLog p| ≤ 1 / (gridScale : ℝ) := by
  have hs : (0 : ℝ) < (gridScale : ℝ) := by exact_mod_cast gridScale_pos
  have hm := log32_midpoint_error hp hN
  have hw := log32_width_small hp hN
  have hsw : (logWidthQ p : ℝ) * (gridScale : ℝ) ≤ 1 :=
    (le_div_iff₀ hs).mp hw
  have hmScaled := mul_le_mul_of_nonneg_left hm hs.le
  have hr := nearestEven_error_real ((gridScale : ℚ) * logMidpointQ p)
  push_cast at hr
  have hscaled : |(gridScale : ℝ) * Real.log (p : ℝ) -
      (nearestEven ((gridScale : ℚ) * logMidpointQ p) : ℝ)| ≤ 1 := by
    calc
      _ = |(gridScale : ℝ) * (Real.log (p : ℝ) - (logMidpointQ p : ℝ)) +
          ((gridScale : ℝ) * (logMidpointQ p : ℝ) -
            (nearestEven ((gridScale : ℚ) * logMidpointQ p) : ℝ))| := by congr 1; ring
      _ ≤ |(gridScale : ℝ) * (Real.log (p : ℝ) - (logMidpointQ p : ℝ))| +
          |(gridScale : ℝ) * (logMidpointQ p : ℝ) -
            (nearestEven ((gridScale : ℚ) * logMidpointQ p) : ℝ)| := abs_add _ _
      _ ≤ 1 := by rw [abs_mul, abs_of_pos hs]; nlinarith
  obtain ⟨hl0, hl32⟩ := true_log_bounds hp hN
  have hc := clampInteger_distance (cap := 32 * (gridScale : ℤ))
    (by positivity) (mul_nonneg hs.le hl0)
    (by push_cast; nlinarith [mul_le_mul_of_nonneg_left hl32 hs.le] :
      (gridScale : ℝ) * Real.log (p : ℝ) ≤
      ((32 * (gridScale : ℤ) : ℤ) : ℝ))
    (nearestEven ((gridScale : ℚ) * logMidpointQ p))
  have ha : |(gridScale : ℝ) * Real.log (p : ℝ) - (logPoint p : ℝ)| ≤ 1 :=
    hc.trans hscaled
  unfold quantizedLog
  have he : Real.log (p : ℝ) - (logPoint p : ℝ) / (gridScale : ℝ) =
      ((gridScale : ℝ) * Real.log (p : ℝ) - (logPoint p : ℝ)) / (gridScale : ℝ) := by
    field_simp [hs.ne'] <;> ring
  rw [he, abs_div, abs_of_pos hs]
  exact div_le_div_of_nonneg_right ha hs.le

end GoldbachLogQuantization22

#print axioms GoldbachLogQuantization22.gridScale
#print axioms GoldbachLogQuantization22.logTerm
#print axioms GoldbachLogQuantization22.logPartial
#print axioms GoldbachLogQuantization22.logRemainder
#print axioms GoldbachLogQuantization22.logTermQ
#print axioms GoldbachLogQuantization22.logPartialQ
#print axioms GoldbachLogQuantization22.reductionExponent
#print axioms GoldbachLogQuantization22.reducedArg
#print axioms GoldbachLogQuantization22.logLowerQ
#print axioms GoldbachLogQuantization22.logWidthQ
#print axioms GoldbachLogQuantization22.logMidpointQ
#print axioms GoldbachLogQuantization22.nearestEven
#print axioms GoldbachLogQuantization22.clampInteger
#print axioms GoldbachLogQuantization22.logPoint
#print axioms GoldbachLogQuantization22.quantizedLog
#print axioms GoldbachLogQuantization22.gridScale_pos
#print axioms GoldbachLogQuantization22.logTerm_nonneg
#print axioms GoldbachLogQuantization22.logSeries
#print axioms GoldbachLogQuantization22.logTailSeries
#print axioms GoldbachLogQuantization22.logTailTerm_bound
#print axioms GoldbachLogQuantization22.logRemainder_nonneg
#print axioms GoldbachLogQuantization22.logPartial_encloses
#print axioms GoldbachLogQuantization22.logPartialQ_cast
#print axioms GoldbachLogQuantization22.reductionExponent_bounds
#print axioms GoldbachLogQuantization22.reducedArg_bounds
#print axioms GoldbachLogQuantization22.log_reduction_identity
#print axioms GoldbachLogQuantization22.logTwo_encloses
#print axioms GoldbachLogQuantization22.logWidthQ_nonneg
#print axioms GoldbachLogQuantization22.log32_enclosure
#print axioms GoldbachLogQuantization22.log32_width_small
#print axioms GoldbachLogQuantization22.log32_midpoint_error
#print axioms GoldbachLogQuantization22.nearestEven_error
#print axioms GoldbachLogQuantization22.nearestEven_error_real
#print axioms GoldbachLogQuantization22.clampInteger_bounds
#print axioms GoldbachLogQuantization22.clampInteger_distance
#print axioms GoldbachLogQuantization22.true_log_bounds
#print axioms GoldbachLogQuantization22.logPoint_bounds
#print axioms GoldbachLogQuantization22.quantizedLog_precision
