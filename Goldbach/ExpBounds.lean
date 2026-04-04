/-
  Goldbach/ExpBounds.lean
  Exponential bound lemmas for log(p) enclosures.

  API consumed by PrimeLogEnclosures.lean and ThresholdReal.lean:
  - `expPartialSum_le_exp`: S_n(x) ≤ exp(x)  [wraps Mathlib]
  - `exp_le_partial_sum_plus_tail`: exp(x) ≤ S_n(x) + tail  [proved via tsum]
  - `log_enclosure_of_exp_bounds`: master enclosure combinator
  - `lt_exp_of_lt_partial_sum`: convenience for hi-side
  - `exp_lt_of_partial_sum_tail_lt`: convenience for lo-side

  Sorry count: 0
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Goldbach

open Finset Real BigOperators Nat

/-! ### Definitions -/

/-- The n-th partial sum of the exp(x) Taylor series:
    S_n(x) = Σ_{i<n} x^i / i! -/
noncomputable def expPartialSum (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i in range n, x ^ i / ↑(Nat.factorial i)

/-- Geometric tail bound for the exp Taylor remainder:
    T_n(x) = x^n / (n! · (1 − x/(n+1)))
    Bounds Σ_{i≥n} x^i/i! from above when 0 ≤ x < n+1. -/
noncomputable def expTailBound (x : ℝ) (n : ℕ) : ℝ :=
  x ^ n / (↑(Nat.factorial n) * (1 - x / (↑n + 1)))

/-! ### Hi-side: partial Taylor sum ≤ exp (Mathlib wrapper) -/

theorem expPartialSum_le_exp {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    expPartialSum x n ≤ Real.exp x :=
  Real.sum_le_exp_of_nonneg hx n

/-! ### Helper: ascending factorial dominates power -/

/-- n! · (n+1)^j ≤ (n+j)! — each ascending factor ≥ n+1. -/
private theorem factorial_mul_pow_le (n j : ℕ) :
    Nat.factorial n * (n + 1) ^ j ≤ Nat.factorial (n + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : Nat.factorial n * (n + 1) ^ j * (n + 1) ≤
        Nat.factorial (n + j) * (n + 1) :=
      Nat.mul_le_mul_right _ ih
    have h2 : Nat.factorial (n + j) * (n + 1) ≤
        Nat.factorial (n + j) * (n + j + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    calc Nat.factorial n * (n + 1) ^ (j + 1)
        = Nat.factorial n * (n + 1) ^ j * (n + 1) := by ring
      _ ≤ Nat.factorial (n + j) * (n + j + 1) := le_trans h1 h2
      _ = Nat.factorial (n + j + 1) := by
          rw [Nat.mul_comm, ← Nat.factorial_succ]

/-- Each tail term of the exp series is bounded by a geometric series term:
    x^(n+j) / (n+j)! ≤ (x^n / n!) · (x/(n+1))^j -/
private theorem taylor_term_bound {x : ℝ} (hx : 0 ≤ x) (n j : ℕ) :
    x ^ (n + j) / ↑(Nat.factorial (n + j)) ≤
      (x ^ n / ↑(Nat.factorial n)) * (x / (↑n + 1)) ^ j := by
  -- Rewrite RHS to x^(n+j) / (n! · (n+1)^j)
  have hrhs : (x ^ n / ↑(Nat.factorial n)) * (x / (↑n + 1)) ^ j =
      x ^ (n + j) / (↑(Nat.factorial n) * (↑n + 1) ^ j) := by
    field_simp [pow_add]
  rw [hrhs]
  -- Suffices: n! · (n+1)^j ≤ (n+j)!  (as ℝ)
  have hc_pos : (0 : ℝ) < ↑(Nat.factorial n) * (↑n + 1) ^ j := by positivity
  have hc_le : ↑(Nat.factorial n) * (↑n + 1) ^ j ≤ (↑(Nat.factorial (n + j)) : ℝ) := by
    norm_cast
    exact factorial_mul_pow_le n j
  exact div_le_div_of_nonneg_left (pow_nonneg hx _) hc_pos hc_le

/-! ### Key upper bound: exp ≤ partial sum + tail -/

/-- **exp(x) ≤ S_n(x) + T_n(x)** for 0 ≤ x < n+1.

    Proof: write exp as tsum, split at n, bound each tail term by a
    geometric series term, sum the geometric series.

    Mathlib ingredients:
    - `Real.exp_eq_tsum_div`: exp(x) = Σ' x^i/i!
    - `sum_add_tsum_nat_add`: split tsum = finite sum + shifted tsum
    - `tsum_le_tsum`: pointwise bound implies tsum bound
    - `tsum_geometric_of_lt_one`: geometric series evaluation -/
theorem exp_le_partial_sum_plus_tail
    {x : ℝ} {n : ℕ} (hx : 0 ≤ x) (hxn : x < ↑n + 1) :
    Real.exp x ≤ expPartialSum x n + expTailBound x n := by
  -- Ratio r = x/(n+1) ∈ [0, 1)
  have hn1_pos : (0 : ℝ) < ↑n + 1 := by positivity
  have hr : x / (↑n + 1) < 1 := (div_lt_one hn1_pos).mpr hxn
  have hr0 : 0 ≤ x / (↑n + 1) := div_nonneg hx hn1_pos.le
  have hd : 0 < 1 - x / (↑n + 1) := by linarith
  -- Define the sequence f(i) = x^i / i!
  set f : ℕ → ℝ := fun i => x ^ i / ↑(Nat.factorial i) with hf_def
  -- f is summable (exp series converges for all x)
  have hf_sum : Summable f := Real.summable_pow_div_factorial x
  -- exp(x) = Σ' f(i)
  have hexp : Real.exp x = ∑' i, f i := by
    show Real.exp x = ∑' i, x ^ i / ↑(Nat.factorial i)
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  -- Split: Σ' f = (Σ_{i<n} f i) + Σ'_{j} f(j+n)
  have hsplit : (∑ i in range n, f i) + ∑' j, f (j + n) = ∑' i, f i :=
    sum_add_tsum_nat_add n hf_sum
  -- Decompose exp(x) = S_n(x) + tail
  have hdecomp : Real.exp x = expPartialSum x n + ∑' j, f (j + n) := by
    have : ∑ i in range n, f i = expPartialSum x n := by
      simp only [hf_def, expPartialSum]
    conv_lhs => rw [hexp, ← hsplit]
    rw [this]
  -- Each tail term bounded by geometric term
  have hterm : ∀ j, f (j + n) ≤
      (x ^ n / ↑(Nat.factorial n)) * (x / (↑n + 1)) ^ j := by
    intro j
    show x ^ (j + n) / ↑(Nat.factorial (j + n)) ≤ _
    rw [add_comm j n]
    exact taylor_term_bound hx n j
  -- Shifted sequence is summable
  have hshift : Summable (fun j => f (j + n)) :=
    (summable_nat_add_iff n).mpr hf_sum
  -- Geometric bound is summable
  have hgeom_sum : Summable (fun j =>
      (x ^ n / ↑(Nat.factorial n)) * (x / (↑n + 1)) ^ j) :=
    (summable_geometric_of_lt_one hr0 hr).mul_left _
  -- Tail tsum ≤ geometric tsum
  have htail : ∑' j, f (j + n) ≤
      ∑' j, (x ^ n / ↑(Nat.factorial n)) * (x / (↑n + 1)) ^ j :=
    tsum_le_tsum hterm hshift hgeom_sum
  -- Evaluate geometric tsum = (x^n/n!) / (1 - x/(n+1))
  have hgeom_eq : ∑' j, (x ^ n / ↑(Nat.factorial n)) * (x / (↑n + 1)) ^ j =
      x ^ n / ↑(Nat.factorial n) * (1 - x / (↑n + 1))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr]
  -- (x^n/n!) · (1-r)⁻¹ = expTailBound
  have htail_eq : x ^ n / ↑(Nat.factorial n) * (1 - x / (↑n + 1))⁻¹ =
      expTailBound x n := by
    unfold expTailBound
    have h1 : (↑(Nat.factorial n) : ℝ) ≠ 0 := by positivity
    have h2 : (1 : ℝ) - x / (↑n + 1) ≠ 0 := ne_of_gt hd
    field_simp
  -- Combine: exp(x) = S_n + tail ≤ S_n + geometric_sum = S_n + T_n
  have hbound : ∑' j, f (j + n) ≤ expTailBound x n := by
    calc ∑' j, f (j + n)
        ≤ ∑' j, (x ^ n / ↑(Nat.factorial n)) * (x / (↑n + 1)) ^ j := htail
      _ = x ^ n / ↑(Nat.factorial n) * (1 - x / (↑n + 1))⁻¹ := hgeom_eq
      _ = expTailBound x n := htail_eq
  linarith [hdecomp, hbound]

/-! ### Master enclosure combinator -/

/-- If exp(lo) < p and p < exp(hi), then lo < log(p) < hi.
    Uses the same Mathlib API as ThresholdReal.lean. -/
theorem log_enclosure_of_exp_bounds
    {lo hi : ℝ} {p : ℕ} (hp : 0 < p)
    (hlo : Real.exp lo < (p : ℝ))
    (hhi : (p : ℝ) < Real.exp hi) :
    lo < Real.log (p : ℝ) ∧ Real.log (p : ℝ) < hi := by
  have hp_real : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp
  constructor
  · rwa [Real.lt_log_iff_exp_lt hp_real]
  · rwa [Real.log_lt_iff_lt_exp hp_real]

/-! ### Convenience lemmas for individual prime proofs -/

/-- Prove p < exp(hi) by showing p < S_n(hi) ≤ exp(hi).
    Computation argument first so n is inferred before bounds. -/
theorem lt_exp_of_lt_partial_sum
    {hi : ℝ} {p : ℝ} {n : ℕ}
    (h : p < expPartialSum hi n) (hhi : 0 ≤ hi) :
    p < Real.exp hi :=
  lt_of_lt_of_le h (expPartialSum_le_exp hhi n)

/-- Prove exp(lo) < p by showing exp(lo) ≤ S_n(lo) + T_n(lo) < p.
    Computation argument first so n is inferred before bounds. -/
theorem exp_lt_of_partial_sum_tail_lt
    {lo : ℝ} {p : ℝ} {n : ℕ}
    (h : expPartialSum lo n + expTailBound lo n < p)
    (hlo : 0 ≤ lo) (hlon : lo < ↑n + 1) :
    Real.exp lo < p :=
  lt_of_le_of_lt (exp_le_partial_sum_plus_tail hlo hlon) h

end Goldbach
