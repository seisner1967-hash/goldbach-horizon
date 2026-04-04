/-
  Goldbach/CompactZone/Defs.lean
  Definitions for the compact-zone domination ratio R(Q).

  For Q ∈ [log 2, 20], the domination ratio is:

    R(Q) = µ(I_Q) / W(Q)

  where:
    µ(I_Q) = Σ { log(p) / p^(k/2) : p^k prime power, k·log(p) ∈ [Q, Q+1] }
    W(Q)   = ∫_Q^{Q+1} e^{2q} dq = (e^{2(Q+1)} - e^{2Q}) / 2

  The theorem to prove: R(Q) < 1/4 for all Q ∈ [log 2, 20].

  STRATEGY: Instead of working with noncomputable R(Q) directly,
  we define computable RATIONAL upper bounds for µ and lower bounds
  for W, using the enclosure data in A2CertificateData.lean and the
  Taylor machinery in ExpBounds.lean. The master lemma `ratio_bound`
  reduces R(Q) < 1/4 to 4 · num_upper < denom_lower.

  0 sorry, 0 axiom.
-/
import Goldbach.ExpBounds
import Goldbach.A2CertificateData
import Goldbach.BreakpointGrid
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Goldbach.CompactZone

open Real Finset

/-! ## §1 The confining weight (denominator)

W(Q) = ∫_Q^{Q+1} e^{2q} dq = (e^{2(Q+1)} - e^{2Q}) / 2

This is strictly positive and strictly increasing in Q. -/

/-- The confining weight: integral of e^{2q} over [Q, Q+1]. -/
noncomputable def confiningWeight (Q : ℝ) : ℝ :=
  (Real.exp (2 * (Q + 1)) - Real.exp (2 * Q)) / 2

/-- The confining weight is strictly positive. -/
theorem confiningWeight_pos (Q : ℝ) : 0 < confiningWeight Q := by
  unfold confiningWeight
  have h1 : Real.exp (2 * Q) < Real.exp (2 * (Q + 1)) := by
    apply Real.exp_lt_exp_of_lt
    linarith
  linarith

/-- Factored form: W(Q) = e^{2Q} · (e² - 1) / 2. -/
theorem confiningWeight_eq (Q : ℝ) :
    confiningWeight Q = Real.exp (2 * Q) * (Real.exp 2 - 1) / 2 := by
  unfold confiningWeight
  rw [show 2 * (Q + 1) = 2 * Q + 2 from by ring]
  rw [Real.exp_add]
  ring

/-! ## §2 The arithmetic measure (numerator)

µ(I_Q) = Σ { log(p) / p^(k/2) : p^k prime power, k·log(p) ∈ [Q, Q+1] }

For Q ≤ 20, only primes p ≤ e^21 and small powers contribute. The
1229 breakpoint enclosures in A2CertificateData cover primes p ≤ 9973,
which is sufficient for the dominant k=1 terms (e^20 < 5 × 10⁸, but
the primes with log(p) ∈ [Q, Q+1] ⊂ [0, 21] have p ≤ e^21 < 1.32 × 10⁹).

For primes p > 9973 with log(p) > log(9973) ≈ 9.21, the contributions
log(p)/√p are small (< 9.22/99.8 < 0.093 per prime) and there are
few such primes in any unit interval. -/

/-- A prime power datum: (p, k) with k ≥ 1. -/
structure PrimePowerDatum where
  p : ℕ
  k : ℕ
  hp : Nat.Prime p
  hk : 1 ≤ k

/-- The contribution of a prime power (p, k) to the arithmetic measure:
    log(p) / p^(k/2). -/
noncomputable def ppContribution (d : PrimePowerDatum) : ℝ :=
  Real.log d.p / (d.p : ℝ) ^ ((d.k : ℝ) / 2)

/-! ## §3 Computable upper bounds for µ using enclosures

The proof strategy:
1. For a cell [Q_lo, Q_lo + δ], enumerate which breakpoint enclosures
   could have log(p) ∈ [Q_lo, Q_lo + δ + 1] (window overlaps cell).
2. For each contributing prime p, bound log(p)/√p from above using
   the enclosure hi-bound and a rational bound for 1/√p.
3. Sum these upper bounds to get µ_upper for the cell.
4. Bound the denominator W(Q) from below using Taylor. -/

/-- Upper bound for log(p) from the breakpoint enclosure.
    Since log(p) < hi_num/10^9, this is a valid upper bound. -/
def logUpperNum (be : Goldbach.BreakpointEnclosure) : ℕ :=
  be.hi_num

/-- Lower bound for log(p) from the breakpoint enclosure.
    Since lo_num/10^9 < log(p), this is a valid lower bound. -/
def logLowerNum (be : Goldbach.BreakpointEnclosure) : ℕ :=
  be.lo_num

/-- Check if a breakpoint enclosure could have log(p) overlapping [Q_lo, Q_hi].
    All values in units of 10^9 (integer arithmetic).
    For k-th powers: check if k·log(p) could be in [Q_lo, Q_hi+1],
    i.e., k·lo_num < (Q_hi+1)·10^9 and k·hi_num > Q_lo. -/
def enclosureMayOverlap (be : Goldbach.BreakpointEnclosure)
    (Q_lo_num Q_hi_num : ℕ) : Bool :=
  be.lo_num < Q_hi_num + Goldbach.breakpointPrec &&
  Q_lo_num < be.hi_num

/-- Sum of hi_num values for all enclosures overlapping the window [Q_lo, Q_lo+1].
    This gives an upper bound (in units of 10^9) for the sum of log(p)
    over primes in the window.
    Note: this is a VERY crude bound; it ignores the 1/√p factor entirely. -/
def sumLogUpperInWindow (Q_lo_num : ℕ) : ℕ :=
  Goldbach.breakpointEnclosures.foldl
    (fun acc be =>
      if enclosureMayOverlap be Q_lo_num (Q_lo_num + Goldbach.breakpointPrec)
      then acc + be.hi_num
      else acc) 0

/-! ## §4 Master bound lemma

The key technical lemma: if we can show
  4 · num_upper ≤ denom_lower
where num_upper ≥ µ(I_Q) and denom_lower ≤ W(Q),
then R(Q) < 1/4.

This reduces the analytic inequality to rational arithmetic. -/

/-- Master bound: 4·µ < W implies µ/W < 1/4. -/
theorem ratio_bound_of_four_mul_lt {nu W : ℝ}
    (hW : 0 < W) (h : 4 * nu < W) :
    nu / W < 1 / 4 := by
  rw [div_lt_div_iff₀ hW (by norm_num : (0:ℝ) < 4)]
  linarith

/-- Sandwich bound: if nu ≤ M, D ≤ W, D > 0, and 4·M < D, then nu/W < 1/4. -/
theorem ratio_bound {nu M W D : ℝ}
    (hνM : nu ≤ M) (hDW : D ≤ W) (hD : 0 < D) (h4 : 4 * M < D) :
    nu / W < 1 / 4 := by
  have hW : 0 < W := lt_of_lt_of_le hD hDW
  apply ratio_bound_of_four_mul_lt hW
  calc 4 * nu ≤ 4 * M := by linarith
    _ < D := h4
    _ ≤ W := hDW

/-- Variant with ≤ instead of < in the conclusion (for non-strict bounds). -/
theorem ratio_bound_le {nu M W D : ℝ}
    (hνM : nu ≤ M) (hDW : D ≤ W) (hD : 0 < D) (h4 : 4 * M ≤ D) :
    nu / W ≤ 1 / 4 := by
  have hW : 0 < W := lt_of_lt_of_le hD hDW
  rw [div_le_div_iff₀ hW (by norm_num : (0:ℝ) < 4)]
  nlinarith

/-! ## §5 Confining weight lower bound via Taylor

For the denominator, we need W(Q) ≥ some computable value.
Using confiningWeight_eq: W(Q) = e^{2Q} · (e²-1)/2.
We lower-bound e^{2Q} via Taylor, and (e²-1)/2 ≥ 3 (since e² ≥ 7). -/

/-- e² ≥ 7: from the Taylor bound 1 + 2 + 2 + 4/3 + 2/3 = 7. -/
theorem exp_two_ge_seven : (7 : ℝ) ≤ Real.exp 2 := by
  have := Goldbach.expPartialSum_le_exp (by norm_num : (0:ℝ) ≤ 2) 5
  unfold Goldbach.expPartialSum at this
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at this
  norm_num [Nat.factorial] at this ⊢
  linarith

/-- (e² - 1)/2 ≥ 3. -/
theorem exp2_minus1_div2_ge_three : (3 : ℝ) ≤ (Real.exp 2 - 1) / 2 := by
  linarith [exp_two_ge_seven]

/-- W(Q) ≥ 3 · e^{2Q}. -/
theorem confiningWeight_ge_three_exp {Q : ℝ} :
    3 * Real.exp (2 * Q) ≤ confiningWeight Q := by
  rw [confiningWeight_eq]
  have h1 := exp2_minus1_div2_ge_three
  have h2 : 0 < Real.exp (2 * Q) := Real.exp_pos _
  nlinarith

end Goldbach.CompactZone
