/-
  Goldbach/A2Certificate.lean
  A2 certificate: PNT tail bound and domination ratio proxy.

  Main result: tail_bound_A2 proves
    ∀ Q > 20, log(Q+1)/exp(Q) < 1/4
  using Taylor lower bounds from ExpBounds.lean.

  0 sorry, 0 axiom.
-/
import Goldbach.ExpBounds
import Goldbach.Roadmap
import Goldbach.BreakpointGrid
import Goldbach.A2CertificateData
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Goldbach

open Real Finset

/-! ## Taylor helpers -/

/-- The 3-term Taylor partial sum equals 1 + x + x²/2. -/
private theorem expPartialSum_three (x : ℝ) :
    expPartialSum x 3 = 1 + x + x ^ 2 / 2 := by
  unfold expPartialSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero, pow_one, pow_succ, mul_one,
    Nat.factorial, zero_add]
  push_cast; ring

/-- Lower bound: 1 + x + x²/2 ≤ exp(x) for x ≥ 0. -/
theorem quadratic_le_exp {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 ≤ Real.exp x := by
  rw [← expPartialSum_three]
  exact expPartialSum_le_exp hx 3

/-! ## PNT tail bound

The A2 certificate requires that the PNT remainder tail
  log(Q+1) / exp(Q) < 1/4
for Q > 20. This ensures the domination ratio decays fast enough
in the analytic zone above Q = 20.

Proof:
1. log(Q+1) ≤ Q    (since Q+1 ≤ 1+Q+Q²/2 ≤ exp(Q))
2. 4Q < exp(Q)      (since 1+Q+Q²/2 > 4Q for Q > 6)
3. Combine: log(Q+1)/exp(Q) ≤ Q/exp(Q) < 1/4.
-/

/-- For Q > 20, 4Q < exp(Q). Uses quadratic Taylor bound. -/
theorem four_mul_lt_exp {Q : ℝ} (hQ : Q > 20) :
    4 * Q < Real.exp Q := by
  have hQ_nn : 0 ≤ Q := by linarith
  calc 4 * Q
      < 1 + Q + Q ^ 2 / 2 := by
        nlinarith [mul_pos (show (0:ℝ) < Q by linarith) (show Q - 6 > 0 by linarith)]
    _ ≤ Real.exp Q := quadratic_le_exp hQ_nn

/-- log(Q+1) ≤ Q for Q > 0. -/
theorem log_succ_le {Q : ℝ} (hQ : Q > 0) :
    Real.log (Q + 1) ≤ Q := by
  have hQ1 : (0 : ℝ) < Q + 1 := by linarith
  have hQ_nn : 0 ≤ Q := by linarith
  have hle : Q + 1 ≤ Real.exp Q := by
    calc Q + 1
        ≤ 1 + Q + Q ^ 2 / 2 := by nlinarith [sq_nonneg Q]
      _ ≤ Real.exp Q := quadratic_le_exp hQ_nn
  calc Real.log (Q + 1)
      ≤ Real.log (Real.exp Q) := Real.log_le_log hQ1 hle
    _ = Q := Real.log_exp Q

/-- **MAIN THEOREM**: ∀ Q > 20, log(Q+1)/exp(Q) < 1/4.
    Discharges PO_A2_stage2 (PNT tail bound). -/
theorem tail_bound_A2 :
    ∀ Q : ℝ, Q > 20 → Real.log (Q + 1) / Real.exp Q < 1 / 4 := by
  intro Q hQ
  have hexp_pos : (0 : ℝ) < Real.exp Q := Real.exp_pos Q
  have hlog : Real.log (Q + 1) ≤ Q := log_succ_le (by linarith)
  have hfour : 4 * Q < Real.exp Q := four_mul_lt_exp hQ
  -- log(Q+1)/exp(Q) ≤ Q/exp(Q) < 1/4
  have h1 : Real.log (Q + 1) / Real.exp Q ≤ Q / Real.exp Q :=
    (div_le_div_iff_of_pos_right hexp_pos).mpr hlog
  have h2 : Q / Real.exp Q < 1 / 4 := by
    rw [div_lt_div_iff₀ hexp_pos (by norm_num : (0:ℝ) < 4)]
    linarith
  linarith

/-! ## Proof obligation wiring -/

/-- Discharges Proof Obligation A2 Stage 2. -/
theorem po_a2_stage2_proved : Roadmap.PO_A2_stage2 :=
  tail_bound_A2

/-! ## Computable prime count via breakpoint enclosures -/

/-- Count primes whose enclosure is in (lo_bound/10⁹, hi_bound/10⁹]. -/
def primesInWindow (lo_bound hi_bound : ℕ) : ℕ :=
  breakpointEnclosures.countP fun be =>
    decide (lo_bound ≤ be.lo_num ∧ be.hi_num ≤ hi_bound)

/-! ## Certificate status -/

/-- Human-readable status of the A2 certificate. -/
def a2CertificateStatus : String :=
  "A2Certificate v2.0:\n" ++
  "  PROVED:   tail_bound_A2 (PO_A2_stage2, Q > 20, 0 sorry)\n" ++
  "  INFRA:    BreakpointGrid (cells + indices, 0 sorry)\n" ++
  "  DEFINED:  primesInWindow (computable proxy)\n" ++
  "  OPEN:     PO_A2_stage1 (compact zone bound)\n" ++
  "  BLOCKED:  PO_A2_stage3 (KLMN, waiting on Mathlib)\n" ++
  "  AXIOMS:   0 (no trusted Python bounds introduced)"

end Goldbach
