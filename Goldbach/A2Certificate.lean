/-
  Goldbach/A2Certificate.lean
  A2 self-adjointness certificate: tail bound + domination ratio proxy.

  Proved (0 sorry, 0 axiom):
    tail_bound_A2         — ∀ Q > 20, log(Q+1)/exp(Q) < 1/4
    po_a2_stage2_proved   — wires to Roadmap.PO_A2_stage2

  Defined (computable):
    primesInWindow        — count of primes in an enclosure window

  Cowork v3 — replaces A2CertificateTrustedInstance.lean (which had 2 axioms).
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

open Finset Real BigOperators

/-! ## Taylor helpers -/

/-- The 3-term Taylor partial sum equals 1 + x + x²/2. -/
private theorem expPartialSum_three (x : ℝ) :
    expPartialSum x 3 = 1 + x + x ^ 2 / 2 := by
  unfold expPartialSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [pow_zero, pow_one, pow_succ, Nat.factorial,
             Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- Lower bound: 1 + x + x²/2 ≤ exp(x) for x ≥ 0. -/
theorem quadratic_le_exp {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 ≤ Real.exp x := by
  rw [← expPartialSum_three]
  exact expPartialSum_le_exp hx 3

/-! ## Tail bound components -/

/-- For Q > 20, 4Q < exp(Q).
    Uses: 4Q < 1 + Q + Q²/2 (by nlinarith, since Q² > 6Q+2)
    and 1 + Q + Q²/2 ≤ exp(Q) (Taylor). -/
theorem four_mul_lt_exp {Q : ℝ} (hQ : Q > 20) :
    4 * Q < Real.exp Q := by
  have hQ_nn : 0 ≤ Q := by linarith
  calc 4 * Q
      < 1 + Q + Q ^ 2 / 2 := by nlinarith [sq_nonneg Q]
    _ ≤ Real.exp Q := quadratic_le_exp hQ_nn

/-- log(Q+1) ≤ Q for Q > 0.
    Uses: Q+1 ≤ exp(Q) (from Taylor), then log monotonicity. -/
theorem log_succ_le {Q : ℝ} (hQ : Q > 0) :
    Real.log (Q + 1) ≤ Q := by
  have hQ1 : (0 : ℝ) < Q + 1 := by linarith
  have hQ_nn : 0 ≤ Q := by linarith
  have hle : Q + 1 ≤ Real.exp Q :=
    le_trans (by nlinarith [sq_nonneg Q] : Q + 1 ≤ 1 + Q + Q ^ 2 / 2)
             (quadratic_le_exp hQ_nn)
  calc Real.log (Q + 1)
      ≤ Real.log (Real.exp Q) := Real.log_le_log (le_of_lt hQ1) hle
    _ = Q := Real.log_exp Q

/-! ## Main theorem -/

/-- **Tail bound**: for Q > 20, log(Q+1)/exp(Q) < 1/4.

    Discharges Proof Obligation A2 Stage 2 (PNT tail bound).
    Proof: log(Q+1) ≤ Q (monotonicity) and 4Q < exp(Q) (Taylor),
    so log(Q+1)/exp(Q) ≤ Q/exp(Q) < 1/4. -/
theorem tail_bound_A2 :
    ∀ Q : ℝ, Q > 20 → Real.log (Q + 1) / Real.exp Q < 1 / 4 := by
  intro Q hQ
  have hexp_pos : (0 : ℝ) < Real.exp Q := Real.exp_pos Q
  have hlog : Real.log (Q + 1) ≤ Q := log_succ_le (by linarith : Q > 0)
  have hfour : 4 * Q < Real.exp Q := four_mul_lt_exp hQ
  calc Real.log (Q + 1) / Real.exp Q
      ≤ Q / Real.exp Q := by
        apply div_le_div_of_nonneg_right hlog (le_of_lt hexp_pos)
    _ < 1 / 4 := by
        rw [div_lt_div_iff hexp_pos (by norm_num : (0:ℝ) < 4)]
        linarith

/-! ## Wiring -/

/-- Discharges Proof Obligation A2 Stage 2. -/
theorem po_a2_stage2_proved : Roadmap.PO_A2_stage2 := tail_bound_A2

/-! ## Computable proxy -/

/-- Count primes whose enclosure falls within (lo_bound/10⁹, hi_bound/10⁹]. -/
def primesInWindow (lo_bound hi_bound : ℕ) : ℕ :=
  breakpointEnclosures.countP fun be =>
    lo_bound ≤ be.lo_num ∧ be.hi_num ≤ hi_bound

/-! ## Status -/

/-- Certificate status (honest). -/
def a2CertificateStatus : String :=
  "A2Certificate v2.0:\n" ++
  "  PROVED:   tail_bound_A2 (PO_A2_stage2, Q > 20, 0 sorry)\n" ++
  "  INFRA:    BreakpointGrid (cells + indices, 0 sorry)\n" ++
  "  DEFINED:  primesInWindow (computable proxy)\n" ++
  "  OPEN:     PO_A2_stage1 (compact zone bound)\n" ++
  "  BLOCKED:  PO_A2_stage3 (KLMN, waiting on Mathlib)\n" ++
  "  AXIOMS:   0 (no trusted Python bounds introduced)"

end Goldbach
