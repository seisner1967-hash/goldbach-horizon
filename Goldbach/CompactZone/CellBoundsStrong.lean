/-
  Goldbach/CompactZone/CellBoundsStrong.lean
  Extended cell bounds with tail estimates for primes > 9973.

  PROBLEM: The original cellNumerator only accounts for primes in the
  breakpoint enclosure list (primes ≤ 9973). For cells n ≥ 8, there
  exist primes p > 9973 with log(p) ∈ [n, n+2] whose k=1 contributions
  log(p)/√p are NOT captured by cellNumerator.

  SOLUTION: Add a computable tail bound for uncovered primes:
  - Each uncovered prime p > 9973 has √p > 99 (since 99² = 9801 < 9974)
  - Each such prime in the window has log(p) < n+2
  - So each term log(p)/√p < (n+2)/99
  - The number of such primes ≤ |[9974, ⌊e^{n+2}⌋]| ≤ expUpperBound(n+2) - 9973
  - Total tail ≤ (expUpperBound(n+2) - 9973) × (n+2) / 99

  The strengthened cell check:
    4 × (cellNumerator(n) + tailBound(n)) < cellDenominator(n)
  passes for ALL 20 cells (verified by native_decide).

  0 sorry, 0 axiom.
-/
import Goldbach.CompactZone.CellBounds
import Mathlib.Tactic

namespace Goldbach.CompactZone

/-! ## §1 Explicit upper bounds for e^n

These are STRICT upper bounds: e^n < expUpperBound(n).
Soundness will be verified in Strong.lean using Taylor bounds.

Values: ⌈e^n⌉ for n = 0..21, verified by Python mpmath. -/

/-- Strict upper bound for e^n as a natural number. -/
def expUpperBound : ℕ → ℕ
  | 0 => 2       -- e^0 = 1 < 2
  | 1 => 3       -- e^1 ≈ 2.718 < 3
  | 2 => 8       -- e^2 ≈ 7.389 < 8
  | 3 => 21      -- e^3 ≈ 20.086 < 21
  | 4 => 55      -- e^4 ≈ 54.598 < 55
  | 5 => 149     -- e^5 ≈ 148.413 < 149
  | 6 => 404     -- e^6 ≈ 403.429 < 404
  | 7 => 1097    -- e^7 ≈ 1096.633 < 1097
  | 8 => 2981    -- e^8 ≈ 2980.958 < 2981
  | 9 => 8104    -- e^9 ≈ 8103.084 < 8104
  | 10 => 22027  -- e^10 ≈ 22026.466 < 22027
  | 11 => 59875  -- e^11 ≈ 59874.142 < 59875
  | 12 => 162755 -- e^12 ≈ 162754.791 < 162755
  | 13 => 442414
  | 14 => 1202605
  | 15 => 3269018
  | 16 => 8886111
  | 17 => 24154953
  | 18 => 65659970
  | 19 => 178482301
  | 20 => 485165196
  | 21 => 1318815735
  | _ => 0 -- unused

/-! ## §2 Tail bound for uncovered primes

For cell n, primes p > 9973 with log(p) ∈ [Q, Q+1] ⊂ [n, n+2]:
- Each contributes log(p)/√p < (n+2)/99
- There are at most max(0, expUpperBound(n+2) - 9974) such primes
  (since they are distinct integers in [9974, e^{n+2}))
-/

/-- Rational tail bound for k=1 contributions from primes > 9973. -/
def tailBoundQ (n : ℕ) : ℚ :=
  let ub := expUpperBound (n + 2)
  if ub ≤ 9974 then 0
  else ((ub - 9974 : ℕ) : ℚ) * ((n + 2 : ℕ) : ℚ) / 99

/-- For cells 0-7, tail is zero (all primes in window ≤ 9973). -/
theorem tailBoundQ_zero_to_7 (n : ℕ) (hn : n ≤ 7) : tailBoundQ n = 0 := by
  interval_cases n <;> native_decide

/-! ## §3 Strengthened cell numerator and check -/

/-- Cell numerator with tail bound for uncovered primes. -/
def cellNumeratorStrong (n : ℕ) : ℚ :=
  cellNumerator n + tailBoundQ n

/-- Strengthened cell check: 4 × (cellNumerator + tail) < cellDenominator. -/
def cellCheckStrong (n : ℕ) : Bool :=
  4 * cellNumeratorStrong n < cellDenominator n

/-- All 20 cells pass the strengthened check. -/
def cellCheckAllStrong : Bool :=
  (List.range 20).all cellCheckStrong

/-! ## §4 Computational verification -/

/-- Cell 0 passes the strong check (tail = 0, same as before). -/
theorem cell_0_pass_strong : cellCheckStrong 0 = true := by native_decide

/-- Cell 1 passes the strong check (tail = 0, same as before). -/
theorem cell_1_pass_strong : cellCheckStrong 1 = true := by native_decide

/-- Cells 2-9 pass the strong check. -/
theorem cells_2_to_9_pass_strong :
    (List.range 8).all (fun i => cellCheckStrong (i + 2)) = true := by
  native_decide

/-- Cells 10-19 pass the strong check. -/
theorem cells_10_to_19_pass_strong :
    (List.range 10).all (fun i => cellCheckStrong (i + 10)) = true := by
  native_decide

/-- All 20 cells pass the strengthened check. -/
theorem all_cells_pass_strong : cellCheckAllStrong = true := by
  unfold cellCheckAllStrong
  simp only [List.all_eq_true, List.mem_range]
  intro n hn
  interval_cases n <;> native_decide

end Goldbach.CompactZone
