/-
  Goldbach/DominationRatioComputable.lean
  Computable rational domination ratio bounds.

  Étape 2/4 : provides computable ℚ versions of the domination ratio
  that were previously only available as `noncomputable opaque` in
  A2CertificateTrustedInstance.lean.

  ARCHITECTURE:
  - §1: Computable domination ratio bound per cell (ℚ)
  - §2: Proof that all bounds are < 1/4 (native_decide)
  - §3: Bridge theorem to real-valued framework
  - §4: Axiom elimination roadmap
  - §5: Tests

  The key insight: `dominationRatio : ℝ → ℝ` CANNOT be made computable
  (it involves Real.log, Real.sqrt, Real.exp). Instead, we provide
  computable RATIONAL UPPER BOUNDS per cell that satisfy the same
  inequality R(Q) < 1/4. This is exactly what the CompactZone path
  already achieves via cellNumeratorStrong / cellDenominator.

  0 sorry, 0 axiom.
-/
import Goldbach.CompactZone.CellBoundsStrong
import Goldbach.CompactZone.Strong
import Mathlib.Tactic

namespace Goldbach.DominationRatioComputable

open Goldbach.CompactZone

/-! ## §1 Computable domination ratio bound

The computable analog of `dominationRatio`:
  dominationRatioBoundQ(n) = cellNumeratorStrong(n) / cellDenominator(n)

This is a computable ℚ value that upper-bounds R(Q) for Q in cell n
(modulo NumeratorSoundness, the Finset↔foldl bridge). -/

/-- Computable upper bound for the domination ratio in cell n.
    dominationRatioBoundQ(n) = cellNumeratorStrong(n) / cellDenominator(n)
    where cellNumeratorStrong ≥ µ(I_Q) and cellDenominator ≤ W(Q). -/
def dominationRatioBoundQ (n : ℕ) : ℚ :=
  cellNumeratorStrong n / cellDenominator n

/-- Computable node bound: the numerator upper bound for cell n.
    This is the computable analog of `nodeBoundVal`. -/
def nodeBoundQ (n : ℕ) : ℚ := cellNumeratorStrong n

/-- Computable denominator lower bound for cell n.
    This is the computable analog of `confiningWeight`. -/
def denomBoundQ (n : ℕ) : ℚ := cellDenominator n

/-! ## §2 The domination ratio is < 1/4 for all 20 cells

This is the computational certificate: for each cell,
4 × numerator < denominator, hence the ratio < 1/4. -/

/-- Check that dominationRatioBoundQ(n) < 1/4 for a single cell.
    Equivalent to 4 * cellNumeratorStrong(n) < cellDenominator(n). -/
def ratioCheckQ (n : ℕ) : Bool :=
  4 * cellNumeratorStrong n < cellDenominator n

/-- All 20 cells satisfy the ratio bound (delegates to cellCheckAllStrong). -/
theorem ratioCheckQ_all : ∀ n : Fin 20, ratioCheckQ (n : ℕ) = true := by
  intro n
  simp only [ratioCheckQ]
  exact cellCheckStrong_passes n

/-- The domination ratio bound is strictly less than 1/4 for each cell.
    Proved via native_decide in CellBoundsStrong. -/
theorem dominationRatioBoundQ_lt_quarter (n : Fin 20) :
    4 * cellNumeratorStrong (n : ℕ) < cellDenominator (n : ℕ) :=
  four_mul_numStrong_lt_denom n

/-- Real-valued version: 4 × (cellNumeratorStrong n : ℝ) < (cellDenominator n : ℝ). -/
theorem dominationRatioBoundQ_lt_quarter_real (n : Fin 20) :
    (4 : ℝ) * (cellNumeratorStrong (n : ℕ) : ℝ) < (cellDenominator (n : ℕ) : ℝ) :=
  four_mul_numStrong_lt_denom_real n

/-! ## §3 Bridge: the CompactZone path subsumes the axiom path

The CompactZone computational certificate (CellBoundsStrong + Strong.lean)
achieves the SAME result as the axiom-based path in
A2CertificateTrustedInstance.lean, but without axioms.

Architecture:
  OLD (axiom path):
    opaque dominationRatio → axiom node_bound → axiom lip_bound
    → cell_bound_from_node_and_lip → interp_bound_from_enclosures → DEAD END

  NEW (CompactZone path):
    cellNumerator (computable ℚ) → cellNumeratorStrong (+ tail) → cellDenominator
    → native_decide: 4 × num < denom → four_mul_numStrong_lt_denom_real
    → (with NumeratorSoundness) → CompactZoneBoundStrong

The axiom path is dead code: `interp_bound_from_enclosures` has no consumers.

The bridge theorem below shows that the computational certificate implies
the real-valued bound, completing the chain. -/

/-- Positive denominator for each cell (verified computationally). -/
theorem cellDenominator_pos (n : Fin 20) : (0 : ℚ) < cellDenominator (n : ℕ) := by
  fin_cases n <;> native_decide

/-- Real-valued positive denominator. -/
theorem cellDenominator_pos_real (n : Fin 20) : (0 : ℝ) < (cellDenominator (n : ℕ) : ℝ) := by
  exact_mod_cast cellDenominator_pos n

/-- The domination ratio bound as a proper fraction < 1/4.
    Uses: 4 * num < denom and denom > 0, hence num / denom < 1/4. -/
theorem dominationRatioBoundQ_lt (n : Fin 20) :
    dominationRatioBoundQ (n : ℕ) < 1 / 4 := by
  unfold dominationRatioBoundQ
  rw [div_lt_div_iff₀ (cellDenominator_pos n) (by norm_num : (0 : ℚ) < 4)]
  linarith [dominationRatioBoundQ_lt_quarter n]

/-! ## §4 Axiom elimination roadmap

The 2 axioms in A2CertificateTrustedInstance.lean can be eliminated by:

1. REMOVING the import of A2CertificateTrustedInstance from Goldbach.lean
   (and BreakpointSoundness.lean). These files are dead code.

2. The main proof chain through CompactZone is ALREADY axiom-free:
   CellBounds → CellBoundsStrong → Strong → Grid → Wire → po_a2_stage1_proved

3. For the STRONG result (CompactZoneBoundStrong), complete NumeratorSoundness
   for cells 0-9 (cells 10-19 are done in NumeratorBound.lean).

The present file provides the COMPUTABLE side. The opaques themselves
cannot receive computable bodies because they involve transcendental
functions (Real.log, Real.sqrt, Real.exp). -/

/-! ## §5 Tests -/

-- Test 1: Show ratio bounds for cells 0, 1, 9, 19
#eval
  let cells := [0, 1, 9, 19]
  cells.map fun n =>
    (n, dominationRatioBoundQ n)

-- Test 2: Verify 4*num < denom for cells 0, 1
#eval
  let cells := [0, 1]
  cells.map fun n =>
    (n, decide (4 * cellNumeratorStrong n < cellDenominator n))

-- Test 3: Node bounds (= cellNumeratorStrong) for cells 0-4
#eval
  (List.range 5).map fun n =>
    (n, nodeBoundQ n)

-- Test 4: Denominator bounds for cells 0-4
#eval
  (List.range 5).map fun n =>
    (n, denomBoundQ n)

-- Test 5: All 20 cells pass the ratio check
#eval
  (List.range 20).map fun n =>
    (n, ratioCheckQ n)

-- Test 6: Verify ratio < 1/4 for all 20 cells
#eval
  (List.range 20).map fun n =>
    (n, decide (dominationRatioBoundQ n < 1/4))

end Goldbach.DominationRatioComputable
