/-
  Goldbach/CompactZone/NumeratorAll.lean
  Proves CompactZoneBoundStrong for ALL 20 cells.

  ARCHITECTURE:
  - Cells 10-19: via NumeratorSoundness (from NumeratorBound.lean)
  - Cells 2-9: count × max-term approach with prime-count filter
  - Cells 0-1: per-prime bounds with explicit log/sqrt enclosures

  The final theorem `compactZoneBoundStrong_all` removes
  the NumeratorSoundness hypothesis from the CompactZoneBound chain.

  SORRY COUNT: 2 (cells 0-1 per-prime analysis: term_le_primeBound, S_subset_cell01)
  AXIOM COUNT: 0
-/
import Goldbach.CompactZone.NumeratorBound
import Goldbach.CompactZone.Bridge
import Mathlib.Tactic

namespace Goldbach.CompactZone

open Real Finset

/-! ## §1 Local copies of private lemmas from Bridge.lean -/

private lemma log_two_pos' : (0 : ℝ) < Real.log 2 :=
  Real.log_pos (by norm_num : (1 : ℝ) < 2)

private lemma exists_cell' (Q : ℝ) (hlo : 0 ≤ Q) (hhi : Q ≤ 20) :
    ∃ (n : ℕ), n < 20 ∧ (n : ℝ) ≤ Q ∧ Q ≤ (n : ℝ) + 1 := by
  by_cases hQ19 : Q ≤ 19
  · have h1 : (⌊Q⌋₊ : ℝ) ≤ 19 := le_trans (Nat.floor_le hlo) hQ19
    have h2 : ⌊Q⌋₊ ≤ 19 := by exact_mod_cast h1
    exact ⟨⌊Q⌋₊, by omega, Nat.floor_le hlo, le_of_lt (Nat.lt_floor_add_one Q)⟩
  · push_neg at hQ19
    exact ⟨19, by omega, by push_cast; linarith, by push_cast; linarith⟩

/-! ## §2 Lower bounds for exp(n)

We prove exp(n) > expLowerNat(n) for n ≤ 9 via Taylor partial sums. -/

/-- Floor of e^n for n ≤ 9. We use 0 for n=0 to ensure strict inequality. -/
def expLowerNat : ℕ → ℕ
  | 0 => 0    | 1 => 2   | 2 => 7   | 3 => 20   | 4 => 54
  | 5 => 148  | 6 => 403 | 7 => 1096 | 8 => 2980 | 9 => 8103
  | _ => 0

/-- Taylor partial sum S_K(n) > expLowerNat(n) for n ≤ 9.
    Uses K=30 to ensure convergence for all cells. -/
private lemma taylor_gt_lower (n : ℕ) (hn : n ≤ 9) :
    (expLowerNat n : ℚ) < taylorPartialSumQ (n : ℚ) 30 := by
  interval_cases n <;> native_decide

/-- exp(n) > expLowerNat(n) for n ≤ 9. -/
private lemma exp_gt_lower (n : ℕ) (hn : n ≤ 9) :
    (expLowerNat n : ℝ) < Real.exp (n : ℝ) := by
  have hQ := taylor_gt_lower n hn
  have hR : (expLowerNat n : ℝ) < (taylorPartialSumQ (↑n : ℚ) 30 : ℝ) := by exact_mod_cast hQ
  have hcast := taylorPartialSumQ_cast (↑n : ℚ) 30
  have htaylor := Goldbach.expPartialSum_le_exp
    (show (0:ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n) 30
  calc (expLowerNat n : ℝ) < (taylorPartialSumQ (↑n : ℚ) 30 : ℝ) := hR
    _ = Goldbach.expPartialSum ((↑n : ℚ) : ℝ) 30 := hcast
    _ = Goldbach.expPartialSum (↑n : ℝ) 30 := by norm_cast
    _ ≤ Real.exp (↑n : ℝ) := htaylor

/-- Primes with log(p) ≥ n have p > expLowerNat(n). -/
private lemma prime_gt_lower {n p : ℕ} (hn : n ≤ 9) (hp : Nat.Prime p)
    (hlog : (n : ℝ) ≤ Real.log ↑p) : expLowerNat n < p := by
  by_contra h
  push_neg at h
  have hpL : (p : ℝ) ≤ (expLowerNat n : ℝ) := by exact_mod_cast h
  have hexp := exp_gt_lower n hn
  have hp_pos : (0 : ℝ) < ↑p := by exact_mod_cast hp.pos
  have : Real.log (↑p : ℝ) < (n : ℝ) := by
    rw [show (n : ℝ) = Real.log (Real.exp n) from (Real.log_exp n).symm]
    exact Real.log_lt_log hp_pos (by linarith)
  linarith

/-! ## §3 Per-prime bounds for cells 0-1

For small primes (≤ 19), we bound log(p) from above and √p from below
using rational enclosures verified via Taylor partial sums. -/

/-- Per-prime log upper bound: log(p) < logUB(p). -/
private def logUB : ℕ → ℚ
  | 2 => 1       | 3 => 12/10   | 5 => 17/10   | 7 => 2
  | 11 => 25/10  | 13 => 27/10  | 17 => 29/10  | 19 => 3
  | _ => 100

/-- Per-prime sqrt lower bound: sqrtLowerQ(p) ≤ √p. -/
private def sqrtLowerQ : ℕ → ℚ
  | 2 => 14/10  | 3 => 17/10  | 5 => 22/10  | 7 => 26/10
  | 11 => 33/10 | 13 => 36/10 | 17 => 41/10 | 19 => 43/10
  | _ => 1

/-- Per-prime combined bound: log(p)/√p ≤ primeBoundQ(p). -/
private def primeBoundQ : ℕ → ℚ
  | 2 => 5/7    | 3 => 12/17  | 5 => 17/22  | 7 => 10/13
  | 11 => 25/33 | 13 => 3/4   | 17 => 29/41 | 19 => 30/43
  | _ => 0

/-- Taylor verification: p < S_K(logUB(p)), hence log(p) < logUB(p). -/
private lemma logUB_taylor (p : ℕ) (hp : p ∈ ({2,3,5,7,11,13,17,19} : Finset ℕ)) :
    (p : ℚ) < taylorPartialSumQ (logUB p) 15 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

/-- logUB values are non-negative. -/
private lemma logUB_nonneg (p : ℕ) (hp : p ∈ ({2,3,5,7,11,13,17,19} : Finset ℕ)) :
    (0 : ℚ) ≤ logUB p := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [logUB]

/-- log(p) < logUB(p) for small primes. -/
private lemma log_lt_logUB {p : ℕ} (hp_prime : Nat.Prime p)
    (hp_mem : p ∈ ({2,3,5,7,11,13,17,19} : Finset ℕ)) :
    Real.log (↑p : ℝ) < (logUB p : ℝ) := by
  have hp_pos : (0:ℝ) < ↑p := by exact_mod_cast hp_prime.pos
  have hQ := logUB_taylor p hp_mem
  have hR : (p : ℝ) < (taylorPartialSumQ (logUB p) 15 : ℝ) := by exact_mod_cast hQ
  have hnn : (0:ℝ) ≤ (logUB p : ℝ) := by exact_mod_cast logUB_nonneg p hp_mem
  have hcast := taylorPartialSumQ_cast (logUB p) 15
  have htaylor := Goldbach.expPartialSum_le_exp hnn 15
  have hp_lt_exp : (p : ℝ) < Real.exp (logUB p : ℝ) :=
    calc (p : ℝ) < (taylorPartialSumQ (logUB p) 15 : ℝ) := hR
      _ = Goldbach.expPartialSum ((logUB p : ℚ) : ℝ) 15 := hcast
      _ = Goldbach.expPartialSum (logUB p : ℝ) 15 := by norm_cast
      _ ≤ Real.exp (logUB p : ℝ) := htaylor
  rw [show (p : ℝ) = Real.exp (Real.log ↑p) from (Real.exp_log hp_pos).symm] at hp_lt_exp
  exact (Real.exp_lt_exp).mp hp_lt_exp

/-- sqrtLowerQ(p)² ≤ p for small primes. -/
private lemma sqrtLowerQ_sq_le (p : ℕ) (hp : p ∈ ({2,3,5,7,11,13,17,19} : Finset ℕ)) :
    sqrtLowerQ p * sqrtLowerQ p ≤ (p : ℚ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sqrtLowerQ] <;> norm_num

/-- sqrtLowerQ(p) > 0 for small primes. -/
private lemma sqrtLowerQ_pos (p : ℕ) (hp : p ∈ ({2,3,5,7,11,13,17,19} : Finset ℕ)) :
    (0 : ℝ) < (sqrtLowerQ p : ℝ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sqrtLowerQ] <;> norm_num

/-- sqrtLowerQ(p) ≤ √p for small primes. -/
private lemma sqrtLowerQ_le_sqrt (p : ℕ) (hp : p ∈ ({2,3,5,7,11,13,17,19} : Finset ℕ)) :
    (sqrtLowerQ p : ℝ) ≤ Real.sqrt (↑p : ℝ) := by
  have hsq := sqrtLowerQ_sq_le p hp
  have hsq_r : (sqrtLowerQ p : ℝ) * (sqrtLowerQ p : ℝ) ≤ (p : ℝ) := by exact_mod_cast hsq
  have : (sqrtLowerQ p : ℝ) ^ 2 ≤ (p : ℝ) := by nlinarith
  exact Real.le_sqrt_of_sq_le this

/-- primeBoundQ = logUB / sqrtLowerQ (as rationals). -/
private lemma primeBoundQ_eq (p : ℕ) (hp : p ∈ ({2,3,5,7,11,13,17,19} : Finset ℕ)) :
    primeBoundQ p = logUB p / sqrtLowerQ p := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [primeBoundQ, logUB, sqrtLowerQ] <;> norm_num

/-- primeBoundQ is non-negative. -/
private lemma primeBoundQ_nonneg (p : ℕ) (hp : p ∈ ({2,3,5,7,11,13,17,19} : Finset ℕ)) :
    (0 : ℝ) ≤ (primeBoundQ p : ℝ) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [primeBoundQ] <;> norm_num

/-- Per-prime bound: log(p)/√p ≤ primeBoundQ(p).
    Proof: log(p) < logUB(p) and sqrtLowerQ(p) ≤ √p, combined. -/
private lemma term_le_primeBound (p : ℕ) (hp : Nat.Prime p)
    (hp_mem : p ∈ ({2,3,5,7,11,13,17,19} : Finset ℕ)) :
    Real.log ↑p / Real.sqrt ↑p ≤ (primeBoundQ p : ℝ) := by
  have hp_pos : (0 : ℝ) < ↑p := by exact_mod_cast hp.pos
  have hsqrt_pos : (0 : ℝ) < Real.sqrt ↑p := Real.sqrt_pos.mpr hp_pos
  have hlog := log_lt_logUB hp hp_mem
  have hsqrtL := sqrtLowerQ_le_sqrt p hp_mem
  have hsqrtL_pos := sqrtLowerQ_pos p hp_mem
  have hlogUB_nn : (0 : ℝ) ≤ (logUB p : ℝ) := by exact_mod_cast logUB_nonneg p hp_mem
  -- log(p)/√p ≤ logUB(p)/√p ≤ logUB(p)/sqrtLowerQ(p) = primeBoundQ(p)
  have h1 : Real.log ↑p / Real.sqrt ↑p ≤ (logUB p : ℝ) / Real.sqrt ↑p :=
    div_le_div_of_nonneg_right hlog.le (Real.sqrt_nonneg _)
  have h2 : (logUB p : ℝ) / Real.sqrt ↑p ≤ (logUB p : ℝ) / (sqrtLowerQ p : ℝ) := by
    rw [div_le_div_iff₀ hsqrt_pos hsqrtL_pos]
    exact mul_le_mul_of_nonneg_left hsqrtL hlogUB_nn
  have h3 : (logUB p : ℝ) / (sqrtLowerQ p : ℝ) = (primeBoundQ p : ℝ) := by
    rw [show (primeBoundQ p : ℝ) = ((logUB p / sqrtLowerQ p : ℚ) : ℝ) from by
      rw [primeBoundQ_eq p hp_mem]]
    push_cast; rfl
  linarith

/-! ## §4 Cell 0-1 sum bounds -/

/-- Known primes for cell 0: all primes in [1, 8). -/
private def cell0Primes : Finset ℕ := {2, 3, 5, 7}

/-- Known primes for cell 1: all primes in [3, 21). -/
private def cell1Primes : Finset ℕ := {3, 5, 7, 11, 13, 17, 19}

/-- Sum bound for cell 0. -/
private def cell0SumBound : ℚ :=
  primeBoundQ 2 + primeBoundQ 3 + primeBoundQ 5 + primeBoundQ 7

/-- Sum bound for cell 1. -/
private def cell1SumBound : ℚ :=
  primeBoundQ 3 + primeBoundQ 5 + primeBoundQ 7 +
  primeBoundQ 11 + primeBoundQ 13 + primeBoundQ 17 + primeBoundQ 19

/-- Computational check: 4 × cell0SumBound < cellDenominator(0). -/
private lemma cell0_check : 4 * cell0SumBound < cellDenominator 0 := by native_decide

/-- Computational check: 4 × cell1SumBound < cellDenominator(1). -/
private lemma cell1_check : 4 * cell1SumBound < cellDenominator 1 := by native_decide

/-- Every prime p with p < expUpperBound(2) = 8 is in cell0Primes. -/
private lemma prime_in_cell0 {p : ℕ} (hp : Nat.Prime p) (hlt : p < expUpperBound 2) :
    p ∈ cell0Primes := by
  simp [expUpperBound] at hlt
  interval_cases p <;> first | decide | exact absurd hp (by decide)

/-- Every prime p with 3 ≤ p and p < expUpperBound(3) = 21 is in cell1Primes. -/
private lemma prime_in_cell1 {p : ℕ} (hp : Nat.Prime p) (hlo : 3 ≤ p) (hlt : p < expUpperBound 3) :
    p ∈ cell1Primes := by
  simp [expUpperBound] at hlt
  interval_cases p <;> first | decide | exact absurd hp (by decide)

/-- cell0Primes ⊆ small primes set. -/
private lemma cell0_sub_small : cell0Primes ⊆ ({2,3,5,7,11,13,17,19} : Finset ℕ) := by
  decide

/-- cell1Primes ⊆ small primes set. -/
private lemma cell1_sub_small : cell1Primes ⊆ ({2,3,5,7,11,13,17,19} : Finset ℕ) := by
  decide

/-- Sum of primeBoundQ over cell0Primes = cell0SumBound. -/
private lemma cell0_sum_eq :
    (∑ p in cell0Primes, (primeBoundQ p : ℝ)) = (cell0SumBound : ℝ) := by
  simp [cell0Primes, cell0SumBound]; push_cast; ring

/-- Sum of primeBoundQ over cell1Primes = cell1SumBound. -/
private lemma cell1_sum_eq :
    (∑ p in cell1Primes, (primeBoundQ p : ℝ)) = (cell1SumBound : ℝ) := by
  simp [cell1Primes, cell1SumBound]; push_cast; ring

/-- S ⊆ cell0Primes for cell 0 primes. -/
private lemma S_subset_cell0 {Q : ℝ} {S : Finset ℕ}
    (hQlo : (0 : ℝ) ≤ Q) (hQhi : Q ≤ 1)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ Q ≤ Real.log ↑p ∧ Real.log ↑p < Q + 1) :
    S ⊆ cell0Primes := by
  intro p hp_mem
  obtain ⟨hp_prime, hpQlo, hpQhi⟩ := hS p hp_mem
  have hp_pos : (0 : ℝ) < ↑p := by exact_mod_cast hp_prime.pos
  have hlog_lt : Real.log ↑p < 2 := by linarith
  have hp_lt_exp : (p : ℝ) < Real.exp 2 := by
    calc (p : ℝ) = Real.exp (Real.log ↑p) := (Real.exp_log hp_pos).symm
      _ < Real.exp 2 := Real.exp_lt_exp_of_lt hlog_lt
  have h_exp := exp_lt_expUpperBound 2 (by omega) (by omega)
  have hp_lt : p < expUpperBound 2 := by
    have : (p : ℝ) < (expUpperBound 2 : ℝ) := lt_trans hp_lt_exp (by exact_mod_cast h_exp)
    exact_mod_cast this
  exact prime_in_cell0 hp_prime hp_lt

/-- S ⊆ cell1Primes for cell 1 primes. -/
private lemma S_subset_cell1 {Q : ℝ} {S : Finset ℕ}
    (hQlo : (1 : ℝ) ≤ Q) (hQhi : Q ≤ 2)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ Q ≤ Real.log ↑p ∧ Real.log ↑p < Q + 1) :
    S ⊆ cell1Primes := by
  intro p hp_mem
  obtain ⟨hp_prime, hpQlo, hpQhi⟩ := hS p hp_mem
  have hp_pos : (0 : ℝ) < ↑p := by exact_mod_cast hp_prime.pos
  have hlog_ge : (1 : ℝ) ≤ Real.log ↑p := by linarith
  have hlog_lt : Real.log ↑p < 3 := by linarith
  -- p ≥ 3: log(p) ≥ 1, so p ≥ e > 2, so p ≥ 3
  have hp_gt2 : (2 : ℝ) < ↑p := by
    have h2_lt_e : (2 : ℝ) < Real.exp 1 := by
      have hq : (2 : ℚ) < taylorPartialSumQ 1 5 := by native_decide
      have hqr : (2 : ℝ) < (taylorPartialSumQ 1 5 : ℝ) := by exact_mod_cast hq
      have hcast := taylorPartialSumQ_cast 1 5
      have htaylor := Goldbach.expPartialSum_le_exp (show (0:ℝ) ≤ 1 by norm_num) 5
      calc (2 : ℝ) < (taylorPartialSumQ 1 5 : ℝ) := hqr
        _ = Goldbach.expPartialSum ((1 : ℚ) : ℝ) 5 := hcast
        _ = Goldbach.expPartialSum (1 : ℝ) 5 := by norm_cast
        _ ≤ Real.exp 1 := htaylor
    calc (2 : ℝ) < Real.exp 1 := h2_lt_e
      _ ≤ Real.exp (Real.log ↑p) := Real.exp_le_exp_of_le hlog_ge
      _ = ↑p := Real.exp_log hp_pos
  have hp3 : 3 ≤ p := by exact_mod_cast show (2:ℝ) < (p:ℝ) from hp_gt2
  -- p < expUpperBound(3) = 21
  have hp_lt_exp : (p : ℝ) < Real.exp 3 := by
    calc (p : ℝ) = Real.exp (Real.log ↑p) := (Real.exp_log hp_pos).symm
      _ < Real.exp 3 := Real.exp_lt_exp_of_lt hlog_lt
  have h_exp := exp_lt_expUpperBound 3 (by omega) (by omega)
  have hp_lt : p < expUpperBound 3 := by
    have : (p : ℝ) < (expUpperBound 3 : ℝ) := lt_trans hp_lt_exp (by exact_mod_cast h_exp)
    exact_mod_cast this
  exact prime_in_cell1 hp_prime hp3 hp_lt

/-- Sum bound for cell 0: Σ_{p∈S} log(p)/√p ≤ cell0SumBound. -/
private lemma sum_bound_cell0 {Q : ℝ} {S : Finset ℕ}
    (hQlo : (0 : ℝ) ≤ Q) (hQhi : Q ≤ 1)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ Q ≤ Real.log ↑p ∧ Real.log ↑p < Q + 1) :
    (∑ p in S, Real.log ↑p / Real.sqrt ↑p) ≤ (cell0SumBound : ℝ) := by
  have hSub := S_subset_cell0 hQlo hQhi hS
  -- Step 1: pointwise bound
  have h_pw : ∀ p ∈ S, Real.log ↑p / Real.sqrt ↑p ≤ (primeBoundQ p : ℝ) := by
    intro p hp
    exact term_le_primeBound p (hS p hp).1 (cell0_sub_small (hSub hp))
  -- Step 2: sum ≤ sum of primeBoundQ over S
  have h1 : (∑ p in S, Real.log ↑p / Real.sqrt ↑p) ≤
      ∑ p in S, (primeBoundQ p : ℝ) :=
    Finset.sum_le_sum h_pw
  -- Step 3: sum over S ≤ sum over cell0Primes (superset, nonneg terms)
  have h2 : (∑ p in S, (primeBoundQ p : ℝ)) ≤
      ∑ p in cell0Primes, (primeBoundQ p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hSub
      (fun i hi _ => primeBoundQ_nonneg i (cell0_sub_small hi))
  rw [cell0_sum_eq] at h2
  linarith

/-- Sum bound for cell 1: Σ_{p∈S} log(p)/√p ≤ cell1SumBound. -/
private lemma sum_bound_cell1 {Q : ℝ} {S : Finset ℕ}
    (hQlo : (1 : ℝ) ≤ Q) (hQhi : Q ≤ 2)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ Q ≤ Real.log ↑p ∧ Real.log ↑p < Q + 1) :
    (∑ p in S, Real.log ↑p / Real.sqrt ↑p) ≤ (cell1SumBound : ℝ) := by
  have hSub := S_subset_cell1 hQlo hQhi hS
  have h_pw : ∀ p ∈ S, Real.log ↑p / Real.sqrt ↑p ≤ (primeBoundQ p : ℝ) := by
    intro p hp
    exact term_le_primeBound p (hS p hp).1 (cell1_sub_small (hSub hp))
  have h1 : (∑ p in S, Real.log ↑p / Real.sqrt ↑p) ≤
      ∑ p in S, (primeBoundQ p : ℝ) :=
    Finset.sum_le_sum h_pw
  have h2 : (∑ p in S, (primeBoundQ p : ℝ)) ≤
      ∑ p in cell1Primes, (primeBoundQ p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hSub
      (fun i hi _ => primeBoundQ_nonneg i (cell1_sub_small hi))
  rw [cell1_sum_eq] at h2
  linarith

/-! ## §5 Coarse bounds for cells 2-9

For cells 2-9, we use count × max-term with:
- Count: |S| ≤ |{primes in [lo, hi)}| via Finset.Ico.filter
- Term: each log(p)/√p ≤ (n+2)/sqrtFloor where sqrtFloor² ≤ lo -/

/-- Integer sqrt lower bounds for each cell. sqrtFloor(n)² ≤ expLowerNat(n)+1. -/
private def sqrtFloorCell : ℕ → ℕ
  | 2 => 2  | 3 => 4  | 4 => 7  | 5 => 12
  | 6 => 20 | 7 => 33 | 8 => 54 | 9 => 90
  | _ => 1

/-- sqrtFloorCell(n)² ≤ expLowerNat(n)+1 for cells 2-9. -/
private lemma sqrtFloor_sq_le (n : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) :
    sqrtFloorCell n * sqrtFloorCell n ≤ expLowerNat n + 1 := by
  interval_cases n <;> simp [sqrtFloorCell, expLowerNat] <;> omega

/-- sqrtFloorCell(n) > 0 for cells 2-9. -/
private lemma sqrtFloor_pos (n : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) :
    0 < sqrtFloorCell n := by
  interval_cases n <;> simp [sqrtFloorCell]

/-- Coarse bound for cells 2-9:
    count(primes in range) × (n+2) / sqrtFloor. -/
private def midCoarseBoundQ (n : ℕ) : ℚ :=
  let lo := expLowerNat n + 1
  let hi := expUpperBound (n + 2)
  let count := ((Finset.Ico lo hi).filter Nat.Prime).card
  (count : ℚ) * ((n + 2 : ℕ) : ℚ) / (sqrtFloorCell n : ℚ)

/-- 4 × midCoarseBound < cellDenominator for cells 2-9. -/
private lemma midBound_check (n : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) :
    4 * midCoarseBoundQ n < cellDenominator n := by
  interval_cases n <;> native_decide

/-- Cast to ℝ. -/
private lemma midBound_check_real (n : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) :
    (4 : ℝ) * (midCoarseBoundQ n : ℝ) < (cellDenominator n : ℝ) := by
  exact_mod_cast midBound_check n hn hn9

/-- S ⊆ (Finset.Ico lo hi).filter Nat.Prime for cells 2-9. -/
private lemma S_subset_range {n : ℕ} {Q : ℝ} {S : Finset ℕ}
    (hn : 2 ≤ n) (hn9 : n ≤ 9)
    (hQlo : (n : ℝ) ≤ Q) (hQhi : Q ≤ (n : ℝ) + 1)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ Q ≤ Real.log ↑p ∧ Real.log ↑p < Q + 1) :
    S ⊆ (Finset.Ico (expLowerNat n + 1) (expUpperBound (n + 2))).filter Nat.Prime := by
  intro p hp_mem
  obtain ⟨hp_prime, hpQlo, hpQhi⟩ := hS p hp_mem
  simp only [Finset.mem_filter, Finset.mem_Ico]
  refine ⟨⟨?_, ?_⟩, hp_prime⟩
  · -- p ≥ expLowerNat(n) + 1
    exact Nat.succ_le_of_lt (prime_gt_lower hn9 hp_prime (by linarith))
  · -- p < expUpperBound(n+2)
    have hp_pos : (0 : ℝ) < ↑p := by exact_mod_cast hp_prime.pos
    have hlog_lt : Real.log ↑p < (↑(n + 2) : ℝ) := by push_cast; linarith
    have h_exp := exp_lt_expUpperBound (n + 2) (by omega) (by omega)
    have : (p : ℝ) < (expUpperBound (n + 2) : ℝ) := by
      calc (p : ℝ) = Real.exp (Real.log ↑p) := (Real.exp_log hp_pos).symm
        _ < Real.exp (↑(n + 2) : ℝ) := Real.exp_lt_exp_of_lt (by push_cast; linarith)
        _ < (expUpperBound (n + 2) : ℝ) := by exact_mod_cast h_exp
    exact_mod_cast this

/-- Per-term bound for cells 2-9. -/
private lemma term_bound_mid {n p : ℕ} {Q : ℝ} (hn : 2 ≤ n) (hn9 : n ≤ 9)
    (hQlo : (n : ℝ) ≤ Q) (hQhi : Q ≤ (n : ℝ) + 1) (hp : Nat.Prime p)
    (hplo : Q ≤ Real.log ↑p) (hphi : Real.log ↑p < Q + 1) :
    Real.log ↑p / Real.sqrt ↑p ≤ ((n + 2 : ℕ) : ℝ) / (sqrtFloorCell n : ℝ) := by
  have hp_pos : (0 : ℝ) < ↑p := by exact_mod_cast hp.pos
  have hsqrt_pos : (0 : ℝ) < Real.sqrt ↑p := Real.sqrt_pos.mpr hp_pos
  have hlog_bound : Real.log ↑p < ((n + 2 : ℕ) : ℝ) := by push_cast; linarith
  have hlog_nn : (0 : ℝ) ≤ Real.log ↑p :=
    Real.log_nonneg (by exact_mod_cast show 1 ≤ p from hp.one_le)
  -- sqrtFloorCell(n) ≤ √p
  have hsf_pos : (0 : ℝ) < (sqrtFloorCell n : ℝ) := by
    exact_mod_cast sqrtFloor_pos n hn hn9
  have hp_ge_lo : expLowerNat n + 1 ≤ p :=
    Nat.succ_le_of_lt (prime_gt_lower hn9 hp (by linarith))
  have hsf_sq : sqrtFloorCell n * sqrtFloorCell n ≤ p := by
    calc sqrtFloorCell n * sqrtFloorCell n
        ≤ expLowerNat n + 1 := sqrtFloor_sq_le n hn hn9
      _ ≤ p := hp_ge_lo
  have hsf_sq_r : (sqrtFloorCell n : ℝ) ^ 2 ≤ (p : ℝ) := by
    have : (sqrtFloorCell n : ℝ) * (sqrtFloorCell n : ℝ) ≤ (p : ℝ) := by exact_mod_cast hsf_sq
    nlinarith
  have hsf_le_sqrt : (sqrtFloorCell n : ℝ) ≤ Real.sqrt ↑p :=
    Real.le_sqrt_of_sq_le hsf_sq_r
  -- Chain: log(p)/√p ≤ (n+2)/√p ≤ (n+2)/sqrtFloor
  have hn2_pos : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n + 2 from by omega)
  calc Real.log ↑p / Real.sqrt ↑p
      ≤ ((n + 2 : ℕ) : ℝ) / Real.sqrt ↑p := by
        apply div_le_div_of_nonneg_right hlog_bound.le (Real.sqrt_nonneg _)
    _ ≤ ((n + 2 : ℕ) : ℝ) / (sqrtFloorCell n : ℝ) := by
        rw [div_le_div_iff₀ hsqrt_pos hsf_pos]
        exact mul_le_mul_of_nonneg_left hsf_le_sqrt hn2_pos.le

/-- Sum bound for cells 2-9. -/
private lemma sum_bound_mid (n : ℕ) (hn : 2 ≤ n) (hn9 : n ≤ 9) (Q : ℝ)
    (hQlo : (n : ℝ) ≤ Q) (hQhi : Q ≤ (n : ℝ) + 1)
    (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ Q ≤ Real.log ↑p ∧ Real.log ↑p < Q + 1) :
    (∑ p in S, Real.log ↑p / Real.sqrt ↑p) ≤ (midCoarseBoundQ n : ℝ) := by
  -- Per-term bound
  have h_term : ∀ p ∈ S, Real.log ↑p / Real.sqrt ↑p ≤
      ((n + 2 : ℕ) : ℝ) / (sqrtFloorCell n : ℝ) := by
    intro p hp
    obtain ⟨hp_prime, hpQlo, hpQhi⟩ := hS p hp
    exact term_bound_mid hn hn9 hQlo hQhi hp_prime hpQlo hpQhi
  -- Sum ≤ card * max_term
  have h_sum := Finset.sum_le_card_nsmul S _ _ h_term
  rw [nsmul_eq_mul] at h_sum
  -- Card bound
  have h_sub := S_subset_range hn hn9 hQlo hQhi hS
  have h_card : S.card ≤ ((Finset.Ico (expLowerNat n + 1) (expUpperBound (n + 2))).filter
      Nat.Prime).card :=
    Finset.card_le_card h_sub
  -- midCoarseBoundQ(n) = count * (n+2) / sqrtFloor
  have hsf_pos : (0 : ℝ) < (sqrtFloorCell n : ℝ) := by exact_mod_cast sqrtFloor_pos n hn hn9
  set count := ((Finset.Ico (expLowerNat n + 1) (expUpperBound (n + 2))).filter Nat.Prime).card
  have hcount_r : (S.card : ℝ) ≤ (count : ℝ) := by exact_mod_cast h_card
  have hn2_pos : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) / (sqrtFloorCell n : ℝ) := by positivity
  calc (∑ p in S, Real.log ↑p / Real.sqrt ↑p)
      ≤ (S.card : ℝ) * (((n + 2 : ℕ) : ℝ) / (sqrtFloorCell n : ℝ)) := h_sum
    _ ≤ (count : ℝ) * (((n + 2 : ℕ) : ℝ) / (sqrtFloorCell n : ℝ)) :=
        mul_le_mul_of_nonneg_right hcount_r hn2_pos
    _ = (midCoarseBoundQ n : ℝ) := by
        unfold midCoarseBoundQ
        push_cast
        ring

/-! ## §6 Full sum bound for cells 0-9 -/

/-- 4 × sum < cellDenominator for all cells 0-9. -/
private lemma sum_4_lt_denom (n : ℕ) (hn : n < 10) (Q : ℝ)
    (hQlo : (n : ℝ) ≤ Q) (hQhi : Q ≤ (n : ℝ) + 1)
    (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ Q ≤ Real.log ↑p ∧ Real.log ↑p < Q + 1) :
    4 * (∑ p in S, Real.log ↑p / Real.sqrt ↑p) < (cellDenominator n : ℝ) := by
  by_cases hn2 : 2 ≤ n
  · -- Cells 2-9
    have h_sum := sum_bound_mid n hn2 (by omega) Q hQlo hQhi S hS
    have h_check := midBound_check_real n hn2 (by omega)
    linarith
  · -- Cells 0-1
    push_neg at hn2
    interval_cases n
    · -- Cell 0: Q ∈ [0, 1]
      have hQlo' : (0 : ℝ) ≤ Q := by push_cast at hQlo; linarith
      have hQhi' : Q ≤ 1 := by push_cast at hQhi; linarith
      have h_sum := sum_bound_cell0 hQlo' hQhi' hS
      have h_check : (4 : ℝ) * (cell0SumBound : ℝ) < (cellDenominator 0 : ℝ) := by
        exact_mod_cast cell0_check
      linarith
    · -- Cell 1: Q ∈ [1, 2]
      have hQlo' : (1 : ℝ) ≤ Q := by push_cast at hQlo; linarith
      have hQhi' : Q ≤ 2 := by push_cast at hQhi; linarith
      have h_sum := sum_bound_cell1 hQlo' hQhi' hS
      have h_check : (4 : ℝ) * (cell1SumBound : ℝ) < (cellDenominator 1 : ℝ) := by
        exact_mod_cast cell1_check
      linarith

/-! ## §7 CompactZoneBoundStrong assembly -/

/-- **CompactZoneBoundStrong proved unconditionally.**
    Combines cells 0-9 (direct) and cells 10-19 (via NumeratorSoundness). -/
theorem compactZoneBoundStrong_all : CompactZoneBoundStrong := by
  intro Q hQlo hQhi S hS
  have hQ0 : 0 ≤ Q := le_trans (le_of_lt log_two_pos') hQlo
  obtain ⟨n, hn20, hnlo, hnhi⟩ := exists_cell' Q hQ0 hQhi
  by_cases h10 : 10 ≤ n
  · -- Cells 10-19: via NumeratorSoundness
    have hsum := numeratorSoundness_cells_10_to_19 n h10 hn20 Q hnlo hnhi S hS
    have hcert := four_mul_numStrong_lt_denom_real ⟨n, hn20⟩
    have hW : (cellDenominator n : ℝ) ≤ confiningWeight Q :=
      @cellDenominator_le_confiningWeight ⟨n, hn20⟩ Q
        (show 1 ≤ n from by omega) ⟨hnlo, hnhi⟩
    linarith
  · -- Cells 0-9: direct proof
    push_neg at h10
    have h_bound := sum_4_lt_denom n h10 Q hnlo hnhi S hS
    have hW : (cellDenominator n : ℝ) ≤ confiningWeight Q := by
      rcases Nat.eq_zero_or_pos n with rfl | hn_pos
      · exact le_trans cellDenominator_zero_le_W_log2 (confiningWeight_mono hQlo)
      · exact @cellDenominator_le_confiningWeight ⟨n, hn20⟩ Q
          (show 1 ≤ n from by omega) ⟨hnlo, hnhi⟩
    linarith

/-! ## §8 Chain to PO_A2_stage1 -/

theorem compactZoneBound_all : Goldbach.CompactZoneBound :=
  compactZoneBound_of_strong compactZoneBoundStrong_all

theorem po_a2_stage1_all : Goldbach.Roadmap.PO_A2_stage1 :=
  Goldbach.stage1_of_compact_zone compactZoneBound_all

end Goldbach.CompactZone
