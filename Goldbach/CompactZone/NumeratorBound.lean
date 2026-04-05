/-
  Goldbach/CompactZone/NumeratorBound.lean
  Partial proof of NumeratorSoundness for cells 10-19.

  KEY INSIGHT: For cells n ≥ 10, every prime p in the window
  [Q, Q+1] ⊂ [n, n+2] satisfies p > 9973 (since p ≥ e^Q ≥ e^10 > 22026).
  Therefore:
  1. Each term: log(p)/√p < (n+2)/99  (from log_div_sqrt_le_of_large)
  2. Count: |S| ≤ expUpperBound(n+2) - 9974 (integers in [9974, e^{n+2}))
  3. Sum: Σ ≤ tailBoundQ(n) ≤ cellNumeratorStrong(n)

  No Finset↔foldl bridge needed. The enclosure data is not used at all.

  SORRY COUNT: 0
  AXIOM COUNT: 0
-/
import Goldbach.CompactZone.Strong
import Goldbach.ExpBounds
import Mathlib.Tactic

namespace Goldbach.CompactZone

open Real Finset

/-! ## §1 Preliminary: exp(10) > 9974

We need this to show that primes with log(p) ≥ 10 have p ≥ 9974.
Proved via Taylor partial sums: S_K(10) ≤ exp(10) and S_K(10) > 9974. -/

/-- S_15(10) > 9974, verified computationally. -/
private lemma taylorSum_10_gt_9974 :
    (9974 : ℚ) < taylorPartialSumQ 10 15 := by native_decide

/-- exp(10) > 9974. -/
private lemma exp_10_gt_9974 : (9974 : ℝ) < Real.exp 10 := by
  have h_cast := taylorPartialSumQ_cast (10 : ℚ) 15
  have h_taylor := Goldbach.expPartialSum_le_exp (show (0:ℝ) ≤ 10 by norm_num) 15
  have h_gt := taylorSum_10_gt_9974
  have h_gt_r : (9974 : ℝ) < (taylorPartialSumQ 10 15 : ℝ) := by exact_mod_cast h_gt
  calc (9974 : ℝ) < (taylorPartialSumQ 10 15 : ℝ) := h_gt_r
    _ = Goldbach.expPartialSum (10 : ℝ) 15 := by
        rw [h_cast]; push_cast; ring_nf
    _ ≤ Real.exp 10 := h_taylor

/-- Any prime with log(p) ≥ 10 satisfies p ≥ 9974. -/
private lemma prime_large_of_log_ge_10 {p : ℕ} (hp : Nat.Prime p)
    (hlog : (10 : ℝ) ≤ Real.log ↑p) : 9974 ≤ p := by
  by_contra h
  push_neg at h
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have h9974 : (p : ℝ) < 9974 := by exact_mod_cast h
  have hlog_lt : Real.log (p : ℝ) < Real.log 9974 :=
    Real.log_lt_log hp_pos h9974
  have hlog_9974 : Real.log (9974 : ℝ) < 10 := by
    rw [show (10 : ℝ) = Real.log (Real.exp 10) from (Real.log_exp 10).symm]
    exact Real.log_lt_log (by positivity) exp_10_gt_9974
  linarith

/-! ## §2 The per-term bound for cells ≥ 10 -/

/-- In cells ≥ 10, each prime term is bounded by (n+2)/99. -/
private lemma term_bound_high_cell {n : ℕ} {p : ℕ} {Q : ℝ}
    (hn : 10 ≤ n) (hn20 : n < 20)
    (hQlo : (n : ℝ) ≤ Q) (hQhi : Q ≤ (n : ℝ) + 1)
    (hp : Nat.Prime p)
    (hpQlo : Q ≤ Real.log ↑p) (hpQhi : Real.log ↑p < Q + 1) :
    Real.log ↑p / Real.sqrt ↑p ≤ ((n + 2 : ℕ) : ℝ) / 99 := by
  have hlog_bound : Real.log ↑p < (n + 2 : ℕ) := by
    push_cast; linarith
  have hn10 : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp_large : 9974 ≤ p :=
    prime_large_of_log_ge_10 hp (by linarith)
  exact log_div_sqrt_le_of_large hp_large hlog_bound

/-! ## §3 The cardinality bound -/

/-- Every prime in S is < expUpperBound(n+2). -/
private lemma prime_lt_expUpperBound {n p : ℕ} {Q : ℝ}
    (hn : 10 ≤ n) (hn20 : n < 20)
    (hQhi : Q ≤ (n : ℝ) + 1)
    (hpQhi : Real.log ↑p < Q + 1)
    (hp : Nat.Prime p) : p < expUpperBound (n + 2) := by
  have hlog_lt : Real.log ↑p < (n + 2 : ℕ) := by push_cast; linarith
  have hp_pos : (0 : ℝ) < ↑p := by exact_mod_cast hp.pos
  have h_exp := exp_lt_expUpperBound (n + 2) (by omega) (by omega)
  have hp_lt_exp : (p : ℝ) < Real.exp (n + 2 : ℕ) := by
    rw [show (p : ℝ) = Real.exp (Real.log ↑p) from (Real.exp_log hp_pos).symm]
    exact Real.exp_lt_exp_of_lt (by push_cast; linarith)
  exact_mod_cast show (p : ℝ) < (expUpperBound (n + 2) : ℝ) by linarith

/-- S ⊆ Finset.Ico 9974 (expUpperBound(n+2)) for cells ≥ 10. -/
private lemma S_subset_Ico {n : ℕ} {Q : ℝ} {S : Finset ℕ}
    (hn : 10 ≤ n) (hn20 : n < 20)
    (hQlo : (n : ℝ) ≤ Q) (hQhi : Q ≤ (n : ℝ) + 1)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ Q ≤ Real.log ↑p ∧ Real.log ↑p < Q + 1) :
    S ⊆ Finset.Ico 9974 (expUpperBound (n + 2)) := by
  intro p hp_mem
  obtain ⟨hp_prime, hpQlo, hpQhi⟩ := hS p hp_mem
  simp only [Finset.mem_Ico]
  constructor
  · apply prime_large_of_log_ge_10 hp_prime
    have : (10:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  · exact prime_lt_expUpperBound hn hn20 hQhi hpQhi hp_prime

/-- expUpperBound(n+2) > 9974 for n ≥ 10. -/
private lemma expUpperBound_gt_9974 (n : ℕ) (hn : 10 ≤ n) (hn20 : n < 20) :
    9974 < expUpperBound (n + 2) := by
  interval_cases n <;> simp [expUpperBound] <;> omega

/-- Cardinality bound. -/
private lemma card_S_le {n : ℕ} {Q : ℝ} {S : Finset ℕ}
    (hn : 10 ≤ n) (hn20 : n < 20)
    (hQlo : (n : ℝ) ≤ Q) (hQhi : Q ≤ (n : ℝ) + 1)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ Q ≤ Real.log ↑p ∧ Real.log ↑p < Q + 1) :
    S.card ≤ expUpperBound (n + 2) - 9974 := by
  have h_ub := expUpperBound_gt_9974 n hn hn20
  calc S.card
      ≤ (Finset.Ico 9974 (expUpperBound (n + 2))).card :=
        Finset.card_le_card (S_subset_Ico hn hn20 hQlo hQhi hS)
    _ = expUpperBound (n + 2) - 9974 := by
        rw [Nat.card_Ico]

/-! ## §4 Assembly: sum ≤ cellNumeratorStrong(n) for cells 10-19 -/

/-- tailBoundQ(n) ≤ cellNumeratorStrong(n) for cells 10-19,
    verified computationally. -/
private lemma tailBoundQ_le_cellNumeratorStrong_Q
    (n : ℕ) (hn : 10 ≤ n) (hn20 : n < 20) :
    tailBoundQ n ≤ cellNumeratorStrong n := by
  interval_cases n <;> native_decide

private lemma tailBoundQ_le_cellNumeratorStrong
    (n : ℕ) (hn : 10 ≤ n) (hn20 : n < 20) :
    (tailBoundQ n : ℝ) ≤ (cellNumeratorStrong n : ℝ) := by
  exact_mod_cast tailBoundQ_le_cellNumeratorStrong_Q n hn hn20

/-- **NumeratorSoundness for cells 10-19**:
    For Q ∈ [n, n+1] with 10 ≤ n < 20, any finite set S of primes
    with log(p) ∈ [Q, Q+1] satisfies:
      Σ_{p∈S} log(p)/√p ≤ cellNumeratorStrong(n) -/
theorem numeratorSoundness_cells_10_to_19
    (n : ℕ) (hn : 10 ≤ n) (hn20 : n < 20) (Q : ℝ)
    (hQlo : (n : ℝ) ≤ Q) (hQhi : Q ≤ (n : ℝ) + 1)
    (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ Q ≤ Real.log ↑p ∧ Real.log ↑p < Q + 1) :
    (∑ p in S, Real.log ↑p / Real.sqrt ↑p) ≤ (cellNumeratorStrong n : ℝ) := by
  -- Step 1: bound each term and get sum ≤ |S| * (n+2)/99
  have h_bound : ∀ p ∈ S, Real.log ↑p / Real.sqrt ↑p ≤ ((n + 2 : ℕ) : ℝ) / 99 := by
    intro p hp
    obtain ⟨hp_prime, hpQlo, hpQhi⟩ := hS p hp
    exact term_bound_high_cell hn hn20 hQlo hQhi hp_prime hpQlo hpQhi
  have h_sum_le : (∑ p in S, Real.log ↑p / Real.sqrt ↑p) ≤
      S.card • (((n + 2 : ℕ) : ℝ) / 99) :=
    Finset.sum_le_card_nsmul S _ _ h_bound
  rw [nsmul_eq_mul] at h_sum_le
  -- Step 2: |S| * (n+2)/99 ≤ tailBoundQ(n)
  have h_card := card_S_le hn hn20 hQlo hQhi hS
  have h_ub := expUpperBound_gt_9974 n hn hn20
  -- tailBoundQ(n) = (expUpperBound(n+2) - 9974) * (n+2) / 99
  have h_tail_val : (tailBoundQ n : ℝ) =
      ((expUpperBound (n + 2) - 9974 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) / 99 := by
    unfold tailBoundQ
    simp only [show ¬ expUpperBound (n + 2) ≤ 9974 from by omega, ite_false]
    push_cast; ring
  -- |S|*(n+2)/99 ≤ (expUpperBound(n+2)-9974)*(n+2)/99 = tailBoundQ(n)
  have h_product : (S.card : ℝ) * (((n + 2 : ℕ) : ℝ) / 99) ≤ (tailBoundQ n : ℝ) := by
    rw [h_tail_val]
    have hcard_r : (S.card : ℝ) ≤ ((expUpperBound (n + 2) - 9974 : ℕ) : ℝ) := by
      exact_mod_cast h_card
    have hn2_pos : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) / 99 := by positivity
    calc (S.card : ℝ) * (((n + 2 : ℕ) : ℝ) / 99)
        ≤ ((expUpperBound (n + 2) - 9974 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) / 99) :=
          mul_le_mul_of_nonneg_right hcard_r hn2_pos
      _ = ((expUpperBound (n + 2) - 9974 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) / 99 := by ring
  -- Step 3: tailBoundQ(n) ≤ cellNumeratorStrong(n)
  linarith [tailBoundQ_le_cellNumeratorStrong n hn hn20]

end Goldbach.CompactZone
