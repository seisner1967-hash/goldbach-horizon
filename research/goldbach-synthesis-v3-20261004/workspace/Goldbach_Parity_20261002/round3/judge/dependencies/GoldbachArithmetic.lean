import GoldbachBridge
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction

/-!
# The actual Moebius-twisted arithmetic rows for Goldbach

This module instantiates the finite algebra with Mathlib's actual von Mangoldt,
Moebius and totient functions. The moving cofactor interval is strict and
excludes n = 0 and n = N. No analytic estimate for the off-diagonal is assumed
or proved. The statements remain finite identities and inequalities.
-/

namespace GoldbachResearch.ActualArithmetic

open scoped BigOperators
open ArithmeticBridge

def muReal (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℝ)

noncomputable def actualSequence (N n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * muReal (N - n)

/-- Inclusive modulus cap, with positive, coprime and squarefree support. -/
def actualModuli (N Q : ℕ) : Finset ℕ :=
  (Finset.range (Q + 1)).filter (fun k => 1 ≤ k ∧ k.Coprime N ∧ Squarefree k)

/-- Literal centered progression row, including the strict moving cutoff. -/
noncomputable def actualRow (N alpha k n : ℕ) : ℝ :=
  if 1 ≤ n ∧ n < N ∧ n < N - alpha * k then
    ((if k ∣ N - n then (1 : ℝ) else 0) - 1 / (Nat.totient k : ℝ)) *
      Real.log ((k : ℝ) / (N - n : ℕ))
  else 0

noncomputable def actualEpsilon (N alpha k : ℕ) : ℝ :=
  rowSum (Finset.range N) (actualSequence N) (actualRow N alpha) k

noncomputable def actualSignedError (N alpha Q : ℕ) : ℝ :=
  ∑ k ∈ actualModuli N Q, muReal k * actualEpsilon N alpha k

noncomputable def actualVariance (N alpha Q : ℕ) : ℝ :=
  ∑ k ∈ actualModuli N Q,
    (k : ℝ) * (muReal k) ^ 2 * (actualEpsilon N alpha k) ^ 2

noncomputable def actualDiagonal (N alpha Q : ℕ) : ℝ :=
  diagonal (actualModuli N Q) (Finset.range N) (fun k : ℕ => (k : ℝ))
    muReal (actualSequence N) (actualRow N alpha)

noncomputable def actualOffDiagonal (N alpha Q : ℕ) : ℝ :=
  offDiagonal (actualModuli N Q) (Finset.range N) (fun k : ℕ => (k : ℝ))
    muReal (actualSequence N) (actualRow N alpha)

noncomputable def actualKernel (N alpha Q n r : ℕ) : ℝ :=
  gramKernel (actualModuli N Q) (fun k : ℕ => (k : ℝ))
    muReal (actualRow N alpha) n r

theorem actualModuli_membership {N Q k : ℕ} :
    k ∈ actualModuli N Q ↔ k ≤ Q ∧ 1 ≤ k ∧ k.Coprime N ∧ Squarefree k := by
  simp only [actualModuli, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

theorem actual_modulus_positive {N Q k : ℕ} (hk : k ∈ actualModuli N Q) :
    0 < (k : ℝ) := by
  have h : 1 ≤ k := (actualModuli_membership.mp hk).2.1
  exact_mod_cast (show 0 < k by omega)

theorem actual_modulus_mu_sq_eq_one {N Q k : ℕ} (hk : k ∈ actualModuli N Q) :
    (muReal k) ^ 2 = 1 := by
  have hsq : Squarefree k := (actualModuli_membership.mp hk).2.2.2
  unfold muReal
  exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq

theorem actualRow_zero_at_zero (N alpha k : ℕ) : actualRow N alpha k 0 = 0 := by
  simp [actualRow]

theorem actualRow_zero_outside_target {N alpha k n : ℕ} (hn : N ≤ n) :
    actualRow N alpha k n = 0 := by
  simp [actualRow, not_lt.mpr hn]

theorem actualRow_zero_outside_moving_interval {N alpha k n : ℕ}
    (hn : N - alpha * k ≤ n) : actualRow N alpha k n = 0 := by
  simp [actualRow, not_lt.mpr hn]

/-- Every nonzero row has positive complementary integer and the strict cofactor inequality. -/
theorem actualRow_nonzero_support {N alpha k n : ℕ}
    (hh : actualRow N alpha k n ≠ 0) :
    1 ≤ n ∧ n < N ∧ n + alpha * k < N := by
  have hs : 1 ≤ n ∧ n < N ∧ n < N - alpha * k := by
    by_contra hs
    simp [actualRow, hs] at hh
  omega

/-- A strict moving cutoff excludes its endpoint exactly. -/
theorem actualRow_zero_at_moving_endpoint (N alpha k : ℕ) :
    actualRow N alpha k (N - alpha * k) = 0 := by
  exact actualRow_zero_outside_moving_interval le_rfl

theorem actualVariance_eq_variance (N alpha Q : ℕ) :
    actualVariance N alpha Q =
      variance (actualModuli N Q) (Finset.range N) (fun k : ℕ => (k : ℝ))
        muReal (actualSequence N) (actualRow N alpha) := rfl

/-- Cauchy for the literal von Mangoldt--Moebius rows, with no abstract a or h parameter. -/
theorem actualSignedError_sq_le_variance (N alpha Q : ℕ) :
    (actualSignedError N alpha Q) ^ 2 ≤
      (∑ k ∈ actualModuli N Q, 1 / (k : ℝ)) * actualVariance N alpha Q := by
  unfold actualSignedError actualVariance actualEpsilon
  exact signed_rows_sq_le_variance (actualModuli N Q) (Finset.range N)
    (fun k : ℕ => (k : ℝ)) muReal (actualSequence N) (actualRow N alpha)
    (fun k hk => actual_modulus_positive hk)

/-- The literal arithmetic variance includes every centered off-diagonal term. -/
theorem actualVariance_eq_diagonal_add_offDiagonal (N alpha Q : ℕ) :
    actualVariance N alpha Q = actualDiagonal N alpha Q + actualOffDiagonal N alpha Q := by
  rw [actualVariance_eq_variance]
  exact variance_eq_diagonal_add_offDiagonal (actualModuli N Q) (Finset.range N)
    (fun k : ℕ => (k : ℝ)) muReal (actualSequence N) (actualRow N alpha)

theorem actualVariance_eq_kernel (N alpha Q : ℕ) :
    actualVariance N alpha Q =
      ∑ n ∈ Finset.range N, ∑ r ∈ Finset.range N,
        actualSequence N n * actualSequence N r * actualKernel N alpha Q n r := by
  rw [actualVariance_eq_variance]
  exact variance_eq_gramKernel (actualModuli N Q) (Finset.range N)
    (fun k : ℕ => (k : ℝ)) muReal (actualSequence N) (actualRow N alpha)

theorem actualVariance_nonneg (N alpha Q : ℕ) : 0 ≤ actualVariance N alpha Q := by
  rw [actualVariance_eq_variance]
  exact variance_nonneg (actualModuli N Q) (Finset.range N)
    (fun k : ℕ => (k : ℝ)) muReal (actualSequence N) (actualRow N alpha)
    (fun k hk => le_of_lt (actual_modulus_positive hk))

theorem actualDiagonal_nonneg (N alpha Q : ℕ) : 0 ≤ actualDiagonal N alpha Q := by
  exact diagonal_nonneg (actualModuli N Q) (Finset.range N)
    (fun k : ℕ => (k : ℝ)) muReal (actualSequence N) (actualRow N alpha)
    (fun k hk => le_of_lt (actual_modulus_positive hk))

/-- Explicit finite budgets remain assumptions; no off-diagonal estimate is inserted. -/
theorem actualSignedError_sq_le_diagonal_off_budget (N alpha Q : ℕ) (d o : ℝ)
    (hd : actualDiagonal N alpha Q ≤ d) (ho : actualOffDiagonal N alpha Q ≤ o) :
    (actualSignedError N alpha Q) ^ 2 ≤
      (∑ k ∈ actualModuli N Q, 1 / (k : ℝ)) * (d + o) := by
  unfold actualSignedError actualEpsilon
  exact signed_rows_sq_le_diagonal_off_budget (actualModuli N Q) (Finset.range N)
    (fun k : ℕ => (k : ℝ)) muReal (actualSequence N) (actualRow N alpha)
    (fun k hk => actual_modulus_positive hk) d o hd ho

end GoldbachResearch.ActualArithmetic

#print axioms GoldbachResearch.ActualArithmetic.actualModuli_membership
#print axioms GoldbachResearch.ActualArithmetic.actual_modulus_positive
#print axioms GoldbachResearch.ActualArithmetic.actual_modulus_mu_sq_eq_one
#print axioms GoldbachResearch.ActualArithmetic.actualRow_zero_at_zero
#print axioms GoldbachResearch.ActualArithmetic.actualRow_zero_outside_target
#print axioms GoldbachResearch.ActualArithmetic.actualRow_zero_outside_moving_interval
#print axioms GoldbachResearch.ActualArithmetic.actualRow_nonzero_support
#print axioms GoldbachResearch.ActualArithmetic.actualRow_zero_at_moving_endpoint
#print axioms GoldbachResearch.ActualArithmetic.actualVariance_eq_variance
#print axioms GoldbachResearch.ActualArithmetic.actualSignedError_sq_le_variance
#print axioms GoldbachResearch.ActualArithmetic.actualVariance_eq_diagonal_add_offDiagonal
#print axioms GoldbachResearch.ActualArithmetic.actualVariance_eq_kernel
#print axioms GoldbachResearch.ActualArithmetic.actualVariance_nonneg
#print axioms GoldbachResearch.ActualArithmetic.actualDiagonal_nonneg
#print axioms GoldbachResearch.ActualArithmetic.actualSignedError_sq_le_diagonal_off_budget
