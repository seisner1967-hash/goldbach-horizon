import FriableKernelEnvelope
import Mathlib.Data.Complex.ExponentialBounds

namespace GoldbachRound20.Friable

open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def inverseTotient : ArithmeticFunction ℝ :=
  ⟨fun n => (Nat.totient n : ℝ)⁻¹, by simp⟩

def weightedInverseTotient : ArithmeticFunction ℝ :=
  ⟨fun n => ((n : ℝ) * (Nat.totient n : ℝ))⁻¹, by simp⟩

theorem inverseTotient_multiplicative : inverseTotient.IsMultiplicative := by
  refine ⟨by simp [inverseTotient], ?_⟩
  intro m n h
  simp only [inverseTotient, ArithmeticFunction.coe_mk, Nat.totient_mul h, Nat.cast_mul, mul_inv_rev]
  ring

theorem weightedInverseTotient_multiplicative : weightedInverseTotient.IsMultiplicative := by
  refine ⟨by simp [weightedInverseTotient], ?_⟩
  intro m n h
  simp only [weightedInverseTotient, ArithmeticFunction.coe_mk, Nat.totient_mul h, Nat.cast_mul, mul_inv_rev]
  ring

theorem squarefree_divisor_sum_product {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors with Squarefree d, f d) =
      ∏ p ∈ n.primeFactors, (1 + f p) := by
  rw [Nat.sum_divisors_filter_squarefree hn, Nat.factors_eq, List.toFinset_coe, Nat.toFinset_factors]
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro t ht
  simpa only [Finset.prod_val] using hf.map_prod_of_subset_primeFactors n t (mem_powerset.mp ht)

theorem inverseTotient_prime (p : ℕ) (hp : p.Prime) :
    inverseTotient p = ((p : ℝ) - 1)⁻¹ := by
  simp only [inverseTotient, ArithmeticFunction.coe_mk, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le, Nat.cast_one]

theorem one_add_inverseTotient_prime (p : ℕ) (hp : p.Prime) :
    1 + inverseTotient p = (1 - (p : ℝ)⁻¹)⁻¹ := by
  rw [inverseTotient_prime p hp]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hh : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
    linarith
  field_simp [hpR.ne', hp1]

/-- The actual squarefree divisor identity underlying TK. -/
theorem nat_div_totient_squarefree_sum {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) / (Nat.totient n : ℝ) =
      ∑ d ∈ n.divisors with Squarefree d, (Nat.totient d : ℝ)⁻¹ := by
  have hp : (Nat.totient n : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have hh := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
      Rat.cast_one, Rat.cast_inv] using hh
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hprod : ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpr : 1 < (p : ℝ) := by exact_mod_cast hprime.one_lt
    have hinv : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by linarith : 0 < (p : ℝ))).mpr hpr
    linarith
  rw [show (∑ d ∈ n.divisors with Squarefree d, (Nat.totient d : ℝ)⁻¹) =
      ∏ p ∈ n.primeFactors, (1 + inverseTotient p) from
        squarefree_divisor_sum_product inverseTotient_multiplicative hn]
  have hratio : (n : ℝ) / (Nat.totient n : ℝ) =
      (∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ := by
    rw [hp, div_eq_mul_inv, mul_inv_rev]
    calc
      _ = ((n : ℝ) * (n : ℝ)⁻¹) *
          (∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ := by ring
      _ = _ := by rw [mul_inv_cancel₀ hnR, one_mul]
  rw [hratio]
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact (one_add_inverseTotient_prime p (Nat.prime_of_mem_primeFactors hp)).symm

def squarefreeUpTo (X : ℕ) : Finset ℕ := (Icc 1 X).filter Squarefree

/-- Positive Euler upper bound on an actual finite squarefree sum. -/
theorem squarefree_sum_le_prime_product (X : ℕ) {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hfpos : ∀ n, 0 ≤ f n) :
    (∑ d ∈ squarefreeUpTo X, f d) ≤
      ∏ p ∈ Nat.primesBelow (X + 1), (1 + f p) := by
  let S := squarefreeUpTo X
  have hsub : ∀ d ∈ S, d.primeFactors ⊆ Nat.primesBelow (X + 1) := by
    intro d hd p hp
    have hdX := (mem_Icc.mp (mem_filter.mp hd).1).2
    exact Nat.mem_primesBelow.mpr ⟨(Nat.le_of_mem_primeFactors hp).trans_lt (by omega),
      Nat.prime_of_mem_primeFactors hp⟩
  have hinj : Set.InjOn Nat.primeFactors S := by
    intro d hd e he hde
    have hsD := (mem_filter.mp hd).2
    have hsE := (mem_filter.mp he).2
    rw [← Nat.prod_primeFactors_of_squarefree hsD,
      ← Nat.prod_primeFactors_of_squarefree hsE, hde]
  have heq : (∑ d ∈ S, f d) =
      ∑ t ∈ S.image Nat.primeFactors, ∏ p ∈ t, f p := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← hf.map_prod_of_prime]
    · rw [Nat.prod_primeFactors_of_squarefree (mem_filter.mp hd).2]
    · intro p hp
      exact Nat.prime_of_mem_primeFactors hp
  calc
    _ = ∑ t ∈ S.image Nat.primeFactors, ∏ p ∈ t, f p := heq
    _ ≤ ∑ t ∈ (Nat.primesBelow (X + 1)).powerset, ∏ p ∈ t, f p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        obtain ⟨d, hd, rfl⟩ := mem_image.mp ht
        exact mem_powerset.mpr (hsub d hd)
      · intro t _ _
        exact Finset.prod_nonneg (fun p _ => hfpos p)
    _ = _ := (Finset.prod_one_add _).symm

theorem reciprocal_successive_sum (X : ℕ) (hX : 1 ≤ X) :
    (∑ j ∈ Icc 2 X, ((j : ℝ) * ((j : ℝ) - 1))⁻¹) = 1 - (X : ℝ)⁻¹ := by
  induction X with
  | zero => omega
  | succ X ih =>
      by_cases hX0 : X = 0
      · simp [hX0]
      have hp : 1 ≤ X := by omega
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ X + 1), ih hp]
      have hxR : (X : ℝ) ≠ 0 := by exact_mod_cast hX0
      have hx1 : (X : ℝ) + 1 ≠ 0 := by positivity
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp [hxR, hx1]
      ring

theorem squarefree_weighted_inverse_sum_le_three (X : ℕ) :
    (∑ d ∈ squarefreeUpTo X, ((d : ℝ) * (Nat.totient d : ℝ))⁻¹) ≤ 3 := by
  have hh := squarefree_sum_le_prime_product X weightedInverseTotient_multiplicative
    (fun n => by simp only [weightedInverseTotient, ArithmeticFunction.coe_mk]; positivity)
  have hlocal : ∀ p ∈ Nat.primesBelow (X + 1),
      weightedInverseTotient p = ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
    intro p hp
    simp only [weightedInverseTotient, ArithmeticFunction.coe_mk, Nat.totient_prime (Nat.prime_of_mem_primesBelow hp),
      Nat.cast_sub (Nat.prime_of_mem_primesBelow hp).one_le, Nat.cast_one]
  have hsum : (∑ p ∈ Nat.primesBelow (X + 1), weightedInverseTotient p) ≤ 1 := by
    calc
      _ ≤ ∑ j ∈ Icc 2 X, ((j : ℝ) * ((j : ℝ) - 1))⁻¹ := by
        have hsub : Nat.primesBelow (X + 1) ⊆ Icc 2 X := by
          intro p hp
          have hprime := Nat.prime_of_mem_primesBelow hp
          have hlt := Nat.lt_of_mem_primesBelow hp
          exact mem_Icc.mpr ⟨hprime.two_le, by omega⟩
        calc
          _ = ∑ p ∈ Nat.primesBelow (X + 1), ((p : ℝ) * ((p : ℝ) - 1))⁻¹ :=
            Finset.sum_congr rfl hlocal
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j hj _ => by
              have hj2 := (mem_Icc.mp hj).1
              have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
              have : 0 ≤ (j : ℝ) - 1 := by linarith
              positivity)
      _ ≤ 1 := by
        by_cases hX : X = 0
        · simp [hX]
        · rw [reciprocal_successive_sum X (by omega)]
          have hp : 0 ≤ (X : ℝ)⁻¹ := by positivity
          linarith
  calc
    _ ≤ ∏ p ∈ Nat.primesBelow (X + 1), (1 + weightedInverseTotient p) := hh
    _ ≤ ∏ p ∈ Nat.primesBelow (X + 1), Real.exp (weightedInverseTotient p) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpos : 0 ≤ weightedInverseTotient p := by
          simp only [weightedInverseTotient, ArithmeticFunction.coe_mk]; positivity
        linarith
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (weightedInverseTotient p)
    _ = Real.exp (∑ p ∈ Nat.primesBelow (X + 1), weightedInverseTotient p) :=
      (Real.exp_sum _ _).symm
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hsum
    _ ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)

/-- Every multiple is injected into its physical quotient; no residue front is erased. -/
theorem multiples_inverse_sum_le_harmonic {d X : ℕ} (hd : 1 ≤ d) :
    (∑ n ∈ (Icc 1 X).filter (fun n => d ∣ n), (n : ℝ)⁻¹) ≤
      (d : ℝ)⁻¹ * (harmonic X : ℝ) := by
  let S := (Icc 1 X).filter (fun n => d ∣ n)
  have hinj : Set.InjOn (fun n : ℕ => n / d) S := by
    intro n hn m hm he
    have hn' := Nat.div_mul_cancel (mem_filter.mp hn).2
    have hm' := Nat.div_mul_cancel (mem_filter.mp hm).2
    change n / d = m / d at he
    rw [← hn', ← hm', he]
  have hsub : S.image (fun n => n / d) ⊆ Icc 1 X := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
    have hn1 := (mem_Icc.mp (mem_filter.mp hn).1).1
    have hnX := (mem_Icc.mp (mem_filter.mp hn).1).2
    have hdn := Nat.le_of_dvd (by omega : 0 < n) (mem_filter.mp hn).2
    exact mem_Icc.mpr ⟨Nat.div_pos hdn (by omega), (Nat.div_le_self n d).trans hnX⟩
  have he : (∑ n ∈ S, (n : ℝ)⁻¹) =
      (d : ℝ)⁻¹ * ∑ k ∈ S.image (fun n => n / d), (k : ℝ)⁻¹ := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : (n / d) * d = n := Nat.div_mul_cancel (mem_filter.mp hn).2
    conv_lhs => rw [← hn', Nat.cast_mul, mul_inv_rev]
  calc
    _ = (d : ℝ)⁻¹ * ∑ k ∈ S.image (fun n => n / d), (k : ℝ)⁻¹ := he
    _ ≤ (d : ℝ)⁻¹ * ∑ k ∈ Icc 1 X, (k : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
        (by positivity)
    _ = _ := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem inverseTotient_interval_expansion {X n : ℕ} (hn : n ∈ Icc 1 X) :
    (Nat.totient n : ℝ)⁻¹ = (n : ℝ)⁻¹ *
      ∑ d ∈ Icc 1 X, if Squarefree d ∧ d ∣ n then (Nat.totient d : ℝ)⁻¹ else 0 := by
  have hn1 := (mem_Icc.mp hn).1
  have hnX := (mem_Icc.mp hn).2
  have hn0 : n ≠ 0 := by omega
  have hset : ((Icc 1 X).filter (fun d => Squarefree d ∧ d ∣ n)) =
      n.divisors.filter Squarefree := by
    ext d
    constructor
    · intro hd
      have hs := (mem_filter.mp hd).2
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hs.2, hn0⟩, hs.1⟩
    · intro hd
      have hdiv := (mem_filter.mp hd).1
      exact mem_filter.mpr ⟨mem_Icc.mpr
        ⟨Nat.pos_of_mem_divisors hdiv, (Nat.divisor_le hdiv).trans hnX⟩,
        (mem_filter.mp hd).2, (Nat.mem_divisors.mp hdiv).1⟩
  have hsum : (∑ d ∈ Icc 1 X, if Squarefree d ∧ d ∣ n then (Nat.totient d : ℝ)⁻¹ else 0) =
      (n : ℝ) / (Nat.totient n : ℝ) := by
    rw [← Finset.sum_filter, hset]
    exact (nat_div_totient_squarefree_sum hn0).symm
  rw [hsum, div_eq_mul_inv, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hn0 : (n : ℝ) ≠ 0), one_mul]

/-- Elementary uniform TK, derived from actual divisors and finite positive Euler sums. -/
theorem totient_inverse_sum_le_three_one_add_log (X : ℕ) :
    totientInverseSum X ≤ 3 * (1 + Real.log (X : ℝ)) := by
  by_cases hX0 : X = 0
  · simp [totientInverseSum, hX0]
  have hX : 1 ≤ X := by omega
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hexp : totientInverseSum X =
      ∑ d ∈ Icc 1 X, ∑ n ∈ Icc 1 X, (n : ℝ)⁻¹ *
        (if Squarefree d ∧ d ∣ n then (Nat.totient d : ℝ)⁻¹ else 0) := by
    unfold totientInverseSum
    have he : (∑ n ∈ Icc 1 X, (Nat.totient n : ℝ)⁻¹) =
        ∑ n ∈ Icc 1 X, (n : ℝ)⁻¹ *
          ∑ d ∈ Icc 1 X,
            if Squarefree d ∧ d ∣ n then (Nat.totient d : ℝ)⁻¹ else 0 :=
      Finset.sum_congr rfl (fun n hn => inverseTotient_interval_expansion hn)
    rw [he]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hpoint : ∀ d ∈ Icc 1 X,
      (∑ n ∈ Icc 1 X, (n : ℝ)⁻¹ *
        (if Squarefree d ∧ d ∣ n then (Nat.totient d : ℝ)⁻¹ else 0)) ≤
      if Squarefree d then ((d : ℝ) * (Nat.totient d : ℝ))⁻¹ *
        (1 + Real.log (X : ℝ)) else 0 := by
    intro d hd
    by_cases hs : Squarefree d
    · rw [if_pos hs]
      have he : (∑ n ∈ Icc 1 X, (n : ℝ)⁻¹ *
          (if Squarefree d ∧ d ∣ n then (Nat.totient d : ℝ)⁻¹ else 0)) =
          (Nat.totient d : ℝ)⁻¹ *
            ∑ n ∈ (Icc 1 X).filter (fun n => d ∣ n), (n : ℝ)⁻¹ := by
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hv : d ∣ n <;> simp [hs, hv, mul_comm]
      rw [he]
      have hm := multiples_inverse_sum_le_harmonic (X := X) (mem_Icc.mp hd).1
      have hh := harmonic_le_one_add_log X
      have hphi : 0 ≤ (Nat.totient d : ℝ)⁻¹ := by positivity
      calc
        _ ≤ (Nat.totient d : ℝ)⁻¹ * ((d : ℝ)⁻¹ * (harmonic X : ℝ)) :=
          mul_le_mul_of_nonneg_left hm hphi
        _ ≤ (Nat.totient d : ℝ)⁻¹ * ((d : ℝ)⁻¹ * (1 + Real.log (X : ℝ))) := by
          apply mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hh (by positivity)) hphi
        _ = _ := by rw [mul_inv_rev]; ring
    · simp [hs]
  calc
    _ = ∑ d ∈ Icc 1 X, ∑ n ∈ Icc 1 X, (n : ℝ)⁻¹ *
        (if Squarefree d ∧ d ∣ n then (Nat.totient d : ℝ)⁻¹ else 0) := hexp
    _ ≤ ∑ d ∈ Icc 1 X,
        if Squarefree d then ((d : ℝ) * (Nat.totient d : ℝ))⁻¹ *
          (1 + Real.log (X : ℝ)) else 0 := Finset.sum_le_sum hpoint
    _ = (1 + Real.log (X : ℝ)) *
        ∑ d ∈ squarefreeUpTo X, ((d : ℝ) * (Nat.totient d : ℝ))⁻¹ := by
      simp only [squarefreeUpTo, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hs : Squarefree d <;> simp [hs, mul_comm]
    _ ≤ (1 + Real.log (X : ℝ)) * 3 :=
      mul_le_mul_of_nonneg_left (squarefree_weighted_inverse_sum_le_three X) (by linarith)
    _ = _ := by ring

theorem actual_TotientSumBound (X : ℕ) : TotientSumBound X :=
  totient_inverse_sum_le_three_one_add_log X

/-- The provisional TK input is discharged by the uniform elementary theorem. -/
theorem actual_harmonicKernel_abs_unconditional {Q a N n m : ℕ}
    (ha : 1 ≤ a) (hm : 0 < m) (hmN : m ≤ N) (hQN : Q ≤ N) :
    |GoldbachRound11.harmonicKernel Q a N n m| ≤
      3 * Real.log (N : ℝ) * (1 + Real.log (N : ℝ)) :=
  actual_harmonicKernel_abs_of_TotientSumBound ha hm hmN hQN (actual_TotientSumBound N)

#print axioms inverseTotient
#print axioms weightedInverseTotient
#print axioms inverseTotient_multiplicative
#print axioms weightedInverseTotient_multiplicative
#print axioms squarefree_divisor_sum_product
#print axioms inverseTotient_prime
#print axioms one_add_inverseTotient_prime
#print axioms nat_div_totient_squarefree_sum
#print axioms squarefreeUpTo
#print axioms squarefree_sum_le_prime_product
#print axioms reciprocal_successive_sum
#print axioms squarefree_weighted_inverse_sum_le_three
#print axioms multiples_inverse_sum_le_harmonic
#print axioms inverseTotient_interval_expansion
#print axioms totient_inverse_sum_le_three_one_add_log
#print axioms actual_TotientSumBound
#print axioms actual_harmonicKernel_abs_unconditional

end
end GoldbachRound20.Friable
