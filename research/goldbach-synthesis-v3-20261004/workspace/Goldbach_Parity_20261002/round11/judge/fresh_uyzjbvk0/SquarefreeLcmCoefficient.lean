import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact finite AP coefficient B6. No estimate on a coupled prime moment is assumed. -/
namespace GoldbachRound11

open Finset

theorem totient_square (d : ℕ) : Nat.totient (d ^ 2) = d * Nat.totient d := by
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.primeFactors_pow d (by decide),
    Nat.totient_eq_div_primeFactors_mul d, pow_two,
    Nat.mul_div_assoc d (Nat.prod_primeFactors_dvd d)]
  ring

theorem totient_gcd_lcm {a b : ℕ} (ha : 0 < a) :
    Nat.totient (Nat.gcd a b) * Nat.totient (Nat.lcm a b) =
      Nat.totient a * Nat.totient b := by
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hdiv : Nat.gcd a b ∣ Nat.lcm a b :=
    (Nat.gcd_dvd_left a b).trans (Nat.dvd_lcm_left a b)
  have hx := Nat.totient_gcd_mul_totient_mul a b
  have hy := Nat.totient_gcd_mul_totient_mul (Nat.gcd a b) (Nat.lcm a b)
  rw [Nat.gcd_eq_left hdiv, Nat.gcd_mul_lcm] at hy
  nlinarith

theorem gcd_square_of_squarefree {r d : ℕ} (hr : Squarefree r) :
    Nat.gcd r (d ^ 2) = Nat.gcd r d := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left r (d ^ 2))
    exact ((hr.squarefree_of_dvd (Nat.gcd_dvd_left r (d ^ 2))).dvd_pow_iff_dvd
      (by decide)).mp (Nat.gcd_dvd_right r (d ^ 2))
  · exact Nat.dvd_gcd (Nat.gcd_dvd_left r d)
      ((Nat.gcd_dvd_right r d).trans (dvd_pow_self d (by decide)))

/-- A genuine multiplicative arithmetic coefficient, not a free model. -/
noncomputable def normalized (r : ℕ) : ArithmeticFunction ℚ :=
  ⟨fun d => (ArithmeticFunction.moebius d : ℚ) * (Nat.totient (Nat.gcd r d) : ℚ) /
    ((d : ℚ) * (Nat.totient d : ℚ)), by simp⟩

theorem normalized_isMultiplicative (r : ℕ) : (normalized r).IsMultiplicative := by
  refine ⟨by simp [normalized], ?_⟩
  intro m n h
  have hgc : Nat.Coprime (Nat.gcd r m) (Nat.gcd r n) := h.gcd_both r r
  simp only [normalized, ArithmeticFunction.coe_mk, ZeroHom.coe_mk,
    h.gcd_mul r, Nat.totient_mul h, Nat.totient_mul hgc,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h,
    Nat.cast_mul, Int.cast_mul, div_eq_mul_inv, mul_inv_rev]
  ring

theorem normalized_eq_lcm {r d : ℕ} (hr : Squarefree r) (hd : 0 < d) :
    normalized r d = (Nat.totient r : ℚ) *
      ((ArithmeticFunction.moebius d : ℚ) / (Nat.totient (Nat.lcm r (d ^ 2)) : ℚ)) := by
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  have hn := totient_gcd_lcm (b := d ^ 2) hrpos
  rw [gcd_square_of_squarefree hr, totient_square] at hn
  have hq : (Nat.totient (Nat.gcd r d) : ℚ) * (Nat.totient (Nat.lcm r (d ^ 2)) : ℚ) =
      (Nat.totient r : ℚ) * ((d : ℚ) * (Nat.totient d : ℚ)) := by exact_mod_cast hn
  have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  have hdphi : (Nat.totient d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.totient_pos.mpr hd))
  have hlpos : 0 < Nat.lcm r (d ^ 2) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have h := Nat.gcd_mul_lcm r (d ^ 2)
    rw [hz, mul_zero] at h
    exact (mul_ne_zero hr.ne_zero (pow_ne_zero 2 (Nat.ne_of_gt hd))) h.symm
  have hlphi : (Nat.totient (Nat.lcm r (d ^ 2)) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.totient_pos.mpr hlpos))
  have hm := congrArg (fun x : ℚ => (ArithmeticFunction.moebius d : ℚ) * x) hq
  dsimp only at hm
  simp only [normalized, ArithmeticFunction.coe_mk, ZeroHom.coe_mk]
  field_simp
  nlinarith

theorem normalized_prime {r p : ℕ} (hp : Nat.Prime p) :
    normalized r p = if p ∣ r then -(1 / (p : ℚ)) else
      -(1 / ((p : ℚ) * ((p : ℚ) - 1))) := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hp1 : (p : ℚ) - 1 ≠ 0 := by
    have h : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
    linarith
  by_cases h : p ∣ r
  · rw [if_pos h]
    simp only [normalized, ArithmeticFunction.coe_mk, ZeroHom.coe_mk,
      Nat.gcd_eq_right h, ArithmeticFunction.moebius_apply_prime hp,
      Nat.totient_prime hp, Int.cast_neg, Int.cast_one, Nat.cast_sub hp.one_le, Nat.cast_one]
    field_simp
    ring
  · rw [if_neg h]
    have hgc : Nat.gcd r p = 1 := (hp.coprime_iff_not_dvd.mpr h).symm.gcd_eq_one
    simp only [normalized, ArithmeticFunction.coe_mk, ZeroHom.coe_mk, hgc,
      Nat.totient_one, ArithmeticFunction.moebius_apply_prime hp, Int.cast_neg, Int.cast_one,
      Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
    ring

theorem primeFactors_filter_dvd {P r : ℕ} (hP : P ≠ 0) (hr : r ≠ 0) (hrP : r ∣ P) :
    P.primeFactors.filter (fun p => p ∣ r) = r.primeFactors := by
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors_of_ne_zero hP,
    Nat.mem_primeFactors_of_ne_zero hr]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hrP⟩, h.2⟩⟩

/-- B6: the actual finite Möbius/totient/lcm coefficient. -/
theorem squarefree_lcm_coefficient {P r : ℕ} (hP : Squarefree P) (hrP : r ∣ P) :
    (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℚ) /
        (Nat.totient (Nat.lcm r (d ^ 2)) : ℚ)) =
      (1 / (r : ℚ)) * ∏ p ∈ P.primeFactors.filter (fun p => ¬ p ∣ r),
        (1 - 1 / ((p : ℚ) * ((p : ℚ) - 1))) := by
  classical
  have hr : Squarefree r := hP.squarefree_of_dvd hrP
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne_zero
  have hrphi : (Nat.totient r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hr.ne_zero)))
  have hprod : (∏ p ∈ r.primeFactors, (1 - 1 / (p : ℚ))) =
      (Nat.totient r : ℚ) / (r : ℚ) := by
    have h := Nat.totient_eq_mul_prod_factors r
    simp only [inv_eq_one_div] at h
    apply (eq_div_iff hr0).mpr
    simpa [mul_comm] using h.symm
  have hsum : (Nat.totient r : ℚ) *
      (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℚ) /
        (Nat.totient (Nat.lcm r (d ^ 2)) : ℚ)) =
      ∏ p ∈ P.primeFactors, (1 + normalized r p) := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ d ∈ P.divisors, normalized r d := by
        apply Finset.sum_congr rfl
        intro d hd
        exact (normalized_eq_lcm hr (Nat.pos_of_mem_divisors hd)).symm
      _ = _ := (normalized_isMultiplicative r).prodPrimeFactors_one_add_of_squarefree hP |>.symm
  have hlocal : (∏ p ∈ P.primeFactors, (1 + normalized r p)) =
      (Nat.totient r : ℚ) / (r : ℚ) *
        ∏ p ∈ P.primeFactors.filter (fun p => ¬ p ∣ r),
          (1 - 1 / ((p : ℚ) * ((p : ℚ) - 1))) := by
    calc
      _ = ∏ p ∈ P.primeFactors, if p ∣ r then (1 - 1 / (p : ℚ)) else
          (1 - 1 / ((p : ℚ) * ((p : ℚ) - 1))) := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [normalized_prime (Nat.prime_of_mem_primeFactors hp)]
        split_ifs <;> ring
      _ = _ := by
        rw [Finset.prod_ite, primeFactors_filter_dvd hP.ne_zero hr.ne_zero hrP, hprod]
  rw [hlocal] at hsum
  apply (mul_left_cancel₀ hrphi)
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hsum

/-- The reference's exterior unit mask is separate from the generic B6 coefficient. -/
theorem squarefree_lcm_coefficient_unit {P r N : ℕ}
    (hP : Squarefree P) (hrP : r ∣ P) (hunit : Nat.Coprime P N) :
    (if Nat.gcd r N = 1 then
      (∑ d ∈ P.divisors.filter (fun d => Nat.gcd d N = 1), (ArithmeticFunction.moebius d : ℚ) /
        (Nat.totient (Nat.lcm r (d ^ 2)) : ℚ)) else 0) =
      (1 / (r : ℚ)) * ∏ p ∈ P.primeFactors.filter (fun p => ¬ p ∣ r),
        (1 - 1 / ((p : ℚ) * ((p : ℚ) - 1))) := by
  have hf : P.divisors.filter (fun d => Nat.gcd d N = 1) = P.divisors := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact (hunit.coprime_dvd_left (Nat.dvd_of_mem_divisors hd)).gcd_eq_one
  rw [if_pos (hunit.coprime_dvd_left hrP).gcd_eq_one]
  rw [hf]
  exact squarefree_lcm_coefficient hP hrP

end GoldbachRound11

#print axioms GoldbachRound11.totient_square
#print axioms GoldbachRound11.totient_gcd_lcm
#print axioms GoldbachRound11.gcd_square_of_squarefree
#print axioms GoldbachRound11.normalized_isMultiplicative
#print axioms GoldbachRound11.normalized_eq_lcm
#print axioms GoldbachRound11.normalized_prime
#print axioms GoldbachRound11.primeFactors_filter_dvd
#print axioms GoldbachRound11.squarefree_lcm_coefficient
#print axioms GoldbachRound11.squarefree_lcm_coefficient_unit


#print axioms GoldbachRound11.totient_square
#print axioms GoldbachRound11.totient_gcd_lcm
#print axioms GoldbachRound11.gcd_square_of_squarefree
#print axioms GoldbachRound11.normalized_isMultiplicative
#print axioms GoldbachRound11.normalized_eq_lcm
#print axioms GoldbachRound11.normalized_prime
#print axioms GoldbachRound11.primeFactors_filter_dvd
#print axioms GoldbachRound11.squarefree_lcm_coefficient
#print axioms GoldbachRound11.squarefree_lcm_coefficient_unit
