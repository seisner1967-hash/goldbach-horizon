import Mathlib.NumberTheory.LucasPrimality
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

/-! SOURCE ONLY. No author compilation, tactic probe or numerical evaluation.
Each primality claim uses Lucas's theorem in ZMod before any field instance is
available. Only the small factors of p-1 are proved prime by norm_num.
reduce_mod_char produces kernel-checkable modular exponentiation proofs.
Each exact order follows from the whole power and the nontrivial half power;
no primitive root, final projection identity, or primality is an input to any
concrete certificate. This module proves parameters only. It does not prove
machine butterflies, CRT reconstruction, Goldbach, a D_N bound, or a parity
improvement. The independently compiled projection will be imported only by a
separate downstream module with its read-only provenance bound by the Juge.
-/

namespace GoldbachConcreteNTTRoots22

def bankRoot (p g : ℕ) : ZMod p := (g : ZMod p) ^ ((p - 1) / (2 ^ 27))

theorem primitive_of_whole_and_half {M : Type*} [CommMonoid M] (ω : M)
    (hwhole : ω ^ (2 ^ 27) = 1) (hhalf : ω ^ (2 ^ 26) ≠ 1) :
    IsPrimitiveRoot ω (2 ^ 27) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf ω = 2 ^ 27 :=
    orderOf_eq_prime_pow (p := 2) (n := 26) hhalf hwhole
  simpa only [ho] using IsPrimitiveRoot.orderOf ω

theorem prime_divisor_two_power_mul_prime {q r e : ℕ}
    (hq : q.Prime) (hr : r.Prime) (h : q ∣ 2 ^ e * r) :
    q = 2 ∨ q = r := by
  rcases hq.dvd_mul.mp h with htwo | hrq
  · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two htwo)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq hr).mp hrq)

theorem prime_2013265921 : Nat.Prime 2013265921 := by
  refine lucas_primality 2013265921 (31 : ZMod 2013265921) ?_ ?_
  · reduce_mod_char
  · intro q hq hqd
    have hf : 2013265921 - 1 = 2 ^ 27 * 3 * 5 := by norm_num
    rw [hf] at hqd
    rcases hq.dvd_mul.mp hqd with h23 | h5
    · rcases prime_divisor_two_power_mul_prime hq (by norm_num : Nat.Prime 3) h23
        with rfl | rfl
      · intro h
        have hv := congrArg ZMod.val h
        reduce_mod_char at hv
        norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv
      · intro h
        have hv := congrArg ZMod.val h
        reduce_mod_char at hv
        norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv
    · have hq5 : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h5
      subst q
      intro h
      have hv := congrArg ZMod.val h
      reduce_mod_char at hv
      norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv

theorem prime_2281701377 : Nat.Prime 2281701377 := by
  refine lucas_primality 2281701377 (3 : ZMod 2281701377) ?_ ?_
  · reduce_mod_char
  · intro q hq hqd
    have hf : 2281701377 - 1 = 2 ^ 27 * 17 := by norm_num
    rw [hf] at hqd
    rcases prime_divisor_two_power_mul_prime hq (by norm_num : Nat.Prime 17) hqd
        with rfl | rfl
    · intro h
      have hv := congrArg ZMod.val h
      reduce_mod_char at hv
      norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv
    · intro h
      have hv := congrArg ZMod.val h
      reduce_mod_char at hv
      norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv

theorem prime_3221225473 : Nat.Prime 3221225473 := by
  refine lucas_primality 3221225473 (5 : ZMod 3221225473) ?_ ?_
  · reduce_mod_char
  · intro q hq hqd
    have hf : 3221225473 - 1 = 2 ^ 30 * 3 := by norm_num
    rw [hf] at hqd
    rcases prime_divisor_two_power_mul_prime hq (by norm_num : Nat.Prime 3) hqd
        with rfl | rfl
    · intro h
      have hv := congrArg ZMod.val h
      reduce_mod_char at hv
      norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv
    · intro h
      have hv := congrArg ZMod.val h
      reduce_mod_char at hv
      norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv

theorem prime_3489660929 : Nat.Prime 3489660929 := by
  refine lucas_primality 3489660929 (3 : ZMod 3489660929) ?_ ?_
  · reduce_mod_char
  · intro q hq hqd
    have hf : 3489660929 - 1 = 2 ^ 28 * 13 := by norm_num
    rw [hf] at hqd
    rcases prime_divisor_two_power_mul_prime hq (by norm_num : Nat.Prime 13) hqd
        with rfl | rfl
    · intro h
      have hv := congrArg ZMod.val h
      reduce_mod_char at hv
      norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv
    · intro h
      have hv := congrArg ZMod.val h
      reduce_mod_char at hv
      norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv

theorem prime_3892314113 : Nat.Prime 3892314113 := by
  refine lucas_primality 3892314113 (3 : ZMod 3892314113) ?_ ?_
  · reduce_mod_char
  · intro q hq hqd
    have hf : 3892314113 - 1 = 2 ^ 27 * 29 := by norm_num
    rw [hf] at hqd
    rcases prime_divisor_two_power_mul_prime hq (by norm_num : Nat.Prime 29) hqd
        with rfl | rfl
    · intro h
      have hv := congrArg ZMod.val h
      reduce_mod_char at hv
      norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv
    · intro h
      have hv := congrArg ZMod.val h
      reduce_mod_char at hv
      norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv

theorem primitive_2013265921 :
    IsPrimitiveRoot (bankRoot 2013265921 31) (2 ^ 27) := by
  unfold bankRoot
  have hc : (2013265921 - 1) / (2 ^ 27) = 15 := by norm_num
  rw [hc]
  apply primitive_of_whole_and_half
  · reduce_mod_char
  · intro h
    have hv := congrArg ZMod.val h
    reduce_mod_char at hv
    norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv

theorem primitive_2281701377 :
    IsPrimitiveRoot (bankRoot 2281701377 3) (2 ^ 27) := by
  unfold bankRoot
  have hc : (2281701377 - 1) / (2 ^ 27) = 17 := by norm_num
  rw [hc]
  apply primitive_of_whole_and_half
  · reduce_mod_char
  · intro h
    have hv := congrArg ZMod.val h
    reduce_mod_char at hv
    norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv

theorem primitive_3221225473 :
    IsPrimitiveRoot (bankRoot 3221225473 5) (2 ^ 27) := by
  unfold bankRoot
  have hc : (3221225473 - 1) / (2 ^ 27) = 24 := by norm_num
  rw [hc]
  apply primitive_of_whole_and_half
  · reduce_mod_char
  · intro h
    have hv := congrArg ZMod.val h
    reduce_mod_char at hv
    norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv

theorem primitive_3489660929 :
    IsPrimitiveRoot (bankRoot 3489660929 3) (2 ^ 27) := by
  unfold bankRoot
  have hc : (3489660929 - 1) / (2 ^ 27) = 26 := by norm_num
  rw [hc]
  apply primitive_of_whole_and_half
  · reduce_mod_char
  · intro h
    have hv := congrArg ZMod.val h
    reduce_mod_char at hv
    norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv

theorem primitive_3892314113 :
    IsPrimitiveRoot (bankRoot 3892314113 3) (2 ^ 27) := by
  unfold bankRoot
  have hc : (3892314113 - 1) / (2 ^ 27) = 29 := by norm_num
  rw [hc]
  apply primitive_of_whole_and_half
  · reduce_mod_char
  · intro h
    have hv := congrArg ZMod.val h
    reduce_mod_char at hv
    norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv

theorem size_2013265921 : (2 : ℕ) ^ 27 < 2013265921 := by norm_num
theorem size_2281701377 : (2 : ℕ) ^ 27 < 2281701377 := by norm_num
theorem size_3221225473 : (2 : ℕ) ^ 27 < 3221225473 := by norm_num
theorem size_3489660929 : (2 : ℕ) ^ 27 < 3489660929 := by norm_num
theorem size_3892314113 : (2 : ℕ) ^ 27 < 3892314113 := by norm_num

end GoldbachConcreteNTTRoots22

#print axioms GoldbachConcreteNTTRoots22.bankRoot
#print axioms GoldbachConcreteNTTRoots22.primitive_of_whole_and_half
#print axioms GoldbachConcreteNTTRoots22.prime_divisor_two_power_mul_prime
#print axioms GoldbachConcreteNTTRoots22.prime_2013265921
#print axioms GoldbachConcreteNTTRoots22.prime_2281701377
#print axioms GoldbachConcreteNTTRoots22.prime_3221225473
#print axioms GoldbachConcreteNTTRoots22.prime_3489660929
#print axioms GoldbachConcreteNTTRoots22.prime_3892314113
#print axioms GoldbachConcreteNTTRoots22.primitive_2013265921
#print axioms GoldbachConcreteNTTRoots22.primitive_2281701377
#print axioms GoldbachConcreteNTTRoots22.primitive_3221225473
#print axioms GoldbachConcreteNTTRoots22.primitive_3489660929
#print axioms GoldbachConcreteNTTRoots22.primitive_3892314113
#print axioms GoldbachConcreteNTTRoots22.size_2013265921
#print axioms GoldbachConcreteNTTRoots22.size_2281701377
#print axioms GoldbachConcreteNTTRoots22.size_3221225473
#print axioms GoldbachConcreteNTTRoots22.size_3489660929
#print axioms GoldbachConcreteNTTRoots22.size_3892314113
