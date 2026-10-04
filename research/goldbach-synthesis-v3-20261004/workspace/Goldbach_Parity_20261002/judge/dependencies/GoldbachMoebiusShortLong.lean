import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic

/-!
Actual short/long Moebius splitting in the Dirichlet-convolution ring.
Finite exact identities and support only. No analytic cancellation axiom.
-/

namespace GoldbachResearch.MoebiusShortLong

open scoped BigOperators
open ArithmeticFunction Finset

def shortMoebius (y : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≤ y then ArithmeticFunction.moebius n else 0, by simp⟩

def longMoebius (y : ℕ) : ArithmeticFunction ℤ :=
  ArithmeticFunction.moebius - shortMoebius y

def shortDouble (y : ℕ) : ArithmeticFunction ℤ :=
  shortMoebius y * shortMoebius y * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)

def longDouble (y : ℕ) : ArithmeticFunction ℤ :=
  longMoebius y * longMoebius y * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)

@[simp] theorem short_apply (y n : ℕ) :
    shortMoebius y n = if n ≤ y then ArithmeticFunction.moebius n else 0 := rfl

theorem short_apply_of_le {y n : ℕ} (hn : n ≤ y) :
    shortMoebius y n = ArithmeticFunction.moebius n := by simp [hn]

theorem short_apply_of_gt {y n : ℕ} (hn : y < n) :
    shortMoebius y n = 0 := by simp [Nat.not_le.mpr hn]

theorem long_apply_of_le {y n : ℕ} (hn : n ≤ y) :
    longMoebius y n = 0 := by
  change ArithmeticFunction.moebius n - shortMoebius y n = 0
  simp [hn]

theorem long_apply_of_gt {y n : ℕ} (hn : y < n) :
    longMoebius y n = ArithmeticFunction.moebius n := by
  change ArithmeticFunction.moebius n - shortMoebius y n = ArithmeticFunction.moebius n
  simp [Nat.not_le.mpr hn]

theorem convolution_vanishes_below {f g : ArithmeticFunction ℤ} {A B n : ℕ}
    (hf : ∀ m < A, f m = 0) (hg : ∀ m < B, g m = 0) (hn : n < A * B) :
    (f * g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases ha : p.1 < A
  · simp [hf p.1 ha]
  · have hb : p.2 < B := by
      by_contra hb
      have hle := Nat.mul_le_mul (Nat.le_of_not_gt ha) (Nat.le_of_not_gt hb)
      rw [hprod] at hle
      omega
    simp [hg p.2 hb]

theorem convolution_with_arbitrary_preserves_vanishing
    {f g : ArithmeticFunction ℤ} {A n : ℕ}
    (hf : ∀ m < A, f m = 0) (hn : n < A) : (f * g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hp).1
  have hp2 := Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp)
  have hle : p.1 ≤ n := by
    calc
      p.1 = p.1 * 1 := by simp
      _ ≤ p.1 * p.2 := Nat.mul_le_mul_left p.1 hp2
      _ = n := hprod
  simp [hf p.1 (lt_of_le_of_lt hle hn)]

theorem long_double_support {y n : ℕ} (hn : n < (y + 1) ^ 2) :
    longDouble y n = 0 := by
  unfold longDouble
  apply convolution_with_arbitrary_preserves_vanishing (A := (y + 1) ^ 2)
  · intro m hm
    apply convolution_vanishes_below (A := y + 1) (B := y + 1)
    · intro t ht
      exact long_apply_of_le (by omega)
    · intro t ht
      exact long_apply_of_le (by omega)
    · simpa [pow_two] using hm
  · exact hn

theorem algebraic_short_long_identity (M : ArithmeticFunction ℤ) :
    ArithmeticFunction.moebius =
      2 * M - M * M * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) +
      (ArithmeticFunction.moebius - M) * (ArithmeticFunction.moebius - M) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℤ) := by
  have hinv := ArithmeticFunction.moebius_mul_coe_zeta
  linear_combination (2 * M - ArithmeticFunction.moebius) * hinv

theorem moebius_short_long (y : ℕ) :
    ArithmeticFunction.moebius = 2 * shortMoebius y - shortDouble y + longDouble y := by
  simpa [shortDouble, longDouble, longMoebius] using
    algebraic_short_long_identity (shortMoebius y)

theorem moebius_long_region {y n : ℕ} (hn : y < n) :
    ArithmeticFunction.moebius n = -shortDouble y n + longDouble y n := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) (moebius_short_long y)
  have htwo : (2 * shortMoebius y) n = 2 * shortMoebius y n := by
    have htwo' : (2 : ArithmeticFunction ℤ) = 1 + 1 := by norm_num
    rw [htwo', add_mul]
    simp only [one_mul, ArithmeticFunction.add_apply]
    ring
  change ArithmeticFunction.moebius n =
    (2 * shortMoebius y) n - shortDouble y n + longDouble y n at h
  rw [htwo, short_apply_of_gt hn] at h
  simpa using h

theorem long_double_of_no_long_divisor {y n : ℕ}
    (hn : ∀ u v : ℕ, y < u → y < v → ¬ u * v ∣ n) :
    longDouble y n = 0 := by
  unfold longDouble
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hpdvd : p.1 ∣ n := ⟨p.2, (Nat.mem_divisorsAntidiagonal.mp hp).1.symm⟩
  have hinner : (longMoebius y * longMoebius y) p.1 = 0 := by
    rw [ArithmeticFunction.mul_apply]
    apply Finset.sum_eq_zero
    intro q hq
    by_cases hu : q.1 ≤ y
    · simp [long_apply_of_le hu]
    · have hv : q.2 ≤ y := by
        by_contra hv
        have hprod := (Nat.mem_divisorsAntidiagonal.mp hq).1
        apply hn q.1 q.2 (Nat.lt_of_not_ge hu) (Nat.lt_of_not_ge hv)
        simpa only [hprod] using hpdvd
      simp [long_apply_of_le hv]
  simp [hinner]

theorem long_double_prime {y p : ℕ} (hy : 1 ≤ y) (hp : p.Prime) :
    longDouble y p = 0 := by
  apply long_double_of_no_long_divisor
  intro u v hu hv hdiv
  have hudvd : u ∣ p := dvd_trans (dvd_mul_right u v) hdiv
  rcases hp.eq_one_or_self_of_dvd u hudvd with huone | hup
  · omega
  · subst u
    have hle : p * v ≤ p := Nat.le_of_dvd hp.pos hdiv
    have hpp := hp.two_le
    have hvv : 2 ≤ v := by omega
    nlinarith

theorem short_double_prime {y p : ℕ} (hy : 1 ≤ y) (hp : p.Prime) (hpy : y < p) :
    shortDouble y p = 1 := by
  have h := moebius_long_region hpy
  rw [long_double_prime hy hp, ArithmeticFunction.moebius_apply_prime hp] at h
  linarith

theorem long_region_product {ya yr a r : ℕ} (ha : ya < a) (hr : yr < r) :
    ArithmeticFunction.moebius a * ArithmeticFunction.moebius r =
      shortDouble ya a * shortDouble yr r - shortDouble ya a * longDouble yr r -
      longDouble ya a * shortDouble yr r + longDouble ya a * longDouble yr r := by
  rw [moebius_long_region ha, moebius_long_region hr]
  ring

#print axioms short_apply
#print axioms short_apply_of_le
#print axioms short_apply_of_gt
#print axioms long_apply_of_le
#print axioms long_apply_of_gt
#print axioms convolution_vanishes_below
#print axioms convolution_with_arbitrary_preserves_vanishing
#print axioms long_double_support
#print axioms algebraic_short_long_identity
#print axioms moebius_short_long
#print axioms moebius_long_region
#print axioms long_double_of_no_long_divisor
#print axioms long_double_prime
#print axioms short_double_prime
#print axioms long_region_product

end GoldbachResearch.MoebiusShortLong
