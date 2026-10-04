import ThreeAdicPrimePairing

namespace GoldbachRound13.HarmonicKernelVariation

open Finset GoldbachRound10.ShortDivisorComplement GoldbachRound11

noncomputable def unitCoefficient (N k : ℕ) : ℝ :=
  if k.Coprime N then mu k / (Nat.totient k : ℝ) else 0

noncomputable def unitPrefix (N R : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 R, unitCoefficient N k

noncomputable def unitLogPrefix (N R m : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 R, unitCoefficient N k * Real.log ((k : ℝ) / (m : ℝ))

noncomputable def unitLogTail (N R₁ R₀ m : ℕ) : ℝ :=
  ∑ k ∈ Icc (R₁ + 1) R₀, unitCoefficient N k * Real.log ((k : ℝ) / (m : ℝ))

def sourceFront (Q a m : ℕ) : ℕ := min Q ((m - 1) / a)

theorem prime_above_cap_units {Q N n k : ℕ} (hn : n.Prime)
    (hQn : Q < n) (hk : k ∈ Icc 1 Q) :
    k.Coprime (n * N) ↔ k.Coprime N := by
  obtain ⟨hkpos, hkQ⟩ := mem_Icc.mp hk
  have hkn : k.Coprime n :=
    (hn.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt hkpos (lt_of_le_of_lt hkQ hQn))).symm
  simp [Nat.coprime_mul_iff_right, hkn]

theorem strict_front_iff {a m k : ℕ} (ha : 0 < a) (hm : 0 < m) :
    a * k < m ↔ k ≤ (m - 1) / a := by
  rw [Nat.le_div_iff_mul_le ha]
  rw [Nat.mul_comm k a]
  omega

theorem front_filter_eq {Q a m : ℕ} (ha : 0 < a) (hm : 0 < m) :
    (Icc 1 Q).filter (fun k => a * k < m) = Icc 1 (sourceFront Q a m) := by
  ext k
  simp only [mem_filter, mem_Icc, sourceFront, le_min_iff]
  rw [strict_front_iff ha hm]
  omega

/-- The literal prime-axis harmonic kernel, not a free model function. -/
theorem actual_kernel_eq_prefix {Q a N n m : ℕ} (ha : 0 < a) (hm : 0 < m)
    (hn : n.Prime) (hQn : Q < n) :
    harmonicKernel Q a N n m = unitLogPrefix N (sourceFront Q a m) m := by
  classical
  unfold harmonicKernel unitLogPrefix
  rw [← front_filter_eq ha hm, sum_filter]
  apply sum_congr rfl
  intro k hk
  have hmask := prime_above_cap_units hn hQn hk
  by_cases hf : a * k < m <;> by_cases hu : k.Coprime N
  · simp [hf, hu, hmask, unitCoefficient]
    ring
  · simp [hf, hu, hmask, unitCoefficient]
  · simp [hf]
  · simp [hf]

theorem source_front_mono {Q a m₁ m₀ : ℕ} (hm : m₁ ≤ m₀) :
    sourceFront Q a m₁ ≤ sourceFront Q a m₀ := by
  exact min_le_min_left Q (Nat.div_le_div_right (Nat.sub_le_sub_right hm 1))

theorem source_cap_inactive {N alpha a m : ℕ} (ha : 0 < alpha)
    (haa : alpha ≤ a) (hmN : m ≤ N) :
    sourceFront ((N - 1) / alpha) a m = (m - 1) / a := by
  unfold sourceFront
  apply min_eq_right
  exact le_trans (Nat.div_le_div_right (Nat.sub_le_sub_right hmN 1))
    (Nat.div_le_div_left haa)

theorem interval_split {R₁ R₀ : ℕ} (hR : R₁ ≤ R₀) :
    Icc 1 R₀ = Icc 1 R₁ ∪ Icc (R₁ + 1) R₀ := by
  ext k
  simp only [mem_Icc, mem_union]
  omega

theorem interval_disjoint (R₁ R₀ : ℕ) :
    Disjoint (Icc 1 R₁) (Icc (R₁ + 1) R₀) := by
  apply disjoint_left.mpr
  intro k hk ht
  have h₁ := mem_Icc.mp hk
  have h₀ := mem_Icc.mp ht
  omega

theorem prefix_split {N R₁ R₀ m : ℕ} (hR : R₁ ≤ R₀) :
    unitLogPrefix N R₀ m = unitLogPrefix N R₁ m + unitLogTail N R₁ R₀ m := by
  unfold unitLogPrefix unitLogTail
  rw [interval_split hR, sum_union (interval_disjoint R₁ R₀)]

theorem logarithm_change {k m₀ m₁ : ℕ} (hk : 0 < k) (hm₀ : 0 < m₀)
    (hm₁ : 0 < m₁) :
    Real.log ((k : ℝ) / (m₁ : ℝ)) - Real.log ((k : ℝ) / (m₀ : ℝ)) =
      Real.log ((m₀ : ℝ) / (m₁ : ℝ)) := by
  rw [Real.log_div (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk))
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm₁)),
    Real.log_div (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk))
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm₀)),
    Real.log_div (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm₀))
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm₁))]
  ring

theorem prefix_log_change {N R m₀ m₁ : ℕ} (hm₀ : 0 < m₀) (hm₁ : 0 < m₁) :
    unitLogPrefix N R m₁ - unitLogPrefix N R m₀ =
      Real.log ((m₀ : ℝ) / (m₁ : ℝ)) * unitPrefix N R := by
  unfold unitLogPrefix unitPrefix
  rw [← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hkpos := (mem_Icc.mp hk).1
  rw [← mul_sub, logarithm_change hkpos hm₀ hm₁]
  ring

/-- X7 with the original cap, both strict fronts and every tail incidence. -/
theorem actual_kernel_variation {Q a N n₀ n₁ m₀ m₁ : ℕ}
    (ha : 0 < a) (hm₀ : 0 < m₀) (hm₁ : 0 < m₁) (hm : m₁ ≤ m₀)
    (hn₀ : n₀.Prime) (hn₁ : n₁.Prime) (hQn₀ : Q < n₀) (hQn₁ : Q < n₁) :
    harmonicKernel Q a N n₁ m₁ - harmonicKernel Q a N n₀ m₀ =
      Real.log ((m₀ : ℝ) / (m₁ : ℝ)) * unitPrefix N (sourceFront Q a m₁) -
        unitLogTail N (sourceFront Q a m₁) (sourceFront Q a m₀) m₀ := by
  rw [actual_kernel_eq_prefix ha hm₁ hn₁ hQn₁,
    actual_kernel_eq_prefix ha hm₀ hn₀ hQn₀,
    prefix_split (source_front_mono hm)]
  rw [sub_add_eq_sub_sub, prefix_log_change hm₀ hm₁]

theorem coefficient_abs_le_reciprocal {N k : ℕ} (hk : 0 < k) :
    |unitCoefficient N k| ≤ 1 / (Nat.totient k : ℝ) := by
  have hphi : 0 < (Nat.totient k : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hk
  have hmu : |mu k| ≤ 1 := by
    unfold mu
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
  by_cases hu : k.Coprime N
  · simp only [unitCoefficient, if_pos hu, abs_div, abs_of_pos hphi]
    exact div_le_div_of_nonneg_right hmu (le_of_lt hphi)
  · simp [unitCoefficient, hu, le_of_lt hphi]

theorem prefix_abs_bound (N R : ℕ) :
    |unitPrefix N R| ≤ ∑ k ∈ Icc 1 R, 1 / (Nat.totient k : ℝ) := by
  unfold unitPrefix
  apply le_trans (abs_sum_le_sum_abs _ _)
  apply sum_le_sum
  intro k hk
  exact coefficient_abs_le_reciprocal (mem_Icc.mp hk).1

theorem tail_abs_bound (N R₁ R₀ m : ℕ) :
    |unitLogTail N R₁ R₀ m| ≤
      ∑ k ∈ Icc (R₁ + 1) R₀,
        (1 / (Nat.totient k : ℝ)) * |Real.log ((k : ℝ) / (m : ℝ))| := by
  unfold unitLogTail
  apply le_trans (abs_sum_le_sum_abs _ _)
  apply sum_le_sum
  intro k hk
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right
    (coefficient_abs_le_reciprocal (by have h := (mem_Icc.mp hk).1; omega)) (abs_nonneg _)

/-- Quantitative finite variation on the actual kernel; no small target assumed. -/
theorem actual_kernel_abs_variation {Q a N n₀ n₁ m₀ m₁ : ℕ}
    (ha : 0 < a) (hm₀ : 0 < m₀) (hm₁ : 0 < m₁) (hm : m₁ ≤ m₀)
    (hn₀ : n₀.Prime) (hn₁ : n₁.Prime) (hQn₀ : Q < n₀) (hQn₁ : Q < n₁) :
    |harmonicKernel Q a N n₁ m₁ - harmonicKernel Q a N n₀ m₀| ≤
      |Real.log ((m₀ : ℝ) / (m₁ : ℝ))| *
        (∑ k ∈ Icc 1 (sourceFront Q a m₁), 1 / (Nat.totient k : ℝ)) +
      ∑ k ∈ Icc (sourceFront Q a m₁ + 1) (sourceFront Q a m₀),
        (1 / (Nat.totient k : ℝ)) * |Real.log ((k : ℝ) / (m₀ : ℝ))| := by
  rw [actual_kernel_variation ha hm₀ hm₁ hm hn₀ hn₁ hQn₀ hQn₁]
  apply le_trans (abs_sub_le _ _)
  rw [abs_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (prefix_abs_bound N _) (abs_nonneg _))
    (tail_abs_bound N _ _ m₀)

end GoldbachRound13.HarmonicKernelVariation

#print axioms GoldbachRound13.HarmonicKernelVariation.unitCoefficient
#print axioms GoldbachRound13.HarmonicKernelVariation.unitPrefix
#print axioms GoldbachRound13.HarmonicKernelVariation.unitLogPrefix
#print axioms GoldbachRound13.HarmonicKernelVariation.unitLogTail
#print axioms GoldbachRound13.HarmonicKernelVariation.sourceFront
#print axioms GoldbachRound13.HarmonicKernelVariation.prime_above_cap_units
#print axioms GoldbachRound13.HarmonicKernelVariation.strict_front_iff
#print axioms GoldbachRound13.HarmonicKernelVariation.front_filter_eq
#print axioms GoldbachRound13.HarmonicKernelVariation.actual_kernel_eq_prefix
#print axioms GoldbachRound13.HarmonicKernelVariation.source_front_mono
#print axioms GoldbachRound13.HarmonicKernelVariation.source_cap_inactive
#print axioms GoldbachRound13.HarmonicKernelVariation.interval_split
#print axioms GoldbachRound13.HarmonicKernelVariation.interval_disjoint
#print axioms GoldbachRound13.HarmonicKernelVariation.prefix_split
#print axioms GoldbachRound13.HarmonicKernelVariation.logarithm_change
#print axioms GoldbachRound13.HarmonicKernelVariation.prefix_log_change
#print axioms GoldbachRound13.HarmonicKernelVariation.actual_kernel_variation
#print axioms GoldbachRound13.HarmonicKernelVariation.coefficient_abs_le_reciprocal
#print axioms GoldbachRound13.HarmonicKernelVariation.prefix_abs_bound
#print axioms GoldbachRound13.HarmonicKernelVariation.tail_abs_bound
#print axioms GoldbachRound13.HarmonicKernelVariation.actual_kernel_abs_variation
