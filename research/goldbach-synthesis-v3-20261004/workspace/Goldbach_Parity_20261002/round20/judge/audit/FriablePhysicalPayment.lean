import FriableTotientEnvelope
import FriablePrimeHarmonic

namespace GoldbachRound20.Friable

open Finset GoldbachRound19.Switch GoldbachRound19.NonSS
open GoldbachRound10.ShortDivisorComplement GoldbachRound11
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A single actual congruence class in an interval, including its literal +1. -/
theorem finite_interval_congruence_card_le {S : Finset ℕ} {L U d : ℕ}
    (hd : 0 < d) (hS : ∀ q ∈ S, L ≤ q ∧ q ≤ U)
    (hmod : ∀ q ∈ S, ∀ r ∈ S, q ≡ r [MOD d]) :
    S.card ≤ (U - L) / d + 1 := by
  by_cases hne : S.Nonempty
  · let first := S.min' hne
    have hfirst : first ∈ S := S.min'_mem hne
    have hlow : ∀ q ∈ S, first ≤ q := fun q hq => S.min'_le q hq
    have hdiv : ∀ q ∈ S, d ∣ q - first := by
      intro q hq
      exact (Nat.modEq_iff_dvd' (hlow q hq)).mp (hmod first hfirst q hq)
    have hinj : Set.InjOn (fun q : ℕ => (q - first) / d) S := by
      intro q hq r hr heq
      have hqeq := Nat.div_mul_cancel (hdiv q hq)
      have hreq := Nat.div_mul_cancel (hdiv r hr)
      change (q - first) / d = (r - first) / d at heq
      have hh : q - first = r - first := by
        rw [← hqeq, ← hreq, heq]
      have hql := hlow q hq
      have hrl := hlow r hr
      omega
    have hsub : S.image (fun q => (q - first) / d) ⊆ range ((U - L) / d + 1) := by
      intro k hk
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hk
      have hbounds := hS q hq
      have hstart := hS first hfirst
      have hdiff : q - first ≤ U - L := by omega
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hdiff))
    calc
      S.card = (S.image (fun q => (q - first) / d)).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ (range ((U - L) / d + 1)).card := Finset.card_le_card hsub
      _ = _ := Finset.card_range _
  · have hh : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hh]

theorem finite_interval_congruence_card_le_real {S : Finset ℕ} {L U d : ℕ}
    (hd : 0 < d) (hS : ∀ q ∈ S, L ≤ q ∧ q ≤ U)
    (hmod : ∀ q ∈ S, ∀ r ∈ S, q ≡ r [MOD d]) :
    (S.card : ℝ) ≤ ((U - L : ℕ) : ℝ) / (d : ℝ) + 1 := by
  have hh : (S.card : ℝ) ≤ (((U - L) / d : ℕ) : ℝ) + 1 := by
    exact_mod_cast finite_interval_congruence_card_le hd hS hmod
  exact hh.trans (add_le_add_right Nat.cast_div_le 1)

theorem structural_q_interval {alpha N Z M e q : ℕ}
    (he : 0 < e) (h : StructuralSupport alpha N Z M e q) :
    M ≤ q ∧ q ≤ (N - (N - 1) / alpha - 1) / e := by
  refine ⟨h.2.2.1, ?_⟩
  apply (Nat.le_div_iff_mul_le he).mpr
  have hc := h.2.2.2.2.2.2.1
  have hh : e * q ≤ N - (N - 1) / alpha - 1 := by omega
  simpa only [mul_comm] using hh

theorem actual_resource1_incidence_card_le {S : Finset ℕ} {alpha N Z M e d : ℕ}
    (he : 0 < e) (hd : 0 < d)
    (hH : ∀ q ∈ S, StructuralSupport alpha N Z M e q)
    (hdiv : ∀ q ∈ S, d ∣ resource1 N q) :
    (S.card : ℝ) ≤
      (((N - (N - 1) / alpha - 1) / e - M : ℕ) : ℝ) / (d : ℝ) + 1 := by
  apply finite_interval_congruence_card_le_real hd
    (fun q hq => structural_q_interval he (hH q hq))
  intro q hq r hr
  have hqN := (resource1_divisor_class (q_lt_N (hH q hq).1).le).mp (hdiv q hq)
  have hrN := (resource1_divisor_class (q_lt_N (hH r hr).1).le).mp (hdiv r hr)
  exact hqN.trans hrN.symm

theorem actual_resource0_incidence_card_le {S : Finset ℕ} {alpha N Z M e d : ℕ}
    (he : 0 < e) (hd : 0 < d)
    (hH : ∀ q ∈ S, StructuralSupport alpha N Z M e q)
    (hdiv : ∀ q ∈ S, d ∣ resource0 N q) :
    (S.card : ℝ) ≤
      (((N - (N - 1) / alpha - 1) / e - M : ℕ) : ℝ) / (d : ℝ) + 1 := by
  by_cases hne : S.Nonempty
  · obtain ⟨first, hfirst⟩ := hne
    have hc : (anchor N).Coprime d :=
      (anchor_resource0_coprime (hH first hfirst).1).of_dvd_right (hdiv first hfirst)
    apply finite_interval_congruence_card_le_real hd
      (fun q hq => structural_q_interval he (hH q hq))
    intro q hq r hr
    have hqN := (resource0_divisor_class (hH q hq).1.anchor_mul_q_lt.le).mp (hdiv q hq)
    have hrN := (resource0_divisor_class (hH r hr).1.anchor_mul_q_lt.le).mp (hdiv r hr)
    exact Nat.ModEq.cancel_left_of_coprime hc.symm.gcd_eq_one (hqN.trans hrN.symm)
  · have hh : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hh, card_empty, Nat.cast_zero]
    positivity

theorem actual_front_le_N_div_e_d (alpha N M e d : ℕ) :
    (((N - (N - 1) / alpha - 1) / e - M : ℕ) : ℝ) / (d : ℝ) ≤
      (N : ℝ) / ((e : ℝ) * (d : ℝ)) := by
  have hwidth : (((N - (N - 1) / alpha - 1) / e - M : ℕ) : ℝ) ≤
      (((N - (N - 1) / alpha - 1) / e : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le ((N - (N - 1) / alpha - 1) / e) M
  have hhead : (N - (N - 1) / alpha - 1 : ℕ) ≤ N :=
    (Nat.sub_le (N - (N - 1) / alpha) 1).trans (Nat.sub_le N ((N - 1) / alpha))
  have hquot : (((N - (N - 1) / alpha - 1) / e : ℕ) : ℝ) ≤ (N : ℝ) / (e : ℝ) :=
    Nat.cast_div_le.trans (div_le_div_of_nonneg_right (by exact_mod_cast hhead) (Nat.cast_nonneg e))
  have hh := div_le_div_of_nonneg_right (hwidth.trans hquot) (Nat.cast_nonneg d)
  simpa only [div_div] using hh

theorem actual_resource1_incidence_card_le_N {S : Finset ℕ} {alpha N Z M e d : ℕ}
    (he : 0 < e) (hd : 0 < d)
    (hH : ∀ q ∈ S, StructuralSupport alpha N Z M e q)
    (hdiv : ∀ q ∈ S, d ∣ resource1 N q) :
    (S.card : ℝ) ≤ (N : ℝ) / ((e : ℝ) * (d : ℝ)) + 1 :=
  (actual_resource1_incidence_card_le he hd hH hdiv).trans
    (add_le_add_right (actual_front_le_N_div_e_d alpha N M e d) 1)

theorem actual_resource0_incidence_card_le_N {S : Finset ℕ} {alpha N Z M e d : ℕ}
    (he : 0 < e) (hd : 0 < d)
    (hH : ∀ q ∈ S, StructuralSupport alpha N Z M e q)
    (hdiv : ∀ q ∈ S, d ∣ resource0 N q) :
    (S.card : ℝ) ≤ (N : ℝ) / ((e : ℝ) * (d : ℝ)) + 1 :=
  (actual_resource0_incidence_card_le he hd hH hdiv).trans
    (add_le_add_right (actual_front_le_N_div_e_d alpha N M e d) 1)

/-- Actual smoothness provides the union; both affine fronts are counted. -/
theorem actual_friable_union_card_le_mass {S : Finset ℕ} {alpha N Z M e D Y : ℕ}
    (he : 0 < e) (hD : 1 < D) (hDM : D ≤ M) (hY : 0 < Y)
    (hH : ∀ q ∈ S, StructuralSupport alpha N Z M e q)
    (hF : ∀ q ∈ S, Smooth Y (resource0 N q) ∨ Smooth Y (resource1 N q)) :
    (S.card : ℝ) ≤ 2 * ((N : ℝ) / (e : ℝ) *
      (∑ d ∈ divisorBand D Y, (d : ℝ)⁻¹) + ((divisorBand D Y).card : ℝ)) := by
  let C0 : ℕ → Finset ℕ := fun d => S.filter (fun q => d ∣ resource0 N q)
  let C1 : ℕ → Finset ℕ := fun d => S.filter (fun q => d ∣ resource1 N q)
  have hcover : S ⊆ (divisorBand D Y).biUnion (fun d => C0 d ∪ C1 d) := by
    intro q hq
    rcases hF q hq with hf | hf
    · obtain ⟨d, hd, hdiv⟩ := actual_friable_resource0_cover (hH q hq) hDM hD hY hf
      exact mem_biUnion.mpr ⟨d, hd, mem_union_left _ (mem_filter.mpr ⟨hq, hdiv⟩)⟩
    · obtain ⟨d, hd, hdiv⟩ := actual_friable_resource1_cover (hH q hq) hDM hD hY hf
      exact mem_biUnion.mpr ⟨d, hd, mem_union_right _ (mem_filter.mpr ⟨hq, hdiv⟩)⟩
  have hcard : S.card ≤ ∑ d ∈ divisorBand D Y, ((C0 d).card + (C1 d).card) := by
    calc
      _ ≤ ((divisorBand D Y).biUnion (fun d => C0 d ∪ C1 d)).card := card_le_card hcover
      _ ≤ ∑ d ∈ divisorBand D Y, (C0 d ∪ C1 d).card := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum (fun d _ => card_union_le (C0 d) (C1 d))
  have hcardR : (S.card : ℝ) ≤
      ∑ d ∈ divisorBand D Y, (((C0 d).card : ℝ) + ((C1 d).card : ℝ)) := by
    exact_mod_cast hcard
  calc
    _ ≤ ∑ d ∈ divisorBand D Y, (((C0 d).card : ℝ) + ((C1 d).card : ℝ)) := hcardR
    _ ≤ ∑ d ∈ divisorBand D Y, 2 * ((N : ℝ) / ((e : ℝ) * (d : ℝ)) + 1) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := by have := (mem_Icc.mp (mem_filter.mp hd).1).1; omega
      have h0 := actual_resource0_incidence_card_le_N (S := C0 d) he hdpos
        (fun q hq => hH q (mem_filter.mp hq).1) (fun q hq => (mem_filter.mp hq).2)
      have h1 := actual_resource1_incidence_card_le_N (S := C1 d) he hdpos
        (fun q hq => hH q (mem_filter.mp hq).1) (fun q hq => (mem_filter.mp hq).2)
      linarith
    _ = _ := by
      simp only [mul_add, add_mul, one_mul, mul_one, Finset.sum_add_distrib, Finset.mul_sum,
        div_eq_mul_inv, mul_inv_rev, Finset.sum_const, nsmul_eq_mul,
        mul_assoc, mul_left_comm, mul_comm]

def friableLabels1 (alpha N Z M Y : ℕ) : Finset (ℕ × ℕ) :=
  (physicalDomain alpha N Z M).filter (fun v => Smooth Y (resource1 N v.2))

def friableQ1 (alpha N Z M Y : ℕ) : Finset ℕ :=
  (friableLabels1 alpha N Z M Y).image Prod.snd

def uniqueResources1 (alpha N Z M Y : ℕ) : Finset ℕ :=
  (friableQ1 alpha N Z M Y).image (resource1 N)

theorem friableQ1_witness {alpha N Z M Y q : ℕ}
    (hq : q ∈ friableQ1 alpha N Z M Y) :
    ∃ e, StructuralSupport alpha N Z M e q ∧ Smooth Y (resource1 N q) := by
  obtain ⟨v, hv, hqeq⟩ := mem_image.mp hq
  have hh := mem_filter.mp hv
  refine ⟨v.1, ?_, ?_⟩
  · simpa only [hqeq] using physicalDomain_support hh.1
  · simpa only [hqeq] using hh.2

theorem friableQ1_resource_injective (alpha N Z M Y : ℕ) :
    Set.InjOn (resource1 N) (friableQ1 alpha N Z M Y) := by
  intro q hq r hr he
  obtain ⟨e, hs, _⟩ := friableQ1_witness hq
  obtain ⟨f, ht, _⟩ := friableQ1_witness hr
  have hqN := q_lt_N hs.1
  have hrN := q_lt_N ht.1
  unfold resource1 at he
  omega

theorem uniqueResources1_subset_smoothInterval (alpha N Z M Y : ℕ) :
    uniqueResources1 alpha N Z M Y ⊆ smoothInterval M N Y := by
  intro m hm
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hm
  obtain ⟨e, hs, hf⟩ := friableQ1_witness hq
  exact mem_filter.mpr ⟨mem_Icc.mpr
    ⟨resource1_ge_M_of_actual_cap hs, Nat.sub_le N q⟩, hf⟩

/-- This sum merges e before counting any reciprocal resource. -/
theorem actual_unique_F1_tau_sum_le (alpha N Z M Y : ℕ) :
    (∑ q ∈ friableQ1 alpha N Z M Y, tau (resource1 N q)) ≤
      ∑ m ∈ smoothInterval M N Y, tau m := by
  have he : (∑ q ∈ friableQ1 alpha N Z M Y, tau (resource1 N q)) =
      ∑ m ∈ uniqueResources1 alpha N Z M Y, tau m := by
    unfold uniqueResources1
    rw [Finset.sum_image (friableQ1_resource_injective alpha N Z M Y)]
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (uniqueResources1_subset_smoothInterval alpha N Z M Y) (fun m _ _ => tau_nonneg m)

theorem actual_unique_F1_tau_sum_le_N_u_neg42 {alpha N Z M Y : ℕ} {u : ℝ}
    (hM : 0 < M) (hu : 0 < u) (hY : 4 ≤ Real.log (Y : ℝ))
    (hYu : 1 + Real.log (Y : ℝ) ≤ u)
    (hMlog : 3 * u / 4 ≤ Real.log (M : ℝ))
    (hscale : 128 * Real.log u * Real.log (Y : ℝ) ≤ u) :
    (∑ q ∈ friableQ1 alpha N Z M Y, tau (resource1 N q)) ≤ (N : ℝ) * u ^ (-42 : ℝ) :=
  (actual_unique_F1_tau_sum_le alpha N Z M Y).trans
    (actual_smooth_tau_tail_le_N_u_neg42 hM hu hY hYu hMlog hscale)

theorem actual_physicalDivisorKernel_abs_bound {Q a N n m : ℕ}
    (hm : 0 < m) (hmN : m ≤ N) :
    |physicalDivisorKernel Q a m n N| ≤ Real.log (N : ℝ) * tau m := by
  have hN : 1 ≤ N := by omega
  have hu : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  unfold physicalDivisorKernel
  calc
    _ ≤ ∑ k ∈ m.divisors,
        |if k ≤ Q ∧ a * k < m ∧ k.Coprime (n * N) then
          mu k * Real.log ((k : ℝ) / (m : ℝ)) else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ m.divisors, Real.log (N : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hg : k ≤ Q ∧ a * k < m ∧ k.Coprime (n * N)
      · rw [if_pos hg, abs_mul]
        have hl := log_ratio_abs_le_log (Nat.pos_of_mem_divisors hk)
          (Nat.divisor_le hk) hmN
        exact (mul_le_mul_of_nonneg_right (mu_abs_le_one k) (abs_nonneg _)).trans
          (by simpa using hl)
      · simpa [hg] using hu
    _ = _ := by simp [tau, mul_comm]

theorem primeIncidence_abs_le_one (N n : ℕ) : |primeIncidence N n| ≤ 1 := by
  unfold primeIncidence
  split_ifs <;> norm_num

theorem theta_abs_le_log {N n : ℕ} (hnN : n ≤ N) :
    |theta N n| ≤ Real.log (N : ℝ) := by
  by_cases hinc : n.Prime ∧ n.Coprime N
  · have hn1 : 1 ≤ n := hinc.1.one_lt.le
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hinc.1.pos
    have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
    simp only [theta, primeIncidence, if_pos hinc, one_mul, abs_of_nonneg hl]
    exact Real.log_le_log hnpos (by exact_mod_cast hnN)
  · simp only [theta, primeIncidence, if_neg hinc, zero_mul, abs_zero]
    by_cases hN : N = 0
    · simp [hN]
    · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))

theorem rawLambda_abs_le_log {N n : ℕ} (hnN : n ≤ N) :
    |rawLambda N n| ≤ Real.log (N : ℝ) := by
  have hlog : Real.log (n : ℝ) ≤ Real.log (N : ℝ) := by
    by_cases hn0 : n = 0
    · simp only [hn0, Nat.cast_zero, Real.log_zero]
      by_cases hN : N = 0
      · simp [hN]
      · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    · exact Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
        (by exact_mod_cast hnN)
  have hbound := (ArithmeticFunction.vonMangoldt_le_log (n := n)).trans hlog
  unfold rawLambda
  split_ifs
  · rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact hbound
  · simp only [abs_zero]
    exact (ArithmeticFunction.vonMangoldt_nonneg (n := n)).trans hbound

theorem actual_sourceBracket_abs_tau_envelope {alpha a N n m : ℕ}
    (ha : 1 ≤ a) (hm : 0 < m) (hmN : m ≤ N) (hnN : n ≤ N)
    (hu : 1 ≤ Real.log (N : ℝ)) :
    |sourceBracket alpha a N n m| ≤
      Real.log (N : ℝ) ^ 2 * tau m + 6 * Real.log (N : ℝ) ^ 3 := by
  have hQ : (N - 1) / alpha ≤ N := (Nat.div_le_self _ _).trans (Nat.sub_le N 1)
  have hD := actual_physicalDivisorKernel_abs_bound (Q := (N - 1) / alpha) (a := a)
    (n := n) hm hmN
  have hW := actual_harmonicKernel_abs_unconditional (Q := (N - 1) / alpha)
    (n := n) ha hm hmN hQ
  have htriangle : |physicalDivisorKernel ((N - 1) / alpha) a m n N -
      harmonicKernel ((N - 1) / alpha) a N n m| ≤
      |physicalDivisorKernel ((N - 1) / alpha) a m n N| +
      |harmonicKernel ((N - 1) / alpha) a N n m| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add
      (physicalDivisorKernel ((N - 1) / alpha) a m n N)
      (-harmonicKernel ((N - 1) / alpha) a N n m)
  have hc : |physicalDivisorKernel ((N - 1) / alpha) a m n N -
      harmonicKernel ((N - 1) / alpha) a N n m| ≤
      Real.log (N : ℝ) * tau m + 6 * Real.log (N : ℝ) ^ 2 := by
    have hW' : 3 * Real.log (N : ℝ) * (1 + Real.log (N : ℝ)) ≤
        6 * Real.log (N : ℝ) ^ 2 := by nlinarith
    exact htriangle.trans (add_le_add hD (hW.trans hW'))
  unfold sourceBracket
  rw [abs_mul, abs_mul, abs_neg]
  calc
    _ ≤ Real.log (N : ℝ) *
        (1 * |physicalDivisorKernel ((N - 1) / alpha) a m n N -
          harmonicKernel ((N - 1) / alpha) a N n m|) :=
      mul_le_mul (theta_abs_le_log hnN)
        (mul_le_mul_of_nonneg_right (mu_abs_le_one m) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by linarith)
    _ ≤ Real.log (N : ℝ) *
        (Real.log (N : ℝ) * tau m + 6 * Real.log (N : ℝ) ^ 2) := by
      simpa using mul_le_mul_of_nonneg_left hc (show 0 ≤ Real.log (N : ℝ) by linarith)
    _ = _ := by ring

theorem tau_one_le {m : ℕ} (hm : 0 < m) : 1 ≤ tau m := by
  have hh : 1 ≤ m.divisors.card := Finset.one_le_card.mpr
    ⟨1, Nat.one_mem_divisors.mpr (Nat.ne_of_gt hm)⟩
  unfold tau
  exact_mod_cast hh

theorem actual_sourceBracket_abs_le_seven_tau {alpha a N n m : ℕ}
    (ha : 1 ≤ a) (hm : 0 < m) (hmN : m ≤ N) (hnN : n ≤ N)
    (hu : 1 ≤ Real.log (N : ℝ)) :
    |sourceBracket alpha a N n m| ≤ 7 * Real.log (N : ℝ) ^ 3 * tau m := by
  have hh := actual_sourceBracket_abs_tau_envelope (alpha := alpha) ha hm hmN hnN hu
  have ht := tau_one_le hm
  have hu0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have hu23 : Real.log (N : ℝ) ^ 2 ≤ Real.log (N : ℝ) ^ 3 := by nlinarith [sq_nonneg (Real.log (N : ℝ) - 1)]
  have hfirst := mul_le_mul_of_nonneg_right hu23 (tau_nonneg m)
  have hsecond := mul_le_mul_of_nonneg_left ht (show 0 ≤ 6 * Real.log (N : ℝ) ^ 3 by positivity)
  nlinarith

def uniqueReciprocalCost1 (alpha a N Z M Y : ℕ) : ℝ :=
  ∑ q ∈ friableQ1 alpha N Z M Y, |sourceBracket alpha a N q (resource1 N q)|

theorem actual_unique_F1_reciprocal_cost_le {alpha a N Z M Y : ℕ}
    (ha : 1 ≤ a) (hu : 1 ≤ Real.log (N : ℝ)) :
    uniqueReciprocalCost1 alpha a N Z M Y ≤
      7 * Real.log (N : ℝ) ^ 3 * ∑ q ∈ friableQ1 alpha N Z M Y, tau (resource1 N q) := by
  unfold uniqueReciprocalCost1
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  obtain ⟨e, hs, hf⟩ := friableQ1_witness hq
  exact actual_sourceBracket_abs_le_seven_tau ha (by have := hs.1.resource1_two; omega)
    (Nat.sub_le N q) (q_lt_N hs.1).le hu

/-- Local F3 with geometric guards, not the source floors/ceils wrapper or F4. -/
theorem actual_unique_F1_reciprocal_payment {alpha a N Z M Y : ℕ}
    (ha : 1 ≤ a) (hM : 0 < M) (hu : 1 ≤ Real.log (N : ℝ))
    (hY : 4 ≤ Real.log (Y : ℝ))
    (hYu : 1 + Real.log (Y : ℝ) ≤ Real.log (N : ℝ))
    (hMlog : 3 * Real.log (N : ℝ) / 4 ≤ Real.log (M : ℝ))
    (hscale : 128 * Real.log (Real.log (N : ℝ)) * Real.log (Y : ℝ) ≤ Real.log (N : ℝ)) :
    uniqueReciprocalCost1 alpha a N Z M Y ≤
      7 * (N : ℝ) * Real.log (N : ℝ) ^ (-39 : ℝ) := by
  have hu0 : 0 < Real.log (N : ℝ) := by linarith
  calc
    _ ≤ 7 * Real.log (N : ℝ) ^ 3 *
        ∑ q ∈ friableQ1 alpha N Z M Y, tau (resource1 N q) :=
      actual_unique_F1_reciprocal_cost_le ha hu
    _ ≤ 7 * Real.log (N : ℝ) ^ 3 * ((N : ℝ) * Real.log (N : ℝ) ^ (-42 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (actual_unique_F1_tau_sum_le_N_u_neg42 hM hu0 hY hYu hMlog hscale) (by positivity)
    _ = _ := by
      have he : Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) ^ (-42 : ℝ) =
          Real.log (N : ℝ) ^ (-39 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hu0]
        norm_num
      calc
        _ = 7 * (N : ℝ) *
            (Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) ^ (-42 : ℝ)) := by ring
        _ = _ := by rw [he]

#print axioms friableLabels1
#print axioms finite_interval_congruence_card_le
#print axioms finite_interval_congruence_card_le_real
#print axioms structural_q_interval
#print axioms actual_resource1_incidence_card_le
#print axioms actual_resource0_incidence_card_le
#print axioms actual_front_le_N_div_e_d
#print axioms actual_resource1_incidence_card_le_N
#print axioms actual_resource0_incidence_card_le_N
#print axioms actual_friable_union_card_le_mass
#print axioms friableQ1
#print axioms uniqueResources1
#print axioms friableQ1_witness
#print axioms friableQ1_resource_injective
#print axioms uniqueResources1_subset_smoothInterval
#print axioms actual_unique_F1_tau_sum_le
#print axioms actual_unique_F1_tau_sum_le_N_u_neg42
#print axioms actual_physicalDivisorKernel_abs_bound
#print axioms primeIncidence_abs_le_one
#print axioms theta_abs_le_log
#print axioms rawLambda_abs_le_log
#print axioms actual_sourceBracket_abs_tau_envelope
#print axioms tau_one_le
#print axioms actual_sourceBracket_abs_le_seven_tau
#print axioms uniqueReciprocalCost1
#print axioms actual_unique_F1_reciprocal_cost_le
#print axioms actual_unique_F1_reciprocal_payment

end
end GoldbachRound20.Friable
