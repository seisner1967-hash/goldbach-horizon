import SeparatedTypeII

/-! Distinct calibration prices on the actual product v*w.  This module
does not identify the prime weight with the raw von Mangoldt weight. -/
namespace GoldbachRound18.SeparatedTypeII
open scoped BigOperators
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def productReference (P : Parameters) (I : Finset ℕ) (H j : ℕ) : ℝ :=
  if onProgression P I j then reference P I H ((P.N - j) / conductor P) else 0

def weightedBilinear (P : Parameters) (I : Finset ℕ) (H ell : ℕ)
    (E : Finset ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ t ∈ E.product (range (P.N + 1)),
    xi E t.1 * kappa P.N (conductor P) ell E t.2 *
      profile P I H (t.1 * t.2) * weight (t.1 * t.2)

def bilinearPrice (P : Parameters) (I : Finset ℕ) (H H' ell : ℕ)
    (E : Finset ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ t ∈ E.product (range (P.N + 1)),
    xi E t.1 * kappa P.N (conductor P) ell E t.2 *
      (productReference P I H' (t.1 * t.2) -
        productReference P I H (t.1 * t.2)) * weight (t.1 * t.2)

theorem profile_calibration (P : Parameters) (I : Finset ℕ) (H H' j : ℕ) :
    profile P I H j = profile P I H' j +
      (productReference P I H' j - productReference P I H j) := by
  by_cases hp : onProgression P I j
  · simp only [profile, productReference, if_pos hp, centered]
    ring
  · simp [profile, productReference, hp]

theorem bilinear_calibration (P : Parameters) (I : Finset ℕ)
    (H H' ell : ℕ) (E : Finset ℕ) (weight : ℕ → ℝ) :
    weightedBilinear P I H ell E weight = weightedBilinear P I H' ell E weight +
      bilinearPrice P I H H' ell E weight := by
  unfold weightedBilinear bilinearPrice
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  rw [profile_calibration P I H H' (t.1 * t.2)]
  ring

theorem weighted_one_is_adversarial (P : Parameters) (I : Finset ℕ)
    (H ell : ℕ) (E : Finset ℕ) :
    weightedBilinear P I H ell E (fun _ => 1) = adversarialSum P I H ell E := by
  simp [weightedBilinear, adversarialSum]

theorem weighted_bilinear_reindex (P : Parameters) (I : Finset ℕ)
    (V h ell H : ℕ) (weight : ℕ → ℝ)
    (hd : 0 < conductor P) (hcap : ∀ b ∈ I, conductor P * b ≤ P.N) :
    weightedBilinear P I H ell (rows P V h ell) weight =
      ∑ t ∈ divisorPairs P I (rows P V h ell),
        kappa P.N (conductor P) ell (rows P V h ell) (toProduct P t).2 *
          centered P I H t.2 * weight (candidate P t.2) := by
  let E := rows P V h ell
  have hfilter : weightedBilinear P I H ell E weight =
      ∑ t ∈ productPairs P I E,
        kappa P.N (conductor P) ell E t.2 * centered P I H (toDivisor P t).2 *
          weight (t.1 * t.2) := by
    unfold weightedBilinear productPairs
    rw [sum_filter]
    apply sum_congr rfl
    intro t ht
    have hv := (mem_product.mp ht).1
    by_cases hp : onProgression P I (t.1 * t.2)
    · simp [profile, hp, xi, hv, toDivisor]
    · simp [profile, hp]
  rw [hfilter]
  apply sum_bij' (fun t _ => toDivisor P t) (fun t _ => toProduct P t)
  · intro t ht
    exact forward_mem P I E ht
  · intro t ht
    exact backward_mem P I V h ell hd hcap ht
  · intro t ht
    exact inverse_product P I V h ell ht
  · intro t ht
    exact inverse_divisor P I V h ell hd hcap ht
  · intro t ht
    have he := inverse_product P I V h ell ht
    have hc : candidate P (toDivisor P t).2 = t.1 * t.2 := by
      have heq := product_equation P I E ht
      unfold candidate
      omega
    change kappa P.N (conductor P) ell E t.2 * centered P I H (toDivisor P t).2 *
        weight (t.1 * t.2) =
      kappa P.N (conductor P) ell E (toProduct P (toDivisor P t)).2 *
        centered P I H (toDivisor P t).2 * weight (candidate P (toDivisor P t).2)
    rw [he, hc]

theorem weighted_adversarial_identity (P : Parameters) (I : Finset ℕ)
    (V h ell : ℕ) (weight : ℕ → ℝ)
    (hd : 0 < conductor P) (hNd : Nat.Coprime P.N (conductor P))
    (hwidth : V < conductor P) (hdel : Nat.Coprime ell (conductor P))
    (hell : ell.Prime) (hellSmall : ell * ell ≤ P.a)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ h → p * p ≤ P.a)
    (hcap : ∀ b ∈ I, conductor P * b ≤ P.N) :
    weightedBilinear P I (P.N * conductor P * h) ell (rows P V h ell) weight =
      density P I (P.N * conductor P * h) *
        ∑ t ∈ omittedPairs P I (P.N * conductor P * h) ell (rows P V h ell),
          weight (candidate P t.2) := by
  rw [weighted_bilinear_reindex P I V h ell _ weight hd hcap]
  unfold omittedPairs
  rw [sum_filter, mul_sum]
  apply sum_congr rfl
  intro t ht
  rw [adversarial_entry P I V h ell hNd hwidth hdel hell hellSmall hsmall hcap ht]
  split_ifs <;> simp

theorem calibrated_adversarial_entry_zero (P : Parameters) (I : Finset ℕ)
    (V h ell H : ℕ) (hNd : Nat.Coprime P.N (conductor P))
    (hwidth : V < conductor P) (hdel : Nat.Coprime ell (conductor P))
    (hell : ell.Prime) (hellSmall : ell * ell ≤ P.a)
    (hcap : ∀ b ∈ I, conductor P * b ≤ P.N)
    {t : ℕ × ℕ} (ht : t ∈ divisorPairs P I (rows P V h ell)) :
    kappa P.N (conductor P) ell (rows P V h ell) (toProduct P t).2 *
      centered P I (H * ell) t.2 = 0 := by
  have hprod := mem_product.mp (mem_filter.mp ht).1
  have heq := divisor_equation P I (rows P V h ell) hcap ht
  have hclass := periodic_class_iff_omitted P hNd hwidth hdel hprod.1 heq
  by_cases hl : ell ∣ t.2
  · have hz := omitted_mask_zero P hell hellSmall hl
    have hu : t.2 ∉ units I (H * ell) := by
      intro hh
      have he : Nat.Coprime t.2 ell :=
        (mem_filter.mp hh).2.coprime_dvd_right (dvd_mul_left ell H)
      exact (hell.coprime_iff_not_dvd.mp he.symm) hl
    simp [centered, hz, reference, hu]
  · have hc : ¬ ∃ u ∈ rows P V h ell,
        Nat.ModEq (conductor P * ell) (u * (toProduct P t).2) P.N :=
      fun hh => hl (hclass.mp hh)
    simp [kappa, hc]

theorem calibrated_adversarial_zero (P : Parameters) (I : Finset ℕ)
    (V h ell H : ℕ) (weight : ℕ → ℝ)
    (hd : 0 < conductor P) (hNd : Nat.Coprime P.N (conductor P))
    (hwidth : V < conductor P) (hdel : Nat.Coprime ell (conductor P))
    (hell : ell.Prime) (hellSmall : ell * ell ≤ P.a)
    (hcap : ∀ b ∈ I, conductor P * b ≤ P.N) :
    weightedBilinear P I (H * ell) ell (rows P V h ell) weight = 0 := by
  rw [weighted_bilinear_reindex P I V h ell _ weight hd hcap]
  apply sum_eq_zero
  intro t ht
  rw [calibrated_adversarial_entry_zero P I V h ell H hNd hwidth hdel hell hellSmall hcap ht]
  simp

theorem calibrated_price_is_entire_old_sum (P : Parameters) (I : Finset ℕ)
    (V h ell H : ℕ) (weight : ℕ → ℝ)
    (hd : 0 < conductor P) (hNd : Nat.Coprime P.N (conductor P))
    (hwidth : V < conductor P) (hdel : Nat.Coprime ell (conductor P))
    (hell : ell.Prime) (hellSmall : ell * ell ≤ P.a)
    (hcap : ∀ b ∈ I, conductor P * b ≤ P.N) :
    bilinearPrice P I H (H * ell) ell (rows P V h ell) weight =
      weightedBilinear P I H ell (rows P V h ell) weight := by
  have he := bilinear_calibration P I H (H * ell) ell (rows P V h ell) weight
  rw [calibrated_adversarial_zero P I V h ell H weight hd hNd hwidth hdel hell hellSmall hcap,
    zero_add] at he
  exact he.symm

theorem raw_theta_bilinear_price_difference (P : Parameters) (I : Finset ℕ)
    (H H' ell : ℕ) (E : Finset ℕ) :
    bilinearPrice P I H H' ell E (rawLambda P.N) -
      bilinearPrice P I H H' ell E (theta P.N) =
    bilinearPrice P I H H' ell E (fun j => rawLambda P.N j - theta P.N j) := by
  unfold bilinearPrice
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro t ht
  ring

theorem prime_weight_on_divisor_pair_zero (P : Parameters) (I : Finset ℕ)
    (V h ell : ℕ)
    (hfront : ∀ b ∈ I, 2 * V < candidate P b)
    {t : ℕ × ℕ} (ht : t ∈ divisorPairs P I (rows P V h ell)) :
    theta P.N (candidate P t.2) = 0 := by
  have hprod := mem_product.mp (mem_filter.mp ht).1
  have hv := mem_Ioc.mp (mem_filter.mp hprod.1).1
  have hdiv := (mem_filter.mp ht).2
  have hn : ¬ (candidate P t.2).Prime := by
    intro hp
    rcases hp.eq_one_or_self_of_dvd t.1 hdiv with he | he
    · omega
    · have hf := hfront t.2 hprod.2
      omega
  simp [theta, hn]

theorem prime_weight_bilinear_zero (P : Parameters) (I : Finset ℕ)
    (V h ell H : ℕ) (hd : 0 < conductor P)
    (hcap : ∀ b ∈ I, conductor P * b ≤ P.N)
    (hfront : ∀ b ∈ I, 2 * V < candidate P b) :
    weightedBilinear P I H ell (rows P V h ell) (theta P.N) = 0 := by
  rw [weighted_bilinear_reindex P I V h ell H (theta P.N) hd hcap]
  apply sum_eq_zero
  intro t ht
  rw [prime_weight_on_divisor_pair_zero P I V h ell hfront ht]
  simp

end
end GoldbachRound18.SeparatedTypeII

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound18.SeparatedTypeII.productReference
#print axioms GoldbachRound18.SeparatedTypeII.weightedBilinear
#print axioms GoldbachRound18.SeparatedTypeII.bilinearPrice
#print axioms GoldbachRound18.SeparatedTypeII.profile_calibration
#print axioms GoldbachRound18.SeparatedTypeII.bilinear_calibration
#print axioms GoldbachRound18.SeparatedTypeII.weighted_one_is_adversarial
#print axioms GoldbachRound18.SeparatedTypeII.weighted_bilinear_reindex
#print axioms GoldbachRound18.SeparatedTypeII.weighted_adversarial_identity
#print axioms GoldbachRound18.SeparatedTypeII.calibrated_adversarial_entry_zero
#print axioms GoldbachRound18.SeparatedTypeII.calibrated_adversarial_zero
#print axioms GoldbachRound18.SeparatedTypeII.calibrated_price_is_entire_old_sum
#print axioms GoldbachRound18.SeparatedTypeII.raw_theta_bilinear_price_difference
#print axioms GoldbachRound18.SeparatedTypeII.prime_weight_on_divisor_pair_zero
#print axioms GoldbachRound18.SeparatedTypeII.prime_weight_bilinear_zero
