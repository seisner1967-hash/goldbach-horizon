import DivisorSecondMoment

namespace GoldbachRound21.NonfriableReciprocal

open Finset GoldbachRound19.Switch GoldbachRound19.NonSS
open GoldbachRound20.Friable GoldbachRound20.Friable.SourceGeometry
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 8000000

def labels0not1 (alpha N Z M Y : ℕ) : Finset (ℕ × ℕ) :=
  (physicalDomain alpha N Z M).filter fun v =>
    Smooth Y (resource0 N v.2) ∧ ¬ Smooth Y (resource1 N v.2)

def q0not1 (alpha N Z M Y : ℕ) : Finset ℕ :=
  (labels0not1 alpha N Z M Y).image (fun v => v.2)

def q01 (alpha N Z M Y : ℕ) : Finset ℕ :=
  (friableDemandDomain alpha N Z M Y).image (fun v => v.2)

theorem q0not1_witness {alpha N Z M Y q : ℕ}
    (hq : q ∈ q0not1 alpha N Z M Y) :
    ∃ e, StructuralSupport alpha N Z M e q ∧
      Smooth Y (resource0 N q) ∧ ¬ Smooth Y (resource1 N q) := by
  obtain ⟨v, hv, heq⟩ := mem_image.mp hq
  obtain ⟨hH, hF⟩ := mem_filter.mp hv
  refine ⟨v.1, ?_, ?_, ?_⟩
  · simpa only [heq] using physicalDomain_support hH
  · simpa only [heq] using hF.1
  · simpa only [heq] using hF.2

theorem q0not1_resource_injective (alpha N Z M Y : ℕ) :
    Set.InjOn (resource1 N) (q0not1 alpha N Z M Y) := by
  intro q hq r hr heq
  obtain ⟨e, hs, _, _⟩ := q0not1_witness hq
  obtain ⟨f, ht, _, _⟩ := q0not1_witness hr
  have hqN := q_lt_N hs.1
  have hrN := q_lt_N ht.1
  unfold resource1 at heq
  omega

theorem q01_partition (alpha N Z M Y : ℕ) :
    q01 alpha N Z M Y = friableQ1 alpha N Z M Y ∪ q0not1 alpha N Z M Y := by
  have he : friableDemandDomain alpha N Z M Y =
      friableLabels1 alpha N Z M Y ∪ labels0not1 alpha N Z M Y := by
    ext v
    simp only [friableDemandDomain, friableLabels1, labels0not1, mem_union, mem_filter]
    tauto
  unfold q01 friableQ1 q0not1
  rw [he, image_union]

theorem q01_partition_disjoint (alpha N Z M Y : ℕ) :
    Disjoint (friableQ1 alpha N Z M Y) (q0not1 alpha N Z M Y) := by
  apply Finset.disjoint_left.mpr
  intro q hq hr
  obtain ⟨e, _, hF⟩ := friableQ1_witness hq
  obtain ⟨f, _, _, hnot⟩ := q0not1_witness hr
  exact hnot hF

theorem q0not1_reciprocal_image_subset (alpha N Z M Y : ℕ) :
    (q0not1 alpha N Z M Y).image (resource1 N) ⊆ Icc 1 N := by
  intro m hm
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hm
  obtain ⟨e, hs, _, _⟩ := q0not1_witness hq
  exact mem_Icc.mpr ⟨by have hh := hs.1.resource1_two; omega, Nat.sub_le N q⟩

theorem actual_q0not1_tau_square_sum_le_global (alpha N Z M Y : ℕ) :
    (∑ q ∈ q0not1 alpha N Z M Y, tau (resource1 N q) ^ 2) ≤
      ∑ n ∈ Icc 1 N, tau n ^ 2 := by
  have he : (∑ q ∈ q0not1 alpha N Z M Y, tau (resource1 N q) ^ 2) =
      ∑ n ∈ (q0not1 alpha N Z M Y).image (resource1 N), tau n ^ 2 := by
    rw [Finset.sum_image (q0not1_resource_injective alpha N Z M Y)]
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (q0not1_reciprocal_image_subset alpha N Z M Y) (fun n _ _ => sq_nonneg _)

/-- Unlike the rank-wise result20, e may differ for every q in this class. -/
theorem actual_resource0_projection_class_card {S : Finset ℕ} {alpha N Z M d : ℕ}
    (hd : 0 < d) (hH : ∀ q ∈ S, ∃ e, StructuralSupport alpha N Z M e q)
    (hdiv : ∀ q ∈ S, d ∣ resource0 N q) :
    (S.card : ℝ) ≤ (N : ℝ) / (d : ℝ) + 1 := by
  by_cases hne : S.Nonempty
  · obtain ⟨first, hfirst⟩ := hne
    obtain ⟨e, he⟩ := hH first hfirst
    have hc : (anchor N).Coprime d :=
      (anchor_resource0_coprime he.1).of_dvd_right (hdiv first hfirst)
    have hb := finite_interval_congruence_card_le_real (S := S) (L := M) (U := N) hd
      (fun q hq => by
        obtain ⟨f, hf⟩ := hH q hq
        exact ⟨hf.2.2.1, (q_lt_N hf.1).le⟩)
      (fun q hq r hr => by
        obtain ⟨f, hf⟩ := hH q hq
        obtain ⟨g, hg⟩ := hH r hr
        have hqN := (resource0_divisor_class hf.1.anchor_mul_q_lt.le).mp (hdiv q hq)
        have hrN := (resource0_divisor_class hg.1.anchor_mul_q_lt.le).mp (hdiv r hr)
        exact Nat.ModEq.cancel_left_of_coprime hc.symm.gcd_eq_one (hqN.trans hrN.symm))
    have hwidth : ((N - M : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N M
    exact hb.trans (add_le_add_right
      (div_le_div_of_nonneg_right hwidth (Nat.cast_nonneg d)) 1)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he, card_empty, Nat.cast_zero]
    positivity

theorem actual_q0not1_card_le_mass {alpha N Z M D Y : ℕ}
    (hD : 1 < D) (hDM : D ≤ M) (hY : 0 < Y) :
    ((q0not1 alpha N Z M Y).card : ℝ) ≤
      (N : ℝ) * (∑ d ∈ divisorBand D Y, (d : ℝ)⁻¹) +
        ((divisorBand D Y).card : ℝ) := by
  let S := q0not1 alpha N Z M Y
  let C : ℕ → Finset ℕ := fun d => S.filter (fun q => d ∣ resource0 N q)
  have hcover : S ⊆ (divisorBand D Y).biUnion C := by
    intro q hq
    obtain ⟨e, hs, hF, _⟩ := q0not1_witness hq
    obtain ⟨d, hd, hdiv⟩ := actual_friable_resource0_cover hs hDM hD hY hF
    exact mem_biUnion.mpr ⟨d, hd, mem_filter.mpr ⟨hq, hdiv⟩⟩
  have hcard : S.card ≤ ∑ d ∈ divisorBand D Y, (C d).card :=
    (card_le_card hcover).trans Finset.card_biUnion_le
  have hcardR : (S.card : ℝ) ≤ ∑ d ∈ divisorBand D Y, ((C d).card : ℝ) := by
    exact_mod_cast hcard
  calc
    _ ≤ ∑ d ∈ divisorBand D Y, ((C d).card : ℝ) := hcardR
    _ ≤ ∑ d ∈ divisorBand D Y, ((N : ℝ) / (d : ℝ) + 1) := by
      apply sum_le_sum
      intro d hd
      have hdpos : 0 < d := by have hh := (mem_Icc.mp (mem_filter.mp hd).1).1; omega
      apply actual_resource0_projection_class_card hdpos
      · intro q hq
        obtain ⟨e, hs, _, _⟩ := q0not1_witness (mem_filter.mp hq).1
        exact ⟨e, hs⟩
      · intro q hq
        exact (mem_filter.mp hq).2
    _ = _ := by
      simp only [sum_add_distrib, div_eq_mul_inv, mul_sum, sum_const, nsmul_eq_mul, mul_one]

theorem source_DY_le_two_N {N : ℕ} (h : SourceOnset N) :
    (sourceD N : ℝ) * (sourceY N : ℝ) ≤ 2 * (N : ℝ) := by
  have hE : (1 : ℝ) ≤ (sourceEupper N : ℝ) := by
    exact_mod_cast (show 1 ≤ sourceEupper N from source_Eupper_pos h)
  calc
    _ = 1 * ((sourceD N : ℝ) * (sourceY N : ℝ)) := by ring
    _ ≤ (sourceEupper N : ℝ) * ((sourceD N : ℝ) * (sourceY N : ℝ)) :=
      mul_le_mul_of_nonneg_right hE (by positivity)
    _ ≤ _ := source_rank_front_le_two_N h

theorem actual_source_q0not1_card_le_three {N : ℕ} (h : SourceOnset N) :
    ((q0not1 (sourceAlpha N) N (sourceZ N) (sourceM N) (sourceY N)).card : ℝ) ≤
      3 * (N : ℝ) * sourceU N ^ (-37 : ℝ) := by
  have g := source_geometry h
  have hfirst := actual_q0not1_card_le_mass (alpha := sourceAlpha N) (N := N)
    (Z := sourceZ N) g.D_one g.D_le_M g.Y_pos
  have hcard := actual_divisor_band_card_le_mass (sourceD N) (sourceY N)
  simp only [Nat.cast_mul] at hcard
  have hmass0 : 0 ≤ ∑ d ∈ divisorBand (sourceD N) (sourceY N), (d : ℝ)⁻¹ :=
    sum_nonneg (fun d _ => by positivity)
  have hDY := source_DY_le_two_N h
  calc
    _ ≤ (N : ℝ) * (∑ d ∈ divisorBand (sourceD N) (sourceY N), (d : ℝ)⁻¹) +
        ((divisorBand (sourceD N) (sourceY N)).card : ℝ) := hfirst
    _ ≤ ((N : ℝ) + (sourceD N : ℝ) * (sourceY N : ℝ)) *
        (∑ d ∈ divisorBand (sourceD N) (sourceY N), (d : ℝ)⁻¹) := by
      have hh := add_le_add_left hcard
        ((N : ℝ) * (∑ d ∈ divisorBand (sourceD N) (sourceY N), (d : ℝ)⁻¹))
      exact hh.trans_eq (by ring)
    _ ≤ (3 * (N : ℝ)) *
        (∑ d ∈ divisorBand (sourceD N) (sourceY N), (d : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right (by linarith) hmass0
    _ ≤ _ := mul_le_mul_of_nonneg_left (actual_source_divisor_band_mass h) (by positivity)

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound21.NonfriableReciprocal.labels0not1
#print axioms GoldbachRound21.NonfriableReciprocal.q0not1
#print axioms GoldbachRound21.NonfriableReciprocal.q01
#print axioms GoldbachRound21.NonfriableReciprocal.q0not1_witness
#print axioms GoldbachRound21.NonfriableReciprocal.q0not1_resource_injective
#print axioms GoldbachRound21.NonfriableReciprocal.q01_partition
#print axioms GoldbachRound21.NonfriableReciprocal.q01_partition_disjoint
#print axioms GoldbachRound21.NonfriableReciprocal.q0not1_reciprocal_image_subset
#print axioms GoldbachRound21.NonfriableReciprocal.actual_q0not1_tau_square_sum_le_global
#print axioms GoldbachRound21.NonfriableReciprocal.actual_resource0_projection_class_card
#print axioms GoldbachRound21.NonfriableReciprocal.actual_q0not1_card_le_mass
#print axioms GoldbachRound21.NonfriableReciprocal.source_DY_le_two_N
#print axioms GoldbachRound21.NonfriableReciprocal.actual_source_q0not1_card_le_three

end
end GoldbachRound21.NonfriableReciprocal
