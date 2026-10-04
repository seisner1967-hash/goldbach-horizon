import NonSSBracketSwitch
import Mathlib.NumberTheory.SmoothNumbers

namespace GoldbachRound20.Friable

open Finset GoldbachRound19.Switch GoldbachRound19.NonSS
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Inclusive smoothness; the actual factor list retains multiplicity. -/
def Smooth (Y n : ℕ) : Prop := n ∈ Nat.smoothNumbers (Y + 1)

theorem resource0_ge_q_add_front {alpha N Z M e q : ℕ}
    (h : StructuralSupport alpha N Z M e q) :
    q + (N - 1) / alpha + 1 ≤ resource0 N q := by
  have hanchor := h.2.2.2.1
  have he : anchor N + 1 ≤ e := by omega
  have hh := Nat.mul_le_mul_right q he
  have hc := h.2.2.2.2.2.2.1
  unfold resource0
  rw [Nat.add_mul, one_mul] at hh
  omega

theorem resource1_ge_three_q_add_front {alpha N Z M e q : ℕ}
    (h : StructuralSupport alpha N Z M e q) :
    3 * q + (N - 1) / alpha + 1 ≤ resource1 N q := by
  have hp := anchor_three h.1
  have hanchor := h.2.2.2.1
  have he : 4 ≤ e := by omega
  have hh := Nat.mul_le_mul_right q he
  have hc := h.2.2.2.2.2.2.1
  unfold resource1
  have h4 : 4 * q = 3 * q + q := by omega
  omega

theorem resource0_ge_M_of_actual_cap {alpha N Z M e q : ℕ}
    (h : StructuralSupport alpha N Z M e q) : M ≤ resource0 N q := by
  have hh := resource0_ge_q_add_front h
  calc
    M ≤ q := h.2.2.1
    _ ≤ q + (N - 1) / alpha + 1 :=
      (Nat.le_add_right q ((N - 1) / alpha)).trans (Nat.le_add_right _ 1)
    _ ≤ resource0 N q := hh

theorem resource1_ge_M_of_actual_cap {alpha N Z M e q : ℕ}
    (h : StructuralSupport alpha N Z M e q) : M ≤ resource1 N q := by
  have hh := resource1_ge_three_q_add_front h
  calc
    M ≤ q := h.2.2.1
    _ ≤ 3 * q := by simpa using Nat.mul_le_mul_right q (show 1 ≤ 3 by decide)
    _ ≤ 3 * q + (N - 1) / alpha + 1 :=
      (Nat.le_add_right (3 * q) ((N - 1) / alpha)).trans (Nat.le_add_right _ 1)
    _ ≤ resource1 N q := hh

/-- A genuine prefix of the input list, not a set of distinct prime factors. -/
theorem bounded_list_prefix (l : List ℕ) :
    ∀ (acc D Y : ℕ), acc < D → 0 < Y → D ≤ acc * l.prod →
      (∀ p ∈ l, p ≤ Y) →
      ∃ first rest : List ℕ, l = first ++ rest ∧
        D ≤ acc * first.prod ∧ acc * first.prod < D * Y := by
  induction l with
  | nil =>
      intro acc D Y ha hY hp _
      simp only [List.prod_nil, mul_one] at hp
      omega
  | cons p l ih =>
      intro acc D Y ha hY hp hb
      have hpY : p ≤ Y := hb p (by simp)
      have hl : ∀ v ∈ l, v ≤ Y := fun v hv => hb v (by simp [hv])
      by_cases hit : D ≤ acc * p
      · refine ⟨[p], l, by simp, ?_, ?_⟩
        · simpa using hit
        · simp only [List.prod_cons, List.prod_nil, mul_one]
          exact (Nat.mul_le_mul_left acc hpY).trans_lt
            (Nat.mul_lt_mul_of_pos_right ha hY)
      · have ha' : acc * p < D := by omega
        have hp' : D ≤ (acc * p) * l.prod := by
          simpa only [List.prod_cons, mul_assoc] using hp
        obtain ⟨first, rest, heq, hlow, hupp⟩ := ih (acc * p) D Y ha' hY hp' hl
        refine ⟨p :: first, rest, by simp [heq], ?_, ?_⟩
        · simpa only [List.prod_cons, mul_assoc] using hlow
        · simpa only [List.prod_cons, mul_assoc] using hupp

/-- The selected divisor is the product of a prefix of primeFactorsList n. -/
theorem primeFactorsList_prefix_divisor {Y D n : ℕ} (hD : 1 < D)
    (hY : 0 < Y) (hn : D ≤ n) (hs : Smooth Y n) :
    ∃ first rest : List ℕ, n.primeFactorsList = first ++ rest ∧
      first.prod ∣ n ∧ D ≤ first.prod ∧ first.prod < D * Y ∧
      Smooth Y first.prod := by
  have hn0 : n ≠ 0 := hs.1
  have hprod : n.primeFactorsList.prod = n := Nat.prod_primeFactorsList hn0
  have hb : ∀ p ∈ n.primeFactorsList, p ≤ Y := by
    intro p hp
    have hh := hs.2 p hp
    omega
  obtain ⟨first, rest, heq, hlow, hupp⟩ :=
    bounded_list_prefix n.primeFactorsList 1 D Y hD hY (by simpa [hprod] using hn) hb
  have hd : first.prod ∣ n := by
    refine ⟨rest.prod, ?_⟩
    rw [← hprod, heq, List.prod_append]
  refine ⟨first, rest, heq, hd, by simpa using hlow, by simpa using hupp, ?_⟩
  exact Nat.mem_smoothNumbers_of_dvd hs hd

def divisorBand (D Y : ℕ) : Finset ℕ :=
  (Icc D (D * Y)).filter (Smooth Y)

theorem smooth_large_has_actual_band_divisor {Y D n : ℕ} (hD : 1 < D)
    (hY : 0 < Y) (hn : D ≤ n) (hs : Smooth Y n) :
    ∃ d ∈ divisorBand D Y, d ∣ n := by
  obtain ⟨first, rest, heq, hd, hlow, hupp, hsf⟩ :=
    primeFactorsList_prefix_divisor hD hY hn hs
  exact ⟨first.prod, mem_filter.mpr ⟨mem_Icc.mpr ⟨hlow, hupp.le⟩, hsf⟩, hd⟩

theorem actual_friable_resource0_cover {alpha N Z M e q D Y : ℕ}
    (h : StructuralSupport alpha N Z M e q) (hDM : D ≤ M)
    (hD : 1 < D) (hY : 0 < Y) (hf : Smooth Y (resource0 N q)) :
    ∃ d ∈ divisorBand D Y, d ∣ resource0 N q :=
  smooth_large_has_actual_band_divisor hD hY
    (hDM.trans (resource0_ge_M_of_actual_cap h)) hf

theorem actual_friable_resource1_cover {alpha N Z M e q D Y : ℕ}
    (h : StructuralSupport alpha N Z M e q) (hDM : D ≤ M)
    (hD : 1 < D) (hY : 0 < Y) (hf : Smooth Y (resource1 N q)) :
    ∃ d ∈ divisorBand D Y, d ∣ resource1 N q :=
  smooth_large_has_actual_band_divisor hD hY
    (hDM.trans (resource1_ge_M_of_actual_cap h)) hf

theorem resource1_divisor_class {N q d : ℕ} (hq : q ≤ N) :
    d ∣ resource1 N q ↔ q ≡ N [MOD d] := by
  unfold resource1
  exact (Nat.modEq_iff_dvd' hq).symm

theorem resource0_divisor_class {N q d : ℕ} (hq : anchor N * q ≤ N) :
    d ∣ resource0 N q ↔ anchor N * q ≡ N [MOD d] := by
  unfold resource0
  exact (Nat.modEq_iff_dvd' hq).symm

theorem resource0_anchor_nonunit_impossible {N q d : ℕ}
    (h : ResourceCell N q) (hd : anchor N ∣ d) : ¬ d ∣ resource0 N q := by
  intro hr
  exact (anchor_spec h).1.coprime_iff_not_dvd.mp (anchor_resource0_coprime h)
    (hd.trans hr)

theorem resource1_N_nonunit_impossible {N q d : ℕ}
    (h : ResourceCell N q) (hd : ¬ d.Coprime N) : ¬ d ∣ resource1 N q := by
  intro hr
  exact hd (Nat.Coprime.of_dvd_left hr (resource1_unit h))

theorem resource0_N_nonunit_impossible {N q d : ℕ}
    (h : ResourceCell N q) (hd : ¬ d.Coprime N) : ¬ d ∣ resource0 N q := by
  intro hr
  exact hd (Nat.Coprime.of_dvd_left hr (resource0_unit h))

#print axioms Smooth
#print axioms resource0_ge_q_add_front
#print axioms resource1_ge_three_q_add_front
#print axioms resource0_ge_M_of_actual_cap
#print axioms resource1_ge_M_of_actual_cap
#print axioms bounded_list_prefix
#print axioms primeFactorsList_prefix_divisor
#print axioms divisorBand
#print axioms smooth_large_has_actual_band_divisor
#print axioms actual_friable_resource0_cover
#print axioms actual_friable_resource1_cover
#print axioms resource1_divisor_class
#print axioms resource0_divisor_class
#print axioms resource0_anchor_nonunit_impossible
#print axioms resource1_N_nonunit_impossible
#print axioms resource0_N_nonunit_impossible

end
end GoldbachRound20.Friable
