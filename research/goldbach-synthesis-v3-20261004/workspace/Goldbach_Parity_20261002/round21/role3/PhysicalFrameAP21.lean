import SwitchedIncidenceEstimator

/-! Round21 / 13.13. Exact extraction of the already constructed physical
domain. There is no primality test on the candidate j. -/
namespace GoldbachRound21.PhysicalAP

open scoped BigOperators
open Finset
open GoldbachRound18.SeparatedTypeII
open GoldbachRound20.SwitchedComposite
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 8000000

structure StaticAxes (F : Parameters) (s : ℕ) : Prop where
  c_prime : F.c.Prime
  r_prime : F.r.Prime
  s_prime : s.Prime
  c_lt_r : F.c < F.r
  r_lt_s : F.r < s
  s_le_a : s ≤ F.a
  cr_le_a : conductor F ≤ F.a
  cs_le_a : F.c * s ≤ F.a
  a_lt_rs : F.a < F.r * s
  a_lt_crs : F.a < conductor F * s
  unit_t : Nat.Coprime (switchedConductor F s) F.N

theorem StaticAxes.conductor_pos {F : Parameters} {s : ℕ}
    (h : StaticAxes F s) : 0 < switchedConductor F s := by
  unfold switchedConductor conductor
  exact Nat.mul_pos (Nat.mul_pos h.c_prime.pos h.r_prime.pos) h.s_prime.pos

theorem ceilDiv_le_iff (v t q : ℕ) (ht : 0 < t) :
    (v + t - 1) / t ≤ q ↔ v ≤ t * q := by
  rw [Nat.div_le_iff_le_mul_add_pred ht]
  have he : v + t - 1 = v + (t - 1) := by omega
  rw [he]
  omega

theorem frameLower_le_iff {F : Parameters} {s x q : ℕ}
    (ht : 0 < switchedConductor F s) :
    frameLower F s x ≤ q ↔
      F.a < q ∧ F.r * s < q ∧ F.N - x ≤ switchedConductor F s * q ∧
        F.M ≤ switchedConductor F s * q := by
  simp only [frameLower, max_le_iff, ceilDiv_le_iff _ _ _ ht]
  omega

theorem frameUpper_ge_iff {F : Parameters} {s x q : ℕ}
    (ht : 0 < switchedConductor F s) :
    q ≤ frameUpper F s x ↔
      switchedConductor F s * q ≤ F.N - x / 2 - 1 ∧
        switchedConductor F s * q ≤ F.N - F.Q - 1 := by
  simp only [frameUpper, le_min_iff, Nat.le_div_iff_mul_le ht]
  simp only [Nat.mul_comm q (switchedConductor F s)]

theorem frameCandidate_bounds {F : Parameters} {s x q : ℕ}
    (ht : 0 < switchedConductor F s) (hq : 0 < q) (hx : x ≤ F.N)
    (hframe : q ∈ frameInterval F s x) :
    x / 2 < switchedCandidate F s q ∧ switchedCandidate F s q ≤ x ∧
      switchedConductor F s * q + F.Q < F.N := by
  obtain ⟨hl, hu⟩ := mem_Icc.mp hframe
  obtain ⟨_, _, hlx, _⟩ := (frameLower_le_iff ht).mp hl
  obtain ⟨hux, huQ⟩ := (frameUpper_ge_iff ht).mp hu
  have hprod : 0 < switchedConductor F s * q := Nat.mul_pos ht hq
  unfold switchedCandidate
  omega

theorem physicalQDomain_frame_exact {F : Parameters} {s z x : ℕ}
    (haxes : StaticAxes F s) (hx : x ≤ F.N)
    (hfront : max 1 z < x / 2 + 1) :
    physicalQDomain F s z (frameInterval F s x) =
      (frameInterval F s x).filter fun q => q.Prime ∧ Nat.Coprime q F.N := by
  ext q
  constructor
  · intro hq
    have hmem := (mem_physicalQDomain.mp hq).1
    have hp := physicalQDomain_prime hq
    have hu : Nat.Coprime q F.N :=
      (physicalQDomain_unit hq).coprime_dvd_left (dvd_mul_left q _)
    exact mem_filter.mpr ⟨hmem, hp, hu⟩
  · intro hq
    obtain ⟨hmem, hp, hu⟩ := mem_filter.mp hq
    have ht := haxes.conductor_pos
    obtain ⟨hl, _⟩ := mem_Icc.mp hmem
    obtain ⟨haq, hrsq, _, hbulk⟩ := (frameLower_le_iff ht).mp hl
    obtain ⟨hjleft, _, horiginal⟩ := frameCandidate_bounds ht hp.pos hx hmem
    have hunit : Nat.Coprime (switchedConductor F s * q) F.N :=
      Nat.coprime_mul_iff_left.mpr ⟨haxes.unit_t, hu⟩
    let w : PhysicalWitness F (s * q) :=
      { s := s, q := q, c_prime := haxes.c_prime, r_prime := haxes.r_prime,
        s_prime := haxes.s_prime, q_prime := hp,
        c_lt_r := haxes.c_lt_r, r_lt_s := haxes.r_lt_s,
        s_le_a := haxes.s_le_a, a_lt_q := haq,
        cr_le_a := haxes.cr_le_a, cs_le_a := haxes.cs_le_a,
        a_lt_rs := haxes.a_lt_rs, rs_lt_q := hrsq,
        a_lt_crs := haxes.a_lt_crs, b_eq := rfl,
        unit_m := by simpa [switchedConductor, Nat.mul_assoc] using hunit,
        bulk := by simpa [switchedConductor, Nat.mul_assoc] using hbulk,
        original_front := by simpa [switchedConductor, Nat.mul_assoc] using horiginal }
    have hzj : z < switchedCandidate F s q := by
      have hz := le_max_right 1 z
      omega
    have hj2 : 2 ≤ switchedCandidate F s q := by
      have h1 := le_max_left 1 z
      omega
    exact mem_physicalQDomain.mpr ⟨hmem, ⟨w, rfl, rfl⟩, hj2, hzj⟩

theorem physicalCompositeWindow_frame_exact {F : Parameters} {s z x p : ℕ}
    (haxes : StaticAxes F s) (hx : x ≤ F.N)
    (hfront : max 1 z < x / 2 + 1) :
    physicalCompositeWindow F s z p (frameInterval F s x) =
      if p ^ 2 ≤ F.N then
        (Icc (frameLower F s x)
          (min (frameUpper F s x) ((F.N - p ^ 2) / switchedConductor F s))).filter
            (fun q => q.Prime ∧ Nat.Coprime q F.N)
      else ∅ := by
  ext q
  by_cases hpN : p ^ 2 ≤ F.N
  · rw [if_pos hpN]
    constructor
    · intro hq
      have hbase : q ∈ physicalQDomain F s z (frameInterval F s x) :=
        (mem_filter.mp hq).1
      have hcap := (physicalCompositeWindow_cap haxes.conductor_pos hbase).mp hq
      rw [physicalQDomain_frame_exact haxes hx hfront] at hbase
      obtain ⟨hb, hprime, hunit⟩ := mem_filter.mp hbase
      obtain ⟨hl, hu⟩ := mem_Icc.mp hb
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hl, le_min hu hcap.2⟩, hprime, hunit⟩
    · intro hq
      obtain ⟨hb, hprime, hunit⟩ := mem_filter.mp hq
      obtain ⟨hl, hu⟩ := mem_Icc.mp hb
      obtain ⟨hU, hcap⟩ := le_min_iff.mp hu
      have hbase : q ∈ physicalQDomain F s z (frameInterval F s x) := by
        rw [physicalQDomain_frame_exact haxes hx hfront]
        exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hl, hU⟩, hprime, hunit⟩
      exact (physicalCompositeWindow_cap haxes.conductor_pos hbase).mpr ⟨hpN, hcap⟩
  · rw [if_neg hpN, mem_empty, iff_false]
    intro hq
    have hbase := (mem_filter.mp hq).1
    exact hpN ((physicalCompositeWindow_cap haxes.conductor_pos hbase).mp hq).1

def primeUnitAPMass (N t nu L U : ℕ) : ℝ :=
  ∑ q ∈ (Icc L U).filter (fun q => q.Prime ∧ Nat.Coprime q N),
    if Nat.ModEq nu (t * q) N then Real.log ((N - t * q : ℕ) : ℝ) else 0

theorem actualPrimeAP_frame_reindex {F : Parameters} {s z x nu : ℕ}
    (haxes : StaticAxes F s) (hx : x ≤ F.N)
    (hfront : max 1 z < x / 2 + 1) :
    actualPrimeAP F s z nu (frameInterval F s x) =
      primeUnitAPMass F.N (switchedConductor F s) nu
        (frameLower F s x) (frameUpper F s x) := by
  unfold actualPrimeAP primeUnitAPMass
  apply sum_congr (physicalQDomain_frame_exact haxes hx hfront)
  intro q hq
  simp only [physical_candidate_AP_iff hq, switchedCandidate]

theorem actualCompositeAP_frame_reindex {F : Parameters} {s z x k l h p : ℕ}
    (haxes : StaticAxes F s) (hx : x ≤ F.N)
    (hfront : max 1 z < x / 2 + 1) :
    actualCompositeAP F s z k l h p (frameInterval F s x) =
      if p ^ 2 ≤ F.N then
        primeUnitAPMass F.N (switchedConductor F s)
          (compositeAPConductor k l h p) (frameLower F s x)
          (min (frameUpper F s x) ((F.N - p ^ 2) / switchedConductor F s))
      else 0 := by
  unfold actualCompositeAP
  by_cases hpN : p ^ 2 ≤ F.N
  · rw [if_pos hpN]
    unfold primeUnitAPMass
    apply sum_congr (by simpa [hpN] using
      physicalCompositeWindow_frame_exact (p := p) haxes hx hfront)
    intro q hq
    have hbase : q ∈ physicalQDomain F s z (frameInterval F s x) :=
      (mem_filter.mp hq).1
    simp only [physical_candidate_AP_iff hbase, switchedCandidate]
  · rw [if_neg hpN, physicalCompositeWindow_frame_exact haxes hx hfront]
    simp [hpN]

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound21.PhysicalAP.StaticAxes
#print axioms GoldbachRound21.PhysicalAP.StaticAxes.conductor_pos
#print axioms GoldbachRound21.PhysicalAP.ceilDiv_le_iff
#print axioms GoldbachRound21.PhysicalAP.frameLower_le_iff
#print axioms GoldbachRound21.PhysicalAP.frameUpper_ge_iff
#print axioms GoldbachRound21.PhysicalAP.frameCandidate_bounds
#print axioms GoldbachRound21.PhysicalAP.physicalQDomain_frame_exact
#print axioms GoldbachRound21.PhysicalAP.physicalCompositeWindow_frame_exact
#print axioms GoldbachRound21.PhysicalAP.primeUnitAPMass
#print axioms GoldbachRound21.PhysicalAP.actualPrimeAP_frame_reindex
#print axioms GoldbachRound21.PhysicalAP.actualCompositeAP_frame_reindex

end
end GoldbachRound21.PhysicalAP
