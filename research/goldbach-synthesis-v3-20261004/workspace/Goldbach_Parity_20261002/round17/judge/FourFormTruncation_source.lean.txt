import PowersetMoment
import SelbergFourForms

/-! A finite truncation for the constructed actual G. The prime-log sum input
is an explicit analytic obligation, not a lower bound on G or C4/C6. -/
namespace GoldbachRound17.FourFormTruncation
open Finset
open scoped BigOperators
open GoldbachRound17
noncomputable section

def actualH (N e p0 : ℕ) (p : ℕ) : ℝ :=
  Selberg.actualDensity N e p0 p / (1 - Selberg.actualDensity N e p0 p)

def actualEuler (N e p0 y : ℕ) : ℝ :=
  ∏ p ∈ Selberg.primeSupport y, (1 + actualH N e p0 p)

theorem primeSupport_mono {y z : ℕ} (hyz : y ≤ z) :
    Selberg.primeSupport y ⊆ Selberg.primeSupport z := by
  intro p hp
  exact Selberg.mem_primeSupport.mpr
    ⟨(Selberg.mem_primeSupport.mp hp).1, le_trans (Selberg.mem_primeSupport.mp hp).2 hyz⟩

theorem G_mono_support {P Q : Finset ℕ} {z : ℕ} {g : ℕ → ℝ}
    (hPQ : P ⊆ Q) (hg : ∀ p ∈ Q, 0 < g p ∧ g p < 1) :
    Selberg.G P z g ≤ Selberg.G Q z g := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    obtain ⟨hsP, hsz⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hsP).trans hPQ), hsz⟩
  · intro s hs _
    exact (Selberg.hprod_pos hg (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1)).le

theorem actualH_nonneg {N e p0 y : ℕ}
    (hns : ∀ p ∈ Selberg.primeSupport y, FourFormRoots.actualRho p N e p0 < p) :
    ∀ p ∈ Selberg.primeSupport y, 0 ≤ actualH N e p0 p := by
  intro p hp
  obtain ⟨hg0, hg1⟩ := Selberg.actual_density_properties hns p hp
  exact (div_pos hg0 (sub_pos.mpr hg1)).le

theorem actualH_ratio {N e p0 y p : ℕ}
    (hns : ∀ p ∈ Selberg.primeSupport y, FourFormRoots.actualRho p N e p0 < p)
    (hp : p ∈ Selberg.primeSupport y) :
    actualH N e p0 p / (1 + actualH N e p0 p) = Selberg.actualDensity N e p0 p := by
  obtain ⟨_, hg1⟩ := Selberg.actual_density_properties hns p hp
  have hn : 1 - Selberg.actualDensity N e p0 p ≠ 0 := (sub_pos.mpr hg1).ne'
  unfold actualH
  field_simp

theorem actual_weighted_moment {N e p0 y : ℕ}
    (hns : ∀ p ∈ Selberg.primeSupport y, FourFormRoots.actualRho p N e p0 < p) :
    (∑ s ∈ (Selberg.primeSupport y).powerset,
      PowersetMoment.subsetWeight (actualH N e p0) s * PowersetMoment.subsetLog s) =
      actualEuler N e p0 y *
        (∑ p ∈ Selberg.primeSupport y, Selberg.actualDensity N e p0 p * Real.log p) := by
  dsimp only [PowersetMoment.subsetLog]
  rw [PowersetMoment.weighted_moment _ _ _ (actualH_nonneg hns)]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [actualH_ratio hns hp]

theorem actual_density_log_sum_le_four {N e p0 y : ℕ}
    (heN : e.Coprime N) (hpN : p0.Coprime N) :
    (∑ p ∈ Selberg.primeSupport y, Selberg.actualDensity N e p0 p * Real.log p) ≤
      4 * (∑ p ∈ Selberg.primeSupport y, Real.log p / p) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  haveI : Fact p.Prime := ⟨(Selberg.mem_primeSupport.mp hp).1⟩
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Selberg.mem_primeSupport.mp hp).1.pos
  have hr : (FourFormRoots.actualRho p N e p0 : ℝ) ≤ 4 := by
    exact_mod_cast (FourFormRoots.rho_le_four heN hpN)
  have hg : Selberg.actualDensity N e p0 p ≤ 4 / (p : ℝ) :=
    div_le_div_of_nonneg_right hr hp0.le
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hm := mul_le_mul_of_nonneg_right hg hl
  dsimp [Selberg.actualDensity, FourFormRoots.localDensity] at *
  convert hm using 1; ring

theorem actual_G_half_euler_of_log_moment {N e p0 y z : ℕ}
    (hyz : y ≤ z) (hz : 0 < (z : ℝ)) (hT : 0 < Real.log z)
    (hns : ∀ p ∈ Selberg.primeSupport z, FourFormRoots.actualRho p N e p0 < p)
    (hm : (∑ p ∈ Selberg.primeSupport y,
      Selberg.actualDensity N e p0 p * Real.log p) ≤ Real.log z / 2) :
    actualEuler N e p0 y / 2 ≤ Selberg.actualG N e p0 z := by
  have hsub := primeSupport_mono hyz
  have hny : ∀ p ∈ Selberg.primeSupport y, FourFormRoots.actualRho p N e p0 < p :=
    fun p hp => hns p (hsub hp)
  have hE : 0 ≤ actualEuler N e p0 y := by
    exact Finset.prod_nonneg fun p hp => by linarith [actualH_nonneg hny p hp]
  have hmoment :
      (∑ s ∈ (Selberg.primeSupport y).powerset,
        PowersetMoment.subsetWeight (actualH N e p0) s * PowersetMoment.subsetLog s) ≤
        Real.log z / 2 * (∑ s ∈ (Selberg.primeSupport y).powerset,
          PowersetMoment.subsetWeight (actualH N e p0) s) := by
    rw [actual_weighted_moment hny, PowersetMoment.total_weight]
    change actualEuler N e p0 y * _ ≤ Real.log z / 2 * actualEuler N e p0 y
    nlinarith
  have hc := PowersetMoment.cutoff_markov (Selberg.primeSupport y) (actualH N e p0) z
    (actualH_nonneg hny)
    (fun p hp => (Selberg.mem_primeSupport.mp hp).1.pos) hz hT hmoment
  rw [PowersetMoment.total_weight] at hc
  have heq : (∑ s ∈ (Selberg.primeSupport y).powerset.filter
      (fun s => (∏ p ∈ s, p) ≤ z), PowersetMoment.subsetWeight (actualH N e p0) s) =
      Selberg.G (Selberg.primeSupport y) z (Selberg.actualDensity N e p0) := rfl
  rw [heq] at hc
  exact hc.trans (G_mono_support hsub (Selberg.actual_density_properties hns))

theorem actual_G_half_euler_of_prime_log_sum {N e p0 y z : ℕ}
    (hyz : y ≤ z) (hz : 0 < (z : ℝ)) (heN : e.Coprime N) (hpN : p0.Coprime N)
    (hns : ∀ p ∈ Selberg.primeSupport z, FourFormRoots.actualRho p N e p0 < p)
    (hlogz : 32 ≤ Real.log z) (hlogy : 32 * Real.log y ≤ Real.log z)
    (hprime : (∑ p ∈ Selberg.primeSupport y, Real.log p / p) ≤ 2 + 2 * Real.log y) :
    actualEuler N e p0 y / 2 ≤ Selberg.actualG N e p0 z := by
  apply actual_G_half_euler_of_log_moment hyz hz (by linarith) hns
  have hm := actual_density_log_sum_le_four (y := y) heN hpN
  nlinarith

#print axioms actualH
#print axioms actualEuler
#print axioms primeSupport_mono
#print axioms G_mono_support
#print axioms actualH_nonneg
#print axioms actualH_ratio
#print axioms actual_weighted_moment
#print axioms actual_density_log_sum_le_four
#print axioms actual_G_half_euler_of_log_moment
#print axioms actual_G_half_euler_of_prime_log_sum

end
end GoldbachRound17.FourFormTruncation
