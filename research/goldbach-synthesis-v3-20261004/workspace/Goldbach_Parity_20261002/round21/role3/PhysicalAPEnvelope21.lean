import PhysicalFrameAP21
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L1Space

/-! Both sides of every AP jump are represented by a nonempty finite maximum.
The envelope is defined from ordinary prime sums before the physical weight. -/
namespace GoldbachRound21.PhysicalAP

open scoped BigOperators
open Finset MeasureTheory
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 8000000

def ordinaryPrimeCoefficient (N t nu q : ℕ) : ℝ :=
  if q.Prime ∧ Nat.ModEq nu (t * q) N then Real.log (q : ℝ) else 0

def ordinaryPrimeTheta (N t nu m : ℕ) : ℝ :=
  ∑ q ∈ Icc 0 m, ordinaryPrimeCoefficient N t nu q

def ordinaryAPError (N t nu : ℕ) (y : ℝ) : ℝ :=
  ordinaryPrimeTheta N t nu ⌊y⌋₊ - y / (Nat.totient nu : ℝ)

def ordinaryErrorCell (N t nu U m : ℕ) : ℝ :=
  max |ordinaryPrimeTheta N t nu m - (m : ℝ) / (Nat.totient nu : ℝ)|
    |ordinaryPrimeTheta N t nu m -
      min ((m : ℝ) + 1) (U : ℝ) / (Nat.totient nu : ℝ)|

def physicalAPEnvelope (N t nu U : ℕ) : ℝ :=
  (range (U + 1)).sup' (by exact ⟨0, by simp⟩)
    (ordinaryErrorCell N t nu U)

theorem ordinaryErrorCell_nonneg (N t nu U m : ℕ) :
    0 ≤ ordinaryErrorCell N t nu U m :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem ordinaryErrorCell_le_envelope {N t nu U m : ℕ} (hm : m ≤ U) :
    ordinaryErrorCell N t nu U m ≤ physicalAPEnvelope N t nu U := by
  unfold physicalAPEnvelope
  exact le_sup' _ (mem_range.mpr (by omega))

theorem physicalAPEnvelope_nonneg (N t nu U : ℕ) :
    0 ≤ physicalAPEnvelope N t nu U :=
  (ordinaryErrorCell_nonneg _ _ _ _ 0).trans (ordinaryErrorCell_le_envelope (Nat.zero_le _))

theorem ordinaryAPError_le_envelope {N t nu U : ℕ} {y : ℝ}
    (hnu : 0 < nu) (hy0 : 0 ≤ y) (hyU : y ≤ (U : ℝ)) :
    |ordinaryAPError N t nu y| ≤ physicalAPEnvelope N t nu U := by
  have hphi : 0 < (Nat.totient nu : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hnu
  have hm : ⌊y⌋₊ ≤ U := Nat.floor_le_of_le hyU
  have hmy : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  have hym : y ≤ min ((⌊y⌋₊ : ℝ) + 1) (U : ℝ) :=
    le_min (Nat.lt_floor_add_one y).le hyU
  have hcell := ordinaryErrorCell_le_envelope (N := N) (t := t) (nu := nu) hm
  have hleft : |ordinaryPrimeTheta N t nu ⌊y⌋₊ -
      (⌊y⌋₊ : ℝ) / (Nat.totient nu : ℝ)| ≤ physicalAPEnvelope N t nu U :=
    (le_max_left _ _).trans hcell
  have hright : |ordinaryPrimeTheta N t nu ⌊y⌋₊ -
      min ((⌊y⌋₊ : ℝ) + 1) (U : ℝ) / (Nat.totient nu : ℝ)| ≤
        physicalAPEnvelope N t nu U := (le_max_right _ _).trans hcell
  obtain ⟨hl0, hl1⟩ := abs_le.mp hleft
  obtain ⟨hr0, hr1⟩ := abs_le.mp hright
  have hdl := div_le_div_of_nonneg_right hmy hphi.le
  have hdr := div_le_div_of_nonneg_right hym hphi.le
  unfold ordinaryAPError
  apply abs_le.mpr
  constructor <;> linarith

theorem measurable_ordinaryAPError (N t nu : ℕ) :
    Measurable (ordinaryAPError N t nu) := by
  unfold ordinaryAPError
  exact ((measurable_from_nat (f := ordinaryPrimeTheta N t nu)).comp
    Nat.measurable_floor).sub (measurable_id.div_const _)

theorem error_mul_integrableOn {N t nu U : ℕ} {A : ℝ} {g : ℝ → ℝ}
    (hnu : 0 < nu) (hA : 0 ≤ A)
    (hg : IntegrableOn g (Set.Icc A (U : ℝ))) :
    IntegrableOn (fun y => ordinaryAPError N t nu y * g y)
      (Set.Icc A (U : ℝ)) := by
  apply hg.bdd_mul' (measurable_ordinaryAPError N t nu).aestronglyMeasurable
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  exact ae_of_all _ fun y hy => by
    rw [Real.norm_eq_abs]
    exact ordinaryAPError_le_envelope hnu (hA.trans hy.1) hy.2

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound21.PhysicalAP.ordinaryPrimeCoefficient
#print axioms GoldbachRound21.PhysicalAP.ordinaryPrimeTheta
#print axioms GoldbachRound21.PhysicalAP.ordinaryAPError
#print axioms GoldbachRound21.PhysicalAP.ordinaryErrorCell
#print axioms GoldbachRound21.PhysicalAP.physicalAPEnvelope
#print axioms GoldbachRound21.PhysicalAP.ordinaryErrorCell_nonneg
#print axioms GoldbachRound21.PhysicalAP.ordinaryErrorCell_le_envelope
#print axioms GoldbachRound21.PhysicalAP.physicalAPEnvelope_nonneg
#print axioms GoldbachRound21.PhysicalAP.ordinaryAPError_le_envelope
#print axioms GoldbachRound21.PhysicalAP.measurable_ordinaryAPError
#print axioms GoldbachRound21.PhysicalAP.error_mul_integrableOn

end
end GoldbachRound21.PhysicalAP
