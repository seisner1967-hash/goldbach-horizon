import NonfriableReciprocalBudget

namespace GoldbachRound21.NonfriableReciprocal

open Finset GoldbachRound19.Switch GoldbachRound19.NonSS
open GoldbachRound20.Friable GoldbachRound20.Friable.SourceGeometry
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000

def demandVertex (N : ℕ) (v : ℕ × ℕ) : ℕ × ℕ := (N - v.1 * v.2, v.1 * v.2)

def reciprocalVertex (N q : ℕ) : ℕ × ℕ := (q, resource1 N q)

def demandVertices (alpha N Z M Y : ℕ) : Finset (ℕ × ℕ) :=
  (friableDemandDomain alpha N Z M Y).image (demandVertex N)

def reciprocalVertices (alpha N Z M Y : ℕ) : Finset (ℕ × ℕ) :=
  (q01 alpha N Z M Y).image (reciprocalVertex N)

def removedVertices (alpha N Z M Y : ℕ) : Finset (ℕ × ℕ) :=
  demandVertices alpha N Z M Y ∪ reciprocalVertices alpha N Z M Y

def vertexAbsCost (alpha a N : ℕ) (w : ℕ × ℕ) : ℝ :=
  |GoldbachRound11.sourceBracket alpha a N w.1 w.2|

def removedUnionAbsCost (alpha a N Z M Y : ℕ) : ℝ :=
  ∑ w ∈ removedVertices alpha N Z M Y, vertexAbsCost alpha a N w

def extendedFriableCost (alpha a N Z M Y : ℕ) : ℝ :=
  friableThetaDemand alpha a N Z M Y + uniqueReciprocalCost1 alpha a N Z M Y +
    uniqueF0notF1Cost alpha a N Z M Y

def sourceRemovedUnionAbsCost (N : ℕ) : ℝ :=
  removedUnionAbsCost (sourceAlpha N) (sourceA N) N (sourceZ N) (sourceM N) (sourceY N)

theorem finite_sum_image_nonnegative_le {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (f : ι → κ) (w : κ → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x ∈ S.image f, w x) ≤ ∑ i ∈ S, w (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [image_insert, sum_insert hi]
    by_cases him : f i ∈ S.image f
    · rw [insert_eq_of_mem him]
      exact ih.trans (le_add_of_nonneg_left (hw (f i)))
    · rw [sum_insert him]
      exact add_le_add_left ih _

theorem actual_demand_vertex_abs_eq_theta {alpha a N Z M Y : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ friableDemandDomain alpha N Z M Y) :
    vertexAbsCost alpha a N (demandVertex N v) = |thetaBracket alpha a N v.1 v.2| := by
  have hs := physicalDomain_support (mem_filter.mp hv).1
  have hp : v.2.Prime ∧ v.2.Coprime N := ⟨hs.2.1, hs.1.q_unit⟩
  simp only [vertexAbsCost, demandVertex, thetaBracket, GoldbachRound11.primeIncidence,
    if_pos hp, one_mul]

theorem actual_demand_vertices_cost_le (alpha a N Z M Y : ℕ) :
    (∑ w ∈ demandVertices alpha N Z M Y, vertexAbsCost alpha a N w) ≤
      friableThetaDemand alpha a N Z M Y := by
  have hi := finite_sum_image_nonnegative_le
    (friableDemandDomain alpha N Z M Y) (demandVertex N) (vertexAbsCost alpha a N)
    (fun w => abs_nonneg _)
  unfold demandVertices friableThetaDemand
  exact hi.trans_eq (sum_congr rfl (fun v hv => actual_demand_vertex_abs_eq_theta hv))

theorem reciprocalVertex_injective (N : ℕ) : Function.Injective (reciprocalVertex N) := by
  intro q r he
  exact congrArg Prod.fst he

theorem actual_reciprocal_vertices_cost_partition (alpha a N Z M Y : ℕ) :
    (∑ w ∈ reciprocalVertices alpha N Z M Y, vertexAbsCost alpha a N w) =
      uniqueReciprocalCost1 alpha a N Z M Y + uniqueF0notF1Cost alpha a N Z M Y := by
  unfold reciprocalVertices
  rw [sum_image (reciprocalVertex_injective N).injOn]
  simp only [vertexAbsCost, reciprocalVertex]
  rw [q01_partition, sum_union (q01_partition_disjoint alpha N Z M Y)]
  rfl

theorem actual_removed_union_cost_le (alpha a N Z M Y : ℕ) :
    removedUnionAbsCost alpha a N Z M Y ≤ extendedFriableCost alpha a N Z M Y := by
  let D := demandVertices alpha N Z M Y
  let R := reciprocalVertices alpha N Z M Y
  let w := vertexAbsCost alpha a N
  have he : (∑ v ∈ D ∪ R, w v) + (∑ v ∈ D ∩ R, w v) =
      (∑ v ∈ D, w v) + ∑ v ∈ R, w v := Finset.sum_union_inter
  have hinter : 0 ≤ ∑ v ∈ D ∩ R, w v := sum_nonneg (fun v _ => abs_nonneg _)
  have hfirst := actual_demand_vertices_cost_le alpha a N Z M Y
  have hsecond := actual_reciprocal_vertices_cost_partition alpha a N Z M Y
  unfold removedUnionAbsCost removedVertices extendedFriableCost
  change (∑ v ∈ D ∪ R, w v) ≤
    friableThetaDemand alpha a N Z M Y + uniqueReciprocalCost1 alpha a N Z M Y +
      uniqueF0notF1Cost alpha a N Z M Y
  change (∑ v ∈ D, w v) ≤ friableThetaDemand alpha a N Z M Y at hfirst
  change (∑ v ∈ R, w v) = uniqueReciprocalCost1 alpha a N Z M Y +
    uniqueF0notF1Cost alpha a N Z M Y at hsecond
  linarith

theorem actual_source_removed_union_cost_le_extended (N : ℕ) :
    sourceRemovedUnionAbsCost N ≤ sourceExtendedFriableCost N := by
  simpa only [sourceRemovedUnionAbsCost, sourceExtendedFriableCost,
    sourceFriableAbsoluteCost, sourceUniqueF0notF1Cost, extendedFriableCost] using
    actual_removed_union_cost_le (sourceAlpha N) (sourceA N) N
      (sourceZ N) (sourceM N) (sourceY N)

theorem actual_source_removed_union_cost_budget {N : ℕ} (h : SourceOnset N) :
    sourceRemovedUnionAbsCost N ≤ (N : ℝ) / (8192 * sourceU N * sourceEll N) :=
  (actual_source_removed_union_cost_le_extended N).trans
    (actual_source_extended_friable_cost_budget h)

-- AXIOM_AUDIT_BEGIN
#print axioms GoldbachRound21.NonfriableReciprocal.demandVertex
#print axioms GoldbachRound21.NonfriableReciprocal.reciprocalVertex
#print axioms GoldbachRound21.NonfriableReciprocal.demandVertices
#print axioms GoldbachRound21.NonfriableReciprocal.reciprocalVertices
#print axioms GoldbachRound21.NonfriableReciprocal.removedVertices
#print axioms GoldbachRound21.NonfriableReciprocal.vertexAbsCost
#print axioms GoldbachRound21.NonfriableReciprocal.removedUnionAbsCost
#print axioms GoldbachRound21.NonfriableReciprocal.extendedFriableCost
#print axioms GoldbachRound21.NonfriableReciprocal.sourceRemovedUnionAbsCost
#print axioms GoldbachRound21.NonfriableReciprocal.finite_sum_image_nonnegative_le
#print axioms GoldbachRound21.NonfriableReciprocal.actual_demand_vertex_abs_eq_theta
#print axioms GoldbachRound21.NonfriableReciprocal.actual_demand_vertices_cost_le
#print axioms GoldbachRound21.NonfriableReciprocal.reciprocalVertex_injective
#print axioms GoldbachRound21.NonfriableReciprocal.actual_reciprocal_vertices_cost_partition
#print axioms GoldbachRound21.NonfriableReciprocal.actual_removed_union_cost_le
#print axioms GoldbachRound21.NonfriableReciprocal.actual_source_removed_union_cost_le_extended
#print axioms GoldbachRound21.NonfriableReciprocal.actual_source_removed_union_cost_budget

end
end GoldbachRound21.NonfriableReciprocal
