import Mathlib.Data.Nat.Defs
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset

namespace TS16
namespace Goldbach

open scoped BigOperators

def localWindow (S : Finset Nat) (n h : Nat) : Finset Nat :=
  S.filter (fun k => n <= k /\ k <= n + h)

def localCount (S : Finset Nat) (n h : Nat) : Nat :=
  (localWindow S n h).card

def closePairs (S : Finset Nat) (h : Nat) : Finset (Nat × Nat) :=
  (S ×ˢ S).filter (fun p => p.1 ≠ p.2 /\ p.1.dist p.2 <= h)

def countPairs (S : Finset Nat) (h : Nat) : Nat :=
  ∑ a ∈ S, ∑ _b ∈ S.filter (fun b => a ≠ b /\ a.dist b <= h), 1

theorem countPairs_eq_closePairs_card (S : Finset Nat) (h : Nat) :
    countPairs S h = (closePairs S h).card := by
  symm
  calc
    (closePairs S h).card =
        ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 ≠ p.2 /\ p.1.dist p.2 <= h), 1 := by
      rw [closePairs, Finset.card_eq_sum_ones]
    _ = ∑ p ∈ S ×ˢ S, if p.1 ≠ p.2 /\ p.1.dist p.2 <= h then 1 else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ a ∈ S, ∑ b ∈ S, if a ≠ b /\ a.dist b <= h then 1 else 0 := by
      rw [Finset.sum_product]
    _ = ∑ a ∈ S, ∑ b ∈ S.filter (fun b => a ≠ b /\ a.dist b <= h), 1 := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [Finset.sum_filter]

def shortEnergy (S : Finset Nat) (x h : Nat) : Nat :=
  ∑ n ∈ Finset.range (x + 1), (localCount S n h)^2

def energyPairs (S : Finset Nat) (x h : Nat) :
    Finset (Sigma fun _ : Nat => Nat × Nat) :=
  (Finset.range (x + 1)).sigma fun n =>
    localWindow S n h ×ˢ localWindow S n h

def closePairToEnergyEmbedding : (Nat × Nat) ↪ Sigma fun _ : Nat => Nat × Nat where
  toFun p := ⟨min p.1 p.2, p⟩
  inj' := by
    intro p q hpq
    exact congrArg Sigma.snd hpq

theorem energyPairs_card (S : Finset Nat) (x h : Nat) :
    (energyPairs S x h).card = shortEnergy S x h := by
  calc
    (energyPairs S x h).card =
        ∑ n ∈ Finset.range (x + 1),
          (localWindow S n h ×ˢ localWindow S n h).card := by
      simp [energyPairs]
    _ = ∑ n ∈ Finset.range (x + 1),
        (localWindow S n h).card * (localWindow S n h).card := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      rw [Finset.card_product]
    _ = shortEnergy S x h := by
      simp [shortEnergy, localCount, pow_two]

theorem closePair_image_subset_energyPairs
    (S : Finset Nat) (x h : Nat) (hS : forall k, k ∈ S -> k <= x) :
    (closePairs S h).map closePairToEnergyEmbedding <= energyPairs S x h := by
  intro y hy
  rcases Finset.mem_map.mp hy with ⟨p, hp, rfl⟩
  rcases Finset.mem_filter.mp hp with ⟨hpSS, hpclose⟩
  rcases Finset.mem_product.mp hpSS with ⟨hp1S, hp2S⟩
  rcases hpclose with ⟨hpne, hpdist⟩
  have hmin_le_x : min p.1 p.2 <= x := by
    exact le_trans (min_le_left p.1 p.2) (hS p.1 hp1S)
  have hmin_mem_range : min p.1 p.2 ∈ Finset.range (x + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hmin_le_x)
  have hp1_window : p.1 ∈ localWindow S (min p.1 p.2) h := by
    rw [localWindow, Finset.mem_filter]
    constructor
    · exact hp1S
    · constructor
      · exact min_le_left p.1 p.2
      · rw [Nat.dist_eq_max_sub_min] at hpdist
        omega
  have hp2_window : p.2 ∈ localWindow S (min p.1 p.2) h := by
    rw [localWindow, Finset.mem_filter]
    constructor
    · exact hp2S
    · constructor
      · exact min_le_right p.1 p.2
      · rw [Nat.dist_eq_max_sub_min] at hpdist
        omega
  rw [energyPairs, Finset.mem_sigma]
  constructor
  · simpa [closePairToEnergyEmbedding] using hmin_mem_range
  · simpa [closePairToEnergyEmbedding] using
      (Finset.mem_product.mpr ⟨hp1_window, hp2_window⟩ :
        p ∈ localWindow S (min p.1 p.2) h ×ˢ localWindow S (min p.1 p.2) h)

theorem pair_count_le_energy
    (S : Finset Nat) (x h : Nat) (hS : forall k, k ∈ S -> k <= x) :
    countPairs S h <= shortEnergy S x h := by
  rw [countPairs_eq_closePairs_card]
  rw [← energyPairs_card S x h]
  rw [← Finset.card_map closePairToEnergyEmbedding]
  exact Finset.card_le_card (closePair_image_subset_energyPairs S x h hS)

end Goldbach
end TS16
