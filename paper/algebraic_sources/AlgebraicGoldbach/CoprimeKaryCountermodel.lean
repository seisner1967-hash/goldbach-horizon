import AlgebraicGoldbach.CoprimeKaryModels
import Mathlib.Tactic.FinCases

/-!
For every k >= 2, the actual k-ary arithmetic divisor family admits a Boolean
common zero of the original ordered g at N = 4. This is a scoped control-family
obstruction, not a Goldbach counterexample or an obstruction to other families.
-/

namespace AlgebraicGoldbach.CoprimeKaryCountermodel

noncomputable section
open scoped BigOperators
open MvPolynomial CoprimeKaryIdeal

instance arithmeticIndexFintype (N k : ℕ) : Fintype (ArithmeticIndex N k) :=
  Fintype.ofFinite _

def modelAtFour : Fin 5 → ℚ := fun i => if i.val = 3 then 1 else 0

theorem modelAtFour_omittedPrimes :
    CoprimeDivisor.omittedPrimes 4 modelAtFour = {(2 : Fin 5)} := by
  ext i
  fin_cases i <;> norm_num [CoprimeDivisor.omittedPrimes, modelAtFour, Fin.ext_iff]

theorem modelAtFour_omitted_card :
    (CoprimeDivisor.omittedPrimes 4 modelAtFour).card = 1 := by
  rw [modelAtFour_omittedPrimes]
  exact Finset.card_singleton _

theorem modelAtFour_family (k : ℕ) (hk : 2 ≤ k) (S : ArithmeticIndex 4 k) :
    eval modelAtFour (arithmeticFamily 4 k S) = 0 := by
  apply (CoprimeKaryModels.family_iff_omitted_card_lt 4 k modelAtFour).mpr _ S
  rw [modelAtFour_omitted_card]
  omega

theorem modelAtFour_boolean (i : Fin 5) :
    eval modelAtFour (booleanConstraint i) = 0 := by
  rw [booleanConstraint_eval]
  unfold modelAtFour
  split_ifs <;> norm_num

theorem modelAtFour_g_zero : eval modelAtFour (g 4 ℚ) = 0 := by
  norm_num [g, Fin.sum_univ_succ, modelAtFour, complement]

theorem family_no_certificate_at_four (k : ℕ) (hk : 2 ≤ k)
    (A : ArithmeticIndex 4 k → R 4 ℚ) (U : Fin 5 → R 4 ℚ) (B : R 4 ℚ) :
    ¬ Certificate (arithmeticFamily 4 k) A U B := by
  intro cert
  exact certificate_excludes_common_zero (arithmeticFamily 4 k) A U B cert modelAtFour
    (modelAtFour_family k hk) modelAtFour_boolean modelAtFour_g_zero

end
end AlgebraicGoldbach.CoprimeKaryCountermodel
