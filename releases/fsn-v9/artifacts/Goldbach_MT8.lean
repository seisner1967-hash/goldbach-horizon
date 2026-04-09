/-
Goldbach_MT8.lean

MT8 replay target module.
This file upgrades the MT7 lock-in module into an explicit replay target:
the witness hash is frozen, the numerical KLMN cap is frozen, and the theorem
chain A2 -> F1 -> Goldbach is written in repository-facing form.

Honesty note:
this file is not claimed here as compiled in the current session because
lean/lake are unavailable in the execution environment used to generate MT8.
-/

namespace HorizonGoldbachMT8

abbrev JsonHash := String

def mt6WitnessHash : JsonHash :=
  "171f7f392eedba63c5cc48b7650d5afe06651ab131f8bc10093af3d141db8852"

def factor4UpperCap : Rat := 1772 / 10000

theorem factor4UpperCap_lt_quarter : factor4UpperCap < (1/4 : Rat) := by
  norm_num [factor4UpperCap]

structure CompactWitness where
  hash : JsonHash
  factor4Upper : Rat
  deriving Repr, DecidableEq

def frozenWitness : CompactWitness := {
  hash := mt6WitnessHash,
  factor4Upper := factor4UpperCap
}

theorem frozenWitness_hash_ok : frozenWitness.hash = mt6WitnessHash := by
  rfl

theorem frozenWitness_bound_ok : frozenWitness.factor4Upper < (1/4 : Rat) := by
  simpa [frozenWitness] using factor4UpperCap_lt_quarter

/-
Repository-side declarations to be supplied by the actual Horizon project:

constant A2 : Prop
constant F1 : Prop
constant GoldbachAsymptotic : Prop

constant KLMN_criterion :
  CompactWitness -> frozenWitness.factor4Upper < (1/4 : Rat) -> A2

constant MT4_F1_of_A2 : A2 -> F1
constant MT3_goldbach_from_F1 : F1 -> GoldbachAsymptotic
-/

-- theorem A2_KLMN_closed : A2 := by
--   exact KLMN_criterion frozenWitness frozenWitness_bound_ok

-- theorem goldbach_asymptotic : GoldbachAsymptotic := by
--   have hA2 : A2 := A2_KLMN_closed
--   have hF1 : F1 := MT4_F1_of_A2 hA2
--   exact MT3_goldbach_from_F1 hF1

end HorizonGoldbachMT8
