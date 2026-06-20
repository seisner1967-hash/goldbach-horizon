import Mathlib.Tactic
import Mathlib.NumberTheory.VonMangoldt
import TS.Goldbach.Strong.TS183.TriangleSplineFiniteWeightedPrimeSumInterface

namespace TS184
namespace Goldbach

/-!
# TS184 - Triangle Spline Von Mangoldt API Probe

TS183 deliberately kept the arithmetic weight generic and introduced a local
`VonMangoldtWeightContract`.  This sprint probes Mathlib's von Mangoldt API and
binds the available real-valued arithmetic function to that TS183 contract.

Mathlib exposes `ArithmeticFunction.vonMangoldt : ArithmeticFunction Real` and
the nonnegativity theorem `ArithmeticFunction.vonMangoldt_nonneg`.  TS184 uses
exactly those objects to define the concrete smoothed von Mangoldt sum.

TS184 does not prove a prime-number estimate, does not prove the explicit
formula, does not construct zeta zeros, does not prove Plancherel, and does not
prove Goldbach.
-/

open Finset

/-- Mathlib's real-valued von Mangoldt function as a plain `Nat -> Real` weight. -/
noncomputable def mathlibVonMangoldtWeight
    (n : Nat) :
    Real :=
  ArithmeticFunction.vonMangoldt n

/-- Mathlib supplies the nonnegativity required by the TS183 local contract. -/
theorem mathlibVonMangoldtWeight_nonneg
    (n : Nat) :
    0 <= mathlibVonMangoldtWeight n := by
  unfold mathlibVonMangoldtWeight
  exact ArithmeticFunction.vonMangoldt_nonneg (n := n)

/-- The TS183 von Mangoldt weight contract instantiated by Mathlib's API. -/
noncomputable def mathlibVonMangoldtWeightContract :
    TS183.Goldbach.VonMangoldtWeightContract where
  weight := mathlibVonMangoldtWeight
  weight_nonneg := mathlibVonMangoldtWeight_nonneg
  mathlib_api_identification_required := True.intro

/-- The concrete triangle-spline smoothed von Mangoldt finite sum. -/
noncomputable def triangleSplineMathlibVonMangoldtWeightedSum
    (X : Nat) :
    Real :=
  TS183.Goldbach.triangleSplineVonMangoldtWeightedSum
    mathlibVonMangoldtWeightContract X

/-- The concrete sum is the TS183 generic weighted sum at Mathlib's weight. -/
theorem triangleSplineMathlibVonMangoldtWeightedSum_eq_generic
    (X : Nat) :
    triangleSplineMathlibVonMangoldtWeightedSum X =
      TS183.Goldbach.triangleSplineWeightedNatSum
        mathlibVonMangoldtWeight X :=
  rfl

/-- The smoothed Mathlib von Mangoldt sum is nonnegative. -/
theorem triangleSplineMathlibVonMangoldtWeightedSum_nonneg
    (X : Nat) :
    0 <= triangleSplineMathlibVonMangoldtWeightedSum X := by
  unfold triangleSplineMathlibVonMangoldtWeightedSum
  exact
    TS183.Goldbach.triangleSplineVonMangoldtWeightedSum_nonneg
      mathlibVonMangoldtWeightContract X

/-- Extending a finite range beyond `X` does not change the concrete sum. -/
theorem triangleSplineMathlibVonMangoldtWeightedSum_range_eq_of_le
    {X N : Nat}
    (hX : 0 < X)
    (hXN : X + 1 <= N) :
    Finset.sum (Finset.range N)
        (fun n =>
          mathlibVonMangoldtWeight n *
            TS182.Goldbach.triangleSplineDiscreteWeight X n) =
      triangleSplineMathlibVonMangoldtWeightedSum X := by
  unfold triangleSplineMathlibVonMangoldtWeightedSum
  exact
    TS183.Goldbach.triangleSplineWeightedNatSum_range_eq_of_le
      mathlibVonMangoldtWeight hX hXN

/-- On the TS182 support, the concrete sum has the affine smoothing formula. -/
theorem triangleSplineMathlibVonMangoldtWeightedSum_affine
    {X : Nat}
    (hX : 0 < X) :
    triangleSplineMathlibVonMangoldtWeightedSum X =
      Finset.sum (Finset.range (X + 1))
        (fun n =>
          mathlibVonMangoldtWeight n *
            (1 - (n : Real) / (X : Real))) := by
  unfold triangleSplineMathlibVonMangoldtWeightedSum
  exact
    TS183.Goldbach.triangleSplineVonMangoldtWeightedSum_affine
      mathlibVonMangoldtWeightContract hX

/-- Named outcomes of the TS184 Mathlib API probe. -/
inductive VonMangoldtAPIProbeOutcome where
  | arithmeticFunctionAvailable
  | realWeightExtracted
  | nonnegativityAvailable
  | ts183ContractInstantiated
  deriving DecidableEq, Repr

/-- The concrete Mathlib symbols stabilized by TS184. -/
def vonMangoldtAPIProbeSymbols :
    List String :=
  ["Mathlib.NumberTheory.VonMangoldt",
    "ArithmeticFunction.vonMangoldt",
    "ArithmeticFunction.vonMangoldt_nonneg"]

/-- Ledger recording the TS184 von Mangoldt API binding. -/
structure TriangleSplineVonMangoldtAPIProbeLedger where
  ts183_interface :
    TS183.Goldbach.TriangleSplineFiniteWeightedPrimeSumInterfaceLedger

  outcome :
    VonMangoldtAPIProbeOutcome

  outcome_eq :
    outcome =
      VonMangoldtAPIProbeOutcome.ts183ContractInstantiated

  probed_symbols :
    List String

  probed_symbols_eq :
    probed_symbols =
      vonMangoldtAPIProbeSymbols

  mathlib_weight :
    Nat -> Real

  mathlib_weight_eq :
    mathlib_weight =
      mathlibVonMangoldtWeight

  mathlib_weight_nonneg :
    forall n : Nat,
      0 <= mathlib_weight n

  ts183_von_mangoldt_contract :
    TS183.Goldbach.VonMangoldtWeightContract

  ts183_von_mangoldt_contract_eq :
    ts183_von_mangoldt_contract =
      mathlibVonMangoldtWeightContract

  smoothed_von_mangoldt_sum :
    Nat -> Real

  smoothed_von_mangoldt_sum_eq :
    smoothed_von_mangoldt_sum =
      triangleSplineMathlibVonMangoldtWeightedSum

  smoothed_von_mangoldt_sum_nonneg :
    forall X : Nat,
      0 <= smoothed_von_mangoldt_sum X

  smoothed_von_mangoldt_sum_range_extension :
    forall {X N : Nat},
        0 < X ->
      X + 1 <= N ->
        Finset.sum (Finset.range N)
          (fun n =>
            mathlib_weight n *
              TS182.Goldbach.triangleSplineDiscreteWeight X n) =
          smoothed_von_mangoldt_sum X

  smoothed_von_mangoldt_sum_affine :
    forall {X : Nat},
      0 < X ->
        smoothed_von_mangoldt_sum X =
          Finset.sum (Finset.range (X + 1))
            (fun n =>
              mathlib_weight n *
                (1 - (n : Real) / (X : Real)))

  prime_number_estimate_not_proved :
    True

  explicit_formula_not_proved :
    True

  zeta_zero_family_not_constructed :
    True

  plancherel_not_claimed :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS184 von Mangoldt API probe ledger. -/
noncomputable def triangleSplineVonMangoldtAPIProbeLedger :
    TriangleSplineVonMangoldtAPIProbeLedger where
  ts183_interface :=
    TS183.Goldbach.triangleSplineFiniteWeightedPrimeSumInterfaceLedger
  outcome := VonMangoldtAPIProbeOutcome.ts183ContractInstantiated
  outcome_eq := rfl
  probed_symbols := vonMangoldtAPIProbeSymbols
  probed_symbols_eq := rfl
  mathlib_weight := mathlibVonMangoldtWeight
  mathlib_weight_eq := rfl
  mathlib_weight_nonneg := mathlibVonMangoldtWeight_nonneg
  ts183_von_mangoldt_contract := mathlibVonMangoldtWeightContract
  ts183_von_mangoldt_contract_eq := rfl
  smoothed_von_mangoldt_sum :=
    triangleSplineMathlibVonMangoldtWeightedSum
  smoothed_von_mangoldt_sum_eq := rfl
  smoothed_von_mangoldt_sum_nonneg := by
    intro X
    exact triangleSplineMathlibVonMangoldtWeightedSum_nonneg X
  smoothed_von_mangoldt_sum_range_extension := by
    intro X N hX hXN
    exact
      triangleSplineMathlibVonMangoldtWeightedSum_range_eq_of_le
        hX hXN
  smoothed_von_mangoldt_sum_affine := by
    intro X hX
    exact triangleSplineMathlibVonMangoldtWeightedSum_affine hX
  prime_number_estimate_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  zeta_zero_family_not_constructed := True.intro
  plancherel_not_claimed := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS184. -/
def TriangleSplineVonMangoldtAPIProbeTarget : Prop :=
  Nonempty TriangleSplineVonMangoldtAPIProbeLedger

/-- The TS184 von Mangoldt API probe target is populated. -/
theorem triangleSplineVonMangoldtAPIProbeTarget :
    TriangleSplineVonMangoldtAPIProbeTarget :=
  Nonempty.intro triangleSplineVonMangoldtAPIProbeLedger

end Goldbach
end TS184
