import Mathlib.Tactic
import TS.Goldbach.Strong.TS182.TriangleSplineDiscreteSieveTraceBridge

namespace TS183
namespace Goldbach

/-!
# TS183 - Triangle Spline Finite Weighted Prime Sum Interface

TS182 defines the discrete triangle-spline smoothing weight
`triangleSplineDiscreteWeight X n`.  This sprint turns that pointwise weight
into the finite arithmetic sum shape needed by later explicit-formula and
sieve-trace ledgers.

To avoid depending too early on the exact Mathlib name for the von Mangoldt
function, TS183 first defines a generic weighted natural sum for any arithmetic
weight `A : Nat -> Real`.  A local `VonMangoldtWeightContract` then records the
future specialization point.

TS183 does not prove a von Mangoldt API identification, does not prove the
explicit formula, does not construct zeta zeros, does not prove Plancherel, and
does not prove Goldbach.
-/

open Finset

/-- Generic finite arithmetic sum weighted by the TS182 discrete spline. -/
noncomputable def triangleSplineWeightedNatSum
    (A : Nat -> Real)
  (X : Nat) :
    Real :=
  Finset.sum (Finset.range (X + 1))
    (fun n => A n * TS182.Goldbach.triangleSplineDiscreteWeight X n)

/-- The definition unfolds to the explicit finite range sum. -/
theorem triangleSplineWeightedNatSum_eq_range_succ
    (A : Nat -> Real)
    (X : Nat) :
    triangleSplineWeightedNatSum A X =
      Finset.sum (Finset.range (X + 1))
        (fun n => A n *
          TS182.Goldbach.triangleSplineDiscreteWeight X n) :=
  rfl

/--
Extending the finite range beyond `X` does not change the weighted sum, because
TS182 proves the discrete spline vanishes for every `n` with `X <= n`.
-/
theorem triangleSplineWeightedNatSum_range_eq_of_le
    (A : Nat -> Real)
    {X N : Nat}
    (hX : 0 < X)
    (hXN : X + 1 <= N) :
    Finset.sum (Finset.range N)
        (fun n => A n * TS182.Goldbach.triangleSplineDiscreteWeight X n) =
      triangleSplineWeightedNatSum A X := by
  unfold triangleSplineWeightedNatSum
  have hsubset :
      Finset.range (X + 1) <= Finset.range N := by
    intro n hn
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hn).trans_le hXN)
  exact
    (Finset.sum_subset hsubset (by
      intro n _hnN hnNot
      have hn_not_lt : Not (n < X + 1) := by
        intro hnlt
        exact hnNot (Finset.mem_range.mpr hnlt)
      have hsucc_le : X + 1 <= n :=
        Nat.le_of_not_lt hn_not_lt
      have hXle : X <= n :=
        le_trans (Nat.le_succ X) hsucc_le
      rw [TS182.Goldbach.triangleSplineDiscreteWeight_eq_zero_of_X_le_n
        hX hXle, mul_zero])).symm

/-- On the support range, the weighted sum has the affine spline formula. -/
theorem triangleSplineWeightedNatSum_affine
    (A : Nat -> Real)
    {X : Nat}
    (hX : 0 < X) :
    triangleSplineWeightedNatSum A X =
      Finset.sum (Finset.range (X + 1))
        (fun n => A n * (1 - (n : Real) / (X : Real))) := by
  unfold triangleSplineWeightedNatSum
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n <= X :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  rw [TS182.Goldbach.triangleSplineDiscreteWeight_eq_one_sub hX hnle]

/-- Nonnegative arithmetic weights give a nonnegative spline-weighted sum. -/
theorem triangleSplineWeightedNatSum_nonneg
    (A : Nat -> Real)
    (X : Nat)
    (hA : forall n : Nat, 0 <= A n) :
    0 <= triangleSplineWeightedNatSum A X := by
  unfold triangleSplineWeightedNatSum
  exact Finset.sum_nonneg (by
    intro n _hn
    exact mul_nonneg (hA n)
      (TS182.Goldbach.triangleSplineDiscreteWeight_nonneg X n))

/--
Local contract for the future von Mangoldt specialization.

The exact Mathlib API name is intentionally not selected in TS183.  A later
sprint can instantiate this contract once the desired arithmetic-function
interface is chosen.
-/
structure VonMangoldtWeightContract where
  weight :
    Nat -> Real

  weight_nonneg :
    forall n : Nat,
      0 <= weight n

  mathlib_api_identification_required :
    True

/-- The future von Mangoldt-smoothed sum, relative to a local weight contract. -/
noncomputable def triangleSplineVonMangoldtWeightedSum
    (V : VonMangoldtWeightContract)
    (X : Nat) :
    Real :=
  triangleSplineWeightedNatSum V.weight X

/-- The contracted von Mangoldt-smoothed sum is nonnegative. -/
theorem triangleSplineVonMangoldtWeightedSum_nonneg
    (V : VonMangoldtWeightContract)
    (X : Nat) :
    0 <= triangleSplineVonMangoldtWeightedSum V X := by
  unfold triangleSplineVonMangoldtWeightedSum
  exact triangleSplineWeightedNatSum_nonneg V.weight X V.weight_nonneg

/-- The contracted von Mangoldt-smoothed sum has the affine form on its support. -/
theorem triangleSplineVonMangoldtWeightedSum_affine
    (V : VonMangoldtWeightContract)
    {X : Nat}
    (hX : 0 < X) :
    triangleSplineVonMangoldtWeightedSum V X =
      Finset.sum (Finset.range (X + 1))
        (fun n => V.weight n * (1 - (n : Real) / (X : Real))) := by
  unfold triangleSplineVonMangoldtWeightedSum
  exact triangleSplineWeightedNatSum_affine V.weight hX

/-- Named status markers for the finite weighted-sum interface. -/
inductive TriangleSplineFiniteWeightedSumStatus where
  | genericWeightedSumDefined
  | rangeExtensionProved
  | vonMangoldtContractNamed
  deriving DecidableEq, Repr

/-- Ledger recording the TS183 finite weighted-sum interface. -/
structure TriangleSplineFiniteWeightedPrimeSumInterfaceLedger where
  ts182_discrete_bridge :
    TS182.Goldbach.TriangleSplineDiscreteSieveTraceBridgeLedger

  status :
    TriangleSplineFiniteWeightedSumStatus

  status_eq :
    status =
      TriangleSplineFiniteWeightedSumStatus.vonMangoldtContractNamed

  weighted_sum :
    (Nat -> Real) -> Nat -> Real

  weighted_sum_eq :
    weighted_sum = triangleSplineWeightedNatSum

  range_extension :
    forall (A : Nat -> Real) {X N : Nat},
          0 < X ->
        X + 1 <= N ->
          Finset.sum (Finset.range N)
              (fun n =>
                A n * TS182.Goldbach.triangleSplineDiscreteWeight X n) =
            weighted_sum A X

  affine_formula :
    forall (A : Nat -> Real) {X : Nat},
      0 < X ->
        weighted_sum A X =
          Finset.sum (Finset.range (X + 1))
            (fun n => A n * (1 - (n : Real) / (X : Real)))

  nonnegative_for_nonnegative_weight :
    forall (A : Nat -> Real) (X : Nat),
      (forall n : Nat, 0 <= A n) ->
        0 <= weighted_sum A X

  von_mangoldt_contract_type :
    Type

  von_mangoldt_contract_type_eq :
    von_mangoldt_contract_type =
      VonMangoldtWeightContract

  von_mangoldt_weighted_sum :
    VonMangoldtWeightContract -> Nat -> Real

  von_mangoldt_weighted_sum_eq :
    von_mangoldt_weighted_sum =
      triangleSplineVonMangoldtWeightedSum

  mathlib_von_mangoldt_api_not_selected :
    True

  explicit_formula_not_proved :
    True

  zeta_zero_family_not_constructed :
    True

  plancherel_not_claimed :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS183 finite weighted prime-sum interface ledger. -/
noncomputable def triangleSplineFiniteWeightedPrimeSumInterfaceLedger :
    TriangleSplineFiniteWeightedPrimeSumInterfaceLedger where
  ts182_discrete_bridge :=
    TS182.Goldbach.triangleSplineDiscreteSieveTraceBridgeLedger
  status := TriangleSplineFiniteWeightedSumStatus.vonMangoldtContractNamed
  status_eq := rfl
  weighted_sum := triangleSplineWeightedNatSum
  weighted_sum_eq := rfl
  range_extension := by
    intro A X N hX hXN
    exact triangleSplineWeightedNatSum_range_eq_of_le A hX hXN
  affine_formula := by
    intro A X hX
    exact triangleSplineWeightedNatSum_affine A hX
  nonnegative_for_nonnegative_weight := by
    intro A X hA
    exact triangleSplineWeightedNatSum_nonneg A X hA
  von_mangoldt_contract_type := VonMangoldtWeightContract
  von_mangoldt_contract_type_eq := rfl
  von_mangoldt_weighted_sum := triangleSplineVonMangoldtWeightedSum
  von_mangoldt_weighted_sum_eq := rfl
  mathlib_von_mangoldt_api_not_selected := True.intro
  explicit_formula_not_proved := True.intro
  zeta_zero_family_not_constructed := True.intro
  plancherel_not_claimed := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS183. -/
def TriangleSplineFiniteWeightedPrimeSumInterfaceTarget : Prop :=
  Nonempty TriangleSplineFiniteWeightedPrimeSumInterfaceLedger

/-- The TS183 finite weighted prime-sum interface target is populated. -/
theorem triangleSplineFiniteWeightedPrimeSumInterfaceTarget :
    TriangleSplineFiniteWeightedPrimeSumInterfaceTarget :=
  Nonempty.intro triangleSplineFiniteWeightedPrimeSumInterfaceLedger

end Goldbach
end TS183
