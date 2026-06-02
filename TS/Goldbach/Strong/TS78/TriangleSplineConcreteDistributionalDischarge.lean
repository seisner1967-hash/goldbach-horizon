import Mathlib.Tactic
import TS.Goldbach.Strong.TS63.TriangleSplineConcreteDistributionalContract
import TS.Goldbach.Strong.TS74.TriangleSplineIPPRecombinationFromAffine
import TS.Goldbach.Strong.TS77.TriangleSplineIPPAffineBranchProof

namespace TS78
namespace MellinJackson

/-!
# TS78 - Triangle Spline Concrete Distributional Discharge

This sprint mechanically combines:

- TS77, which proves the two affine branch integration-by-parts identities;
- TS74, which recombines those branch identities into the concrete TS63
  distributional derivative contract.

It discharges the concrete weak-derivative identity for the triangle spline
against the TS62 concrete test-function API. It does not yet lift the result
to the abstract TS61 distributional contract or the TS49 Sobolev slot.
-/

/-- TS77 and TS74 give the concrete TS63 distributional contract. -/
noncomputable def triangleSplineConcreteDistributionalContract :
    TS63.MellinJackson.TriangleSplineConcreteDistributionalContract :=
  TS74.MellinJackson.concreteDistributionalContract_of_affineBranchContract
    TS77.MellinJackson.triangleSplineIPPAffineBranchContract

/-- TS78 discharges the concrete TS63 distributional target. -/
theorem triangleSplineConcreteDistributionalContractTarget :
    TS63.MellinJackson.TriangleSplineConcreteDistributionalContractTarget :=
  Nonempty.intro triangleSplineConcreteDistributionalContract

/-- Local target for the TS78 concrete distributional discharge. -/
def TriangleSplineConcreteDistributionalDischargeTarget : Prop :=
  TS63.MellinJackson.TriangleSplineConcreteDistributionalContractTarget

/-- TS78 local target is discharged. -/
theorem triangleSplineConcreteDistributionalDischargeTarget :
    TriangleSplineConcreteDistributionalDischargeTarget :=
  triangleSplineConcreteDistributionalContractTarget

end MellinJackson
end TS78
