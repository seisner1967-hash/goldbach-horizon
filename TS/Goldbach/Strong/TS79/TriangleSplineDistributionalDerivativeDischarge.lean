import Mathlib.Tactic
import TS.Goldbach.Strong.TS61.TriangleSplineDistributionalDerivativeLedger
import TS.Goldbach.Strong.TS63.TriangleSplineConcreteDistributionalContract
import TS.Goldbach.Strong.TS78.TriangleSplineConcreteDistributionalDischarge

namespace TS79
namespace MellinJackson

/-!
# TS79 - Triangle Spline Distributional Derivative Discharge

This sprint lifts the concrete TS63 weak-derivative identity discharged in TS78
to the abstract TS61 distributional derivative target.

It is a purely mechanical wrapper: TS78 supplies the concrete contract, and
TS63 supplies the bridge from the concrete TS62 test-function API to the
abstract TS61 test-function API.
-/

/-- TS78 lifted through TS63 gives the abstract TS61 distributional contract. -/
noncomputable def triangleSplineDistributionalDerivativeContract :
    TS61.MellinJackson.TriangleSplineDistributionalDerivativeContract :=
  TS63.MellinJackson.distributionalContract_of_concrete
    TS78.MellinJackson.triangleSplineConcreteDistributionalContract

/-- TS79 discharges the abstract TS61 distributional target. -/
theorem triangleSplineDistributionalDerivativeTarget :
    TS61.MellinJackson.TriangleSplineDistributionalDerivativeTarget :=
  Nonempty.intro triangleSplineDistributionalDerivativeContract

/-- Local target for the TS79 abstract distributional discharge. -/
def TriangleSplineDistributionalDerivativeDischargeTarget : Prop :=
  TS61.MellinJackson.TriangleSplineDistributionalDerivativeTarget

/-- TS79 local target is discharged. -/
theorem triangleSplineDistributionalDerivativeDischargeTarget :
    TriangleSplineDistributionalDerivativeDischargeTarget :=
  triangleSplineDistributionalDerivativeTarget

end MellinJackson
end TS79
