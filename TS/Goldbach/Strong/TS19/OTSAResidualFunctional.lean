import Mathlib.Data.Real.Basic

namespace TS19
namespace OTSA

/--
Functional envelope for the OTSA residual.

`residual x B` is the absolute error term, and `scale x B` is the normalizing
scale for the targeted residual estimate.
-/
structure OTSAResidualFunctional where
  residual : Nat -> Nat -> Real
  scale : Nat -> Nat -> Real
  scale_nonneg : forall x B : Nat, 0 <= scale x B

/-- The TS19 residual target with threshold constant 26. -/
def OTSAResidualBound (R : OTSAResidualFunctional) : Prop :=
  forall x B : Nat, R.residual x B <= 26 * R.scale x B

end OTSA
end TS19
