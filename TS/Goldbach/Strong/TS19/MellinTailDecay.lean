import Mathlib.Data.Real.Basic

namespace TS19
namespace OTSA

/--
Mellin-tail decay control.

`Cm` is the tail-side majorization constant.
-/
structure MellinTailDecay where
  Cm : Real
  Cm_nonneg : 0 <= Cm

end OTSA
end TS19
