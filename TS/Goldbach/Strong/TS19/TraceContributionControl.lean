import Mathlib.Data.Real.Basic

namespace TS19
namespace OTSA

/--
Trace and pole contribution control.

`Ct` is the trace-side majorization constant.
-/
structure TraceContributionControl where
  Ct : Real
  Ct_nonneg : 0 <= Ct

end OTSA
end TS19
