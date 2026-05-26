import Mathlib.Data.Real.Basic

namespace TS19
namespace OTSA

/--
Spectral-kernel control.

`Ck` is the kernel-side majorization constant.
-/
structure KernelSpectralControl where
  Ck : Real
  Ck_nonneg : 0 <= Ck

end OTSA
end TS19
