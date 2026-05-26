import Mathlib.Data.Real.Basic
import TS.Goldbach.Strong.TS19.OTSAResidualFunctional
import TS.Goldbach.Strong.TS19.KernelSpectralControl
import TS.Goldbach.Strong.TS19.TraceContributionControl
import TS.Goldbach.Strong.TS19.MellinTailDecay

namespace TS19
namespace OTSA

/-- Coupled OTSA constant: kernel times trace, plus Mellin tail. -/
noncomputable def coupledConstant
    (K : KernelSpectralControl)
    (T : TraceContributionControl)
    (M : MellinTailDecay) : Real :=
  K.Ck * T.Ct + M.Cm

/-- The coupled OTSA constant is nonnegative under the three local controls. -/
theorem coupledConstant_nonneg
    (K : KernelSpectralControl)
    (T : TraceContributionControl)
    (M : MellinTailDecay) :
    0 <= coupledConstant K T M := by
  unfold coupledConstant
  exact add_nonneg (mul_nonneg K.Ck_nonneg T.Ct_nonneg) M.Cm_nonneg

/--
Local coupling hypothesis: the OTSA residual is bounded by the coupled constant
times the normalizing scale.
-/
structure OTSACouplingHypothesis
    (R : OTSAResidualFunctional)
    (K : KernelSpectralControl)
    (T : TraceContributionControl)
    (M : MellinTailDecay) where
  coupling_bound :
    forall x B : Nat,
      R.residual x B <= coupledConstant K T M * R.scale x B

/-- Threshold condition for the coupled OTSA constant. -/
def couplingConstantLe26
    (K : KernelSpectralControl)
    (T : TraceContributionControl)
    (M : MellinTailDecay) : Prop :=
  coupledConstant K T M <= 26

/--
TS19 relative residual discharge.

If the local coupling estimate holds and the coupled constant is at most 26,
then the OTSA residual satisfies the threshold-26 residual bound.
-/
theorem otsa_residual_bound_26
    (R : OTSAResidualFunctional)
    (K : KernelSpectralControl)
    (T : TraceContributionControl)
    (M : MellinTailDecay)
    (Hcoup : OTSACouplingHypothesis R K T M)
    (Hle : couplingConstantLe26 K T M) :
    OTSAResidualBound R := by
  intro x B
  have h1 :
      R.residual x B <= coupledConstant K T M * R.scale x B :=
    Hcoup.coupling_bound x B
  have h2 :
      coupledConstant K T M * R.scale x B <= 26 * R.scale x B := by
    exact mul_le_mul_of_nonneg_right Hle (R.scale_nonneg x B)
  exact le_trans h1 h2

end OTSA
end TS19
