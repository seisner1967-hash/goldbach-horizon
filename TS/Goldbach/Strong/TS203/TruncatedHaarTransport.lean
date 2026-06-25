import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import TS.Goldbach.Strong.TS202.Wall0MeasureTransportBridge

namespace TS203
namespace Goldbach

open MeasureTheory

/-!
# TS203 - Truncated Haar Transport

TS202 defined the fail-closed Wall 0 Haar transport contract.  TS203 supplies
the first concrete analytic ingredient for that contract: the compact,
finite-endpoint transport identity on a positive real interval.

For a continuous test function `F` on `[epsilon, X]`, the logarithmic
substitution `x = exp u` gives

`integral_{log epsilon}^{log X} F(exp u) du
  = integral_epsilon^X F(x) / x dx`.

This is the truncated form of the Haar identity `dx / x = du`.  It is proved
with Mathlib's interval-integral change-of-variables theorem and does not
claim any improper limit, global transport on `(0, infinity)`, Mellin/Fourier
kernel compatibility, Plancherel, explicit formula, zeta-zero summability,
circle-method correlation, or Goldbach theorem.
-/

/-- The exponential image of the logarithmic compact interval is contained in the x-interval. -/
theorem exp_image_uIcc_log_subset_Icc
    {epsilon X : Real}
    (hepsilon : 0 < epsilon)
    (hepsilonX : epsilon <= X) :
    Real.exp '' Set.uIcc (Real.log epsilon) (Real.log X) <=
      Set.Icc epsilon X := by
  intro y hy
  let u : Real := Classical.choose hy
  have hu_and := Classical.choose_spec hy
  have hu : (Set.uIcc (Real.log epsilon) (Real.log X)) u :=
    hu_and.1
  have hy_eq : Real.exp u = y :=
    hu_and.2
  have hX : 0 < X := lt_of_lt_of_le hepsilon hepsilonX
  have hlog : Real.log epsilon <= Real.log X :=
    Real.log_le_log hepsilon hepsilonX
  have huIcc : (Set.Icc (Real.log epsilon) (Real.log X)) u := by
    simpa [Set.uIcc_of_le hlog] using hu
  rw [<- hy_eq]
  constructor
  next =>
    have h_exp :
        Real.exp (Real.log epsilon) <= Real.exp u :=
      Real.exp_le_exp.mpr huIcc.1
    simpa [Real.exp_log hepsilon] using h_exp
  next =>
    have h_exp :
        Real.exp u <= Real.exp (Real.log X) :=
      Real.exp_le_exp.mpr huIcc.2
    simpa [Real.exp_log hX] using h_exp

/-- The Haar-weighted integrand is continuous on the logarithmic image. -/
theorem continuousOn_div_id_on_exp_image_uIcc_log
    {F : Real -> Real}
    {epsilon X : Real}
    (hepsilon : 0 < epsilon)
    (hepsilonX : epsilon <= X)
    (hF : ContinuousOn F (Set.Icc epsilon X)) :
    ContinuousOn
      (fun x : Real => F x / x)
      (Real.exp '' Set.uIcc (Real.log epsilon) (Real.log X)) := by
  have hsubset :
      Real.exp '' Set.uIcc (Real.log epsilon) (Real.log X) <=
        Set.Icc epsilon X :=
    exp_image_uIcc_log_subset_Icc hepsilon hepsilonX
  have hF_on_image :
      ContinuousOn F (Real.exp '' Set.uIcc (Real.log epsilon) (Real.log X)) :=
    hF.mono hsubset
  have hid :
      ContinuousOn
        (fun x : Real => x)
        (Real.exp '' Set.uIcc (Real.log epsilon) (Real.log X)) :=
    continuous_id.continuousOn
  exact
    hF_on_image.div
      hid
      (by
        intro x hx
        exact
          ne_of_gt
            (lt_of_lt_of_le hepsilon (hsubset hx).1))

/--
Truncated Haar transport on a positive finite interval.

This is the compact `dx / x = du` identity.  The direction starts on the
logarithmic side because it is exactly the output of substituting `x = exp u`.
-/
theorem truncatedHaarTransport_interval
    (F : Real -> Real)
    (epsilon X : Real)
    (hepsilon : 0 < epsilon)
    (hepsilonX : epsilon <= X)
    (hF : ContinuousOn F (Set.Icc epsilon X)) :
    intervalIntegral
      (fun u : Real => F (Real.exp u))
      (Real.log epsilon)
      (Real.log X)
      volume =
      intervalIntegral
        (fun x : Real => F x / x)
        epsilon
        X
        volume := by
  have hX : 0 < X := lt_of_lt_of_le hepsilon hepsilonX
  have hderiv :
      forall u,
        (Set.uIcc (Real.log epsilon) (Real.log X)) u ->
        HasDerivAt Real.exp (Real.exp u) u := by
    intro u _hu
    exact Real.hasDerivAt_exp u
  have hderiv_cont :
      ContinuousOn Real.exp (Set.uIcc (Real.log epsilon) (Real.log X)) :=
    Real.continuous_exp.continuousOn
  have hg :
      ContinuousOn
        (fun x : Real => F x / x)
        (Real.exp '' Set.uIcc (Real.log epsilon) (Real.log X)) :=
    continuousOn_div_id_on_exp_image_uIcc_log
      hepsilon
      hepsilonX
      hF
  have hcov :
      intervalIntegral
        (fun u : Real =>
          (F (Real.exp u) / Real.exp u) * Real.exp u)
        (Real.log epsilon)
        (Real.log X)
        volume =
        intervalIntegral
          (fun x : Real => F x / x)
          (Real.exp (Real.log epsilon))
          (Real.exp (Real.log X))
          volume :=
    intervalIntegral.integral_comp_mul_deriv'
      (a := Real.log epsilon)
      (b := Real.log X)
      (f := Real.exp)
      (f' := Real.exp)
      (g := fun x : Real => F x / x)
      hderiv
      hderiv_cont
      hg
  simpa [Function.comp_def, Real.exp_log hepsilon, Real.exp_log hX] using hcov

/-- Reversed orientation of the same truncated Haar transport identity. -/
theorem truncatedHaarTransport_interval_symm
    (F : Real -> Real)
    (epsilon X : Real)
    (hepsilon : 0 < epsilon)
    (hepsilonX : epsilon <= X)
    (hF : ContinuousOn F (Set.Icc epsilon X)) :
    intervalIntegral
      (fun x : Real => F x / x)
      epsilon
      X
      volume =
      intervalIntegral
        (fun u : Real => F (Real.exp u))
        (Real.log epsilon)
        (Real.log X)
        volume :=
  (truncatedHaarTransport_interval F epsilon X hepsilon hepsilonX hF).symm

/-- The concrete first-slot proposition supplied by TS203. -/
def TruncatedHaarTransportStatement : Prop :=
  forall (F : Real -> Real) (epsilon X : Real),
    0 < epsilon ->
      epsilon <= X ->
        ContinuousOn F (Set.Icc epsilon X) ->
          intervalIntegral
              (fun u : Real => F (Real.exp u))
              (Real.log epsilon)
              (Real.log X)
              volume =
            intervalIntegral
                (fun x : Real => F x / x)
                epsilon
                X
                volume

/-- TS203 proves the compact/truncated Haar transport statement. -/
theorem truncatedHaarTransportStatement :
    TruncatedHaarTransportStatement := by
  intro F epsilon X hepsilon hepsilonX hF
  exact truncatedHaarTransport_interval F epsilon X hepsilon hepsilonX hF

/--
Partial Wall 0 evidence: TS203 populates only the truncated Haar transport
slot.  It deliberately does not fabricate full TS202 evidence for the
improper, Mellin/Fourier, or integrability slots.
-/
structure TruncatedHaarTransportEvidenceLedger where
  ts202_bridge :
    TS202.Goldbach.Wall0MeasureTransportBridgeLedger

  truncated_haar_transport_statement :
    Prop

  truncated_haar_transport_proved :
    truncated_haar_transport_statement

  does_not_populate_full_wall0_evidence :
    True

  improper_haar_transport_not_proved :
    True

  global_haar_transport_not_proved :
    True

  mellin_fourier_kernel_not_proved :
    True

  effective_integrability_not_proved :
    True

  plancherel_not_proved :
    True

  explicit_formula_not_proved :
    True

  zeta_zero_summability_not_proved :
    True

  circle_gallagher_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS203 truncated Haar transport evidence ledger. -/
noncomputable def truncatedHaarTransportEvidenceLedger :
    TruncatedHaarTransportEvidenceLedger where
  ts202_bridge :=
    TS202.Goldbach.wall0MeasureTransportBridgeLedger
  truncated_haar_transport_statement :=
    TruncatedHaarTransportStatement
  truncated_haar_transport_proved :=
    truncatedHaarTransportStatement
  does_not_populate_full_wall0_evidence := True.intro
  improper_haar_transport_not_proved := True.intro
  global_haar_transport_not_proved := True.intro
  mellin_fourier_kernel_not_proved := True.intro
  effective_integrability_not_proved := True.intro
  plancherel_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  zeta_zero_summability_not_proved := True.intro
  circle_gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS203. -/
def TruncatedHaarTransportTarget : Prop :=
  Nonempty TruncatedHaarTransportEvidenceLedger

/-- The TS203 truncated Haar transport target is populated. -/
theorem truncatedHaarTransportTarget :
    TruncatedHaarTransportTarget :=
  Nonempty.intro truncatedHaarTransportEvidenceLedger

end Goldbach
end TS203
