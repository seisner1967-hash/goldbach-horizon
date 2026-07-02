import Mathlib.Tactic
import TS.Goldbach.Strong.TS209.TriangleSplineSincFourthScaleReduction
import TS.Goldbach.Strong.TS212.BoxFourierConvolutionExchange

namespace TS213
namespace Goldbach

open MeasureTheory

/-!
# TS213 - Canonical Sinc-Fourth Direct Dirichlet Route

TS209 reduced the triangle-spline Wall 1 scalar calculation to the canonical
unscaled identity

`integral t, canonicalSincSq t ^ 2 = 2 * Real.pi / 3`.

TS213 records the non-Plancherel route to that identity.  The intended scalar
proof is the classical one: set `f(x) = (1 - cos x)^2`, use three integrations
by parts on `(0, infinity)`, reduce to the Dirichlet sine integral, scale from
`x = 2 * u`, and use evenness.

This sprint does not prove the Dirichlet integral, the improper integration by
parts, the scaling identity, or the evenness identity.  It proves that these
concrete scalar obligations imply the TS209 canonical `sinc^4` statement and
therefore the TS204 triangle-spline Plancherel evidence.  No Plancherel or
Parseval theorem is used.
-/

/-- The numerator used by the direct Dirichlet route. -/
noncomputable def cosSquareRemainder
    (x : Real) :
    Real :=
  (1 - Real.cos x) ^ 2

/-- The improper kernel `(1 - cos x)^2 / x^4` on the positive half-line. -/
noncomputable def cosSquareHaarKernel
    (x : Real) :
    Real :=
  cosSquareRemainder x / x ^ 4

/-- The Dirichlet sine kernel `sin (a*x) / x`. -/
noncomputable def sineDirichletKernel
    (a x : Real) :
    Real :=
  Real.sin (a * x) / x

/-- The third-derivative expression expected after three integrations by parts. -/
noncomputable def cosSquareThirdDerivativeKernel
    (x : Real) :
    Real :=
  (-2 * Real.sin x + 4 * Real.sin (2 * x)) / x

/-- The canonical `sinc^4` integrand from TS209. -/
noncomputable def canonicalSincFourthKernel
    (x : Real) :
    Real :=
  TS209.Goldbach.canonicalSincSq x ^ 2

/-- The positive-half-line integral of `(1 - cos x)^2 / x^4`. -/
noncomputable def cosSquareImproperIntegral :
    Real :=
  integral
    (volume.restrict (Set.Ioi (0 : Real)))
    cosSquareHaarKernel

/-- The positive-half-line canonical `sinc^4` integral. -/
noncomputable def halfLineCanonicalSincFourthIntegral :
    Real :=
  integral
    (volume.restrict (Set.Ioi (0 : Real)))
    canonicalSincFourthKernel

/-- The full-line canonical `sinc^4` integral. -/
noncomputable def fullLineCanonicalSincFourthIntegral :
    Real :=
  integral
    (volume : Measure Real)
    canonicalSincFourthKernel

/--
The pointwise third-derivative formula for `f(x) = (1 - cos x)^2`.

This is kept as a real scalar obligation for a future TS214 finite-interval IPP
discharge.
-/
def CosSquareThirdDerivativeFormulaStatement :
    Prop :=
  forall x : Real,
    deriv
      (fun z : Real =>
        deriv
          (fun y : Real =>
            deriv cosSquareRemainder y) z) x =
      -2 * Real.sin x + 4 * Real.sin (2 * x)

/--
The Dirichlet sine-integral input needed by the direct route.

This statement intentionally carries the positive-frequency parameter `a`.
-/
def DirichletSineIntegralStatement :
    Prop :=
  forall a : Real,
    0 < a ->
      integral
        (volume.restrict (Set.Ioi (0 : Real)))
        (sineDirichletKernel a) =
        Real.pi / 2

/--
The improper triple-integration-by-parts statement for
`(1 - cos x)^2 / x^4`.
-/
def CosSquareTripleIPPStatement :
    Prop :=
  cosSquareImproperIntegral =
    (1 / 6 : Real) *
      integral
        (volume.restrict (Set.Ioi (0 : Real)))
        cosSquareThirdDerivativeKernel

/-- The value of the cosine-square improper integral after IPP and Dirichlet. -/
def CosSquareIntegralValueStatement :
    Prop :=
  cosSquareImproperIntegral = Real.pi / 6

/--
The future scalar reduction from the derivative formula, Dirichlet, and triple
IPP to the value `pi / 6`.
-/
def CosSquareDirichletIPPReductionStatement :
    Prop :=
  CosSquareThirdDerivativeFormulaStatement ->
    DirichletSineIntegralStatement ->
      CosSquareTripleIPPStatement ->
        CosSquareIntegralValueStatement

/--
The scaling identity obtained from `x = 2*u`:
`int_0^infty sinc(u)^4 du = 2 * int_0^infty (1 - cos x)^2 / x^4 dx`.
-/
def HalfLineSincFourthScalingStatement :
    Prop :=
  halfLineCanonicalSincFourthIntegral =
    2 * cosSquareImproperIntegral

/-- The evenness identity reducing the full-line integral to the half-line. -/
def FullLineSincFourthEvennessStatement :
    Prop :=
  fullLineCanonicalSincFourthIntegral =
    2 * halfLineCanonicalSincFourthIntegral

/-- Evidence package for the direct non-Plancherel Dirichlet route. -/
structure CanonicalSincFourthDirectDirichletRouteEvidence where
  third_derivative_formula :
    CosSquareThirdDerivativeFormulaStatement

  dirichlet_sine_integral :
    DirichletSineIntegralStatement

  triple_ipp :
    CosSquareTripleIPPStatement

  dirichlet_ipp_reduction :
    CosSquareDirichletIPPReductionStatement

  sinc_fourth_scaling :
    HalfLineSincFourthScalingStatement

  sinc_fourth_evenness :
    FullLineSincFourthEvennessStatement

/--
The final algebraic assembly: `pi / 6`, the scaling identity, and evenness imply
the canonical TS209 value `2*pi/3`.
-/
theorem canonicalSincFourthIntegral_of_cosSquareValue_scaling_evenness
    (h_cos :
      CosSquareIntegralValueStatement)
    (h_scaling :
      HalfLineSincFourthScalingStatement)
    (h_even :
      FullLineSincFourthEvennessStatement) :
    TS209.Goldbach.CanonicalSincFourthIntegralValueStatement := by
  unfold TS209.Goldbach.CanonicalSincFourthIntegralValueStatement
  change fullLineCanonicalSincFourthIntegral = (2 * Real.pi) / 3
  calc
    fullLineCanonicalSincFourthIntegral =
        2 * halfLineCanonicalSincFourthIntegral := h_even
    _ =
        2 * (2 * cosSquareImproperIntegral) := by
          rw [h_scaling]
    _ =
        2 * (2 * (Real.pi / 6)) := by
          rw [h_cos]
    _ =
        (2 * Real.pi) / 3 := by
          ring

/-- The complete direct Dirichlet route to the canonical TS209 statement. -/
def CanonicalSincFourthDirectDirichletRouteStatement :
    Prop :=
  CanonicalSincFourthDirectDirichletRouteEvidence ->
    TS209.Goldbach.CanonicalSincFourthIntegralValueStatement

/-- The direct Dirichlet route, once its scalar evidence is supplied. -/
theorem canonicalSincFourthIntegral_of_directDirichletRoute :
    CanonicalSincFourthDirectDirichletRouteStatement := by
  intro evidence
  exact
    canonicalSincFourthIntegral_of_cosSquareValue_scaling_evenness
      (evidence.dirichlet_ipp_reduction
        evidence.third_derivative_formula
        evidence.dirichlet_sine_integral
        evidence.triple_ipp)
      evidence.sinc_fourth_scaling
      evidence.sinc_fourth_evenness

/--
The same direct route would populate the TS204 triangle-spline Plancherel
evidence via TS209 and TS208.
-/
theorem triangleSplinePlancherelEvidence_of_directDirichletRoute
    (evidence :
      CanonicalSincFourthDirectDirichletRouteEvidence) :
    TS204.Goldbach.TriangleSplinePlancherelInputEvidence
      TS204.Goldbach.triangleSplinePlancherelInputContract := by
  exact
    TS209.Goldbach.triangleSplinePlancherelInputEvidence_of_canonicalSincFourthIntegral
      (canonicalSincFourthIntegral_of_directDirichletRoute evidence)

/-- Ledger recording the TS213 direct Dirichlet route. -/
structure CanonicalSincFourthDirectDirichletRouteLedger where
  ts209_scale_reduction :
    TS209.Goldbach.TriangleSplineSincFourthScaleReductionLedger

  ts212_box_convolution_route :
    TS212.Goldbach.BoxFourierConvolutionExchangeLedger

  cos_square_remainder_defined :
    True

  dirichlet_statement :
    Prop

  dirichlet_statement_eq :
    dirichlet_statement = DirichletSineIntegralStatement

  triple_ipp_statement :
    Prop

  triple_ipp_statement_eq :
    triple_ipp_statement = CosSquareTripleIPPStatement

  scaling_statement :
    Prop

  scaling_statement_eq :
    scaling_statement = HalfLineSincFourthScalingStatement

  evenness_statement :
    Prop

  evenness_statement_eq :
    evenness_statement = FullLineSincFourthEvennessStatement

  direct_route_statement :
    Prop

  direct_route_statement_eq :
    direct_route_statement = CanonicalSincFourthDirectDirichletRouteStatement

  direct_route_proof :
    direct_route_statement

  route_implies_ts204_plancherel_evidence :
    CanonicalSincFourthDirectDirichletRouteEvidence ->
      TS204.Goldbach.TriangleSplinePlancherelInputEvidence
        TS204.Goldbach.triangleSplinePlancherelInputContract

  dirichlet_sine_integral_not_proved :
    True

  improper_triple_ipp_not_proved :
    True

  scaling_identity_not_proved :
    True

  evenness_identity_not_proved :
    True

  canonical_sinc_fourth_integral_not_proved_unconditionally :
    True

  plancherel_not_used :
    True

  parseval_not_used :
    True

  explicit_formula_not_proved :
    True

  gallagher_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS213 direct Dirichlet route ledger. -/
noncomputable def canonicalSincFourthDirectDirichletRouteLedger :
    CanonicalSincFourthDirectDirichletRouteLedger where
  ts209_scale_reduction :=
    TS209.Goldbach.triangleSplineSincFourthScaleReductionLedger
  ts212_box_convolution_route :=
    TS212.Goldbach.boxFourierConvolutionExchangeLedger
  cos_square_remainder_defined := True.intro
  dirichlet_statement := DirichletSineIntegralStatement
  dirichlet_statement_eq := rfl
  triple_ipp_statement := CosSquareTripleIPPStatement
  triple_ipp_statement_eq := rfl
  scaling_statement := HalfLineSincFourthScalingStatement
  scaling_statement_eq := rfl
  evenness_statement := FullLineSincFourthEvennessStatement
  evenness_statement_eq := rfl
  direct_route_statement := CanonicalSincFourthDirectDirichletRouteStatement
  direct_route_statement_eq := rfl
  direct_route_proof :=
    canonicalSincFourthIntegral_of_directDirichletRoute
  route_implies_ts204_plancherel_evidence :=
    triangleSplinePlancherelEvidence_of_directDirichletRoute
  dirichlet_sine_integral_not_proved := True.intro
  improper_triple_ipp_not_proved := True.intro
  scaling_identity_not_proved := True.intro
  evenness_identity_not_proved := True.intro
  canonical_sinc_fourth_integral_not_proved_unconditionally := True.intro
  plancherel_not_used := True.intro
  parseval_not_used := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS213. -/
def CanonicalSincFourthDirectDirichletRouteLedgerTarget :
    Prop :=
  Nonempty CanonicalSincFourthDirectDirichletRouteLedger

/-- The TS213 direct Dirichlet route ledger target is populated. -/
theorem canonicalSincFourthDirectDirichletRouteLedgerTarget :
    CanonicalSincFourthDirectDirichletRouteLedgerTarget :=
  Nonempty.intro canonicalSincFourthDirectDirichletRouteLedger

end Goldbach
end TS213
