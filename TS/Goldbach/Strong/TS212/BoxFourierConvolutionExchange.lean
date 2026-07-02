import Mathlib.Tactic
import TS.Goldbach.Strong.TS173.TriangleSplineFourierIdentificationDischarge
import TS.Goldbach.Strong.TS210.BoxConvolutionTriangleEvidence
import TS.Goldbach.Strong.TS211.BoxFourierEvaluation

namespace TS212
namespace Goldbach

/-!
# TS212 - Box Fourier Convolution Exchange

TS167 named three local inputs for the convolution route to the triangle-spline
Fourier identity:

1. the centered unit box self-convolution is the triangle spline;
2. the Fourier transform of the box is the non-squared sinc;
3. the Fourier transform of the box self-convolution is the square of the box
   Fourier transform.

TS210 proved the first input and TS211 proved the second.  TS212 proves the
third specialized exchange statement.

The proof is intentionally specialized and fail-closed.  It does not invoke a
general Fourier-convolution theorem from Mathlib.  Instead, it uses TS210 to
rewrite the box self-convolution as the triangle spline, TS173 to evaluate the
Fourier transform of the triangle spline, TS211 to evaluate the Fourier
transform of the box, and TS167's algebraic bridge from squared sinc to
squared-sinc.

No Plancherel theorem, Parseval theorem, canonical `sinc^4` integral, explicit
formula, Gallagher comparison, or Goldbach theorem is claimed.
-/

/-- The exact TS167 Fourier-convolution exchange target. -/
def BoxFourierConvolutionExchangeTarget : Prop :=
  TS167.Goldbach.BoxFourierConvolutionExchangeStatement

/--
The specialized Fourier-convolution exchange for the centered unit box.

This proves the TS167 exchange obligation by comparing both sides with the
already-proved triangle-spline Fourier closed form.  It is not a general
Fourier-convolution theorem.
-/
theorem boxFourierConvolutionExchange :
    TS167.Goldbach.BoxFourierConvolutionExchangeStatement := by
  intro xi
  have h_spatial_fun :
      TS167.Goldbach.unitBoxSelfConvolution =
        TS166.Goldbach.triangleSplineAsComplex := by
    funext x
    exact TS210.Goldbach.boxConvolutionEqualsTriangleSpline x
  calc
    Real.fourierIntegral TS167.Goldbach.unitBoxSelfConvolution xi =
        Real.fourierIntegral TS166.Goldbach.triangleSplineAsComplex xi := by
          rw [h_spatial_fun]
    _ =
        (TS164.Goldbach.scaledSincSq
          TS165.Goldbach.mathlibFourierTargetScale xi : Complex) := by
          exact TS173.Goldbach.triangleSplineFourierIdentification xi
    _ =
        (TS167.Goldbach.scaledSinc
          TS165.Goldbach.mathlibFourierTargetScale xi : Complex) *
          (TS167.Goldbach.scaledSinc
            TS165.Goldbach.mathlibFourierTargetScale xi : Complex) := by
          exact
            (TS167.Goldbach.scaledSinc_mul_self_eq_scaledSincSq
              TS165.Goldbach.mathlibFourierTargetScale xi).symm
    _ =
        Real.fourierIntegral TS167.Goldbach.unitBoxAsComplex xi *
          Real.fourierIntegral TS167.Goldbach.unitBoxAsComplex xi := by
          rw [TS211.Goldbach.boxFourierEvaluation xi]

/--
The full TS167 convolution route now closes using TS210, TS211, and the TS212
specialized exchange.
-/
theorem triangleSplineFourierIdentification_via_boxRoute :
    TS166.Goldbach.TriangleSplineFourierIdentificationStatement :=
  TS167.Goldbach.convolutionRoute_implies_ts166
    TS210.Goldbach.boxConvolutionEqualsTriangleSpline
    TS211.Goldbach.boxFourierEvaluation
    boxFourierConvolutionExchange

/-- Ledger for the TS212 Fourier-convolution exchange evidence. -/
structure BoxFourierConvolutionExchangeLedger where
  ts210_spatial_convolution :
    TS210.Goldbach.BoxConvolutionTriangleEvidenceLedger

  ts211_box_fourier :
    TS211.Goldbach.BoxFourierEvaluationLedger

  exchange_target :
    Prop

  exchange_target_eq :
    exchange_target =
      TS167.Goldbach.BoxFourierConvolutionExchangeStatement

  exchange_proved :
    exchange_target

  box_route_closes_ts166 :
    TS166.Goldbach.TriangleSplineFourierIdentificationStatement

  general_fourier_convolution_theorem_not_proved :
    True

  plancherel_not_proved :
    True

  parseval_not_proved :
    True

  canonical_sinc_fourth_integral_not_proved :
    True

  explicit_formula_not_proved :
    True

  gallagher_not_proved :
    True

  goldbach_not_claimed :
    True

/-- Concrete TS212 box Fourier-convolution exchange ledger. -/
noncomputable def boxFourierConvolutionExchangeLedger :
    BoxFourierConvolutionExchangeLedger where
  ts210_spatial_convolution :=
    TS210.Goldbach.boxConvolutionTriangleEvidenceLedger
  ts211_box_fourier :=
    TS211.Goldbach.boxFourierEvaluationLedger
  exchange_target :=
    TS167.Goldbach.BoxFourierConvolutionExchangeStatement
  exchange_target_eq := rfl
  exchange_proved :=
    boxFourierConvolutionExchange
  box_route_closes_ts166 :=
    triangleSplineFourierIdentification_via_boxRoute
  general_fourier_convolution_theorem_not_proved := True.intro
  plancherel_not_proved := True.intro
  parseval_not_proved := True.intro
  canonical_sinc_fourth_integral_not_proved := True.intro
  explicit_formula_not_proved := True.intro
  gallagher_not_proved := True.intro
  goldbach_not_claimed := True.intro

/-- Target proposition for TS212. -/
def BoxFourierConvolutionExchangeLedgerTarget : Prop :=
  Nonempty BoxFourierConvolutionExchangeLedger

/-- The TS212 Fourier-convolution exchange ledger target is populated. -/
theorem boxFourierConvolutionExchangeLedgerTarget :
    BoxFourierConvolutionExchangeLedgerTarget :=
  Nonempty.intro boxFourierConvolutionExchangeLedger

end Goldbach
end TS212
