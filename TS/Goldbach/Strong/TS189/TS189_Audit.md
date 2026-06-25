# TS189 Audit - Logarithmic Pullback Mellin Fourier Interface

## Scope

TS189 attacks Wall 0, the Mellin/Fourier compatibility gap, by separating the
provable algebraic logarithmic pullback from the unproved measure transport.

The sprint defines `logCoord`, `expCoord`, `realLogarithmicPullback`,
`triangleSplineLogPullback`, and `triangleSplineMellinFourierAmplitude`.  It
proves the log/exp round trips, the support and affine formulas for
`triangleSpline (exp u / X)`, and nonnegativity for both the pullback and the
critical amplitude.

The measure transport `dx / x = du`, the resulting Mellin-as-Fourier
equivalence, explicit-formula compatibility, and convergence/inversion remain
inside a local `LogPullbackMeasureTransportContract`.

## Main Declarations

- `TS189.Goldbach.logCoord`
- `TS189.Goldbach.expCoord`
- `TS189.Goldbach.logCoord_expCoord`
- `TS189.Goldbach.expCoord_logCoord`
- `TS189.Goldbach.realLogarithmicPullback`
- `TS189.Goldbach.realLogarithmicPullback_nonneg`
- `TS189.Goldbach.triangleSplineLogPullback`
- `TS189.Goldbach.triangleSplineLogPullback_nonneg`
- `TS189.Goldbach.triangleSplineLogPullback_eq_zero_of_X_le_exp`
- `TS189.Goldbach.triangleSplineLogPullback_eq_one_sub_of_exp_le_X`
- `TS189.Goldbach.triangleSplineMellinFourierAmplitude`
- `TS189.Goldbach.triangleSplineMellinFourierAmplitude_nonneg`
- `TS189.Goldbach.LogPullbackMeasureTransportContract`
- `TS189.Goldbach.LogPullbackMeasureTransportEvidence`
- `TS189.Goldbach.LogarithmicPullbackMellinFourierInterfaceLedger`
- `TS189.Goldbach.logarithmicPullbackMellinFourierInterfaceLedger`
- `TS189.Goldbach.LogarithmicPullbackMellinFourierInterfaceTarget`

## What TS189 Proves

TS189 proves the algebraic side of the logarithmic pullback:

- `log (exp u) = u`;
- `exp (log x) = x` for `0 < x`;
- `triangleSpline (exp u / X) = 0` when `0 < X` and `X <= exp u`;
- `triangleSpline (exp u / X) = 1 - exp u / X` when `0 < X` and `exp u <= X`;
- nonnegativity of the logarithmic pullback;
- nonnegativity of the critical amplitude.

## Non-Claims

TS189 does not prove:

- the measure transport `dx / x = du`;
- the full Mellin-as-Fourier integral equivalence;
- the contour explicit formula;
- Plancherel;
- zeta-zero summability;
- Goldbach.

Wall 0 is not discharged.  Only the algebraic logarithmic pullback is proved.

## Verification Commands

```powershell
lake env lean TS\Goldbach\Strong\TS189\LogarithmicPullbackMellinFourierInterface.lean
lake build TS.Goldbach.Strong.TS189.LogarithmicPullbackMellinFourierInterface
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS189
git diff --check
git status --short
```
