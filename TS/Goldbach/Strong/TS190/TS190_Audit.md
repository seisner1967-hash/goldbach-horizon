# TS190 Audit - Triangle Spline Critical-Line Amplitude

## Scope

TS190 specializes the TS189 logarithmic Mellin/Fourier amplitude to the
critical-line shift `c = 1 / 2`.  This produces the real profile

```lean
triangleSplineCriticalAmplitude X u
```

which unfolds to

```lean
TS189.Goldbach.triangleSplineMellinFourierAmplitude
  (X : Real) (1 / 2 : Real) u
```

The sprint proves the exact nonnegativity, zero-branch, and affine-branch facts
by direct reuse of the TS189 algebraic pullback lemmas.  It does not add measure
transport or complex-analysis assumptions.

## Main Declarations

- `TS190.Goldbach.triangleSplineCriticalAmplitude`
- `TS190.Goldbach.triangleSplineCriticalAmplitude_nonneg`
- `TS190.Goldbach.triangleSplineCriticalAmplitude_eq_zero_of_X_le_exp`
- `TS190.Goldbach.triangleSplineCriticalAmplitude_eq_affine_of_exp_le_X`
- `TS190.Goldbach.TriangleSplineCriticalAmplitudeLedger`
- `TS190.Goldbach.triangleSplineCriticalAmplitudeLedger`
- `TS190.Goldbach.TriangleSplineCriticalAmplitudeTarget`
- `TS190.Goldbach.triangleSplineCriticalAmplitudeTarget`

## What TS190 Proves

TS190 proves:

- `0 <= triangleSplineCriticalAmplitude X u`;
- if `0 < X` and `(X : Real) <= exp u`, then the amplitude is `0`;
- if `0 < X` and `exp u <= (X : Real)`, then the amplitude is
  `(1 - exp u / (X : Real)) * exp (u / 2)`.

These are algebraic consequences of TS189.

## Non-Claims

TS190 does not prove:

- the Wall 0 measure transport `dx / x = du`;
- the Riemann hypothesis;
- the contour explicit formula;
- Plancherel;
- zeta-zero summability;
- Goldbach.

The choice `c = 1 / 2` is a functional specialization of the amplitude, not a
claim that zeta zeros lie on the critical line.

## Verification Commands

```powershell
lake env lean TS\Goldbach\Strong\TS190\TriangleSplineCriticalAmplitude.lean
lake build TS.Goldbach.Strong.TS190.TriangleSplineCriticalAmplitude
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS190
git diff --check
git status --short
```
