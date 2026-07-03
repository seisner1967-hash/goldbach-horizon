# TS223 Audit - Cos-Square IPP Primitive AtTop Asymptotic

## Scope

TS223 proves the `+infty` asymptotic for the TS220 primitive used in the
cos-square triple-IPP cutoff route.

Main file:

```text
TS/Goldbach/Strong/TS223/CosSquareIPPPrimitiveAtTopAsymptotic.lean
```

## Main declarations

```lean
TS223.Goldbach.cosSquareRemainder_abs_le_four
TS223.Goldbach.cosSquareFirstDerivativeModel_abs_le_four
TS223.Goldbach.cosSquareSecondDerivativeModel_abs_le_six
TS223.Goldbach.cosSquareIPPPrimitiveAtTopVanishing
TS223.Goldbach.CosSquareIPPPrimitiveAtTopAsymptoticLedger
TS223.Goldbach.cosSquareIPPPrimitiveAtTopAsymptoticTarget
```

The proved asymptotic is:

```lean
TS222.Goldbach.CosSquareIPPPrimitiveAtTopVanishingStatement
```

That is, the TS220 primitive `P(T)` tends to `0` as `T -> +infty`.

## Method

The proof uses the explicit TS220 primitive

```text
P(x) = -f(x)/(3*x^3) - f'(x)/(6*x^2) - f''(x)/(6*x)
```

with `f(x) = (1 - cos x)^2`.  TS223 proves global coefficient bounds:

```text
|f(x)| <= 4
|f'(x)| <= 4
|f''(x)| <= 6
```

and combines them with `tendsto_zpow_atTop_zero` for `x^(-3)`, `x^(-2)`,
and `x^(-1)`.

## Non-claims

TS223 does not prove:

```text
P(eps) -> 0 as eps -> 0+
TS219.Goldbach.CosSquareBoundaryVanishingStatement
TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement
Dirichlet cutoff or Abel convergence
the canonical sinc^4 value
Plancherel evidence
the explicit formula
Gallagher or large-sieve estimates
Goldbach
```

## Verification

```powershell
lake build TS.Goldbach.Strong.TS223.CosSquareIPPPrimitiveAtTopAsymptotic
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS223
git diff --check
```

Expected result: build succeeds and the scans produce no matches.

## Status

```text
repo_committed
```
