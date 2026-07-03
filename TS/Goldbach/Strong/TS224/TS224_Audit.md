# TS224 Audit - Cos-Square IPP Primitive Zero-Right Asymptotic

## Scope

TS224 proves the remaining one-variable boundary asymptotic isolated by TS222:

```lean
TS222.Goldbach.CosSquareIPPPrimitiveZeroRightVanishingStatement
```

That is, the TS220 primitive `P` tends to zero as `x -> 0+`.

TS224 also combines this zero-right limit with the TS223 atTop limit through the
TS222 bridge to prove:

```lean
TS219.Goldbach.CosSquareBoundaryVanishingStatement
```

## Main declarations

```lean
TS224.Goldbach.cosSquareRemainder_abs_le_quarter_fourth
TS224.Goldbach.cosSquareFirstDerivativeModel_abs_le_cube
TS224.Goldbach.cosSquareSecondDerivativeModel_abs_le_three_sq
TS224.Goldbach.cosSquareIPPPrimitive_abs_le_three_quarters_mul
TS224.Goldbach.cosSquareIPPPrimitiveZeroRightVanishing
TS224.Goldbach.cosSquareIPPPrimitiveBoundaryLimitEvidence
TS224.Goldbach.cosSquareBoundaryVanishing
TS224.Goldbach.cosSquareIPPPrimitiveZeroRightAsymptoticTarget
```

## Proof method

The proof uses local estimates near zero:

```text
|1 - cos x| <= x^2 / 2
|sin x| <= |x|
|cos x| <= 1
```

For `0 < x`, these yield:

```text
|f(x)| <= x^4 / 4
|f'(x)| <= x^3
|f''(x)| <= 3*x^2
```

Since

```text
P(x) = -f(x)/(3*x^3) - f'(x)/(6*x^2) - f''(x)/(6*x),
```

TS224 proves:

```text
|P(x)| <= (3/4)*x
```

and then squeezes `P(x)` between `-(3/4)*x` and `(3/4)*x` along
`nhdsWithin 0 (Set.Ioi 0)`.

## Non-claims

TS224 does not prove the third-derivative cutoff value.  It does not prove
Dirichlet cutoff convergence or Abel convergence.  It does not prove
`cosSquareImproperIntegral = pi/6`.  It does not prove the canonical `sinc^4`
value, Plancherel evidence, the explicit formula, Gallagher, or Goldbach.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS224.CosSquareIPPPrimitiveZeroRightAsymptotic
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS224
git diff --check
```

Expected result: build succeeds; scan has no matches; diff check reports no
whitespace errors.

## Status

```text
repo_committed
```
