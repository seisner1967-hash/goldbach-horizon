# TS148 Audit

## Scope

TS148 gives the explicit TS147 divisor envelope a coarse polynomial bound in
the Selberg level and the TS122 optimization denominator.

The bound is finite and unconditional for positive levels. It is not claimed
to have optimal growth.

## Support geometry

```text
TS148.Goldbach.selbergOptimizationSupport_eq_Icc
TS148.Goldbach.card_selbergOptimizationSupport
```

The positive TS122 support is exactly `Icc 1 level`, so its cardinality is
`level`.

## Coefficient bounds

```text
TS148.Goldbach.one_le_selbergJordanTwoPenalty
TS148.Goldbach.abs_selbergOptimalDiagonalVector_le_invDenominator
```

TS145 gives `totient(d) <= J2(d)`, while positivity of `totient(d)` for
positive `d` yields `1 <= J2(d)`. Together with `|mu(d)| <= 1` and positivity
of `D`, the explicit TS128 formula gives

```text
|Y(d)| <= 1 / D
```

on the optimization support.

## Divisor mass and envelope

```text
TS148.Goldbach.supportedDivisorMass_term_le_level
TS148.Goldbach.selbergSupportedDivisorMass_le_level_sq
TS148.Goldbach.divisorEnvelope_term_le
TS148.Goldbach.selbergOptimalWeightDivisorEnvelope_le_level_cube_div_denominator
TS148.Goldbach.selbergConcreteLambdaL1_le_level_cube_div_denominator
```

Each divisor-mass summand is at most `level`; there are exactly `level`
support indices. Hence

```text
supportedDivisorMass(level,d) <= level^2.
```

Summing the product with `|Y(d)| <= 1 / D` over the `level` support indices
gives

```text
divisorEnvelope(level) <= level^3 / D(level).
```

## Explicit interval budget

```text
TS148.Goldbach.selbergConcreteSquareMajorantRat_le_explicitPolynomialBudget
TS148.Goldbach.SelbergDivisorEnvelopePolynomialBound
TS148.Goldbach.selbergDivisorEnvelopePolynomialBoundTarget
```

For every positive level, the TS138 rational square majorant now satisfies

```text
squareMajorant <= intervalLength / D + (level^3 / D)^2.
```

## Remaining work

TS148 does not optimize the cubic divisor-envelope bound, establish an
effective lower estimate for `D(level)`, or compare the resulting expression
with the final Brun-Titchmarsh ceiling budget.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS148.SelbergDivisorEnvelopePolynomialBound
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS148
git diff --check
```

Expected result: build succeeds and the audit search returns no matches.
