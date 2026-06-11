# TS149 Audit

## Scope

TS149 refines the TS148 divisor-envelope estimate by using the arithmetic
domination of the divisor sum by the Jordan-two coefficient.

The result is finite and unconditional for every positive Selberg level.

## Prime-power and global domination

```text
TS149.Goldbach.prime_geometric_sum_le_pow
TS149.Goldbach.sigmaOne_prime_pow_le_jordanTwo
TS149.Goldbach.sigmaOne_le_jordanTwo
```

For every prime power with positive exponent, the geometric divisor sum is
bounded by the TS125 prime-power formula for `J2`. Multiplicativity and the
`Nat.factorization` product formula then give

```text
sigma_1(n) <= J2(n)
```

for every positive integer `n`.

## Supported divisor mass

```text
TS149.Goldbach.optimizationSupport_filter_dvd_eq_divisors
TS149.Goldbach.selbergSupportedDivisorMass_eq_sigmaOne
TS149.Goldbach.selbergSupportedDivisorMass_le_jordanTwo
```

For `d` in the positive optimization support, every positive divisor of `d`
also lies in the support. Hence the supported divisor mass is exactly
`sigma_1(d)` and is bounded by `J2(d)`.

## Refined coordinate cancellation

```text
TS149.Goldbach.abs_selbergOptimalDiagonalVector_le_inv_den_mul_jordanTwo
TS149.Goldbach.divisorEnvelope_term_le_invDenominator
```

The explicit TS128 coordinate satisfies

```text
|Y(d)| <= 1 / (D * J2(d)).
```

Multiplying by the supported divisor mass and using `sigma_1(d) <= J2(d)`
leaves at most `1 / D` per support index.

## Refined envelope and interval budget

```text
TS149.Goldbach.selbergOptimalWeightDivisorEnvelope_le_level_div_denominator
TS149.Goldbach.selbergConcreteLambdaL1_le_level_div_denominator
TS149.Goldbach.selbergConcreteSquareMajorantRat_le_refinedBudget
TS149.Goldbach.SelbergDivisorEnvelopeJordanRefinement
TS149.Goldbach.selbergDivisorEnvelopeJordanRefinementTarget
```

Since the positive support has cardinality `level`, TS149 proves

```text
divisorEnvelope(level) <= level / D(level)
sum |lambda(d)| <= level / D(level).
```

Consequently,

```text
squareMajorant <= intervalLength / D + (level / D)^2.
```

This improves the TS148 error contribution from `level^6 / D^2` to
`level^2 / D^2`.

## Remaining work

TS149 does not optimize the ratio `sigma_1(d) / J2(d)` beyond the coefficient
bound used here, choose the Selberg level as a function of the interval
parameters, or prove the final Brun-Titchmarsh ceiling comparison.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS149.SelbergDivisorEnvelopeJordanRefinement
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS149
git diff --check
```

Expected result: build succeeds and the audit search returns no matches.
