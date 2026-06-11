# TS147 Audit

## Scope

TS147 unfolds the reconstructed optimal Selberg weights used by TS146 and
replaces their opaque finite `L1` norm by an explicit divisor-first envelope.

No asymptotic estimate is claimed in this sprint.

## Exact weight formula

```text
TS147.Goldbach.selbergOptimalWeightMobiusSum
TS147.Goldbach.selbergOptimalWeightExplicitRat
TS147.Goldbach.selbergConcreteLambda_eq_explicit
```

The concrete TS142 coefficient is definitionally the TS130 reconstruction:

```text
lambda(m) = m * sum_{d in support, m | d} mu(d/m) * Y(d),
```

where `Y` is the TS128 optimal diagonal vector.

## Pointwise envelope

```text
TS147.Goldbach.abs_selbergMobiusRatCoefficient_le_one
TS147.Goldbach.selbergOptimalWeightDiagonalEnvelopeRat
TS147.Goldbach.abs_mobius_mul_optimalVector_le
TS147.Goldbach.abs_selbergConcreteLambda_le_diagonalEnvelope
```

Mathlib's integer Mobius bound is transported to `Rat`, and finite triangle
inequalities give

```text
|lambda(m)| <= m * sum_{d in support, m | d} |Y(d)|.
```

## Global divisor envelope

```text
TS147.Goldbach.selbergOptimalWeightL1EnvelopeRat
TS147.Goldbach.selbergConcreteLambdaL1_le_explicitEnvelope
TS147.Goldbach.selbergSupportedDivisorMassRat
TS147.Goldbach.selbergOptimalWeightDivisorEnvelopeRat
TS147.Goldbach.selbergOptimalWeightL1Envelope_eq_divisorEnvelope
TS147.Goldbach.selbergConcreteLambdaL1_le_divisorEnvelope
```

Finite Fubini reindexing produces the divisor-first form

```text
sum_m m * sum_{m | d} |Y(d)|
  = sum_d |Y(d)| * sum_{m | d} m,
```

with every sum restricted to the positive TS122 support.

## Connection to TS146

```text
TS147.Goldbach.selbergConcreteSquareMajorantRat_le_mainBudget_add_divisorEnvelope_sq
TS147.Goldbach.SelbergOptimalWeightExplicitFormula
TS147.Goldbach.selbergOptimalWeightExplicitFormulaTarget
```

For positive level, the concrete interval square majorant is bounded by

```text
intervalLength / D + divisorEnvelope(level)^2.
```

## Remaining work

TS147 does not yet estimate the supported divisor mass or the complete
divisor envelope, estimate the optimization denominator effectively, or
compare the resulting bound with the final Brun-Titchmarsh ceiling budget.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS147.SelbergOptimalWeightExplicitFormula
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS147
git diff --check
```

Expected result: build succeeds and the audit search returns no matches.
