# TS244 Audit - Dirichlet Product-Cutoff and Third-Derivative Discharge

## Scope

TS244 applies the TS243 unit one-sided Dirichlet cutoff value to the product
cutoff infrastructure already proved in TS228 and TS227.

It proves the unit product-filter value, every positive-frequency value, and
the TS219 third-derivative cutoff value.

## Main Declarations

- `dirichletProductCutoffUnitValue`
- `dirichletProductCutoffValue`
- `dirichletProductCutoffFrequencyTwoValue`
- `thirdDerivativeDirichletProductCutoffEvidence`
- `cosSquareThirdDerivativeCutoffValue`
- `DirichletProductCutoffThirdDerivativeDischargeLedger`
- `dirichletProductCutoffThirdDerivativeDischargeTarget`

## What Is Proved

TS243 proves the one-sided unit-frequency value

```text
F(T) -> pi/2 as T -> +infty.
```

TS228 combines this with the lower-endpoint limit to obtain the unit value on
the product cutoff filter.  TS227 then scales the product cutoff endpoints and
proves the value `pi/2` for every positive frequency.

For frequencies `1` and `2`, TS225 and TS226 identify the third-derivative
kernel integral with

```text
-2 * (pi/2) + 4 * (pi/2) = pi.
```

Therefore TS244 unconditionally proves

```lean
TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement
```

## Non-Claims

TS244 does not prove `CosSquareImproperCutoffConvergenceStatement` or
`CosSquareTripleIPPCutoffAssemblyStatement`.  Consequently it does not yet
prove `cosSquareImproperIntegral = pi/6`.

TS244 does not prove the canonical sinc-fourth value, Plancherel evidence, the
explicit formula input, Gallagher, or Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS244.DirichletProductCutoffThirdDerivativeDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS244
git diff --check
```

## Expected Audit Result

The build succeeds.  The TS244 directory contains no placeholder proofs, no
forbidden declarations, and no non-ASCII characters.  `git diff --check`
reports no whitespace errors.
