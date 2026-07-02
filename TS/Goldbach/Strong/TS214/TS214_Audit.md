# TS214 Audit - Cos-Square Third Derivative Formula Discharge

## Scope

TS214 discharges the first scalar obligation introduced by TS213 for the direct
non-Plancherel route to the canonical `sinc^4` integral.  The obligation is the
third-derivative formula for

```lean
f(x) = (1 - cos x)^2
```

as used in the classical triple integration-by-parts route.

## Main Declarations

- `TS214.Goldbach.cosSquareRemainder_deriv`
- `TS214.Goldbach.cosSquareRemainder_second_deriv`
- `TS214.Goldbach.cosSquareRemainder_third_deriv`
- `TS214.Goldbach.cosSquareThirdDerivativeFormula`
- `TS214.Goldbach.CosSquareThirdDerivativeFormulaDischargeLedger`
- `TS214.Goldbach.cosSquareThirdDerivativeFormulaDischargeLedger`
- `TS214.Goldbach.CosSquareThirdDerivativeFormulaDischargeTarget`
- `TS214.Goldbach.cosSquareThirdDerivativeFormulaDischargeTarget`

## What TS214 Proves

TS214 proves:

```lean
TS213.Goldbach.CosSquareThirdDerivativeFormulaStatement
```

Concretely, for every real `x`,

```lean
deriv
  (fun z =>
    deriv
      (fun y =>
        deriv TS213.Goldbach.cosSquareRemainder y) z) x
=
-2 * sin x + 4 * sin (2 * x)
```

The proof proceeds through named first- and second-derivative formulae and then
uses explicit product/add derivative rules plus `Real.sin_two_mul` and `ring`.

## Non-Claims

TS214 does not prove:

- the Dirichlet sine integral;
- the improper triple integration-by-parts identity;
- the scaling identity from `x = 2*u`;
- the evenness identity;
- the canonical `sinc^4` value;
- Plancherel or Parseval;
- the explicit formula;
- Gallagher or large-sieve comparison;
- Goldbach.

## Verification Commands

```powershell
lake env lean TS\Goldbach\Strong\TS214\CosSquareThirdDerivativeFormulaDischarge.lean
lake build TS.Goldbach.Strong.TS214.CosSquareThirdDerivativeFormulaDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS214
git diff --check
git status --short
```
