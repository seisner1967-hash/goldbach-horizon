# TS228 Audit - Dirichlet Product-Cutoff Partial-Integral Bridge

## Scope

TS228 bridges the remaining unit-frequency product-filter Dirichlet cutoff
target from TS227 to a one-variable partial-integral target.

It does not prove the classical Dirichlet value.  It proves that the product
filter limit follows from the one-sided limit

```text
int_0^T sin x / x dx -> pi/2 as T -> +infty.
```

## Main declarations

- `dirichletUnitPartialIntegral`
- `DirichletUnitPartialIntegralAtTopStatement`
- `DirichletUnitPartialIntegralZeroRightStatement`
- `DirichletUnitPartialIntegralDecompositionStatement`
- `dirichletUnitPartialIntegralAtTopStatement_eq_ts216`
- `sineDirichletKernel_one_abs_le_one`
- `dirichletUnitPartialIntegral_abs_le_abs`
- `sineDirichletKernel_one_intervalIntegrable`
- `dirichletUnitPartialIntegral_decomposition`
- `dirichletUnitPartialIntegralZeroRight`
- `dirichletProductCutoffUnitValue_of_partialIntegral`
- `dirichletProductCutoffUnitValue_of_partialIntegralAtTop`
- `DirichletProductCutoffPartialIntegralBridgeLedger`
- `dirichletProductCutoffPartialIntegralBridgeTarget`

## What is proved

TS228 defines the unit partial integral

```text
F(T) = int_0^T sineDirichletKernel 1 x dx.
```

It proves the global bound

```text
|sineDirichletKernel 1 x| <= 1
```

and therefore

```text
|F(T)| <= |T|.
```

This gives the lower-end limit

```text
F(eps) -> 0 as eps -> 0+.
```

TS228 also proves the finite decomposition

```text
int_eps^T D_1(x) dx = F(T) - F(eps)
```

and combines it with a future proof of

```text
F(T) -> pi/2 as T -> +infty
```

to obtain the TS227 unit-frequency product-filter cutoff value.

The atTop statement is definitionally identified with the TS216 cutoff target.

## Non-claims

TS228 does not prove the atTop Dirichlet partial-integral value.

TS228 does not prove Abel convergence, the product-filter Dirichlet value
unconditionally, the TS219 third-derivative cutoff value unconditionally,
`cosSquareImproperIntegral = pi/6`, the canonical `sinc^4` value `2*pi/3`,
Plancherel evidence, the explicit formula, Gallagher, or Goldbach.

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS228.DirichletProductCutoffPartialIntegralBridge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS228
git diff --check
```

## Expected result

The build succeeds.  The scan finds no `s[o]rry`, no `a[x]iom`, and no
non-ASCII characters in TS228.  `git diff --check` reports no whitespace
errors.
