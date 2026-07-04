# TS227 Audit - Dirichlet Product-Cutoff Scaling Reduction

## Scope

TS227 proves the positive-frequency scaling reduction for the product-filter
Dirichlet cutoff values used by TS225.

It reduces all positive frequencies to the unit-frequency cutoff value.  In
particular, the frequency `2` value needed by the third-derivative residual is
a consequence of the frequency `1` value.

## Main declarations

- `scaleCutoffPair`
- `DirichletProductCutoffUnitValueStatement`
- `scaleCutoffPair_tendsto`
- `dirichletProductCutoffIntegral_scale`
- `dirichletProductCutoffValue_of_unit`
- `dirichletProductCutoff_freq_two_of_unit`
- `thirdDerivativeDirichletProductCutoffEvidence_of_unit`
- `cosSquareThirdDerivativeCutoffValue_of_unitDirichlet`
- `DirichletProductCutoffScalingReductionLedger`
- `dirichletProductCutoffScalingReductionTarget`

## What is proved

TS227 proves that the TS219 cutoff filter is stable under the endpoint scaling

```text
(eps, T) |-> (a*eps, a*T)
```

for every `a > 0`.

It also proves the finite interval change of variables

```text
int_eps^T sin(a*x)/x dx =
  int_(a*eps)^(a*T) sin(u)/u du
```

using the pointwise identity

```text
sineDirichletKernel a x =
  a * sineDirichletKernel 1 (a*x)
```

and `intervalIntegral.smul_integral_comp_mul_left`.

Consequently, one unit-frequency product-cutoff Dirichlet value supplies every
positive frequency value, including frequency `2`.  Combined with TS226 finite
linearization and TS225 reduction, the unit-frequency value also supplies the
TS219 third-derivative cutoff value.

## Non-claims

TS227 does not prove the unit-frequency Dirichlet product-cutoff value.

TS227 does not prove Abel convergence, cutoff convergence from scratch, the
cos-square integral value `pi/6`, the canonical `sinc^4` value `2*pi/3`,
Plancherel evidence, the explicit formula, Gallagher, or Goldbach.

## Audit commands

```powershell
lake build TS.Goldbach.Strong.TS227.DirichletProductCutoffScalingReduction
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS227
git diff --check
```

## Expected result

The build succeeds.  The scan finds no `s[o]rry`, no `a[x]iom`, and no
non-ASCII characters in TS227.  `git diff --check` reports no whitespace
errors.
