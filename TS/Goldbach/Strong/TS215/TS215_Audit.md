# TS215 Audit - Dirichlet Sine Integral API Probe

## Scope

TS215 probes the Mathlib API for the second scalar obligation in the TS213
direct Dirichlet route:

```lean
TS213.Goldbach.DirichletSineIntegralStatement
```

The target is the positive-frequency Dirichlet sine integral on the positive
half-line:

```text
forall a > 0, integral_0^infty sin (a*x) / x = pi / 2
```

The local search did not locate a ready-made `sin x / x` Dirichlet value
theorem in the bundled Mathlib.  The sprint therefore records a fail-closed
API probe rather than claiming the value.

## Main Declarations

- `TS215.Goldbach.DirichletSineIntegralAPIStatus`
- `TS215.Goldbach.DirichletUnitFrequencyStatement`
- `TS215.Goldbach.DirichletPositiveFrequencyScalingStatement`
- `TS215.Goldbach.IoiScalingAPISymbolAvailable`
- `TS215.Goldbach.ioiScalingAPISymbolAvailable`
- `TS215.Goldbach.dirichletSineIntegral_of_unitValue_and_scaling`
- `TS215.Goldbach.DirichletSineIntegralAPIProbeLedger`
- `TS215.Goldbach.dirichletSineIntegralAPIProbeLedger`
- `TS215.Goldbach.DirichletSineIntegralAPIProbeTarget`
- `TS215.Goldbach.dirichletSineIntegralAPIProbeTarget`

## What TS215 Proves

TS215 proves that Mathlib exposes the positive-half-line scaling theorem in the
form needed by the project:

```lean
forall g a b, 0 < b ->
  integral (volume.restrict (Set.Ioi a)) (fun x => g (b * x)) =
    (1 / b) * integral (volume.restrict (Set.Ioi (b * a))) g
```

using `integral_comp_mul_left_Ioi`.

It also proves the routing lemma:

```lean
DirichletUnitFrequencyStatement ->
  DirichletPositiveFrequencyScalingStatement ->
    TS213.Goldbach.DirichletSineIntegralStatement
```

Thus the TS213 Dirichlet slot has been reduced to a unit-frequency value plus a
positive-frequency scaling statement.

## Non-Claims

TS215 does not prove:

- the unit-frequency Dirichlet sine integral;
- the positive-frequency scaling of the singular sine kernel;
- `TS213.Goldbach.DirichletSineIntegralStatement`;
- improper triple integration by parts;
- the `sinc^4` scaling identity;
- the evenness identity;
- the canonical `sinc^4` value;
- Plancherel or Parseval;
- the explicit formula;
- Gallagher or large-sieve comparison;
- Goldbach.

## Verification Commands

```powershell
lake env lean TS\Goldbach\Strong\TS215\DirichletSineIntegralAPIProbe.lean
lake build TS.Goldbach.Strong.TS215.DirichletSineIntegralAPIProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS215
git diff --check
git status --short
```
