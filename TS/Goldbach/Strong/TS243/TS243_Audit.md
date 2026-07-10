# TS243 Audit - Dirichlet Cutoff Abel Final-Value Identification

## Scope

TS243 proves the local Abel final-value identification opened by TS242.  It
uses:

- the TS241 convergence of the ordinary cutoff partial integral to the
  canonical real number `dirichletCutoffLimit`;
- the TS242 Abel summation identity;
- the TS237 evaluation of the damped Dirichlet integral.

The result is the unconditional identification

```lean
TS241.Goldbach.dirichletCutoffLimit = Real.pi / 2
```

and therefore the TS228 unit one-sided cutoff target and the TS229/TS238
Abel-to-cutoff bridge are closed.

## Main Declarations

- `InfiniteAbelAverageStatement`
- `AbelAverageFinalValueStatement`
- `infiniteAbelAverage`
- `dirichletUnitPartialIntegral_abs_le`
- `expNegMul_intervalIntegral_eq`
- `scaled_expNegMul_intervalIntegral_le_one`
- `dirichletAbelAverage_sub_cutoffLimit_mass`
- `centered_abel_integrand_compact_bound`
- `centered_abel_integrand_tail_bound`
- `centered_abel_compact_integral_bound`
- `centered_abel_tail_integral_bound`
- `centered_abel_finite_bound`
- `abelAverageFinalValue`
- `localAbelFinalValue`
- `dirichletCutoffLimit_eq_pi_div_two`
- `dirichletUnitPartialIntegralAtTop`
- `abelToCutoffBridge`
- `abelToCutoffBridgeFrontier`
- `DirichletCutoffAbelFinalValueIdentificationLedger`

## What Is Proved

For every `b > 0`, the finite Abel averages

```lean
TS242.Goldbach.dirichletAbelAverage b T
```

tend, as `T -> +infty`, to the already evaluated damped Dirichlet value

```lean
Real.pi / 2 - Real.arctan b
```

The local final-value theorem is then proved by centering the Abel average at
the TS241 cutoff limit `L`.  The finite centered identity is

```lean
dirichletAbelAverage b T - L * (1 - exp (-b*T))
  =
b * int_0^T exp (-b*x) * (F x - L) dx
```

The proof cuts this integral at a fixed `R`:

- on `[0, R]`, the compact part is bounded and killed by the small factor `b`;
- on `[R, T]`, TS241 makes `F x` uniformly close to `L`;
- for fixed `b`, `T` is chosen large enough to compare the finite Abel average
  with its damped value and to make `L * (1 - exp (-b*T))` close to `L`.

This yields

```lean
Tendsto
  (fun b => Real.pi / 2 - Real.arctan b)
  (nhdsWithin 0 (Set.Ioi 0))
  (nhds TS241.Goldbach.dirichletCutoffLimit)
```

and uniqueness of limits with the already proved scalar Abel limit gives

```lean
TS241.Goldbach.dirichletCutoffLimit = Real.pi / 2
```

## Consequences

TS243 proves:

```lean
TS228.Goldbach.DirichletUnitPartialIntegralAtTopStatement
TS229.Goldbach.AbelToCutoffBridgeStatement
TS238.Goldbach.AbelToCutoffBridgeFrontierStatement
```

Thus the unit Dirichlet cutoff value is now available to the upstream
Dirichlet product-filter and third-derivative cutoff reductions.

## Non-claims

TS243 does not prove the cos-square value, does not prove the canonical
sinc-fourth value, does not prove Plancherel evidence, the explicit formula
input, Gallagher estimate, or Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS243.DirichletCutoffAbelFinalValueIdentification
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS243
git diff --check
```

## Expected Audit Result

The TS243 directory contains no placeholder proofs, no forbidden declarations,
and no non-ASCII characters.  `git diff --check` reports no whitespace errors.
