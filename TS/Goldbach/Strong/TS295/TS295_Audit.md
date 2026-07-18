# TS295 Audit - Strong Clean Heights and Log-Derivative Reduction

## Scope

TS295 refines the positive TS294 zero-height separation into the two
quantities actually needed by a horizontal logarithmic-derivative estimate:

```text
finite reciprocal zero load
local Cauchy bound for a holomorphic quotient logarithm.
```

The module deliberately uses the finite local factorization route already
developed for xi.  It does not introduce an infinite Hadamard product.

## Strong clean-height interface

For the concrete nontrivial zeta zeros through height `T+2`, TS295 defines

```text
reciprocalZeroLoad(T,tau)
  = sum m(rho) / abs(tau - abs(Im rho)).
```

The named `StrongCleanPerronContourExistenceStatement delta loadEnvelope`
requires a TS294 contour whose separation is at least `delta T` and whose
reciprocal load is at most `loadEnvelope T`.  Thus the interface records
rates depending on `T`; it does not mistake bare positivity for an
asymptotic estimate.

TS295 also proves the fallback estimate

```text
reciprocalZeroLoad(T,tau)
  <= nearbyZeroMultiplicityMass(T) / zeroSeparation.
```

This inequality is useful but intentionally not advertised as the desired
asymptotic load bound.

## Finite logarithmic derivative

The rational finite-zero contribution is

```text
finiteZeroLogDerivativeSum(T,s)
  = sum m(rho) / (s-rho).
```

The elementary inequalities

```text
abs(tau - abs(Im rho)) <= abs(sigma + i*tau - rho)
abs(tau - abs(Im rho)) <= abs(sigma - i*tau - rho)
```

are proved for every nonnegative `tau`.  Consequently, on both horizontal
sides of the TS294 rectangle,

```text
norm(finiteZeroLogDerivativeSum(T,s))
  <= reciprocalZeroLoad(T,tau).
```

This is a proved finite statement.  It does not use a zero-density theorem,
Stieltjes integration, or an infinite product.

## Nonvanishing quotient

`LocalHolomorphicLogCauchyData` packages:

* a positive ball radius;
* a logarithm differentiable continuously on the closed ball;
* the local identity `exp(logarithm) = g`;
* a norm bound for the logarithm on the sphere.

Mathlib's Cauchy derivative estimate then gives

```text
norm(deriv logarithm center) <= sphereBound / radius.
```

TS295 proves locally that

```text
deriv g(center) / g(center) = deriv logarithm(center)
```

and therefore closes both top- and bottom-side estimates whenever an exact
finite-factor decomposition and the local logarithm datum are supplied:

```text
norm(target)
  <= reciprocalZeroLoad(T,tau) + sphereBound / radius.
```

This is the intended local replacement for a global Hadamard partial
fraction expansion.

## Locked analytic boundary

The locked Mathlib revision contains the Cauchy derivative estimate used in
this sprint.  No ready-made effective Borel-Caratheodory theorem or
horizontal `zeta'/zeta` estimate was found.

The following remain separate named inputs:

* construction of strong clean heights with explicit rates;
* an effective reciprocal-load envelope;
* the exact finite xi/zeta logarithmic-derivative decomposition;
* a sphere bound for the holomorphic logarithm of the quotient.

## Non-claims

TS295 does not prove:

* strong clean-height existence with a rate;
* a reciprocal-load asymptotic;
* a closed horizontal `zeta'/zeta` bound;
* the left-boundary estimate;
* the right-line cutoff estimate;
* exceptional-residue inventory completeness;
* Perron inversion;
* the meromorphic rectangle residue theorem;
* an infinite explicit formula;
* Gallagher, OTSA, or Goldbach.

The intended continuation is:

```text
TS296: construct strong clean heights and instantiate the finite quotient log
TS297: targeted left/right contour estimates and residue inventory
TS298: Perron/residue closure and infinite explicit formula
```

## Verification

Canonical build target:

```powershell
lake build TS.Goldbach.Strong.TS295.StrongCleanHeightLogDerivativeReduction
```

Static checks:

```powershell
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS295
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS295
git diff --check
```

Expected result: the build succeeds and all static scans print no matches.
