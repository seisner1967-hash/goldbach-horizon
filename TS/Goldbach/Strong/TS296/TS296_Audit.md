# TS296 Audit - Concrete Strong Height and Exact Xi Quotient Log

## Scope

TS296 turns the TS295 reduction into concrete finite analytic data.  It
constructs:

```text
a height tau in (T,T+1) avoiding every nearby zero ordinate,
a positive finite separation delta(T),
the exact reciprocal load at tau,
the exact quotient xi / P_T,
a local holomorphic logarithm of that quotient,
and top/bottom horizontal xi'/xi bounds.
```

No new growth, height-existence, or quotient hypothesis is introduced.

The construction is unconditional but not yet asymptotically effective:
the selected minimum gap has no closed lower rate in `T`, and the canonical
sphere supremum of the logarithm has no closed upper rate in `T`.

## Concrete strong height

`nearbyZeroHeights T` is the image of the finite TS295 zero family under
`rho |-> abs(Im rho)`.  Since `(T,T+1)` is infinite, TS296 chooses

```text
strongHeightTau T in (T,T+1)
```

outside this finite image.  The minimum of the resulting positive gaps,
capped by `1`, defines `strongHeightDelta T`.

The exact envelope

```text
strongHeightLoadEnvelope T
  = reciprocalZeroLoad T (strongHeightTau T)
```

then inhabits

```text
StrongCleanPerronContourExistenceStatement
  strongHeightDelta strongHeightLoadEnvelope.
```

This is a real construction, not an existence assumption.  It gives a
positive separation and a finite load for every natural `T >= 1`.

It does not yet prove a lower bound such as

```text
delta(T) >= c / (M(T)+1)
```

or an upper bound such as

```text
load(T) <= C * M(T) * log(M(T)+2).
```

Those require the finite averaging or grid-selection argument proposed for
the next quantitative refinement.

## Exact height quotient

The polynomial is indexed by exactly the TS295 height finset:

```text
P_T(z) =
  product over rho in nearbyConcreteZeros(T)
    of (z-rho)^multiplicity(rho).
```

The quotient is not an anonymous remainder:

```text
g_T(z) = xi(z) / P_T(z).
```

TS296 proves:

* every xi zero lies in the open critical strip;
* every xi zero is a concrete nontrivial zeta zero;
* `P_T` and xi are nonzero on the top and bottom closed balls of radius
  `delta(T)/2`;
* `g_T` is analytic and nonzero on those balls;
* the exact identity

```text
xi'/xi = finiteZeroLogDerivativeSum(T) + g_T'/g_T
```

at both horizontal centers.

Thus the weak TS295 proposition with a freely chosen remainder is not used
to close the decomposition.

## Concrete local logarithm

For each horizontal center, TS296 builds empty-zero buffered Jensen data for
`g_T` with radii

```text
delta(T)/16 < delta(T)/8 < delta(T)/4.
```

The outer closed ball lies in the proved zero-free ball of radius
`delta(T)/2`.  TS279 therefore supplies a concrete holomorphic logarithm of
`g_T`.

The norm of this logarithm on the analytic sphere has compact image.  Its
real supremum supplies the exact `sphereBound` required by
`LocalHolomorphicLogCauchyData`.  TS295 then gives the proved bounds

```text
norm(xi'/xi(sigma + i*tau))
  <= load(T) + sphereBound(top,sigma) / radius

norm(xi'/xi(sigma - i*tau))
  <= load(T) + sphereBound(bottom,sigma) / radius.
```

These statements use the concrete quotient and its concrete TS279
logarithm.

## Quantitative boundary

The following rates remain open:

* a closed lower bound for `strongHeightDelta`;
* a closed upper bound for `strongHeightLoadEnvelope`;
* a Borel-Caratheodory or equivalent upper bound for the logarithm sphere
  supremum using the TS289 xi growth estimate;
* a fixed-radius localization independent of the minimum gap;
* convergence of the complete horizontal envelope divided by `T^2`.

Consequently TS296 is a concrete existence and exact-factorization sprint,
not yet the requested `O(T * log(T+2)^2)` horizontal estimate.

## Non-claims

TS296 does not prove:

* the passage from `xi'/xi` to `-zeta'/zeta`;
* the left-boundary estimate;
* the right-line cutoff estimate;
* completeness of the exceptional residue inventory;
* Perron inversion;
* the meromorphic rectangle residue theorem;
* an infinite explicit formula;
* Gallagher, OTSA, or Goldbach.

## Verification

Canonical build target:

```powershell
lake build TS.Goldbach.Strong.TS296.ConcreteStrongHeightXiQuotientLog
```

Static checks:

```powershell
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS296
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS296
git diff --check
```

Expected result: the build succeeds and all static scans print no matches.
