# TS292 Audit - Effective Infinite Zero-Tail Convergence

## Scope

TS292 separates the arithmetic scale `x` from the spectral truncation height
`T`.  It uses the unconditional TS290 log-linear zero count to pass from the
finite TS291 contribution to an absolutely convergent series over all
concrete nontrivial zeta zeros.

No infinite-convergence hypothesis is introduced.

## Uniform finite tail

For `1 <= T`, the module studies the exact unit shells

```text
(T + n, T + n + 1].
```

The TS271 finite Abel identity is combined with the decreasing potential

```text
P(t) = (log(t + 3) + 2) / t.
```

Its finite differences absorb the logarithmic count and reciprocal-square
weight.  This gives the upper-cutoff-independent estimate

```text
sum_{T < abs(Im rho) <= U}
  multiplicity(rho) / abs(rho * (rho + 1))
    <= 15 * xiGlobalLogLinearConstant
         * (log(T + 2) + 1) / T.
```

The proof is finite.  It uses neither Stieltjes integration nor the divergent
integral of `log(t + 2) / t`.

## Absolute convergence

The global index type is the subtype of concrete nontrivial zeta zeros.
Exact height truncations are pulled back from TS265 with `Finset.preimage`.

Every finite subset of the tail above `T` is inserted into one exact shell
`(T,U]`.  The uniform finite-sum criterion then proves summability of the
tail norms.  The finitely many zeros below height one are added separately.
Consequently, for every natural arithmetic scale `x`,

```text
Summable (fun rho => norm (infiniteZeroSpectralTerm x rho))
```

and hence the complex zero series has a canonical `HasSum`.

## Infinite contribution and effective remainder

TS292 defines

```text
infiniteZeroContribution x
truncatedInfiniteZeroContribution x T
infiniteZeroContributionTail x T.
```

The exact decomposition is

```text
truncatedInfiniteZeroContribution x T
  + infiniteZeroContributionTail x T
    = infiniteZeroContribution x.
```

For `1 <= T`, the effective remainder satisfies

```text
norm (infiniteZeroContribution x
    - truncatedInfiniteZeroContribution x T)
  <= max(1,x) * infiniteZeroResidualTailConstant
       * (log(T + 2) + 1) / T,
```

where

```text
infiniteZeroResidualTailConstant =
  15 * xiGlobalLogLinearConstant.
```

The truncation finsets exhaust the global zero type, so the finite
contributions converge to the infinite contribution and form a Cauchy
sequence.  The tail tends to zero.  On the diagonal `x = T`, the new
two-parameter truncation is exactly the historical TS257 finite sum.

## Non-claims

TS292 does not prove a von Mangoldt identity, a truncated or infinite
explicit formula, a contour residual estimate, Gallagher, an OTSA bridge, or
Goldbach.

The intended next separation is:

```text
TS293: truncated explicit identity and contour residual
TS294: passage to the assembled infinite explicit formula.
```

## Verification

Canonical build target:

```powershell
lake build TS.Goldbach.Strong.TS292.EffectiveInfiniteZeroTailConvergence
```

Static checks:

```powershell
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS292
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS292
git diff --check
```

Expected result: the build succeeds and all static scans print no matches.
