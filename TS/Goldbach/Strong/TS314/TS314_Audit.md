# TS314 Audit: Finite Quadratic Spectral Moment and Good-Scale Selection

## Scope

TS314 is the structural finite-variance bridge between the pointwise TS313
spectral interface and the future discrete zero-correlation analysis. It
defines the natural half-open dyadic window, preserves the complex truncated
trace, forms its finite quadratic mean, proves good-scale selection, and
transfers the effective TS292 tail to a rational TS313 output.

Main file:

```text
TS/Goldbach/Strong/TS314/FiniteQuadraticSpectralMomentGoodScale.lean
```

No quadratic-moment estimate, zero-pair correlation estimate, RH input, or
trace budget is introduced.

## Dyadic window

The window is exactly

```text
Finset.Ico X (2 * X).
```

TS314 proves:

```text
card (dyadicWindow X) = X
0 < X -> dyadicWindow X is nonempty
x in dyadicWindow X -> 1 <= x
```

The half-open convention avoids sharing the endpoint `2 * X` with the next
dyadic window and gives the exact denominator `X` in the quadratic average.

## Complex trace and quadratic moment

The truncated value remains complex:

```text
(canonicalTraceNormalizationFactor x : Complex) *
  truncatedInfiniteZeroContribution x T.
```

Only its norm is squared in `finiteQuadraticSpectralMoment`. This preserves
the phases that TS315 must expose when it expands the square as a double sum
over pairs of zeros. The theorem
`finiteQuadraticSpectralMoment_eq_sum_div_scale` rewrites the denominator
definitionally to `(X : Real)` for that expansion. The moment is also proved
nonnegative for every `X` and `T`.

## Good-scale selection

The generic finite theorem proves that a nonempty quadratic average bounded
by `q^2`, with `q >= 0`, contains an entry at most `q`. Its dyadic
specialization yields:

```text
finiteQuadraticSpectralMoment X T <= q^2 ->
  exists x in dyadicWindow X,
    normalizedTruncatedSpectralSize x T <= q.
```

No square root is introduced.

## Effective tail transfer

TS292 proves

```text
norm (Z_infinite(x) - Z_T(x)) <=
  max 1 x * C_tail * logarithmicTailRate T.
```

For every positive scale, multiplication by the canonical factor `2 / x`
cancels `max 1 x = x`. TS314 therefore obtains the scale-independent envelope

```text
2 * C_tail * logarithmicTailRate T.
```

The reverse triangle inequality then controls the absolute difference between
the normalized infinite and truncated sizes. Combining this result with the
good-scale theorem gives both:

* a real pointwise bound `qMoment + qTail`;
* a rational `NormalizedSpectralTraceBoundStatement` with majorant
  `qMoment + tailMajorant`.

The rational tail certificate remains an input. Its construction belongs to
TS316. The real tail envelope itself is proved nonnegative for every natural
height.

## TS315-facing boundary

The exact open analytic statement is:

```text
FiniteQuadraticSpectralMomentBoundStatement X T q
```

The data package also records

```text
4 * T <= X
```

so a future discrete oscillatory estimate cannot silently enter an aliased
height-frequency regime. TS315 must preserve the actual multiplicity and
Mellin-kernel weights when it expands the moment. A bare unweighted count of
near ordinate pairs is not claimed to suffice.

## Fail-closed boundary

TS314 does not prove:

* the finite quadratic moment estimate;
* a Kusmin-Landau or van der Corput discrete exponential-sum bound;
* the weighted close-pair zero-correlation estimate;
* a concrete rational spectral majorant;
* a value of `TS313.NormalizedTraceBudgetData`;
* a trace budget at most one half;
* RH, OTSA, or Goldbach.

## Verification commands

```powershell
lake env lean TS\Goldbach\Strong\TS314\FiniteQuadraticSpectralMomentGoodScale.lean
lake build TS.Goldbach.Strong.TS314.FiniteQuadraticSpectralMomentGoodScale
lake build
rg -n "s[o]rry|a[x]iom|o[p]aque|a[d]mit|[^\x00-\x7F]" TS\Goldbach\Strong\TS314
git diff --check
git status --short
```

The source and audit are intended to remain strict ASCII and contain no
placeholder declaration.

Verified build results:

```text
Targeted build: 3035/3035
Global build:   2664/2664
```
