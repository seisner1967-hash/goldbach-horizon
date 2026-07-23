# TS300 Audit - Centered Borel-Caratheodory and Closed Load Decay

## Scope

TS300 closes two independent pieces of the horizontal Perron analysis.

First, it backports the local Borel-Caratheodory estimate needed by the
finite-quotient route. The proof uses only the Schwarz lemma available in the
locked Mathlib revision. Second, it routes the explicit TS299 reciprocal-load
envelope through the horizontal power and Mellin-kernel factors and proves
that the resulting fixed-scale integrated component tends to zero.

The quotient minimum-modulus problem is not hidden in either result.

## Schwarz-transform backport

For a differentiable function on `ball 0 R`, vanishing at zero and satisfying
the strict real-part bound

```text
Re(f(z)) < M,
```

TS300 applies the locked Schwarz lemma to

```text
w(z) = f(z) / (2*M - f(z)).
```

The real-part inequality implies `norm(f(z)) < norm(2*M-f(z))`, so the
transform maps into the open unit ball required by the locked API. Inverting
the transform gives

```text
norm(f(z)) <= 2*M*norm(z)/(R-norm(z)).
```

The strict formulation is sufficient for later use: any non-strict envelope
can be enlarged by a positive slack constant.

## Centered logarithm

The definition

```text
centeredLogarithm L c z = L(z) - L(c)
```

has three proved properties:

- it vanishes at `c`;
- adding a global branch constant leaves it unchanged;
- its derivative at `c` equals the derivative of `L`.

`CenteredLogRealPartEnvelopeData` records the genuine remaining input

```text
Re(L(z)-L(c)) < M
```

on the original logarithm ball. Borel-Caratheodory on the half-radius sphere,
followed by the locked Cauchy estimate used in TS295, proves

```text
norm(g'(c)/g(c)) <= 4*M/R.
```

This estimate is branch-independent. It does not infer a quantitative lower
bound for `norm(g(c))` from nonvanishing.

## Closed reciprocal-load decay

Let `C` be the TS290 global log-linear counting constant. TS300 opens the
nested logarithm in the TS299 load envelope using

```text
A(T) <= C*(T+4)^2,
log(4*(A(T)+1)) <= log(4*(C+1)) + 2*log(T+4).
```

It obtains the transparent majorant

```text
finiteGridClosedLoadEnvelope(T)/T^2
  <= 48*C*log(T+4)*(1+K+2*log(T+4))/T,
K = log(4*(C+1)).
```

The locked theorem `Real.tendsto_pow_log_div_mul_add_atTop` for powers one and
two then proves

```text
finiteGridClosedLoadEnvelope(T)/T^2 -> 0.
```

No local zero-density estimate is introduced.

## Horizontal routing

At the quantitative grid height `finiteGridStrongTau T`, TS300 proves on both
horizontal sides:

```text
norm(x^s) <= max(1,x^2),
norm(1/(s*(s+1))) <= 1/tau^2 <= 1/T^2.
```

Combining these inequalities with the exact TS299 reciprocal-load bound gives
a pointwise majorant. Multiplication by the exact rectangle width `7/2`
produces `finiteGridHorizontalZeroLoadComponent x T`, and for every fixed
arithmetic scale `x`:

```text
finiteGridHorizontalZeroLoadComponent x T -> 0.
```

This is a fixed-`x`, spectral-height limit. No diagonal claim `x=T` is made.

## Exact quotient frontier

`FiniteGridCenteredXiQuotientLogData` names the exact missing data at the new
TS299 grid height. It is tied to the concrete TS296 quotient `xi/P_T` and
carries top and bottom local logarithms together with centered real-part
envelopes. Given this data, the top and bottom quotient logarithmic derivative
bounds follow immediately from the centered theorem.

The named proposition

```text
FiniteGridCenteredXiQuotientRealPartEnvelopeStatement
```

is not proved. Growth of xi and zero separation only give an upper bound for
`log|g(z)|`; they do not control `-log|g(c)|`. A quantitative minimum-modulus
or equivalent normalization argument remains necessary.

## Open frontier

The following remain intentionally unproved:

- the centered real-part envelope for the concrete finite-grid xi quotient;
- a quantitative minimum-modulus estimate for that quotient;
- the completion-correction rate;
- decay of the complete horizontal contour contribution;
- the fixed-left boundary estimate;
- completeness and evaluation of exceptional residues;
- Perron inversion and the meromorphic rectangle residue theorem;
- an infinite explicit formula;
- Gallagher, OTSA, or Goldbach.

## Verification

- Target build: `3000/3000`.
- Global build: `2664/2664`.
- No unchecked declaration placeholders in TS300.
- Source and audit are ASCII-only.
- Git whitespace validation is clean.
