# TS297 Audit - Xi/Zeta Horizontal Perron Bridge

## Scope

TS297 closes the exact structural bridge from the finite xi quotient of
TS296 to the horizontal Perron integrand of TS293. It deliberately does not
attempt the asymptotic estimates needed to integrate those pointwise bounds.

The chosen order is fail-closed: stabilize and test the exact truncated
identity first, then prove rates for its already named terms.

## Results proved

### Off-real completion factor

The TS282 bridge now proves that the reciprocal archimedean Gamma factor is
nonzero whenever `s.im != 0`. Consequently the TS290 local multiplier is
differentiable and nonzero at every nonreal point.

### Exact xi/zeta logarithmic derivative identity

On a neighborhood of every nonreal point, TS297 proves

```text
xi = xiZetaLocalMultiplier * riemannZeta.
```

Differentiating that neighborhood equality gives the exact formula

```text
-zeta'/zeta = completionCorrection - xi'/xi,
```

where `completionCorrection` is the logarithmic derivative of the explicit
TS290 multiplier. No anonymous remainder is introduced.

### Exact finite quotient reinsertion

At both TS296 strong-height horizontal centers, the concrete TS296 identity

```text
xi'/xi = finiteZeroLogDerivativeSum + g_T'/g_T
```

is substituted into the completion formula. The resulting top and bottom
identities contain exactly:

1. the explicit completion correction;
2. the finite rational zero sum indexed by `nearbyConcreteZeros T`;
3. the logarithmic derivative of the concrete quotient `heightXiQuotient`.

The same finite zero selection and quotient used by TS296 are preserved.

### Horizontal pointwise bounds

The TS295 reciprocal-load bound and the TS296 local logarithm Cauchy bound
give explicit pointwise envelopes for `|-zeta'/zeta|` on both horizontal
centers. TS297 then rewrites the concrete TS293 Perron integrand and proves
its pointwise norm bound, including the exact factors `|x^s|` and the
triangle-spline Mellin kernel.

## Dependency hygiene

The proof uses only finite products, neighborhood differentiation, the
concrete TS296 quotient, and the local TS279 logarithm already instantiated
there. It does not use an infinite Hadamard product or a tautologically
defined error term.

## Open quantitative frontier

The following statements remain intentionally unproved:

- a closed rate for the reciprocal zero load;
- an effective rate for the local logarithm sphere supremum;
- a closed rate for the completion correction;
- an integrated horizontal-side estimate;
- the left-boundary and right-cutoff estimates;
- completeness of the exceptional residue inventory;
- Perron inversion and the meromorphic rectangle residue theorem;
- an infinite explicit formula;
- Gallagher, OTSA, or Goldbach.

In particular, TS297 does not claim that the horizontal envelope divided by
`T^2` tends to zero. It exposes the exact three terms whose rates must be
proved next.

## Verification

- Target build: `2991/2991`.
- No unchecked placeholder declarations in TS297.
- TS297 source and audit are ASCII-only.
- The only TS282 edit is the off-real nonvanishing lemma in the existing
  intentional Unicode API bridge.
