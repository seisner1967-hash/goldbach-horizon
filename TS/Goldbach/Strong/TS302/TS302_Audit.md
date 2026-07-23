# TS302 Audit - Finite Macroscopic Correction Decay

## Scope

TS302 closes the finite spectral correction introduced by the exact TS301
bridge.  It does not estimate the anchored macroscopic logarithm.  Its only
analytic input is the unconditional TS290 dyadic multiplicity count.

## Exact finite family

The nearby concrete zeros are mapped to their complex values in
`heightZeroValues`.  TS302 proves:

```text
heightZeroValues(T) subset xiMacroscopicSpec(T).factorZeros.
```

The proof uses the exact height truncation, the critical-strip norm bound,
and the very large macroscopic inner radius `64*(T+4)`.  It also proves that
the TS295 concrete multiplicity is exactly the TS284 xi multiplicity used by
the macroscopic factorization.

The extra family is the explicit finite difference

```text
xiMacroscopicExtraZeros(T)
  = macroFactorZeros(T) \ heightZeroValues(T).
```

Consequently the TS301 correction is no longer merely a difference of two
sums:

```text
xiMacroscopicHeightFiniteCorrection(T,s)
  = sum rho in xiMacroscopicExtraZeros(T), m(rho)/(s-rho).
```

## Geometric denominator bound

Every extra macroscopic zero is an xi zero and therefore a concrete
nontrivial zeta zero.  If its ordinate had absolute value at most `T+2`, it
would belong to `heightZeroValues(T)`, contradicting the `sdiff` membership.
Thus

```text
T + 2 < abs(Im rho).
```

The TS299 height satisfies `T < tau_T < T+1`.  Hence the symmetric vertical
gap is greater than one.  The TS295 top and bottom norm inequalities then
give

```text
1 < norm(sigma +/- i*tau_T - rho)
```

on both horizontal sides.  Each rational term is therefore bounded by its
multiplicity, with no local zero-density estimate.

## Closed multiplicity envelope

The total macroscopic factor multiplicity is injected into a second TS290
dyadic disk of radius

```text
4 * 64*(T+4) = 256*(T+4).
```

The analytic radius of the original dyadic geometry is strictly below this
second radius.  The unconditional TS290 theorem then yields the closed bound

```text
count(T) <= C_dyadic * 256*(T+4) * log(256*(T+4)+2).
```

This quantity is `xiMacroscopicCorrectionCountEnvelope`.

## Normalized decay

TS302 proves the elementary logarithmic comparison

```text
log(256*(T+4)+2) <= log(258) + log(T+4)
```

and constructs the transparent decay envelope

```text
1280*C_dyadic * (log(258)+log(T+4))/T.
```

It follows that

```text
xiMacroscopicCorrectionCountEnvelope(T) / T^2 -> 0.
```

After multiplication by the fixed arithmetic scale, the quadratic Mellin
kernel, and the exact horizontal width `7/2`, the integrated correction
component also tends to zero for every fixed `x`.

## TS301 bridge routing

The top and bottom bridge identities are consumed directly.  TS302 proves
that the norm of

```text
heightQuotientLogDeriv - macroscopicQuotientLogDeriv
```

is bounded by the closed correction envelope.  The sign remains the TS301
positive sign:

```text
g_height'/g_height
  = Q_macro'/Q_macro + finiteCorrection.
```

## Logical hygiene

The proof uses none of the following:

- RH or a critical-line assertion;
- a local zero-density estimate;
- an infinite Hadamard product;
- a moving-center minimum-modulus estimate;
- a closed rate for the anchored macroscopic logarithm.

## Open frontier

The following remain intentionally unproved:

- a closed rate for the TS301 anchored real-part envelope;
- the completion-correction rate;
- decay of the complete horizontal contribution;
- the fixed-left boundary estimate;
- completeness and evaluation of exceptional residues;
- Perron inversion and the meromorphic rectangle residue theorem;
- an infinite explicit formula;
- Gallagher, OTSA, or Goldbach.

The natural next target is the closed anchored macroscopic envelope.  TS302
has removed the independent finite spectral correction from that problem.

## Verification

- Direct Lean compilation passes with warnings treated as errors.
- Target build passes: `3002/3002`.
- Global build passes: `2664/2664`.
- Source and audit are ASCII-only.
- No unchecked declaration placeholders occur in TS302.
