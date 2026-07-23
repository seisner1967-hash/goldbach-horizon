# TS304 Audit - Closed Completion Correction and Horizontal Decay

## Scope

TS304 closes the archimedean completion correction from TS297 and combines it
with the three independent horizontal components closed in TS300--TS303.  The
result is an unconditional decay theorem for the complete top and bottom
Perron integrals along the quantitative finite-grid heights of TS299, for each
fixed arithmetic scale.

## Gamma bounds without complex Stirling

The proof deliberately avoids a complex Stirling or digamma estimate.

For real part in `[1/8,3]`, Euler's Gamma integral gives

```text
norm Gamma(z) <= Gamma(re z) <= gammaCompactBound.
```

The functional equation moves `Gamma(s/2)` into that compact strip.  The
reflection identity then supplies the complementary lower bound

```text
norm Gamma(s/2)
  >= pi / (2*gammaCompactBound*exp(pi*abs(im s)/2)).
```

Together with elementary complex-power and polynomial bounds, these estimates
give explicit upper bounds for the completion multiplier on a fixed local
ball and a positive lower bound at its center.

## Centered completion logarithm

The multiplier is analytic and nonzero off the real axis.  TS304 applies the
TS278 primitive construction to its logarithmic derivative and normalizes the
primitive at the center.  The exponential of this centered logarithm is the
exact multiplier ratio.

The value-ratio estimate is converted into the closed real-part envelope

```text
completionClosedRealPartEnvelope(T)
  = completionClosedEnvelopeConstant*(T+4).
```

TS300 Borel-Caratheodory and the local Cauchy estimate then yield

```text
norm completionCorrection(sigma +/- i*tau_T)
  <= completionClosedLogDerivativeEnvelope(T),
```

uniformly for `sigma` in `[-3/2,2]`.  This envelope is linear in `T`, and its
quotient by `T^2` tends to zero.

## Exact four-term assembly

At the TS299 finite-grid height, TS304 proves the exact finite decomposition
before applying any norm estimate:

```text
-zeta'/zeta
  = completionCorrection
    - finiteNearbyZeroSum
    - macroscopicQuotientLogDerivative
    - finiteMacroscopicCorrection.
```

The four terms are bounded independently by:

- TS304: completion correction;
- TS299--TS300: reciprocal zero load;
- TS303: anchored macroscopic quotient;
- TS302: finite macroscopic correction.

Their sum is `finiteGridClosedHorizontalLogDerivativeEnvelope(T)`, and its
quotient by `T^2` tends to zero.

## Complete Perron-side decay

The power factor is bounded by `rightLineScale(x)`, the spline Mellin kernel by
`1/tau_T^2`, and `tau_T >= T`.  Integration over the exact width `7/2` gives

```text
norm topIntegral(x,T)    <= finiteGridCompleteHorizontalComponent(x,T),
norm bottomIntegral(x,T) <= finiteGridCompleteHorizontalComponent(x,T).
```

For each fixed `x`, the common component tends to zero.  The canonical shifted
sequence `T+1` removes dependent positivity proofs and yields direct Tendsto
theorems for both integrals and their oriented difference.

## Logical hygiene

The proof does not use:

- complex Stirling;
- an asymptotic digamma estimate;
- RH or a critical-line assertion;
- a moving minimum-modulus estimate;
- an infinite Hadamard product;
- a local zero-density estimate.

## Open frontier

The following remain intentionally unproved:

- the fixed-left boundary estimate;
- completeness and evaluation of exceptional residues;
- Perron inversion;
- the meromorphic rectangle residue theorem;
- passage to an infinite explicit formula;
- Gallagher, OTSA, or Goldbach.

The natural next target is the fixed-left side.  The right cutoff and both
horizontal sides now have unconditional fixed-scale decay.

## Verification

- Direct Lean compilation passes.
- The audit is ASCII-only.
- No unchecked declaration placeholders occur in TS304.
