# Q390 / RS18H report

## Verdict

```text
Q390_CANONICAL_ENDPOINT_PARAMETER_BINDING_PASS
Q390_CANONICAL_CENTRAL_REGIME_PASS
Q390_EXPLICIT_RATIONAL_COSINE_BOUND_PASS
Q390_ARIAS_NUMERICAL_ENVELOPE_PASS
Q390_CANONICAL_HARDY_DECOMPOSITION_PASS
Q390_CONDITIONAL_ENDPOINT_CHECKER_PASS

Q390_EXPLICIT_RATIONAL_SOURCE_GAP_NOT_OBTAINED
Q390_SHARP_CLOSED_BOUND_RATIONAL_DOMINATION_NOT_OBTAINED
Q390_SOURCE_REMAINDER_TO_ARIAS_TRANSPORT_NOT_OBTAINED
Q390_FINITE_PART_ATOM_CERTIFICATES_NOT_OBTAINED
Q390_EXACT_FINITE_PART_REPLAY_NOT_OBTAINED
Q390_CONCRETE_RS_CERTIFICATE_NOT_OBTAINED
Q390_CANONICAL_ENDPOINT_NOT_OBTAINED
Q390_CARRIER_MEMBERSHIP_NOT_OBTAINED
BRIDGE_A_OPEN

Q390_ANALYTIC_PARTIAL_FAIL_CLOSED
```

Q390 closes the exact endpoint geometry and the arithmetic half of the Arias
route. It does not close the analytic Arias remainder theorem or certify the
finite Riemann--Siegel atoms. Consequently no concrete endpoint, carrier
membership, or Bridge A closure is claimed.

## Exact endpoint data

The requested endpoint is retained:

```text
t0  = 751937898017 / 1073741824
K   = 63
ell = 10
```

Lean proves:

```lean
Q361Probe.rsN requestedEndpoint = 10
```

It also constructs the canonical `xi`, `q`, `theta`, `phi`, and a genuine
central `OuterContourRegime`. The stronger checked coordinate bound is:

```lean
|requestedQ.re - requestedQ.im| <= 1 / 8
```

The endpoint is therefore not imported from the Q360 external census.

## Explicit cosine witness

The existing Q370 witness with `M = 3/2` requires the narrower strip
`|q.re - q.im| <= 1/16`, which is false at the requested endpoint. Q390 proves
a new general theorem on the wider `1/8` strip and constructs:

```lean
requestedCosineBound : OuterCosineLowerBound requestedQ 0
requestedCosineBound.M = 1
```

This is an unconditional rational witness. It is weaker than the proposed
`3/2`, but it is actually justified by Lean.

## Exact Hardy decomposition

Every hypothesis of the Q389 critical-line theorem is discharged at the
requested endpoint. Lean proves the exact identity:

```lean
normalizedHardyZ t0 =
  sourceNormalizedRSFinitePart t0 63 10 requestedXi requestedQ +
  sourceNormalizedRSRemainderContribution
    t0 63 10 requestedXi requestedQ requestedCentralRegime
      (canonicalPhi t0)
```

This result is unconditional and binds the requested endpoint to the true
Q343 target. It is not a numerical enclosure.

## Arias arithmetic

Lean proves, using rational inequalities, elementary pi bounds, powers, and
the exact factorial:

```lean
Q361Probe.explicitAriasBound requestedEndpoint 63 <=
  1 / 100000000000000
```

This closes only the numerical half of Route B. No theorem in Q361--Q389
relates the independently defined `sourceRSRemainder` to this abstract 2011
envelope.

Q390 names the exact first missing theorem:

```lean
def RequestedAriasRemainderTransport : Prop :=
  |sourceNormalizedRSRemainderContribution ...| <=
    explicitAriasBound requestedEndpoint 63
```

The derived theorem `requested_normalized_remainder_le_target` is explicitly
conditional on that proposition.

## Q375 route diagnostic

`Q390Generator/bound_audit.py` mirrors the current Lean definition of
`Q375Probe.sourceSharpClosedIntegralBound`. Its output is diagnostic only.

At the requested endpoint, with the proposed constants and `K = 63`:

```text
gap.a = 3/8, cosine M = 3/2
transported Q375 radius ~= 1.0325657087e-4
target radius             = 1e-14
```

With the proved `M = 1`, optimizing `K` over `1..99` gives approximately:

```text
best K                     = 32
best transported radius    = 4.8420797883e-7
Q360 signed margin         = 1.8885503676e-13
radius / margin            = 2.5639135e6
```

Thus the mandated Q375 inequality is numerically false for the current bound;
it is not merely difficult to formalize. The discrepancy comes from the very
coarse Gaussian-moment and inner-angle factors in Q375, not rational rounding.

A ledger scan under `gap.a = 3/8`, `M = 1`, the checked `1/8` central strip,
and `K = 1..99` found seven individually promising endpoints but no complete
bracket. Changing the endpoint therefore cannot close Bridge A through the
current Q375 bound.

The Q360 census reports `best_K = 55` for the requested endpoint. The mandated
`K = 63` is retained only for the Q368 stress target and the formal Arias
arithmetic theorem.

## Conditional checker closure

`requestedEndpoint_mem_of_checked_finite` proves that the following inputs are
sufficient, with no further hidden premise:

1. `RequestedAriasRemainderTransport`;
2. checked interval membership for every true finite-part atom;
3. a successful Q368 certificate replay;
4. equality of the replayed value with the exact Q384 finite part;
5. a certificate radius at least `1e-14`.

The first input is the immediate analytic leaf. The finite-atom certificate is
the next independent production leaf. Neither is inhabited by Q390.

## Checks

```text
Direct Lean sources          : PASS 7/7
lake build Q390Probe         : PASS 3397/3397
aggregate Q374Probe-Q390Probe: PASS 3432/3432
Axioms                       : propext, Classical.choice, Quot.sound
Forbidden scan               : EMPTY
Development freeze           : 2026-09-04T19:58:31.5230430+02:00
Absolute deadline            : 2026-09-04T23:17:20.2086009+02:00
Timebox                      : PASS
HEAD = origin/main           : 433e29e
Permanent Git operations     : NONE
```

One preliminary direct compilation of `Q390Probe.lean` was attempted before
Lake had emitted the new dependency `.olean`; it failed only for that missing
object. After `lake build Q390Probe`, the same direct compilation passed.

## Frontier

```text
Q390_REQUESTED_ENDPOINT_GEOMETRY        : CLOSED
Q390_ARIAS_ARITHMETIC_ENVELOPE          : CLOSED
Q390_SOURCE_REMAINDER_TO_ARIAS_TRANSPORT: OPEN
Q390_FINITE_ATOM_BINDING                : OPEN
Q390_CANONICAL_ENDPOINT                 : NOT_OBTAINED
Q390_CARRIER_MEMBERSHIP                 : UNPROVED
BRIDGE_A                                : OPEN
TS340_UNCONDITIONAL                     : OPEN_FROZEN
Q391                                    : NOT_AUTHORIZED
```

