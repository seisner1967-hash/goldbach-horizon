# Q391 / RS19H: Unconditional Requested Remainder Transport

## Verdict

Q391_REQUESTED_ARIAS_REMAINDER_TRANSPORT_PASS

The exact requested target is inhabited with no arguments or residual
semantic premise:

```lean
theorem Q391Probe.requestedAriasRemainderTransport :
    Q390Probe.RequestedAriasRemainderTransport
```

This is a specialized direct bound for the independent 2024 source
remainder. It is not a proof of equality of the generic 2011 and 2024
remainders and does not assert the generic Arias theorem.

Fixed parameters: t = 751937898017/1073741824, K = 63, ell = 10.
No finite atom certificate, new endpoint, or Q392 work was started.

## PROVEN_IN_LEAN

The completed proof follows this chain:

1. Q379 identifies the independent sourceRgK with the primary Taylor
   difference at every point of the actual final line, including zero.
2. Taylor-Cauchy cancellation gives the order-64 central bound. Its
   integral on [-17/2,17/2] is at most 1.5e-30.
3. The finite polynomial has an exponential tail envelope. The analytic
   part is bounded by exp(-x^2) up to abs x = 21/2 and by
   exp(-(49/80)*x^2) beyond it. The latter follows from the proved moving
   ray harmonic gap 25/64 and the rational lower bound on pi.
4. The three symmetric tail envelopes are integrable and have exact
   integrals. Their sum is at most 1e-30. The exponential comparison uses
   only the finite Taylor inequality exp(1) >= 163/60 and exp(d) >= 1+d.
5. The full source integrand is explicitly proved integrable and equal
   to the existing primary analytic difference. Its complete integral
   has norm at most 1/400000000000000000000000000000 = 2.5e-30.
6. The exact Q380 transform prefactor has norm at most 1/2. This uses
   the canonical saddle geometry, principal power, and Gaussian factor;
   no sampled prefactor or phase is substituted.
7. Q384's Hardy normalization therefore gives the same bound 2.5e-30
   on the actual normalized source contribution.
8. The Q361 numerical envelope is at least 2.5e-30 at the fixed endpoint.
   The proof uses ariasBase >= 13/125 and inverse sqrt(rsA) >= 1/4,
   followed by exact rational arithmetic with 31! and power 64.
9. The unconditional Q390 target follows. Its existing numerical upper
   bound then gives the requested normalized radius at most 1e-14.

Terminal declarations are in Q391Probe/RequestedTransportClosure.lean.
Full source integration is in RequestedFullIntegral.lean; normalization
and envelope comparison are in RequestedPrefactorBound.lean and
RequestedAriasLowerBound.lean.

## Trust and Anticircularity

The remainder is never defined by subtracting a finite Hardy expression.
The proof consumes the independently defined Q366 integral and the closed
Q379 representation theorem. Integrability is proved separately, not
inferred from a totalized integral value.

The dependency audit traverses actual proof and type constants, rejects
Q386-Q388, Q392, SourceAuxiliaryThetaSeed, and AriasRawBoundWitness, and
checks that the terminal theorem has exactly the Q390 conclusion with no
binders and no open proof variables. RequestedAriasRemainderTransport
occurs as the conclusion type, not as a premise. The earlier conditional
transport helper is applied to a constructed norm-bound proof.

Final replay: 27/27 direct sources PASS, Q391 aggregate PASS, and the
Q374-Q391 aggregate PASS. All 87 audited theorem declarations use only
propext, Classical.choice, and Quot.sound. The dependency audit reports
REJECTED_CONSTANTS: [] and EXACT_Q390_TARGET / NO_BINDERS. The production
forbidden-token scan is EMPTY. No Lean/Lake process remains. Full counts
and signatures are recorded in Q391_BUILD_SUMMARY.txt and Q391_AXIOM_AUDIT.txt.

## NOT_OBTAINED / NOT_ATTEMPTED

- Generic equality of 2011 and 2024 remainders: NOT_OBTAINED, not required
  by this permitted stronger specialized route.
- Generic Arias remainder theorem for arbitrary endpoints: NOT_OBTAINED.
- Q390 finite-part atom certificates: FIRST_OPEN_LEAF.
- Q392: NOT_STARTED.
- CARRIER_MEMBERSHIP: UNPROVED.
- BRIDGE_A: OPEN_AT_FINITE_ATOMS; no global bridge closure claimed.
- TS340_UNCONDITIONAL: OPEN_FROZEN.

## EXTERNAL_DIAGNOSTIC

The retained Python diagnostic is non-probative. No numerical output,
midpoint approximation, or finite-part certificate is used in the proof.
Failed external primary-PDF retrievals are not mathematical evidence.
The normalization audit is based on the retained canonical source objects.

## Governance and Reproduction

The original four-hour timebox remains OVERRUN. This closure is classified
POST_DEADLINE_USER_AUTHORIZED. The proof-development freeze for this
closure was recorded at 2026-09-06T07:20:41.0845091+02:00, after the terminal
direct build succeeded. The original Q391_T0.json is unchanged.

The partial archive of 2026-09-05 and its external attestation remain
unchanged. The closure is packaged separately, with a fresh manifest and
ZIP round-trip check. Q391_REPORT.md describes the prior partial snapshot;
this closure report supersedes its frontier without rewriting that archive.

Replay requires the canonical historical Q343-Q390 sources, Lean 4.15.0,
and Mathlib 9837ca9d65d9de6fad1ef4381750ca688774e608. The source/evidence
archive does not include the multi-gigabyte historical .olean cache.
HEAD and origin/main remain 433e29eff1d9da2bc5937bb82bf5df3a2d59c08f.
No commit, push, branch change, tag, or destructive operation is performed;
historical local changes are preserved.
