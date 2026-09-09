# Q391 / RS19H Continuation Report

## Verdict

Q391_ANALYTIC_PARTIAL_FAIL_CLOSED

RequestedAriasRemainderTransport remains UNINHABITED. Bridge A remains OPEN.
This continuation produces genuine central and tail estimates, not a
production endpoint certificate. Q392 has not been started.

The original four-hour timebox is OVERRUN. The later work is classified
POST_DEADLINE_USER_AUTHORIZED, following the repeated explicit continuation
messages. Q391_T0.json retains the original launch and deadline unchanged.

## PROVEN_IN_LEAN

1. Coefficient conventions sigma=0 and sigma=1/2 are different; the 2024
   source finite correction is bound to the sigma=0 row by the retained
   Q384 theorem. No equality of the two raw remainders is inferred.
2. The independently defined source remainder equals the primary finite
   Taylor remainder through the already closed Q379 identity.
3. An adaptive Cauchy circle provides an explicit geometric remainder
   estimate retaining the Taylor factor of order 64.
4. At the exact Q390 endpoint, the true source integrand integrated over
   [-17/2,17/2] has norm at most 3/2000000000000000000000000000000, or 1.5e-30.
5. The primary finite polynomial satisfies an all-order Cauchy estimate
   even outside the evaluation disc. Its outer tails have an explicit
   exponential envelope, exported as requested_polynomial_tail_envelope.
6. The analytic primary term has a Gaussian bound for abs x <= 21/2.
7. A new exact representation sourceH = 1/2 + integral_0^1 t/(1-tw) is
   proved with the principal-branch condition explicit.
8. On the vertical double cone, Re sourceHZeroExtended >= 25/64. The
   actual canonical moving ray lies in this cone. Consequently its
   analytic outer integrand has a global Gaussian majorant
   exp(-(25*pi/128)*x^2).

The Cauchy cancellation is used before taking norms. No bound is deduced
from an external numerical Hardy value. The central number 1.5e-30 is a
bound on a restricted source integral only, not on the normalized full
remainder and not on explicitAriasBound itself.

## CONDITIONAL

requestedAriasRemainderTransport_of_source_norm_bound and
requested_remainder_le_one_e_minus_fourteen_of_source_norm_bound retain
the explicit hypothesis on 2*norm(prefactor)*norm(source remainder).
They are interfaces, not inhabitants of the terminal proposition.

## First Open Leaf

Q391_PIECEWISE_TAIL_INTEGRALS_AND_FULL_SOURCE_ASSEMBLY_NOT_OBTAINED

The pointwise ingredients are compiled, but the tail integrals have not
yet been combined with the central estimate into a sufficiently small
whole-line source radius. The exact normalization-prefactor inequality
and comparison with Q361's Arias envelope must follow that assembly.

The separate 2011/2024 generic compatibility route also remains unproved.
The new direct route is permitted by the mandate and does not require
claiming such compatibility.

## EXTERNAL_DIAGNOSTIC

Q391Research/source_remainder_diagnostic.json records a 16384-bit diagnostic
using exact dyadic midpoint inputs for the finite expression. Its observed
difference is not a certified enclosure of the canonical source remainder.
It cannot supply a Lean certificate or close a sign leaf. Failed primary
PDF downloads are excluded from the proof evidence.

## Verification

Final replay: 20/20 direct sources PASS; Q391 and Q374-Q391 aggregates PASS.
The axiom audit covers 55 theorem declarations and finds only propext,
Classical.choice and Quot.sound. Rejected transitive dependencies: none.
Forbidden production tokens: EMPTY. Residual Lean/Lake processes: zero.

See Q391_BUILD_SUMMARY.txt, Q391_AXIOM_AUDIT.txt and Q391_DEPENDENCY_AUDIT.txt
for the final replay results and full exported theorem signatures.
The dependency audit traverses actual proof/type constants, not merely
imports. It excludes the two explicitly conditional connectors from the
unconditional closure check and rejects the old exceptional routes and
uninhabited semantic witnesses.

The earlier verification session became unavailable before its completion
was recorded. It is not counted as a complete audit. The final verification
script replays all Q391 sources and the Q374-Q391 aggregate.

## Reproduction and Scope

The archive is an additive source/evidence package. It does not contain
the historical Q343-Q390 sources or their large compiled dependency cache.
Replay requires the detached canonical workspace, Lean 4.15.0 and Mathlib
9837ca9d65d9de6fad1ef4381750ca688774e608. No commit, push, tag, branch change,
or destructive Git command was used. The pre-existing modified lakefile
and historical untracked sources are preserved.

The archive's final SHA-256 is stored only in the external attestation
RS19H_PACKAGE_VERIFICATION.txt; the archive must not attest to its own hash.
