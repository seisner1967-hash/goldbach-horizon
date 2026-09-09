# Q347 retry report - dyadic certificate replay

Date: 2026-08-12  
Baseline: `433e29eff1d9da2bc5937bb82bf5df3a2d59c08f`  
Required Lean: 4.15.0  
Required Mathlib: `9837ca9d65d9de6fad1ef4381750ca688774e608`

## Verdict

```text
Q347_RETRY_PREREQUISITES_PASS
Q347_CERTIFICATE_KERNEL_BUILD_PASS              2524/2524
Q347_CERTIFICATE_KERNEL_AXIOM_AUDIT_PASS
Q347_FIRST_BRACKET_BINDING_SOURCE_ONLY
Q347_FULL_ANALYTIC_BUILD_NOT_COMPLETED
SPECIAL_FUNCTION_ANALYTIC_LEAF_MISSING
Q347_FIRST_BRACKET_SIGN_NOT_OBTAINED
BRIDGE_A_OPEN
CARRIER_MEMBERSHIP_UNPROVED
MUR4_OPEN_REDUCED_TO_ANALYTIC_LEAF
Q347_RETRY_TIMEBOX_OVERRUN
```

The retry materially improves the first Q347 probe: the exact baseline, pinned
Lean environment, complete Q343 payload, accepted Q346 bridge and first Q344
bracket were all available. A deterministic arithmetic certificate checker was
implemented and compiled. Its soundness theorem reconstructs real interval
membership from `check = true` and explicitly supplied atom enclosures.

It does not close Bridge A. Neither endpoint enclosure for
`normalizedHardyZ` was inhabited.

## Time accounting

```text
start             2026-08-12T08:23:22.2876345+02:00
deadline          2026-08-12T10:23:22.2876345+02:00
forced stop       2026-08-12T11:33:31.3512497+02:00
```

The disposable worktree had the pinned Mathlib sources but no usable build
cache. The first cold build reconstructed 2287 Mathlib modules. The wrapper
timed out while the child Lake process continued in the background. The
compiled microkernel result and its axiom audit were obtained after the strict
deadline. They are reported as technical facts, but the sprint cannot receive
a timebox-compliant `PASS`.

## Compiled result

`Q347Probe.CheckedArithmeticCertificate` compiled successfully:

```text
2524/2524
Build completed successfully.
```

The accepted expression language contains only:

```text
atom, rational, neg, add, sub, mul
```

Division and all transcendental operations are rejected. The external
generator is untrusted; Lean recomputes the interval endpoints.

The terminal theorem is:

```lean
CheckedArithmeticCertificate.check atomBox cert = true
-> (forall n, (atomBox n).mem (atomValue n))
-> cert.output.mem (cert.expr.value atomValue)
```

A closed toy certificate is checked by ordinary kernel reduction and proves a
strictly negative result. No `native_decide` or `Lean.ofReduceBool` is used.

## Axiom audit

The following compiled declarations depend only on:

```text
propext, Classical.choice, Quot.sound
```

- `ArithmeticExpr.enclosure_sound`
- `CheckedArithmeticCertificate.check_sound`
- `CheckedArithmeticCertificate.negative`
- `CheckedArithmeticCertificate.positive`
- `toyCertificate_check`
- `toyCertificate_negative`

The Q347 Lean sources contain no `sorry`, `admit`, specialized `axiom`,
`opaque`, `Float`, `native_decide` or `Lean.ofReduceBool`.

## Exact first-bracket binding

The source `FirstBracketCertificateBoundary.lean` binds:

```text
lower endpoint = 60708182221 / 4294967296
upper endpoint = 30354091111 / 2147483648
```

to the exact rational intervals parsed by Q344 from the Q343 Arb balls and to
the Q346 documented phase-convention theorem. It deliberately requires two
semantic leaves:

```lean
firstLoInterval.Contains (normalizedHardyZ firstLo)
firstHiInterval.Contains (normalizedHardyZ firstHi)
```

The full import graph build was stopped before completion. This binding source
is therefore not assigned a build-pass status in this retry.

## Analytic boundary

A repository-wide search found no Riemann-Siegel formula, explicit zeta
remainder, Hardy-Z numerical evaluator, complex-Gamma interval evaluator or
trace-to-carrier theorem in the pinned Goldbach/Mathlib tree.

The eta series from TS341 cannot practically certify endpoint signs of order
`1e-10` at real part `1/2`: its paired convergence is far too slow. The
narrowest credible leaf remains a direct Riemann-Siegel certificate with a
formally proved explicit remainder.

The exact missing result is not rational interval arithmetic. It is the
special-function enclosure theorem connecting a finite checked trace to
`normalizedHardyZ`.

## Git governance

The work used a detached disposable worktree at the exact baseline. No branch,
commit, push, PR, merge or tag was created. `origin/main` and the detached HEAD
both remained at `433e29e`. The pre-existing untracked directories in the main
worktree were not touched.

## Final classification

```text
A_CERTIFICATE_CHECKER_SOUND : COMPILED, OUTSIDE_STRICT_TIMEBOX
A_INSTANCE_REPLAY_PASS      : NOT OBTAINED
FIRST_BRACKET_SIGN_PASS     : NOT OBTAINED
BRIDGE_A                    : OPEN
CARRIER_MEMBERSHIP          : UNPROVED
TS340_UNCONDITIONAL         : OPEN_FROZEN
Q348                        : NOT_LAUNCHED
```
