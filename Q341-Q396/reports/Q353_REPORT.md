# Q353 - Checked transcendental trace kernel

## Verdict

```text
Q353_SEMANTIC_TRACE_KERNEL_PASS
Q353_SINGLE_NODE_REPLAY_PASS        : NOT OBTAINED
Q353_128_NODE_STRETCH_PASS          : NOT OBTAINED
Q353_FULL_8193_NODE_REPLAY_PASS     : NOT OBTAINED
BRIDGE_A                            : OPEN
CARRIER_MEMBERSHIP                  : UNPROVED
Q348_SIGN_LEAVES                    : UNINHABITED
TS340_UNCONDITIONAL                 : OPEN / FROZEN
```

The sprint closed the reusable semantic checker, not the numerical replay.
All positive claims below were compiled before the 120-minute deadline.

## Compiled results

1. `SafeTrapTargets.lean` defines the corrected intervals
   `[8/785 - 23/4000000, 8/785 - 9/4000000]` and
   `[8/901 + 41/4000000, 8/901 + 55/4000000]`.  Membership of the concrete
   8192-panel trapezoidal sums would imply the Q348 enclosures.
2. `RationalTaylor.lean` supplies the Mathlib D20 enclosure of pi, a rational
   Taylor upper bound proving `exp 1 <= 3`, sound coarse exponential leaves
   on certified inputs `x <= 0` or `0 <= x <= 1`, and the canonical cosine
   Taylor `HasSum` identity together with the universal enclosure `[-1,1]`.
3. `TranscendentalTrace.lean` implements append-only SSA instructions
   `rational`, `pi`, `neg`, `add`, `sub`, `mul`, `sq`, `exp`, and `cosRat`.
   The checker recomputes an interval and accepts a serialized output only
   when the computed interval is included in it.
4. `TranscendentalTrace.check_sound` proves by induction that every accepted
   register interval contains its real semantic value.
5. `arithmeticCertificate_sound_of_trace` binds a checked SSA table to the
   existing Q347 `ArithmeticCertificate.sound` theorem.

The aggregate source `Q353Probe.lean` compiles directly.  The axiom audit for
all terminal compiled theorems reports only `propext`, `Classical.choice`, and
`Quot.sound`.  The forbidden-token scan is empty.

## Fail-closed boundary

`SingleNodeReplay.lean` contains the required `u=1`, `k=4096` trace for both
`t=14` and `t=15`, including `exp 1`, `exp(1/4)`, pi,
`exp(-pi*exp 1)`, `exp(-4*pi*exp 1)`, `cos 7`, and `cos(15/2)`.
Its monolithic concrete check was replaced by incremental checking, but Lean
still reached a deterministic elaboration timeout while normalizing the
nested dependent register indices.  Therefore this file is source-only and
no single-node replay PASS is claimed.

The cosine leaf currently proves the exact Taylor-series identity but uses
the coarse `[-1,1]` enclosure.  A tight finite Taylor polynomial with an
explicit rational remainder was not completed.  Consequently no 128-node
stretch, no full 8193-node sum, no safe-target membership, and no sign theorem
was obtained.

## Governance

The work used the existing detached worktree at baseline `433e29e`.  HEAD and
`origin/main` remain equal to that commit.  No branch, commit, push, PR,
merge, tag, or permanent module was created.
