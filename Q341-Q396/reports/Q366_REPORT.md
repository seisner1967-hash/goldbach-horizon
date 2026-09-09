# Q366 report - analytic Riemann-Siegel decomposition

Date: 2026-08-20

## Verdict

```text
Q366_BASELINE_PREFLIGHT_PASS
Q366_Q365_INTEGRITY_PASS
Q366_PRIMARY_SOURCE_GATE_FAIL
Q366_ANALYTIC_DEVELOPMENT_NOT_ATTEMPTED
Q366_INDEPENDENT_REMAINDER_DEFINITION : NOT_OBTAINED
Q366_R_FUNCTION_DECOMPOSITION         : NOT_OBTAINED
Q366_ZETA_RIEMANN_SIEGEL_DECOMPOSITION: NOT_OBTAINED
Q366_NORMALIZED_HARDY_Z_DECOMPOSITION : NOT_OBTAINED
Q366_RIEMANN_SIEGEL_DECOMPOSITION     : NOT_OBTAINED
```

## Preflight

The detached worktree and `origin/main` both resolve to
`433e29eff1d9da2bc5937bb82bf5df3a2d59c08f`. The Q365 archive and manifest
match the mandated SHA-256 values. No Lean or Lake process was active at T0.

## Provenance investigation

The author-supplied TeX for paper II fixes `a`, `N`, `p`, `U`, the Dirichlet
prefix, the Q365 coefficient expansion, and the reflected relation between
`R(s)` and zeta. It explicitly calls `RS_K` the error term and refers its
definition and proof to paper I.

The retained primary capture from paper I covers only the auxiliary function
`F`. The publisher PDF endpoint was protected by an automated access challenge
for command-line retrieval. Metadata and the official article landing page
were verified, but no missing formula was inferred from an inaccessible
payload.

The exact independent analytic definition of `RS_K` was therefore not bound:
the available material did not establish the contour integral of the Taylor
remainder `Rg_K`, its orientation, constants, branches, and equality with the
`RS_K` occurring in the expansion.

## Fail-closed decision

The mandate prohibits both guessing those data and defining the remainder as
the target minus the finite expansion. The primary-source gate therefore
failed before any Q366 Lean module was created. This is a provenance failure,
not a compiler failure and not a theorem counterexample.

The closeout package replays its manifest 11/11 and its ZIP extraction 12/12.
Research stopped 649 seconds after T0; packaging completed 819 seconds after
T0, well before the first mandatory gate.

## Repository state

No branch, commit, push, pull request, merge, tag, or modification of `main`
was performed. Q362-Q365 sources and the toolchain were not modified.

## Frontier

```text
Q365_RS_COEFFICIENTS         : CLOSED
Q366_RS_DECOMPOSITION        : OPEN / PRIMARY_SOURCE_BLOCKED
Q367_ARIAS_REMAINDER         : NOT_STARTED
ARIAS_REMAINDER              : OPEN
BRIDGE_A                     : OPEN
CARRIER_MEMBERSHIP           : UNPROVED
TS340_UNCONDITIONAL          : OPEN_FROZEN
```

The narrow next prerequisite is a readable retained copy of paper I (or an
author-supplied equivalent) containing the complete contour definition of
`R(s)`, the exact independent definition of `RS_K`, and the equation linking
the Taylor remainder to that object.
