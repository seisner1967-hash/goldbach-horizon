# Q393 / RS21H Final Report

## Verdict

**EIGHT ACTUAL ATOMS AND CANONICAL ENDPOINT: PASS. BRIDGE A: OPEN.**

The actual coefficient components, all eight atom memberships, the exact replay,
the requested Hardy endpoint membership and positivity, and a concrete historical
`AnalyticLeaf` now compile without residual semantic premises. The historical sign
bridge also proves the pointwise scaled Lambda carrier is positive at this same
endpoint. No first-bracket, 649-bracket family, counting or saturation closure is
claimed.

```lean
Q393Probe.requestedEndpoint_mem :
  endpointReplayOutput.mem
    (Q343Probe.normalizedHardyZ (Q390Probe.requestedEndpoint : Real))

Q393Probe.requestedEndpoint_positive :
  0 < Q343Probe.normalizedHardyZ (Q390Probe.requestedEndpoint : Real)

Q393Probe.requestedEndpointAnalyticLeaf :
  Q347Probe.AnalyticLeaf Q343Probe.normalizedHardyZ Q390Probe.requestedEndpoint
```

## Exact Target and Result

The point is `751937898017/1073741824`, with `K=63`, `ell=10`. The coefficient
factor is exactly `sourcePrimaryGPhase * riemannSiegelFiniteCoefficientSum 0 63
(-requestedXi) requestedQ`. Both the minus sign on xi and the factorial conversion
from normalized Taylor jets to raw derivatives are retained by proved equalities.

New coefficient boxes:

```text
Re: [-30565290726807201002/10^20, -30565290726807201001/10^20]
Im: [-54672428068935154476/10^20, -54672428068935154475/10^20]
```

These are not the old narrower candidate boxes. The first six certified boxes are
unchanged. The exact table, default-zero rule and proof declarations are in
`Q393_ATOM_TABLE.json` and `Q393_COEFFICIENT_SPEC.md`.

The actual final rational interval is summarized numerically as:

```text
lower ~= 1.88551744380562172196315410070E-13
upper ~= 1.89155813579780598103688083023E-13
width ~= 6.04069199218425907372672952542E-16
```

Only exact rational endpoints are used in Lean. The finite expression is exactly
`2 * Re(G * (S + A * B))`; all eight widths propagate through its checked interval
evaluation. Q391 contributes the proved symmetric radius
`1/400000000000000000000000000000 = 2.5e-30`. No Q375 replacement bound is used.

## Proof Construction

The published entire function F satisfies the global product identity D*F=N.
Finite Leibniz and the normalized Taylor definition give a triangular quotient
recurrence. Actual N/D jets at the true `requestedQ` are enclosed using four
certified complex exponential seeds, exact recurrences and directed inclusions.
The certified nonzero zeroth denominator permits the quotient construction.

All 190 quotient coefficients (orders 0..189) are proved members of their boxes.
All 64 exact rational coefficient rows, including exceptional top entries, are
bound to Q365. The weighted assembly retains all 3072 summands and restores every
factorial. Numerical certificates remain separate from their canonical semantic
bindings until `CoefficientAssemblyProduction.targetBox_mem` closes the argument.

For performance, integer rectangles share a 310-place decimal denominator;
products and cross-scale inclusion retain exact signed arithmetic. Array lookup
avoids repeatedly unfolding long recursive case tables. This replaces neither
the kernel checks nor the analytic membership proofs. No external numerical
result supplies a premise of the final theorem.

## Verification

- Direct new production builds: **294/294 PASS**.
- Second isolated new production replay: **294/294 PASS**.
- Fresh/initial olean byte identity: **294/294**.
- Eight-root exact-type and actual term-dependency audits: PASS, initially and on fresh outputs.
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- Raw-token scan of the actual new production closure: EMPTY.
- Independent review found no concrete mathematical defect in the reviewed kernels and bindings.
- Isolated generator reproductions: PASS; per-file hashes and JSON metadata exceptions are retained.

The strict audit actually reaches every jet membership, every coefficient row,
the true finite expression, Q391's bound, the canonical exact decomposition and
Q368 checker soundness. It rejects the old seed/witness/stress dependencies and
the Q386-Q388 path. The endpoint types have no open proof arguments; the table
theorem has only its legitimate Nat index.

The package provides 1086 local imported source files,
including 792 historical dependencies. Historical
local sources were imported from the existing cache, not all rebuilt by Q393.
External Lean/Mathlib caches are separately required. `Q393_REPLAY.md` supplies
both a full local-source replay procedure and the explicitly narrower measured
new-module replay. No inherited Lake job count is presented as a new build.

## Historical Consumers

The endpoint is bracket 415 right (zero-based ledger index 414). The left endpoint
and both historical first-bracket endpoints are different heights. Q391's bound
is specialized and is not transported to them by proximity.

The old serialized endpoint box has width about 1.572e-77, whereas this replay box
has width about 6.041e-16. The former is strictly inside the latter. Consequently
this particular checked output cannot refine that serialized box. Lean proves
this failure for the fixed output fields; it does not assert that no other
certification strategy could ever refine the box.

The following remain open: the historical serialized refinement, the second
endpoint of bracket 415, first-bracket leaves, the Fin 649 family, the Turing mass
bounds, TS329 counting and saturation, and family-level carrier membership.
`BRIDGE_A` remains `OPEN`; `TS340_UNCONDITIONAL` remains `OPEN_FROZEN`.
See `Q393_BRIDGE_A_CONSUMERS.md` for the unchanged historical types.

## Time and Preservation

The new Q393 clock and deadline are in `Q393_T0.json`. The endpoint first compiled
at 2026-09-08T20:49:12.0780474+00:00; production was frozen at
2026-09-08T20:57:46.887202+00:00. The document freeze is 2026-09-08T21:24:16.810717+00:00.
Package completion and its timebox result are recorded in the external attestation.
The final fifteen-minute verification reserve was not consumed by new proof work.

HEAD and origin/main remain `433e29eff1d9da2bc5937bb82bf5df3a2d59c08f`.
The preexisting tracked change is still 44 added lines in `lakefile.lean`; the
working directory is not described as pristine. No Git mutation was performed.
All three Q392 manifests replay unchanged (65, 1569 and 71 entries), and both
Q391 archives and all three Q392 archives retain their recorded hashes.

The older Q391 current-file manifest matches 80/81 entries; its only difference
is the older lakefile configuration, already superseded by the exact frozen Q392
configuration before this campaign. The Q391 archive itself is unchanged. Old
Q391/Q392 overrun and post-deadline classifications are preserved, not relabeled.

Exploratory failures and performance probes remain distinguished from production.
The quotient proof initially hit dependent-goal ordering; explicit application
fixed it without changing the statement or data. The audit launcher had a date
parsing guard issue, corrected before invoking Lean. Neither is a residual proof
obligation.

## Deliverables

`Q393_STATUS.json`, `Q393_COEFFICIENT_SPEC.md`, `Q393_ATOM_TABLE.json`,
`Q393_BRIDGE_A_CONSUMERS.md`, `Q393_BUILD_SUMMARY.txt`, `Q393_REPLAY.md`, the new
sources and generators, the full local import source inventory, exact build and
audit logs, predecessor archives, and the new manifest are packaged together.
The archive digest and fresh-extraction attestation intentionally remain outside
the archive to avoid circular self-hashing. No Q394 has been opened.
