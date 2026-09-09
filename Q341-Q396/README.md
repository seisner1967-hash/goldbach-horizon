# Q341-Q396: from the analytic contract to certified historical brackets

[Repository overview](../README.md) · [Français](README.fr.md) · [Full chronology](CHRONOLOGY.md) · [Open contracts](BRIDGE_A.md)

**Documented status: September 9, 2026. Latest closeout: Q395. Q396: mandate only; results not supplied.**

This section records the continuation of the Horizon / Goldbach program after the
permanent TS341 milestone. It brings together the campaign history, the mathematical
results reported by the verified research packages, their limits, and the next work.
The Q-numbered experiments and continuations are not additional permanent TS modules.

## What has been achieved

| Layer | Latest documented result | Scope |
| --- | --- | --- |
| Critical-line analytic transport | Q389 connects the independently defined auxiliary pair to completed zeta, and then to `normalizedHardyZ`, for every real height. | Full critical line; the old exceptional global seed is not used. |
| Source remainder | Q391 constructs `Q390Probe.RequestedAriasRemainderTransport` without arguments or residual semantic premises. The actual normalized source contribution is at most `2.5e-30`. | Canonical endpoint `751937898017/1073741824`, `K=63`, `ell=10`; not the generic 2011 Arias theorem. |
| Uniform remainder | Q394 proves a radius `2.5e-30` on `[699,7003/10]`; its separate extension proves `5e-30` on `[685,7003/10]`. | The extension covers eleven historical spans, 405-415. A remainder bound alone does not certify their signs. |
| Actual finite computation | Q393 certifies all eight real atoms of `2 * Re(G * (S + A * B))`, the exact replay, positive Hardy sign, and a concrete `AnalyticLeaf`. | One canonical rational endpoint, the right endpoint of bracket 415. |
| Historical zero brackets | Q394 closes 414-415. Q395 adds 410-413 using eight newly certified endpoints. | Six exact historical rows, with two strict signs each and distinct genuine zeta zeros. |
| Multiplicity lower bound | At least 6 below height 1000; at least 7 after separately adding the disjoint Q358 interval `(14,15)`. | Lower bounds only; neither uniqueness, simplicity, nor an exact global count is inferred. |

The indexed subfamily is exactly
`{i : Fin 649 // i ∈ closedIndices}`, where
`closedIndices = {409,410,411,412,413,414}`. Its cardinality is **6**.
Historical numbering is one-based: these are brackets **410-415**.

## Principal terminal statements

The following are statements reported as compiled in the supplied research packages.
This documentation publication performs no new Lean proof replay.

```lean
Q391Probe.requestedAriasRemainderTransport :
  Q390Probe.RequestedAriasRemainderTransport

Q393Probe.requestedEndpoint_positive :
  0 < Q343Probe.normalizedHardyZ (Q390Probe.requestedEndpoint : Real)

Q393Probe.requestedEndpointAnalyticLeaf :
  Q347Probe.AnalyticLeaf Q343Probe.normalizedHardyZ Q390Probe.requestedEndpoint
```

Q389 also proves the auxiliary-zeta identity and Hardy transport for every real `t`.
The exact types, constructions, and verification scopes appear in the
[Q389](reports/Q389_REPORT.md), [Q391 closure](reports/Q391_CLOSURE_REPORT.md),
[Q393](reports/Q393_REPORT.md), [Q394](reports/Q394_REPORT.md), and
[Q395](reports/Q395_REPORT.md) reports.

## Current frontier

```text
CANONICAL_ENDPOINT               : CERTIFIED
HISTORICAL_BRACKETS_410_TO_415    : CERTIFIED (6/649)
OTHER_HISTORICAL_ROWS            : 643 NOT YET CERTIFIED
BRACKETS_405_TO_409              : OPEN
FULL_H1000_SIGN_FAMILY           : OPEN
TURING_BOUNDS                    : OPEN
EXACT_GLOBAL_COUNT              : OPEN
SATURATION                      : OPEN
BRIDGE_A                        : OPEN
TS340_UNCONDITIONAL              : OPEN_FROZEN
Q396_RESULTS                    : NOT_SUPPLIED
```

The TS340 reference contract concerns height **1,132,490** and the exact positive
count **2,001,050**. A six-row pilot below 1000 does not discharge that contract.
See [BRIDGE_A.md](BRIDGE_A.md) for the distinct family, counting, and refinement obligations.

## Q396: the documented continuation mandate

The next campaign targets the ten exact endpoints of brackets 405-409. It may reuse
one certified box for the inverse of the constant denominator jet `D₀` at a fixed
endpoint throughout its quotient recurrence. This is `D₀⁻¹`, not `q⁻¹`.
The proposed optimization must be validated over the complete 190-jet chain and its
semantic root. Neither faster execution nor additional closed pairs is assumed.

If all five pairs close, the exact ledger subfamily would have 11 rows and 638 rows
would remain. These are conditional projections, not current results.

## Reading and evidence

- [Chronology Q341-Q396](CHRONOLOGY.md): every milestone, including indirect documentation and unattempted gates.
- [English PDF synthesis](pdf/Q341-Q396-Horizon-Goldbach-Continuation-Synthesis-English.pdf), 28 pages.
- [French PDF synthesis](pdf/Q341-Q396-Horizon-Goldbach-Synthese-Continuation.pdf), 28 pages.
- [Evidence index](EVIDENCE.md): campaign reports, archive fingerprints, and compilation scopes.
- [STATUS.json](STATUS.json): exact current counts and open obligations.

The main branch previously stopped at `433e29e` because the subsequent campaigns
preserved their local work and sealed packages without permanent Git operations.
This section publishes their documentary record. The underlying proof packages,
generators, and external Lean/Mathlib caches remain separate from this documentation
addition. Reproducing their proofs requires the package-specific replay procedures.
