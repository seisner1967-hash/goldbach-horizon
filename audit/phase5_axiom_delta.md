# Phase 5 — Axiom Delta Report (v6 fusion vs r1 baseline)

Comparison of axiom dependencies for the 11 verified theorems
between manifest r1 (`b32b8a2`, tag `g26-v5-watchlist-closed-r1`)
and the post-fusion state on branch `feat/g26-g29-fusion` after
commits `1c7ddd4` (Phase 5.2) and `d28fe3f` (Phase 5.3).

## Comparison table

| Theorem | r1 axioms | v6 axioms | Delta |
|---|---|---|---|
| `Horizon.transfer_bound_at_4` | `{propext, Classical.choice, Quot.sound}` | `{propext, Classical.choice, Quot.sound}` | — |
| `Horizon.transfer_absolute_margin` | `{propext, Classical.choice, Quot.sound}` | `{propext, Classical.choice, Quot.sound}` | — |
| `Horizon.urysohn_smooth` | `{propext, Classical.choice, Quot.sound}` | `{propext, Classical.choice, Quot.sound}` | — |
| `Horizon.C₂_pos` | `{propext, Classical.choice, Lean.ofReduceBool, Quot.sound}` | `{propext, Classical.choice, Lean.ofReduceBool, Quot.sound}` | — |
| `Horizon.C₃_bound` | `{propext, Classical.choice, Quot.sound}` | `{propext, Classical.choice, Quot.sound}` | — |
| `Horizon.Certified.beta_exceeds_half` | `{propext, Classical.choice, Quot.sound}` | `{propext, Classical.choice, Quot.sound}` | — |
| `Horizon.Certified.ci_lower_exceeds_half` | `{propext, Classical.choice, Quot.sound}` | `{propext, Classical.choice, Quot.sound}` | — |
| `Horizon.Certified.fit_quality` | `{propext, Classical.choice, Quot.sound}` | `{propext, Classical.choice, Quot.sound}` | — |
| `Horizon.Certified.A_star_is_finite` | `{propext, Classical.choice, Quot.sound}` | `{propext, Classical.choice, Quot.sound}` | — |
| `Horizon.Certified.dispersion_bound_unconditional` | `{propext, Classical.choice, Quot.sound}` | `{propext, Classical.choice, Quot.sound}` | — |
| `Horizon.Certified.dispersion_converges_to_zero` | `{propext, Classical.choice, Quot.sound}` | `{propext, Classical.choice, Quot.sound}` | — |

**Net delta: 0 axioms added, 0 axioms removed across all 11 verified
theorems.** `sorryAx` count remains 0 in both build logs.

## Interpretation

The Phase 4 design archive flagged an expected outcome: "the fusion
will expose the structural axioms (`U1_to_U6_bound`,
`spectral_energy_bound`, `PO4_coverage`, `G_holomorphic`,
`G_bounded`, `spectral_bridge_GRH`) in the transitive dependency of
`grand_bridge`, making the R74 perimeter visible from a single
`#print axioms` invocation." This prediction proved incorrect.

The reason: `grand_bridge`'s proof body never consumes
`P.loss_ledger_closed`. The proof branches on `N ≤ 2·10^18`:

- On the small-N branch (`N ≤ 2·10^18`), `grand_bridge` invokes
  `P.finite_verified` (Pillar 3) — a hypothesis of `ProofPillars`,
  not an axiom in itself, and one that does not transitively
  consume any of the six G26 structural axioms.
- On the large-N branch (`N > 2·10^18`), `grand_bridge` is `sorry`
  by construction (the GRH branch, preserved as the GRH dependency
  per the watchlist closure discipline).

The G26 structural axioms (`U1_to_U6_bound` and the five Riemann
Bridge / U7 Seal axioms) are consumed only by a Lean term that
constructs an actual `LossLedger` and proves its `isClosed`
property. Such a construction would happen at the call site that
builds a `ProofPillars` instance to feed `grand_bridge`. Since no
such call site exists in the G26Verify scope (the architecture
publishes the pillar contract but never instantiates it
mechanically), the axioms remain inert in the verified-theorem
dependency closure.

## Architectural significance

The fusion changed `loss_ledger_closed` from a placeholder `Prop`
to a seal-typed proposition:

```lean
-- Before (r1):
loss_ledger_closed : Prop

-- After (v6):
loss_ledger_closed : ∀ _s : Horizon.U7PlatinumSeal, ∀ N : ℕ,
  N ≥ 4 → ∃ L : Horizon.LossLedger, L.isClosed
```

The visible improvement is structural, not axiomatic: anyone who
attempts to instantiate `ProofPillars` must now provide a Lean term
of this seal-typed proposition. Lean's typechecker will refuse a
construction whose `loss_ledger_closed` field has the wrong
signature, making the contract enforceable at the type level rather
than carried as documentation. The exposition of structural axioms
in `#print axioms grand_bridge` would happen only at the moment of
that hypothetical instantiation — at which point the G26 axioms
become consumed witnesses of the LossLedger closure proof.

In short: the fusion makes the contract visible and machine-checked
without changing what is provable.

## Build artifacts

The audit was run on branch `feat/g26-g29-fusion` immediately after
the Phase 5.3 commit (`d28fe3f`). Build commands:

```
lake build Goldbach.G26Verify.HorizonGoldbach    # 5 theorems
lake build Goldbach.G26Verify.HorizonCertified   # 6 + 5 (transitive)
```

Both exit 0. Total build duration on warm Mathlib cache: ~22 s.
Full logs at `$env:TEMP\g26_phase54_goldbach.log` and
`$env:TEMP\g26_phase54_certified.log` on the development host;
the salient axiom info has been verbatim-extracted into the table
above.
