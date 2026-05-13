# Phase 6 v7 — Axiom Delta Audit (TS6 Large Sieve Typed Bridge)

**Phase:** 6.3
**Branch:** `phase6/ts6-large-sieve-typed-bridge-v1`
**Predecessor tag:** `g26-v6-fusion-merged` (commit `57474e8`)
**Phase 6.1 commit:** `c68c7d4` (typed interface introduced)
**Phase 6.2 commit:** `69db595` (cosmetic axiom removed, dependency routed)
**Audit date:** 2026-05-13

## Predicted vs Observed

### Predicted (cf. `Goldbach/Bridge/TS6LargeSieveInterface.lean`, § "PHASE 6 CALIBRATION")

> Following the Phase 5 v6 methodological lesson, we predict NO change in
> `#print axioms grand_bridge` (or any of the 11 verified theorems) as a
> result of this module. Reason: no caller in the current scope CONSTRUCTS
> an instance of `ProofPillars` requiring a `SpectralBridgeFromLargeSieve`
> witness. The bridge therefore remains inert from the perspective of
> axiomatic transitive closure, exactly as `axiom spectral_bridge_GRH : True`
> was inert.

### Observed (Phase 6.2 build audit)

| Theorem | Axioms pre-Phase-6 (v6) | Axioms post-Phase-6 (v7) | Delta |
|---|---|---|---|
| `Horizon.transfer_bound_at_4` | `{Π, C, Q}` | `{Π, C, Q}` | ∅ |
| `Horizon.C₂_pos` | `{Π, C, Q, R}` | `{Π, C, Q, R}` | ∅ |
| `Horizon.C₃_bound` | `{Π, C, Q}` | `{Π, C, Q}` | ∅ |
| `Horizon.transfer_absolute_margin` | `{Π, C, Q}` | `{Π, C, Q}` | ∅ |
| `Horizon.urysohn_smooth` | `{Π, C, Q}` | `{Π, C, Q}` | ∅ |
| `Horizon.Certified.beta_exceeds_half` | `{Π, C, Q}` | `{Π, C, Q}` | ∅ |
| `Horizon.Certified.ci_lower_exceeds_half` | `{Π, C, Q}` | `{Π, C, Q}` | ∅ |
| `Horizon.Certified.fit_quality` | `{Π, C, Q}` | `{Π, C, Q}` | ∅ |
| `Horizon.Certified.A_star_is_finite` | `{Π, C, Q}` | `{Π, C, Q}` | ∅ |
| `Horizon.Certified.dispersion_bound_unconditional` | `{Π, C, Q}` | `{Π, C, Q}` | ∅ |
| `Horizon.Certified.dispersion_converges_to_zero` | `{Π, C, Q}` | `{Π, C, Q}` | ∅ |

Where Π = `propext`, C = `Classical.choice`, Q = `Quot.sound`,
R = `Lean.ofReduceBool`.

**Result: zero axiom delta across all 11 verified theorems.** No `sorryAx`
introduced; whitelist preserved exactly.

## Diagnosis

The replacement of `axiom spectral_bridge_GRH : True` by the typed
interface in `Goldbach.Bridge.TS6LargeSieveInterface` does not propagate
into the transitive axiom closure of any verified theorem, for the same
structural reason already observed in Phase 5 v6: no caller in the
current G26 scope constructs an instance of `ProofPillars` requiring a
`SpectralBridgeFromLargeSieve` witness, nor invokes
`spectral_bridge_via_large_sieve` directly. The analytic dependency
(Large Sieve + Chebyshev + Bombieri–Vinogradov-pointwise) therefore
remains latent — encoded as a typed obligation but not yet consumed.

The Phase 5 lesson is now confirmed as a recurrent pattern: *predictions
about transitive axiom exposure under refactoring require checking
actual caller consumption*. Type-narrowing alone does not propagate
axioms when the narrowed field is unused.

## Methodological pattern (archived for future phases)

- **Phase 4 prediction (incorrect):** fusion would expose structural axioms.
- **Phase 5.4 observation:** zero delta — lesson archived.
- **Phase 6 prediction (calibrated):** zero delta expected, for the same reason.
- **Phase 6.3 observation:** zero delta — pattern confirmed (two in a row).

For future refactors of this kind (type-structural improvements without
new callers), expect zero axiomatic delta as the baseline. The benefit
is machine-enforceability of the contract for future callers, not
immediate visibility of the underlying obligations.

## Latent bug discovered (orphan doc-comment)

During Phase 6.2 axiom removal, the doc-comment `/-- ... -/` immediately
preceding the deleted `axiom spectral_bridge_GRH` declaration became an
orphan (a `/--` doc-string requires a declaration to follow). Fixed by
conversion `/--` → `/-` (regular block comment). Identical pattern
previously observed in Phase 1a on `HorizonCertified.lean`.

**Pattern flagged for future refactors:** when removing a declaration
preceded by a doc-string, audit for orphan-doc-comment parse errors.
Recurrent across at least two phases of this programme.

## Build verification

- `lake build Goldbach.G26Verify.HorizonGoldbach` → exit 0, 1978/1978 modules.
- `lake build Goldbach.G26Verify.HorizonCertified` → exit 0, 1979/1979 modules.
- `lake build Goldbach.Bridge.TS6LargeSieveInterface` → exit 0 (Phase 6.1).
- Warnings: 6 expected (hors-watchlist preserved sorrys).
- Errors: 0.
- New axioms: 0.
- `sorryAx` occurrences in verified theorems: 0.

## Conclusion

Phase 6 v7 delivers a type-structural improvement: the cosmetic
`axiom spectral_bridge_GRH : True` is removed and replaced by a typed
obligation routed through `Goldbach.Bridge.TS6LargeSieveInterface`.
The 11 verified theorems remain axiom-pure under the documented
whitelist. The dependency on the large-sieve / Chebyshev / Bombieri–
Vinogradov-pointwise stack is now machine-enforceable for any future
caller that instantiates `ProofPillars`, while remaining inert under
the current G26 scope.
