# Axiom-Purity Audit — `goldbach-horizon`

**Commit:** `c5e318366fcdd0594bd932bc6dc80ace48b8193d` (short: `c5e3183`)  
**Tag at HEAD:** *none* (nearest: `g26-v7-ts6-bridge-typed`)  
**Branch:** `main`  
**Worktree status:** dirty (uncommitted changes present — output not fully attributable to commit SHA)  
**Audit date (UTC):** `2026-05-14T05:56:11Z`  
**Toolchain:**

- `Lean (version 4.15.0, x86_64-w64-windows-gnu, commit 11651562caae, Release)`
- `Lake version 5.0.0-1165156 (Lean version 4.15.0)`

**Generated audit module:** `Goldbach/Audit/WatchlistAudit.lean` (auto-regenerated each run)

---

## Summary

| Metric | Count |
|---|---|
| Watchlist size (expected) | 11 |
| Theorems audited (found in Lean output) | 11 |
| Theorems missing from Lean output | 0 |
| PASS (axioms ⊆ whitelist) | 11 |
| FAIL (at least one non-whitelist axiom) | 0 |

✅ **All 11 watchlist theorems verified axiom-pure under the whitelist.**

---

## Whitelist (active)

- `propext`
- `Classical.choice`
- `Quot.sound`
- `Lean.ofReduceBool`
- `Lean.ofReduceNat`

## Per-theorem detail

| Status | Theorem | # axioms | Axioms | Violations |
|---|---|---|---|---|
| ✅ PASS | `Horizon.transfer_bound_at_4` | 3 | propext, Classical.choice, Quot.sound | — |
| ✅ PASS | `Horizon.transfer_absolute_margin` | 3 | propext, Classical.choice, Quot.sound | — |
| ✅ PASS | `Horizon.urysohn_smooth` | 3 | propext, Classical.choice, Quot.sound | — |
| ✅ PASS | `Horizon.C₂_pos` | 4 | propext, Classical.choice, Lean.ofReduceBool, Quot.sound | — |
| ✅ PASS | `Horizon.C₃_bound` | 3 | propext, Classical.choice, Quot.sound | — |
| ✅ PASS | `Horizon.Certified.beta_exceeds_half` | 3 | propext, Classical.choice, Quot.sound | — |
| ✅ PASS | `Horizon.Certified.ci_lower_exceeds_half` | 3 | propext, Classical.choice, Quot.sound | — |
| ✅ PASS | `Horizon.Certified.fit_quality` | 3 | propext, Classical.choice, Quot.sound | — |
| ✅ PASS | `Horizon.Certified.A_star_is_finite` | 3 | propext, Classical.choice, Quot.sound | — |
| ✅ PASS | `Horizon.Certified.dispersion_bound_unconditional` | 3 | propext, Classical.choice, Quot.sound | — |
| ✅ PASS | `Horizon.Certified.dispersion_converges_to_zero` | 3 | propext, Classical.choice, Quot.sound | — |

---

## Reproducibility

To regenerate this report at the same commit on a clean worktree:

```bash
git checkout c5e318366fcdd0594bd932bc6dc80ace48b8193d
lake build                  # ensure all dependencies are built
./scripts/axiom_audit.sh
```

The output filename is keyed on the short commit SHA. Re-running on the same commit with a clean worktree and a deterministic Lean build produces a byte-identical report (modulo the `Audit date (UTC)` field and the `Toolchain` block, which depend on environment).

## Detection logic

1. Generate `Goldbach/Audit/WatchlistAudit.lean` from the WATCHLIST array (a sequence of `#print axioms` calls, one per theorem, plus the project imports).
2. Invoke `lake env lean` on the generated module; capture stdout (axiom messages) separately from stderr (build errors).
3. Single-pass `awk` parser: for every `'X' depends on axioms: [...]` and `'X' does not depend on any axioms` line, extract the theorem name and accumulate the axiom list (lists may wrap across lines).
4. For each parsed row, compare the axiom set against the WHITELIST array; flag any axiom outside the whitelist as a violation.
5. Render Markdown with per-theorem rows in WATCHLIST declaration order (so the report ordering is stable across runs and matches the manifest).

## Known limitations

- **Requires a successful project build.** If `lake build` has not been run (or has failed), this script exits 4 with the Lean error output. Build first.
- **The audit is byte-faithful to whatever `#print axioms` reports.** If Lean is configured to suppress or rewrite axiom messages (unusual), the script cannot recover the missing data.
- **No protection against malicious axiom redefinition.** A project that adds an axiom named `propext` of a different type would silently pass; the whitelist matches by name only. Protection against axiom shadowing is the Lean kernel's responsibility.
- **The script regenerates `Goldbach/Audit/WatchlistAudit.lean` every run.** Manual edits to that file are lost. To change the audit scope, edit the WATCHLIST/WHITELIST arrays in this script and re-run.
- **`Lean.ofReduceNat` is in the whitelist but may not appear in any current theorem's closure** (per manifest v3.0 note: only `Lean.ofReduceBool` is observed, on `Horizon.C₂_pos`). The whitelist is deliberately broader than the observable to absorb future migrations.
