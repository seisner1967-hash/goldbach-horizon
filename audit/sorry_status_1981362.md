# `sorry` Audit — `goldbach-horizon`

**Commit:** `1981362dd08e14c7adea313d956e4d8c3a3bd363` (short: `1981362`)  
**Tag at HEAD:** `g26-v7-ts6-bridge-typed`  
**Branch:** `main`  
**Worktree status:** dirty (uncommitted changes present — output not fully attributable to commit SHA)  
**Audit date (UTC):** `2026-05-14T05:43:37Z`  
**Toolchain (best-effort, metadata only):**

- `Lean (version 4.15.0, x86_64-w64-windows-gnu, commit 11651562caae, Release)`
- `Lake version 5.0.0-1165156 (Lean version 4.15.0)`

---

## Summary

**Total `sorry` tokens detected in code context:** 37

### By file

| File | Count |
|---|---|
| `.claude/worktrees/beautiful-chaplygin-d3d0c4/Goldbach/A2Certificate.lean` | 2 |
| `.claude/worktrees/nice-elgamal-b71379/Goldbach/A2Certificate.lean` | 2 |
| `.claude/worktrees/nostalgic-goldstine-a545d0/Goldbach/A2Certificate.lean` | 2 |
| `Goldbach/A2Certificate.lean` | 2 |
| `Goldbach/G26Verify/HorizonCertified.lean` | 1 |
| `Goldbach/G26Verify/HorizonGoldbach.lean` | 5 |
| `TS6/lean/TS6/Effective/AveragedBounds.lean` | 3 |
| `TS6/lean/TS6/Exact/CenteringShift.lean` | 2 |
| `TS6/lean/TS6/Exact/DirichletVariance.lean` | 2 |
| `TS6/lean/TS6/Exact/FiniteCharacterVariance.lean` | 3 |
| `TS6/lean/TS6/Structure/RankinSelbergDecomp.lean` | 1 |
| `g26_v5_arxiv/anc/lean/HorizonCertified.lean` | 1 |
| `g26_v5_arxiv/anc/lean/HorizonGoldbach.lean` | 5 |
| `g26_v6_arxiv/anc/lean/HorizonCertified.lean` | 1 |
| `g26_v6_arxiv/anc/lean/HorizonGoldbach.lean` | 5 |

### By declaration kind

| Kind | Count |
|---|---|
| def | 20 |
| theorem | 17 |

---

## Detail

Each row is a single `sorry` token in non-comment code. **Declaration** is the nearest preceding top-level declaration on the strip-of-comments view (so it is robust against doc-comments and `/- ... -/` blocks intervening). **Kind** is the Lean keyword. **Source line** is the raw line as written in the file (TABs replaced with 4 spaces, `|` and backticks escaped for Markdown).


### `.claude/worktrees/beautiful-chaplygin-d3d0c4/Goldbach/A2Certificate.lean`

| Line | Kind | Declaration | Source line |
|---|---|---|---|
| 110 | def | `a2CertificateStatus` | `  "  PROVED:   tail_bound_A2 (PO_A2_stage2, Q > 20, 0 sorry)\\n" ++` |
| 111 | def | `a2CertificateStatus` | `  "  INFRA:    BreakpointGrid (cells + indices, 0 sorry)\\n" ++` |

### `.claude/worktrees/nice-elgamal-b71379/Goldbach/A2Certificate.lean`

| Line | Kind | Declaration | Source line |
|---|---|---|---|
| 110 | def | `a2CertificateStatus` | `  "  PROVED:   tail_bound_A2 (PO_A2_stage2, Q > 20, 0 sorry)\\n" ++` |
| 111 | def | `a2CertificateStatus` | `  "  INFRA:    BreakpointGrid (cells + indices, 0 sorry)\\n" ++` |

### `.claude/worktrees/nostalgic-goldstine-a545d0/Goldbach/A2Certificate.lean`

| Line | Kind | Declaration | Source line |
|---|---|---|---|
| 110 | def | `a2CertificateStatus` | `  "  PROVED:   tail_bound_A2 (PO_A2_stage2, Q > 20, 0 sorry)\\n" ++` |
| 111 | def | `a2CertificateStatus` | `  "  INFRA:    BreakpointGrid (cells + indices, 0 sorry)\\n" ++` |

### `Goldbach/A2Certificate.lean`

| Line | Kind | Declaration | Source line |
|---|---|---|---|
| 110 | def | `a2CertificateStatus` | `  "  PROVED:   tail_bound_A2 (PO_A2_stage2, Q > 20, 0 sorry)\\n" ++` |
| 111 | def | `a2CertificateStatus` | `  "  INFRA:    BreakpointGrid (cells + indices, 0 sorry)\\n" ++` |

### `Goldbach/G26Verify/HorizonCertified.lean`

| Line | Kind | Declaration | Source line |
|---|---|---|---|
| 157 | theorem | `grand_bridge` | `  · sorry -- Requires Pillar 1 (GRH-conditional spectral rigidity)` |

### `Goldbach/G26Verify/HorizonGoldbach.lean`

| Line | Kind | Declaration | Source line |
|---|---|---|---|
| 39 | def | `R_F` | `noncomputable def R_F (N : ℕ) : ℝ := sorry` |
| 42 | def | `Main` | `noncomputable def Main (N : ℕ) : ℝ := sorry` |
| 276 | def | `N_start` | `def N_start : ℕ := sorry  -- Must satisfy N_start ≤ N₀` |
| 306 | theorem | `goldbach_conditional_GRH` | `  sorry  -- The crown jewel: requires full formal chain` |
| 313 | def | `G_euler` | `noncomputable def G_euler (s : ℂ) : ℂ := sorry` |

### `TS6/lean/TS6/Effective/AveragedBounds.lean`

| Line | Kind | Declaration | Source line |
|---|---|---|---|
| 139 | theorem | `TS4_weighted_effective_bound` | `  sorry` |
| 164 | theorem | `TS4_unweighted_effective_bound` | `  sorry` |
| 183 | theorem | `TS3_first_effective_bound` | `  sorry` |

### `TS6/lean/TS6/Exact/CenteringShift.lean`

| Line | Kind | Declaration | Source line |
|---|---|---|---|
| 101 | theorem | `variance_shift_of_origin` | `  sorry` |
| 148 | theorem | `TS2_centering_shift` | `  sorry` |

### `TS6/lean/TS6/Exact/DirichletVariance.lean`

| Line | Kind | Declaration | Source line |
|---|---|---|---|
| 121 | theorem | `TS2_exact_identity` | `  sorry` |
| 132 | theorem | `TS1_exact_identity` | `  sorry` |

### `TS6/lean/TS6/Exact/FiniteCharacterVariance.lean`

| Line | Kind | Declaration | Source line |
|---|---|---|---|
| 99 | theorem | `sum_character_eq` | `  sorry` |
| 120 | theorem | `schur_orthogonality` | `  sorry` |
| 157 | theorem | `parseval_identity` | `  sorry` |

### `TS6/lean/TS6/Structure/RankinSelbergDecomp.lean`

| Line | Kind | Declaration | Source line |
|---|---|---|---|
| 164 | theorem | `rankin_selberg_decomposition` | `  sorry` |

### `g26_v5_arxiv/anc/lean/HorizonCertified.lean`

| Line | Kind | Declaration | Source line |
|---|---|---|---|
| 150 | theorem | `grand_bridge` | `  · sorry -- Requires Pillar 1 (GRH-conditional spectral rigidity)` |

### `g26_v5_arxiv/anc/lean/HorizonGoldbach.lean`

| Line | Kind | Declaration | Source line |
|---|---|---|---|
| 38 | def | `R_F` | `noncomputable def R_F (N : ℕ) : ℝ := sorry` |
| 41 | def | `Main` | `noncomputable def Main (N : ℕ) : ℝ := sorry` |
| 275 | def | `N_start` | `def N_start : ℕ := sorry  -- Must satisfy N_start ≤ N₀` |
| 305 | theorem | `goldbach_conditional_GRH` | `  sorry  -- The crown jewel: requires full formal chain` |
| 312 | def | `G_euler` | `noncomputable def G_euler (s : ℂ) : ℂ := sorry` |

### `g26_v6_arxiv/anc/lean/HorizonCertified.lean`

| Line | Kind | Declaration | Source line |
|---|---|---|---|
| 157 | theorem | `grand_bridge` | `  · sorry -- Requires Pillar 1 (GRH-conditional spectral rigidity)` |

### `g26_v6_arxiv/anc/lean/HorizonGoldbach.lean`

| Line | Kind | Declaration | Source line |
|---|---|---|---|
| 38 | def | `R_F` | `noncomputable def R_F (N : ℕ) : ℝ := sorry` |
| 41 | def | `Main` | `noncomputable def Main (N : ℕ) : ℝ := sorry` |
| 275 | def | `N_start` | `def N_start : ℕ := sorry  -- Must satisfy N_start ≤ N₀` |
| 305 | theorem | `goldbach_conditional_GRH` | `  sorry  -- The crown jewel: requires full formal chain` |
| 312 | def | `G_euler` | `noncomputable def G_euler (s : ℂ) : ℂ := sorry` |

---

## Reproducibility

To regenerate this report at the same commit on a clean worktree:

```bash
git checkout 1981362dd08e14c7adea313d956e4d8c3a3bd363
./scripts/sorry_audit.sh
```

The output filename is keyed on the short commit SHA. Re-running on the same commit with a clean worktree overwrites the same file and produces byte-identical content (modulo the `Audit date (UTC)` field and the `Toolchain` block, which depend on environment).

For diff-friendly archival, the report can be normalised by:

```bash
./scripts/sorry_audit.sh --stdout \
  | sed -E 's/^\*\*Audit date.*/[date-stripped]/; s/^- `Lean.*/[lean-stripped]/; s/^- `Lake.*/[lake-stripped]/' \
  > audit/sorry_status_1981362_normalised.md
```

## Detection logic

1. Walk every `*.lean` under the repository root, excluding `.lake/`, `build/`, `lake-packages/`, `.git/`. Sort the file list (so output ordering is reproducible across filesystems).
2. For each file, single-pass `awk` scanner:
   - Tracks block comment depth (`/- ... -/`, nestable per Lean 4 spec).
   - Strips line comments (`--` to end of line).
   - Replaces stripped comment characters with spaces (preserves column alignment for reporting).
   - Updates the current declaration name and kind on every line that matches a top-level declaration header (`theorem`/`lemma`/`def`/`example`/`instance`/`abbrev`/`structure`/`inductive`/`class`/`axiom`/`opaque`, possibly preceded by `@[attribute]` and modifiers `private`/`protected`/`noncomputable`/`partial`/`unsafe`/`nonrec`/`scoped`/`mutual`).
   - Emits a TSV row for every line whose stripped content contains a `sorry` token at word boundaries.
3. Render TSV as Markdown with metadata header, two summary tables (by file, by kind), and per-file detail tables.

## Known limitations

- **Macro quotation is not parsed**: a `sorry` inside `` `(...) `` would be detected as a plain `sorry`. False-positive risk: low in this codebase.
- **Transitive axioms are invisible**: a dependency contributing `sorryAx` is not detected. Run `#print axioms <decl>` per theorem.
- **Multi-line declaration headers**: if the keyword and the name straddle multiple lines (unusual), the tracker may misattribute the next `sorry`. Inspect manually for any unexpected `(file-scope)` attributions.
- **`Term.byTacticSeq` placeholders**: idiomatic `:= by sorry` is detected normally; `:= by { sorry }` is also detected.
- **`scoped` and `mutual` blocks**: `scoped theorem foo` is correctly attributed; `mutual ... end` blocks track only the last entered declaration before a `sorry`.
