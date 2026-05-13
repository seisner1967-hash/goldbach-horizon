# G26 v5 Watchlist Closure — Audit Baseline

Companion human-readable document to `manifests/G26_v5_watchlist_closed.json`.
For machine-verifiable claims, refer to the manifest. This document
explains the work, decisions, and pointers for future contributors.

Status: watchlist v2 fully closed at commit `bc78fdb`. Manifest committed
at `be8b6e6`. This document committed in the Phase 3.2 commit that follows.

## 1. Overview

G26 is the Lean formalisation track for the *Horizon Goldbach* programme.
Its purpose is to mechanically verify, under Mathlib 4.15 + Lean 4.15.0, a
set of theorem stubs and constant-related axioms shipped from the Drive
source (`HorizonGoldbach.lean`, `HorizonCertified.lean`) and to bring the
verified subset to a documented axiom-pure state under an explicit
whitelist.

When this branch (`feat/g26-sorry-cleanup`) started from `main` at commit
`62bdd5c`, neither of the two Drive files existed in the local repo. The
existing `Goldbach` library compiled, with zero real `sorry` proof terms
and zero axiom declarations in the tracked tree (commit `7ed739f` "ZERO
SORRY" had been the prior milestone). G26 brought in two new files under
a fresh sub-directory `Goldbach/G26Verify/`, then progressively closed the
"watchlist v2" subset of their open obligations: five named targets (three
`sorry`-bearing theorems and two `axiom`-with-`sorry`-definition pairs).

The work fits in eight commits on `feat/g26-sorry-cleanup`, advancing
through Phase 0 (tooling and WIP triage), Phase 1a / 1b (compile the two
imported files under Lean 4.15), Phases 2.1 through 2.4 (close the
watchlist), and Phases 3.1 / 3.2 (machine-readable manifest and this
narrative). At HEAD, both files compile, eleven theorems verify
axiom-pure, the watchlist is empty, and the from-scratch build (`lake
clean` then full rebuild of the two targets) completes in 43 minutes 14
seconds with exit code 0 and zero `sorryAx` mentions in the log.

The work explicitly preserves five out-of-scope `sorry`s and six
structural axioms. Those are not bugs to fix in this track; they describe
modules and infrastructure that live outside the `G26Verify` sub-tree.
The watchlist closure is *the* milestone, not a stepping stone to broader
closure of the file.

## 2. Architecture Context

The two Drive files belong to the *Grand Bridge* three-pillar architecture
for an attack on Goldbach's strong conjecture:

- **Pillar 1 — Loss Ledger (GRH-conditional)**: a `LossLedger` structure
  enumerating seven loss channels U1..U7, with closure condition
  `∑ U_i < 1`. The first six channels are bounded by an axiom
  `U1_to_U6_bound` (budget `≤ 0.78`). The seventh, U7, is the "Platinum
  Seal" coupling between Route A (finite verification up to `N₀ = 4·10^18`)
  and Route B (spectral rigidity, GRH-conditional).
- **Pillar 2 — Dispersion bound (unconditional)**: covered in
  `HorizonCertified.lean`. The certified empirical fit from G29
  (β = 0.8528, R² = 0.9925, bootstrap CI [0.8503, 0.8554]) yields the
  formally verifiable theorems `beta_exceeds_half`, `ci_lower_exceeds_half`,
  `fit_quality`, and the unconditional `dispersion_bound_unconditional`
  via `Finset.card_filter_le`. Crossing point `A* = 67` is computed
  rigorously.
- **Pillar 3 — Finite verification (Route A)**: existence of a prime pair
  summing to every even `N` in `[2, 2·10^18]`. Encoded as an axiom hypothesis
  in `ProofPillars`, since the actual finite computational data lives
  outside the G26 sub-tree.

`HorizonGoldbach.lean` defines the framework data structures (`LossLedger`,
`U7PlatinumSeal`, `FiniteLedgerHash`) and the transfer-channel theorems
that quantify U7's behaviour. `HorizonCertified.lean` carries the
G29-certified dispersion-bound proofs and the Grand Bridge structure
theorem `grand_bridge`. The two files are *build-independent*: neither
imports the other. This independence was exploited when Phase 1a
(HorizonCertified) preceded Phase 1b (HorizonGoldbach) without risk of
cross-contamination.

## 3. Scope of This Baseline

### 3.1 In Scope (Watchlist v2)

Five targets from the Drive `programme v2` specification, all closed:

- `transfer_bound_at_4` — Numerical inequality `C_tr(4) < 25.1`. Closed
  in Phase 2.1 (`8783bae`).
- `transfer_absolute_margin` — Universal `∀ N ≥ 64, C_tr(N) < 1`. Closed
  in Phase 2.3 (`9337558`).
- `urysohn_smooth` — Smoothness of the Urysohn bump mollifier. Closed
  in Phase 2.4 (`bc78fdb`) via refactor.
- `C₂` definition + `C₂_pos` axiom — Twin-prime constant `> 0.66`.
  Closed jointly in Phase 2.2 (`01d9f0b`).
- `C₃` definition + `C₃_bound` axiom — Mellin decay constant `≤ 475`.
  Closed jointly in Phase 2.2 (`01d9f0b`).

See `manifests/G26_v5_watchlist_closed.json` section `watchlist_v2_closure`
for the canonical tabulation.

### 3.2 Out of Scope

Five `sorry`s preserved by construction:

- `R_F` (line 38), `Main` (line 41), `N_start` (line 275), `G_euler`
  (line 312) — definitional stubs. Each expects a non-trivial mathematical
  definition that the Drive source did not specify in-file. Replacing
  them with motivated definitions is a multi-week-to-multi-month
  endeavour per stub, depending on the mathematical content.
- `goldbach_conditional_GRH` (line 305) — the "crown jewel" theorem that
  asserts the conditional Goldbach result given a constructed
  `U7PlatinumSeal`. It depends on the full formal chain of the
  architecture plus GRH; far beyond the G26Verify perimeter.

Six structural axioms preserved by construction:

- `U1_to_U6_bound` (line 78, Loss Ledger budget)
- `spectral_energy_bound` (line 227, Spectral / U7)
- `PO4_coverage` (line 278, U7 Seal coverage overlap)
- `G_holomorphic` (line 315, R72bis)
- `G_bounded` (line 319, R72bis)
- `spectral_bridge_GRH` (line 323, R73 Guinand-Weil)

All six describe hypotheses that depend on modules that do not exist in
this sub-tree. They are not "axioms to remove" in the G26 track; they
are architectural placeholders that the broader programme would discharge
in their respective Lean libraries.

## 4. Achievements Summary

Key numbers, all extractable from the manifest:

- **11 theorems verified axiom-pure** under the whitelist
  `{propext, Classical.choice, Quot.sound, Lean.ofReduceBool,
  Lean.ofReduceNat}`. Five live in `HorizonGoldbach.lean`, six in
  `HorizonCertified.lean`.
- **5 of 5 watchlist v2 targets closed** (three `sorry`-bearing theorems,
  two `axiom`-with-`def := sorry` pairs converted to theorems with concrete
  definitions).
- **2 axioms removed** from the file inventory (`C₂_pos`, `C₃_bound` are now
  proved theorems).
- **0 `sorryAx` mentions** in the from-scratch build log.
- **12 imports** in `HorizonGoldbach.lean` (3 original + 9 added across
  Phases 1b, 2.1, 2.3, 2.4). **3 imports** in `HorizonCertified.lean`
  (unchanged since arrival from Drive).
- **From-scratch build duration**: 43 minutes 14 seconds, exit 0. Cache
  Mathlib pré-warmé; pure-source Mathlib rebuild non inclus.

Refer to the manifest for SHA-256 attestations, per-theorem axiom lists,
and the full commit chain.

## 5. Phase-by-Phase Narrative

### Phase 0 — Tooling and WIP Triage (commit `79e8d75`)

Introduced `tools/g26_cleanup/Loop-LakeBuild.ps1`, a guarded `lake build`
wrapper that refuses to proceed when forbidden files appear in the
staged index or working-tree diff. The forbidden list extends the three
build-system files (`lakefile.lean`, `lean-toolchain`, `lake-manifest.json`)
with the five CD12 Lean files belonging to a separate Lean project
(F-MT-004), which were untracked in the working tree but must not be
touched. Matching is by basename via `Split-Path -Leaf` rather than full
path, so `Goldbach/M3cTerminalCD12Interval.lean` is caught correctly.

The initial `audit/g26_baseline.md` recorded the discipline boundary and
the watchlist of (then) zero real `sorry`s in tracked `Goldbach/**.lean`.

Pre-existing WIP from `main` (five `.lean` files unrelated to G26) was
stashed under `stash@{0}: pre-G26-WIP-2026-05-12` to keep the tracked
tree clean before Phase 1.

### Phase 1a — HorizonCertified Compiles, G29 6/6 Axiom-Pure (`0e16e17`)

The two Drive files arrived via base64-encoded transmission across the
session boundary. A subtle markdown rendering bug had collapsed blank
lines inside ```lean fences in an initial plain-text transmission,
causing a 35-byte deficit and SHA mismatch. The base64 round-trip with
fail-closed SHA verification became the reliable transmission protocol.

After decoding, three cosmetic Drive-source corruptions were repaired
to restore exact byte-identity with the canonical Drive SHA: a French
slip ("est que pour tous" → "is that for all"), a phantom status line
in the final comment block, and an extra `=` in a section separator.
Total +49 bytes restored; after restoration, `HorizonCertified.lean`
matched `00b394fc4aa58e0a658d3ed996fcd2a6b199c1592239aab4a7705c7f9ab15909`.

Two compile-blocking issues were then fixed: (a) `splitCount` used an
unbounded existential predicate inside `Finset.filter`, which Lean 4.15
could not synthesise as `DecidablePred`; replacing with bounded
existentials over `PrimeSet a` (which `Finset.decidableBEx` handles
directly) sufficed without invoking `Classical`. (b) An orphan
doc-comment `/-- Status of each sorry... -/` preceded the `end`
keyword with no declaration in between, causing a parse error;
demoting to a plain `/- ... -/` comment fixed it.

Six `#print axioms` lines were appended after `end Horizon.Certified`
to verify each of the six G29-certified theorems: `beta_exceeds_half`,
`ci_lower_exceeds_half`, `fit_quality`, `A_star_is_finite`,
`dispersion_bound_unconditional`, `dispersion_converges_to_zero`. All
showed `[propext, Classical.choice, Quot.sound]` only — kernel axioms.

A separate fix in this commit: `Loop-LakeBuild.ps1`'s
`Invoke-LakeBuildOnce` was capturing `lake`'s stdout into the function's
return-value stream, so the caller's `$code` was an array rather than
the exit integer; piping `lake build $Target | Out-Host` cleared the
function output so only the cast `[int]$LASTEXITCODE` returned. Without
this fix, no Phase 1a / 1b / 2 build would have shown a successful exit.

### Phase 1b — HorizonGoldbach Compiles Under Lean 4.15 (`12b78e9`)

Five missing imports were added so `HorizonGoldbach.lean` would
elaborate: `Mathlib.Analysis.SpecialFunctions.{Log.Basic, Exp,
Pow.Real}`, `Mathlib.Analysis.Calculus.ContDiff.Basic`,
`Mathlib.Data.Complex.Basic`. These cover `Real.log`, `Real.exp`,
`Real.rpow`, `ContDiff`, and `ℂ`.

The parameter `(seal : U7PlatinumSeal)` in `goldbach_conditional_GRH`
was renamed to `(s : U7PlatinumSeal)` — `seal` became a Lean 4.15
keyword (the `seal …` command), and the parameter occurs only inside
the `sorry`-filled body, so the rename has no external call-sites.

A free silencing: `(ha : a > B)` in `dispersion_bound_unconditional`
became `(_ha : a > B)` (Lean convention for intentionally unused
parameter, since the simplified proof goes through `Finset.card_filter_le`
without consuming the hypothesis).

The first build attempt was a clean success on the first try: exit 0
in 12 s, exactly ten `sorry`-bearing-warnings matching the original
inventory, zero errors.

### Phase 2.1 — Close transfer_bound_at_4 (`8783bae`)

The theorem `C_tr(4) < 25.1` reduces, via `log 4 = 2·log 2` and
`4^(-7/4) = 2^(-7/2)`, to a numerical inequality `2898·(log 2)² < 2^(21/2)`
solvable with `nlinarith` plus the decimal bound `Real.log_two_lt_d9`.
The proof imitates the existing pattern in
`Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean:460-469`.

A single STOP-rapport was required: `Real.log_two_lt_d9` lives in
`Mathlib.Data.Complex.ExponentialBounds`, which is not transitively
imported by `Mathlib.Data.Complex.Basic`. Adding it as a ninth import
(despite the misleading name — the file holds real-valued log/exp/π
bounds) is necessary and minimal. After authorisation, the proof
compiled on the first run after the import, with `nlinarith` digesting
the quadratic-in-log times non-rational constant in one shot.

### Phase 2.2 — Constants Cleanup C₂ and C₃ (`01d9f0b`)

`C₃` was trivialised: the Drive source had `noncomputable def C₃ : ℝ :=
sorry` and `axiom C₃_bound : C₃ ≤ 475` with no in-file mathematical
specification — only a doc-string referencing an external Richardson
extrapolation at 50 digits. Redefining `def C₃ : ℝ := 475` makes
`C₃_bound : C₃ ≤ 475 := le_refl _` true by reflexivity, and the
downstream contract `C₃ ≤ 475` is identically preserved.

`C₂` (the Hardy-Littlewood twin-prime constant `≈ 0.6601618`) was defined
as a finite rational partial product over odd primes up to 100,
cast to ℝ. The product converges from above (each factor `1 - 1/(p-1)²`
is less than 1), so any partial product exceeds the limit; the partial
to `p ≤ 100` exceeds `0.66` with a margin of about 2.4·10⁻³.
`C₂_pos : C₂ > 0.66` is proved by `native_decide` on the rational
inequality `C₂_rat > 66/100`, lifted to ℝ via an explicit
`((66 : ℚ) / 100 : ℝ)` bridge (Lean's `exact_mod_cast` does not match the
decimal literal `0.66` directly against the rational cast).

The initial attempt used `Finset.range 1001` (≈ 168 odd primes ≤ 1000)
for fidelity to the true twin-prime constant; this overflowed Lean's
`maxRecDepth` during elaboration of `Finset.filter`. The fallback to
`range 101` (24 odd primes) elaborates trivially and still exceeds the
threshold with comfortable margin. `C₂_pos` consumes
`Lean.ofReduceBool` (the `native_decide` axiom), which the project's
whitelist accepts.

### Phase 2.3 — Close transfer_absolute_margin (`9337558`)

Universal quantification `∀ N ≥ 64, C_tr(N) < 1` was the most
substantive proof of the watchlist. Before writing any code, Phase 2.3.0
was a 15-30 minute targeted reconnaissance of Mathlib's monotonicity
infrastructure. The decisive finding: `Real.log_div_self_rpow_antitoneOn`
in `Mathlib.Analysis.SpecialFunctions.Log.Monotone` states that
`log x / x^a` is antitone on `{x | exp(1/a) ≤ x}` for any `a > 0`. With
`a = 7/8`, this gives antitonicity of `log x / x^(7/8)` on
`[exp(8/7), ∞)`, applicable to `[64, ∞)` since `log 64 = 6 log 2 > 8/7`.

The proof composes (a) antitonicity from `log_div_self_rpow_antitoneOn`,
(b) squaring preservation via `pow_le_pow_left₀` on non-negatives,
(c) the algebraic identity `(log x / x^(7/8))² = (log x)² / x^(7/4)` via
`div_pow` + `Real.rpow_mul`, (d) scalar multiplication by `80.5`, and
(e) the numerical bound `C_tr(64) < 1` decomposed as `(log 2)² < 0.481`
and `2^(21/2) > 1448` (from `(2^(21/2))² = 2097152 > 1448² = 2096704`).

The proof passed on the first compilable attempt (~50 lines, 1
clean-up iteration for two API-drift deprecations: `pow_le_pow_left →
pow_le_pow_left₀` and `div_lt_iff → div_lt_iff₀`). The reconnaissance
investment paid off by a factor of roughly 3-5x relative to the
derivative-based proof initially anticipated.

### Phase 2.4 — Refactor urysohn_mollifier via ContDiffBump (`bc78fdb`)

The reconnaissance in Phase 2.0 had identified a defect in the Drive
definition of `urysohn_mollifier`: on `Set.Icc (1/2) 2`, at the
boundary points `x = 1/2` and `x = 2`, the formula evaluates `1 - g(x)²`
to 0 (since `g(±1) = ±1`); Lean's classical real division returns
`1 / 0 = 0`, so the if-branch returns `exp(1) = e ≈ 2.718` rather than
the limiting 0. The function is discontinuous at the boundary, and
`ContDiff ℝ ⊤ urysohn_mollifier` is mathematically false. This was the
most significant semantic divergence in the entire programme.

The ratified fix (path B in the reconnaissance) refactors
`urysohn_mollifier` as a thin wrapper over Mathlib's `ContDiffBump`
structure: a bump centred at `5/4` with `rIn = 3/8`, `rOut = 3/4` so
the support is `[1/2, 2]`. The `ContDiffBump.contDiff` theorem then
proves smoothness essentially for free.

Two separate frictions surfaced during execution. First, the
`HasContDiffBump ℝ` typeclass instance is not in `BumpFunction.Basic`;
it lives in `BumpFunction.InnerProduct` (priority-100 instance via
`InnerProductSpace ℝ ℝ`). A STOP-rapport was issued; after
authorisation, both `Basic` and `InnerProduct` are imported explicitly.
Second, the theorem signature `ContDiff ℝ ⊤` was itself broken by API
drift: Lean 4.15's `ContDiff` takes `n : WithTop ℕ∞` where `⊤` now
denotes analyticity, not C^∞ smoothness. Bump functions are smooth
but not analytic, so the original signature is provably false under
current Mathlib. The fix is the notation `∞`, which is scoped in the
`ContDiff` namespace and resolves to `((⊤ : ℕ∞) : WithTop ℕ∞)` (the
inner top, lifted) — the canonical smooth level. `open scoped ContDiff`
was added to bring the notation into scope.

Five iterations were required to land the proof, all related to the
two issues above; once both were resolved, the proof body is a
single `exact urysohn_bump.contDiff` after a coercion-disambiguating
`show ContDiff ℝ ∞ (urysohn_bump : ℝ → ℝ)`.

## 6. Semantic Divergences from Drive Source

### 6.1 Divergence #1 — C₃ Trivialization

The Drive source declared `noncomputable def C₃ : ℝ := sorry` together
with `axiom C₃_bound : C₃ ≤ 475`. The doc-string identified `C₃` as
"the Mellin decay constant for the Urysohn mollifier" and asserted
"verified by Richardson extrapolation at 50 digits", but no in-file
formal specification of `C₃` was provided. No other code in
`G26Verify/` consumes `C₃` apart from `C₃_bound`. Phase 2.0
reconnaissance confirmed both points.

The pragmatic resolution: define `C₃ := 475` and prove `C₃_bound` by
`le_refl _`. The downstream contract `C₃ ≤ 475` is preserved
identically; any consumer relying on this guarantee is unaffected.
What is lost is the intended mathematical content of `C₃` as a Mellin
supremum — but that content was never formally present in the Drive
source. Reifying it would be a research programme in itself: pick a
weighted norm, prove a sup bound on a compact-support function under
the Mellin transform, and obtain ≤ 475 via majoration. No precedent
in Mathlib 4.15 for such a bound on this specific bump.

### 6.2 Divergence #2 — urysohn_mollifier Refactor

The Drive definition (piecewise `if x ∈ Set.Icc (1/2) 2 then exp(1 -
1/(1 - g(x)²)) else 0`) was *literally false* for the targeted
smoothness theorem under Lean's classical real division semantics. The
bug was identified during Phase 2.0 reconnaissance and surfaced
explicitly in the rapport; the user ratified a refactor via
`ContDiffBump` rather than a from-scratch patch of the piecewise
definition.

What is preserved: the downstream contract — a C^∞ bump function with
compact support `[1/2, 2]` and peak at centre `5/4`. The smoothness
theorem `urysohn_smooth` is now true (and proved kernel-only). What
is lost: the pointwise exact values of the explicit formula at every
`x ∈ Set.Ioo (1/2) 2`. Reconnaissance verified that no other function
in `G26Verify/` reads these values; the formula was only used
implicitly through the smoothness theorem.

A secondary signature drift, `ContDiff ℝ ⊤ → ContDiff ℝ ∞`, accompanies
this divergence but is not itself a semantic change — it is API drift
correction (see §7 entry 4), preserving the original intent of
C^∞-smoothness as it was meant in the Drive's Lean 4.6 era.

## 7. Lean 4.6 → 4.15 Migration Register

Four API-drift incidents were documented across Phases 1b through 2.4.
Each is preserved in the manifest's `lean_46_to_415_drift_register`
section. Useful for parallel programmes that may inherit the same
Mathlib pin or a similar 4.x snapshot.

### 7.1 `seal` Became a Lean 4.15 Keyword (Phase 1b)

The `seal …` command was introduced in Lean 4.15 to seal a definition's
reducibility. Any identifier named `seal` in argument position must
be renamed. In `goldbach_conditional_GRH`, the parameter
`(seal : U7PlatinumSeal)` was renamed to `(s : U7PlatinumSeal)`. Since
the parameter occurs only inside the `sorry`-filled proof body, the
rename is purely local and breaks no external call-sites.

Parallel programmes inheriting the same pin should sweep their
identifiers for `seal` in argument or field position. The Phase 0
subsidiary sweep over `Goldbach/` confirmed this was the only
occurrence project-wide.

### 7.2 `pow_le_pow_left` → `pow_le_pow_left₀` (Phase 2.3)

Mathlib 4.15 systematically renames lemmas to add a `₀` suffix when
the version takes an explicit `≠ 0` (or `0 ≤`) hypothesis. The
unsuffixed name is deprecated, retained as an alias with a deprecation
warning. Direct rename in the proof body resolves both the warning
and the migration concern.

### 7.3 `div_lt_iff` → `div_lt_iff₀` (Phase 2.3)

Same pattern as above. The convention `lemma_name + ₀` for
non-zero-aware variants is now the canonical form in Mathlib 4.15.

### 7.4 `ContDiff ℝ ⊤` Reparameterised via `WithTop ℕ∞` (Phase 2.4)

In Lean 4.6-era Mathlib, `ContDiff` took `n : ℕ∞`, and `⊤ : ℕ∞`
denoted the smooth level (C^∞). In Lean 4.15 Mathlib, `ContDiff` was
generalised to `n : WithTop ℕ∞`; the outer `⊤ : WithTop ℕ∞` is the
new analytic level (strictly stronger than C^∞), while the inner
`⊤ : ℕ∞` lifted to `WithTop ℕ∞` is the smooth level. The lifted form
is denoted `∞` via the scoped notation in `ContDiff/FTaylorSeries.lean:114`.

Files that wrote `ContDiff ℝ ⊤` to mean smooth must either (a) use
`ContDiff ℝ ∞` and `open scoped ContDiff` in their preamble, or
(b) write the explicit `((⊤ : ℕ∞) : WithTop ℕ∞)`. The former is
idiomatic Mathlib usage.

This drift is the most significant of the four: it changes the
semantic meaning of a previously written theorem statement, not just
a lemma name. Programmes inheriting the same pin should audit for
`ContDiff ℝ ⊤` and decide whether they meant smooth or analytic.

## 8. Reproducibility

### 8.1 From-Scratch Build

The canonical reproducibility check is `lake clean` followed by
`lake build Goldbach.G26Verify.HorizonGoldbach
Goldbach.G26Verify.HorizonCertified`. On the development host, this
takes 43 minutes 14 seconds (2594 seconds), exits 0, and the build
log contains zero `sorryAx` mentions.

Pre-requisite: the Mathlib package cache must be present at
`.lake/packages/mathlib` (≈ 3.95 GB pre-warmed). The 43-minute
duration reflects only Lake's resolution and `.olean` replay across
the twelve transitive Mathlib imports; the Mathlib `.olean` files
themselves are cached, not recompiled. A consumer starting from an
empty Mathlib cache must add the cost of a full Mathlib source build
(roughly 30 to 60 additional minutes depending on hardware) before
the G26Verify rebuild can begin.

The manifest's `reproducibility_checklist` field gives the seven
canonical verification steps.

### 8.2 Axiom Audit Procedure

To independently verify the axiom purity of the eleven PROVED theorems,
either:

- Re-run the `#print axioms <name>` lines already present at the end of
  both source files. Lake's build output streams the resulting `info:`
  lines through stdout. Each line should report exactly the kernel
  triple `[propext, Classical.choice, Quot.sound]`, optionally extended
  by `Lean.ofReduceBool` for theorems that go through `native_decide`
  (only `C₂_pos` in the current state).
- Grep the build log: `Select-String -Pattern 'sorryAx' -SimpleMatch`
  must return zero matches.

Both checks are mechanical and idempotent. The manifest's
`verified_theorems` section is the canonical record of the expected
axiom lists per theorem.

## 9. Process Notes

### 9.1 Base64 Round-Trip as File Transmission Protocol

The two Drive files were transmitted across a session boundary. The
first attempt (plain text inside ```lean fenced code blocks) lost
about 35 bytes per file to a markdown rendering bug that collapsed
blank lines inside fences. Fail-closed SHA-256 verification caught the
discrepancy immediately; switching to base64 transmission (with the
file bytes encoded outside any code-fence rendering risk) reproduced
exact byte-identity.

The protocol is:

1. Encode the source file with `base64` (or `certutil -encode` on
   Windows) and ship the encoded payload inside a fence — base64 uses
   only `[A-Za-z0-9+/=]`, immune to markdown normalisation.
2. On the receiver side, strip all whitespace and decode with
   `[System.Convert]::FromBase64String`.
3. Write the resulting bytes via `[System.IO.File]::WriteAllBytes`.
4. Compare size and SHA-256 against the transmitted metadata. Refuse
   to proceed on any mismatch.

This protocol caught three independent corruptions in the
`HorizonCertified.lean` transmission (two slips, one stray equals sign)
and confirmed `HorizonGoldbach.lean` byte-exact on first decode.

### 9.2 STOP-Rapport-Ratification Cadence

Every phase ended with a brief, factual rapport summarising what
worked, what diverged from the prior plan, and any open questions.
Ratification was an explicit acknowledgement before the next phase
could begin. This discipline produced two concrete benefits:

- Every milestone is observable in the commit chain. The eight
  commits trace exactly the work that was approved, in the order it
  was approved.
- Every divergence from a prior plan was negotiated, not silently
  taken. The two semantic divergences (C₃ and `urysohn_mollifier`)
  and the `ContDiff` signature change were all surfaced in rapports
  and approved by name before execution.

The cadence was strict in the early phases (where the work was
mechanical and predictable) and remained strict in the later phases
(where the work involved real Mathlib navigation and substantive
mathematical content). Strictness did not slow execution; the average
time-per-phase was dominated by Lake builds and reconnaissance, not
by waiting for ratification.

### 9.3 Reconnaissance Before Substantive Work

Two reconnaissance phases — Phase 2.0 (general survey of the five
targets) and Phase 2.3.0 (targeted survey for the monotonicity
infrastructure) — bracketed Phase 2. Each was bounded at 15-30 minutes,
strictly read-only, and produced a single report listing the relevant
Mathlib lemmas, the proof sketch, and the estimated difficulty.

Phase 2.0 surfaced the `urysohn_mollifier` definition bug and the
`C₃` non-specification, both of which would have caused multi-hour
detours if discovered mid-proof. Phase 2.3.0 surfaced
`Real.log_div_self_rpow_antitoneOn`, turning a 4-8 hour
derivative-based proof into a 2-4 hour antitone+squaring proof.

The pattern is reliable: a 15-30 minute up-front reconnaissance
typically saves a factor of 3 to 5 on subsequent execution time when
the Mathlib terrain is unfamiliar. The cost is recouped in the first
iteration that does not have to be rolled back.

## 10. Future Work

### 10.1 Near-Term (G26 Closure)

The four remaining definitional stubs (`R_F`, `Main`, `N_start`,
`G_euler`) and the crown jewel theorem (`goldbach_conditional_GRH`)
together account for the five out-of-scope `sorry`s. Closing the
definitional stubs would require, for each:

- `R_F` — a concrete smoothed representation count, likely involving
  a Schwartz-bump-weighted analogue of `R`. A research-level definition
  in itself.
- `Main` — the Hardy-Littlewood main term, an explicit `2 N ∏ ...`
  product over primes. Closer to formalisable than `R_F` but still
  multi-week.
- `N_start` — a chosen `ℕ` satisfying `N_start ≤ N₀` for the U7 Seal.
  Trivial as a placeholder (any number ≤ `4·10^18`) but the
  surrounding U7 architecture would need to consume it meaningfully.
- `G_euler` — the Euler-product residual function used in the
  Riemann Bridge. Requires importing or re-developing the relevant
  L-series infrastructure.

None of these are within the G26 watchlist scope. They are listed here
so a future contributor can decide whether to pick one up.

### 10.2 Long-Term (Out-of-Scope for G26)

`goldbach_conditional_GRH` is the architecture's "if all three pillars
hold, then Goldbach for `N ≥ 2`" theorem. Its proof requires the full
formal chain (R72bis, R73, R74) plus a Lean-formalised GRH hypothesis.
This is the dependent of all the structural axioms preserved in §3.2;
discharging them would be the natural follow-on programme, requiring
work in separate Lean libraries (`HorizonMFE`, `HorizonMT`, `HorizonG80`,
etc., visible in the parallel `goldbach_lean_v2/` checkout).

The six preserved axioms (`U1_to_U6_bound`, `spectral_energy_bound`,
`PO4_coverage`, `G_holomorphic`, `G_bounded`, `spectral_bridge_GRH`)
are the natural shopping list for that programme. None of them are
within the G26 `G26Verify/` perimeter.

## 10. Phase 5 Cross-Module Fusion (v6)

After the v5 watchlist closure was tagged (`g26-v5-watchlist-closed-r1`,
commit `b32b8a2`), a follow-on programme was conducted on branch
`feat/g26-g29-fusion` to realise the architectural fusion between
`HorizonGoldbach.lean` and `HorizonCertified.lean`. The fusion had
been deferred from Phase 4 as the natural v6 amendment cycle.

### 10.1 What changed

Two surgical edits to `HorizonCertified.lean` (Phase 5.2, commit
`1c7ddd4`, and Phase 5.3, commit `d28fe3f`):

- Added `import Goldbach.G26Verify.HorizonGoldbach` after the three
  Mathlib imports. No namespace clash: `Horizon.Certified` is a
  proper sub-namespace of `Horizon`.
- Retyped the `ProofPillars.loss_ledger_closed` field from a
  placeholder `Prop` to an explicit reference to the G26-side
  `Horizon.LossLedger` / `Horizon.U7PlatinumSeal` structures:

  ```lean
  -- Before (v5, since Phase 1a):
  loss_ledger_closed : Prop

  -- After (v6, Phase 5.3):
  loss_ledger_closed : ∀ _s : Horizon.U7PlatinumSeal, ∀ N : ℕ,
    N ≥ 4 → ∃ L : Horizon.LossLedger, L.isClosed
  ```

`HorizonGoldbach.lean` was not modified (SHA unchanged at
`b1b33b86…`). `HorizonCertified.lean` SHA moved from `3bf0cdfe…`
(6 984 B) to `b6147532…` (7 456 B) — a delta of 472 bytes, reflecting
the added import line, the retyped field, and the documenting
comment.

### 10.2 Predicted vs observed (calibration archive)

The Phase 4 ratification, paper v2 §4.7, and the Phase 5 design
prompt all anticipated that the fusion would *expose* the six G26
structural axioms (`U1_to_U6_bound`, `spectral_energy_bound`,
`PO4_coverage`, `G_holomorphic`, `G_bounded`, `spectral_bridge_GRH`)
in the transitive axiom dependency of `grand_bridge`, making the
R74 perimeter visible from a single `#print axioms` invocation.

This prediction proved incorrect. The Phase 5.4 axiom audit
(committed at `35de0f7`, full report in
`audit/phase5_axiom_delta.md`) found **zero axiom delta** across
all 11 verified theorems between r1 and v6: identical lists, zero
new `sorryAx` introductions.

The diagnosis: `grand_bridge`'s proof body never consumes
`P.loss_ledger_closed` in the current G26Verify scope. The
small-N branch invokes `P.finite_verified` (Pillar 3); the
large-N branch is `sorry` (the GRH dependency, preserved per
the watchlist closure discipline). The structural G26 axioms
become consumed witnesses only at the call site that constructs
a concrete `ProofPillars` instance and supplies a real
`LossLedger.isClosed` proof. No such call site exists in
`G26Verify/`.

The methodological lesson: *predictions about transitive axiom
exposure require checking that callers actually consume the
relevant pillar. Type signatures alone do not propagate axioms.*
This is now archived in the calibration log for future
programmes.

### 10.3 What the fusion accomplishes

The improvement is **type-structural, not axiomatic**:

- Before: any Lean term of any `Prop` type satisfied the
  `loss_ledger_closed` field. A caller could pass `True`, `1 = 1`,
  or any other proposition as a vacuous witness; the contract
  between G26's LossLedger architecture and G29's ProofPillars
  was documentation-only.
- After: any caller must produce a Lean term of the seal-typed
  proposition. Lean's typechecker enforces the contract at
  construction time. The signature is now an executable spec.

The fusion makes the architectural contract *machine-enforceable*
without changing the provable content. Any future caller that
constructs a `ProofPillars` will at that point cause the G26
structural axioms to fire as witnesses in their concrete proof —
that is when the prediction would have become observable. Until
then, the axioms remain inert.

### 10.4 v6 release

Phase 5 closed with commits on `feat/g26-g29-fusion`:

- `1c7ddd4` Phase 5.2 — Import HorizonGoldbach into HorizonCertified
- `d28fe3f` Phase 5.3 — ProofPillars.loss_ledger_closed seal-typed
- `35de0f7` Phase 5.4 — Axiom audit delta documentation
- `ff47434` Phase 5.5 — Manifest v2.0 G26_v6_fusion_merged
- (this commit) Phase 5.6 — Bundle mirror + §10 baseline update

Phase 5.7 merges the branch fast-forward to `main` and creates the
annotated tag `g26-v6-fusion-merged`. The bundle
`g26_v6_arxiv/` is provided as a mirror of `g26_v5_arxiv/` with
the post-fusion artefacts and the v2.0 manifest.

The v5 tag `g26-v5-watchlist-closed-r1` (commit `b32b8a2`) remains
in place as a historical reference. The v5 manifest
(`manifests/G26_v5_watchlist_closed.json`) is preserved alongside
the v6 manifest in `manifests/`, each pointing to its respective
release.

## 11. Manifest Cross-Reference

Machine-verifiable details (SHA-256 attestations, per-theorem axiom
lists, full commit chain, drift register entries, divergence
specifications, reproducibility checklist) live in the manifests:

- v5 watchlist closure:
  [manifests/G26_v5_watchlist_closed.json](../manifests/G26_v5_watchlist_closed.json)
  (tag `g26-v5-watchlist-closed-r1`, commit `b32b8a2`)
- v6 fusion merged (current):
  [manifests/G26_v6_fusion_merged.json](../manifests/G26_v6_fusion_merged.json)
  (tag `g26-v6-fusion-merged`, commit at Phase 5.7 merge)

The manifest is the authoritative record. This document is its
human-readable companion. If the two disagree on a numerical claim,
the manifest wins.
