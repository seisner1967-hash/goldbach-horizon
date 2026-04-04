# Horizon Goldbach — Lean 4 Formalization Framework

A modular Lean 4 formalization of the logical skeleton of the Horizon Goldbach programme (Notes G38–G44 v5).

## What this repository proves — and does not

**This repository does NOT contain an unconditional proof of the Strong Goldbach Conjecture.**

It provides a **machine-verified conditional framework**: if five explicit analytic hypotheses are supplied and the external AMS computational range is granted, then Goldbach-strong follows by a machine-checked logical collage. The core theorem in `Status.lean`:

```lean
theorem whatLeanActuallyProves :
    ∀ (F : GoldbachFramework N0 AMSBound), GoldbachStrong
```

The repository also does **not** claim:

- an internal proof of any of the five remaining analytic inputs (A2-bridge, PCB/Gallagher, F1b/Herglotz, F1a/OTSA, G2/Mellin-Jackson);
- an independent operator-theoretic proof of essential self-adjointness;
- inclusion of the AMS computation up to 4 × 10¹⁸ as internal Lean code.

The package distinguishes carefully between what is proved **inside Lean**, what is provided as **external analytic input**, and what belongs to **external computation**.

## Status

**Release:** G44 v5

| Metric | Value |
|--------|-------|
| Modules | 18 root files |
| Lines | ~25 000 |
| `sorry` | 0 |
| `axiom` | 0 |
| `opaque` | 0 |
| `lake build` | verified |
| A2 stage-2 | proved internally |

Verify independently:

```bash
grep -Rnw Goldbach -e '\bsorry\b' --include="*.lean"
grep -Rnw Goldbach -e '^\s*axiom\b' --include="*.lean"
grep -Rnw Goldbach -e '^\s*opaque\b' --include="*.lean"
lake build
```

## What Lean certifies internally

- **Logical collage**: finite verified range + asymptotic range → Goldbach-strong (`Collage.lean`)
- **Framework wiring**: structured analytic interface → collage (`Framework.lean`, `Interfaces.lean`)
- **Threshold bounds**: 42 < log(N₀) < 43, N₀ ≤ AMSBound (`ThresholdReal.lean`)
- **Exponential bounds**: Taylor partial sums, geometric tail control (`ExpBounds.lean`)
- **1229 log-enclosures**: certified log(p) ∈ (lo/10⁹, hi/10⁹) for all primes p ≤ 9973 (`PrimeLogEnclosures.lean`)
- **A2 tail bound**: ∀ Q > 20, log(Q+1)/exp(Q) < 1/4, proved via Taylor lower bounds (`A2Certificate.lean`)
- **Budget arithmetic**: certified 0.78 + 0.11 < 1 margin (`Budget.lean`)
- **Trace positivity**: compact-window shadow model, Tr(K) ≥ 0 (`CompactWindowShadow.lean`)

## Repository layout

```
goldbach-horizon/
  Goldbach/
    Basic.lean                 Core definitions (GoldbachAt, GoldbachStrong)
    Collage.lean               Logical collage lemma
    Framework.lean             GoldbachFramework structure
    Thresholds.lean            Integer threshold constants
    Interfaces.lean            Structured analytic input types
    AxiomsToLemmas.lean        One-at-a-time refinement lemmas
    Budget.lean                Numerical budget layer
    G43Budget.lean             G43-specific budget check
    CompactWindowShadow.lean   Trace positivity model
    SmallInstances.lean        Small Goldbach instances (sanity)
    Roadmap.lean               Proof obligations decomposition
    Status.lean                Honest 3-level status
    ExpBounds.lean             Taylor bounds and log-enclosure API
    A2CertificateData.lean     1229 breakpoint enclosures (data)
    ThresholdReal.lean         Real-valued threshold bounds
    PrimeLogEnclosures.lean    1229 proved log(p) enclosures
    BreakpointGrid.lean        Grid/cell structure for certificates
    A2Certificate.lean         A2 stage-2 tail bound (theorem)
  Goldbach.lean                Root import aggregator
  lakefile.lean                Lake build configuration
  lean-toolchain               Lean version pin
  BUILD.sh                     Audited build script
  README.md
```

## Build

**Tested configuration:** Lean 4.15.0 + Mathlib (commit `9837ca9`)

```bash
# Standard build
lake update
lake exe cache get
lake build

# Audited build (incremental + sorry/axiom check)
bash BUILD.sh
```

Note: `PrimeLogEnclosures.lean` is the largest module (~22k lines) and may take 10–60 minutes to compile. The enclosure proofs may be split into generated sub-files for compilation feasibility.

## Changelog: v4.1 → v5

Version v5 is a trust-boundary cleanup, not a new analytical breakthrough.

- **Removed** `A2CertificateTrustedInstance.lean` (contained 2 axioms + 3 opaques trusting Python computation)
- **Removed** `BreakpointSoundness.lean` (depended on removed axioms)
- **Added** `A2Certificate.lean` — proves `tail_bound_A2` and `po_a2_stage2_proved` internally, with 0 sorry and 0 axiom
- **Updated** `Goldbach.lean` — 18 clean imports
- **Updated** `BUILD.sh` — honest grep-based audit (no hardcoded claims)

This upgrade concerns the internal certificate architecture only. It does not change the external status of the remaining analytic inputs of the global Goldbach framework.

## License

This repository accompanies the Horizon Goldbach notes (G38–G44 series). See the corresponding G44 documents for the formal status narrative.
