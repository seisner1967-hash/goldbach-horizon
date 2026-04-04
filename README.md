# Horizon Goldbach — Lean 4 Formalization

## Status: Phase VI (sealed) + Phase VII v2 (29 theorems, 0 sorry)

A modular Lean 4 formalization of a conditional framework for the Strong Goldbach Conjecture.

**Preprint:** [OSF Thesis Commons](https://osf.io/preprints/thesiscommons/6d83p_v1)  
**Toolchain:** Lean 4 v4.15.0 / Mathlib v4.15.0 (commit 9837ca9d)  
**Modules:** 23 total (18 Phase VI + 5 Phase VII v2)

---

## What this project IS

A **machine-verified conditional reduction**: if five explicit analytic hypotheses are supplied, and the AMS computational verification up to 4×10¹⁸ is granted, then the Strong Goldbach Conjecture follows as a compiled Lean theorem.

Phase VII v2 adds 5 modules that **name, formalize, and partially reduce** the 5 analytic hypotheses. It does **NOT** discharge them.

## What this project is NOT

An unconditional proof of the Strong Goldbach Conjecture.

---

## Build
```bash
lake update && lake exe cache get && lake build
```

Or incrementally: `bash BUILD.sh`

---

## Phase VII v2 — Analytic Offensive (5 modules, 29 theorems)

| Module | Theorems | Key results |
|--------|----------|-------------|
| PCBGallagher.lean | 8 | verified_500 (Goldbach to 500), circle method reduction |
| HerglotzPositivity.lean | 5 | Rayleigh bound for symmetric operators |
| A2PureAnalytic.lean | 5 | FormBoundData, KLMN formalized, two-stage A2 |
| MellinJackson.lean | 5 | Mellin transform, modulus of continuity, Jackson bound |
| FredholmOTSA.lean | 6 | Fredholm partial determinant, Jost-Pais consequence |

## Open hypotheses (trust boundary)

| Hypothesis | Required mathematics |
|------------|---------------------|
| PCBAsymptotic | Hardy-Littlewood circle method + Bombieri-Vinogradov |
| SpectralPositivityHypothesis | Herglotz representation theorem |
| CompactZoneBound | Interval arithmetic on [ln 2, 20] |
| KLMNHypothesis | Reed-Simon Theorem X.17 |
| BandwidthSufficient | Jackson approximation in Sobolev spaces |
| FredholmOTSAHypothesis | Trace-class operators + Jost-Pais theorem |

## Version history

| Version | Date | Modules | Description |
|---------|------|---------|-------------|
| G44 v4.1 | Mar 2026 | 16 | Initial sorry-free build |
| G44 v5 | Apr 2026 | 18 | Trust boundary cleanup |
| Phase VII v2 | Apr 2026 | 23 | 5 analytic offensive modules, 29 theorems |

## License

CC-By Attribution 4.0 International — Serge Durand, Horizon Research Programme
