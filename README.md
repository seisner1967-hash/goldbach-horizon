# Horizon Goldbach — Lean 4 Formalization

## Status: Phase VI (sealed) + Phase VII v2 (interface contracts + partial proofs)

A modular Lean 4 formalization of a conditional framework for the Strong Goldbach Conjecture.

**Preprint:** [OSF Thesis Commons](https://osf.io/preprints/thesiscommons/6d83p_v1)

## What this project IS

A machine-verified conditional reduction: if five explicit analytic hypotheses are supplied, and the AMS computational verification up to 4×10¹⁸ is granted, then the Strong Goldbach Conjecture follows.

Phase VII v2 adds 5 modules that name, formalize, and partially reduce the 5 analytic hypotheses. It does NOT discharge them.

## What this project is NOT

An unconditional proof of the Strong Goldbach Conjecture.

## Build

Lean 4 v4.15.0 / Mathlib v4.15.0 (commit 9837ca9d)

## Modules: 23 total (18 Phase VI + 5 Phase VII v2)

### Phase VII v2 — 29 theorems, 0 sorry

| Module | Theorems | Description |
|--------|----------|-------------|
| PCBGallagher | 8 | verified_500, circle method reduction |
| HerglotzPositivity | 5 | Rayleigh bound, spectral positivity |
| A2PureAnalytic | 5 | FormBoundData, KLMN, two-stage A2 |
| MellinJackson | 5 | Mellin transform, Jackson bound |
| FredholmOTSA | 6 | Fredholm determinant, Jost-Pais |

## License

CC-By Attribution 4.0 International — Serge Durand, Horizon Research Programme
