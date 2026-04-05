# Horizon Goldbach

**A Machine-Verified Conditional Framework for the Strong Goldbach Conjecture**

Lean 4 formalization — Phase VI (sealed) + Phase VII v2 + CompactZone (proved) + KLMN (reduction)

## Status

| Metric | Value |
|--------|-------|
| Root modules | 36 (18 Phase VI + 5 Phase VII + 9 CompactZone + 4 KLMN) |
| Lean toolchain | v4.15.0 |
| Mathlib | v4.15.0 (commit `9837ca9d`) |
| `sorry` in CompactZone | **0** |
| `axiom` in CompactZone | **0** |
| `sorry` in KLMN | 2 (whole-line Sobolev trace + assembly, documented) |
| `axiom` in KLMN | 0 |

## Main result

The Lean kernel certifies the following conditional reduction:

> If five explicit analytic hypotheses are supplied, and the AMS computational verification
> up to 4 × 10¹⁸ is granted, then every even integer n ≥ 4 is a sum of two primes.

## CompactZoneBoundStrong — PROVED

The compact-zone domination bound is now a **theorem**, not a hypothesis:

```
theorem compactZoneBoundStrong_all : CompactZoneBoundStrong
theorem compactZoneBound_all : Goldbach.CompactZoneBound
theorem po_a2_stage1_all : Goldbach.Roadmap.PO_A2_stage1
```

The proof covers all 20 cells of [log 2, 20] with three strategies:
- **Cells 0–1**: per-prime rational bounds for {2,3,5,7,11,13,17,19} via Taylor log/sqrt enclosures
- **Cells 2–9**: count × max-term with prime-count filter and `native_decide` verification
- **Cells 10–19**: tail bound for primes > 9973

This reduces the external trust boundary from 6 to **5 open hypotheses**.

## Trust boundary (5 open hypotheses)

| Hypothesis | Module | Content |
|-----------|--------|---------|
| `KLMNHypothesis` | A2PureAnalytic | KLMN perturbation theory (Reed-Simon X.17) |
| `PCBAsymptotic` | PCBGallagher | Gallagher/circle-method asymptotic |
| `SpectralPositivityHypothesis` | HerglotzPositivity | Herglotz-type resolvent positivity |
| `BandwidthSufficient` | MellinJackson | Mellin-Jackson bandwidth absorption |
| `FredholmOTSAHypothesis` | FredholmOTSA | Fredholm/Jost-Pais windowed approximation |

### Discharged (no longer external)

| Former hypothesis | Status | Module |
|------------------|--------|--------|
| ~~`CompactZoneBound`~~ | **PROVED** | CompactZone/NumeratorAll |

## KLMN reduction

The KLMN infrastructure decomposes `KLMNHypothesis` into more elementary components:

```
KLMNHypothesis = SobolevTraceInequality ∧ CellWeightBound
```

Key proved theorems (0 sorry):
- `sobolev_trace_bounded_interval`: bounded-interval Sobolev trace inequality (coefficient corrected from 1/(b-a) to 2/(b-a))
- `formBoundData_of_infinitesimal`: infinitesimal form-bound → FormBoundData
- `klmnHypothesis_of_infinitesimal`: infinitesimal form-bound → KLMNHypothesis

Remaining sorry (2: whole-line trace inequality and assembly):
- `sobolevTraceInequality_proof`: trace inequality on ℝ (requires partition of unity or density argument)
- `infinitesimal_form_bound_of_sobolev_summable`: assembly of Sobolev + cell weights

## Module architecture

```
Goldbach.lean (root, 36 imports)
│
├── Phase VI (18 modules, sealed)
│   Basic, Collage, Framework, Thresholds, Interfaces,
│   AxiomsToLemmas, Budget, G43Budget, CompactWindowShadow,
│   SmallInstances, Roadmap, Status, ExpBounds,
│   A2CertificateData, ThresholdReal, PrimeLogEnclosures,
│   BreakpointGrid, A2Certificate
│
├── Phase VII v2 (5 modules)
│   PCBGallagher, HerglotzPositivity, A2PureAnalytic,
│   MellinJackson, FredholmOTSA
│
├── CompactZone (9 modules, 0 sorry, 0 axiom)
│   Defs          — W(Q), ratio_bound, Taylor bounds
│   Grid          — cell decomposition, monotonicity
│   Wire          — framework wiring (trivial path)
│   CellBounds    — rational certificate v1
│   CellBoundsStrong — rational certificate v2 + tail bounds
│   Strong        — Taylor upper bounds, sqrt bounds
│   Bridge        — conditional chain architecture
│   NumeratorBound — cells 10-19 proved
│   NumeratorAll  — ALL 20 cells proved → CompactZoneBoundStrong
│
└── KLMN (4 modules, 2 sorry, 0 axiom)
    Defs          — QuadForm, IsFormBounded, SobolevTrace
    SobolevProof  — bounded-interval trace inequality (PROVED)
    Sobolev       — trace inequality statements (1 sorry)
    Chain         — reduction chain (1 sorry)
```

## Build

```bash
git clone https://github.com/seisner1967-hash/goldbach-horizon.git
cd goldbach-horizon
lake exe cache get
lake build
```

## Scientific disclaimer

This is a conditional framework, not an unconditional proof of the Goldbach conjecture.
The five remaining analytic hypotheses are open mathematical problems. The contribution
is methodological: demonstrating that the conditional structure is logically sound and
machine-checkable, with an explicit and minimal trust boundary.

## References

- Repository: [github.com/seisner1967-hash/goldbach-horizon](https://github.com/seisner1967-hash/goldbach-horizon)
- Preprint: OSF Thesis Commons (pending moderation)
- Technical reports: Horizon Project R22–R24
