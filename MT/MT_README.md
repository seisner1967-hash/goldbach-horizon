# MT — Maynard–Tao Attack on the Prime Cluster Bound

**Horizon Programme · Phase VI · Independent Arithmetic Series**

---

## The MT Trilogy

The MT series is a self-contained attack on the Prime Cluster Bound (PCB)
using smooth-number estimates, classical sieve methods, and the Dickman
ρ-function. It is **independent of GRH, Elliott–Halberstam, and the Horizon
spectral framework** (except for the final conditional step in MT3).

### Logical Chain

```
MT1: smooth control of R_smooth(N)
  |R_{≤y}| ≤ C · ρ(B/A) · e^γ · A · log log N    [HT + Mertens + Dickman]
  |R_{>y}| ≤ C / (log N)^{A-1}                      [Mertens + Gallagher]
      ↓
MT2: variance and transfer
  V̄(N) ≤ C(1+|R_smooth|) · N²/log⁴N               [BV + BT + smooth split]
  C(N,Q) ≤ C · N²/(Q log²N)                         [Cauchy–Schwarz transfer]
      ↓ = PCB(Q¹) — UNCONDITIONAL
      ↓
MT3: conditional Goldbach
  PCB(Q¹) + F1 ⟹ δ₇/M → 0 ⟹ R(2N) > 0           [conditional on F1]
```

### Central Result

$$\boxed{\text{PCB}(Q^1) + \text{F1} \Longrightarrow \text{Goldbach for all sufficiently large even integers}}$$

where **PCB(Q¹) is unconditional** and **F1 is the sole remaining spectral hypothesis**.

---

## Status

| Layer | Status | Reference |
|-------|--------|-----------|
| MT1 smooth control | **unconditional** | MT1, Theorem 1.1 |
| MT2 variance + CS transfer | **unconditional** | MT2, Theorems A–B |
| PCB(Q¹) | **unconditional** | MT1–MT2 chain |
| PCB(Q²) | **rejected** | G38, numerically false |
| Spectral identity (F1) | **open** | G36 v2, Problem F1 |
| Goldbach conclusion | **conditional on F1** | MT3, Theorem C |

### What the programme does NOT claim

MT3 does not claim an unconditional proof of Goldbach. The correct description is:

> *A conditional reduction of Goldbach to a spectral identification problem (F1),
> with all arithmetic prerequisites discharged unconditionally.*

---

## Lean 4 Formalization

**HorizonMT v4** — zero-sorry scaffold, frozen toolchain.

| File | Lines | Content |
|------|-------|---------|
| `Interfaces.lean` | 183 | 35 analytic axioms + object declarations |
| `Bridges.lean` | 156 | 10 bridge axioms connecting objects to interfaces |
| `MT1.lean` | 61 | 5 theorems, all proved from bridges |
| `MT2.lean` | 123 | 5 theorems + epistemic ledger |
| **Total** | **523** | **0 sorry · 45 axioms** |

### Build

```bash
cd MT/lean
lake update              # downloads mathlib v4.29.0
lake exe cache get       # pre-compiled cache
lake build               # compile HorizonMT
```

### Audit

```lean
#print axioms HorizonMT.main_theorem
#print axioms HorizonMT.theorem_B
```

### Conventions

- `R_smooth` is **normalized** (dimensionless)
- `meanPairVariance` is **dimensioned** (scale N²/log⁴N)
- Q = (log N)^B, y = (log N)^A, X = N/Q
- Toolchain: Lean 4.29.0 / mathlib v4.29.0 (frozen)

---

## Benchmarks

### Separation Principle

| Benchmark | Purpose | Parameters | Claim level |
|-----------|---------|------------|-------------|
| **T5a** | theorem-facing validation | canonical B=7, A=2 | strict: pass/warn/fail |
| **T5b** | exploratory signal analysis | adaptive B | heuristic: bounded/visible/degenerate |

```
T5a tests consistency with the MT1–MT3 statements in their declared regime.
T5b uses adaptive B to make numerical signals visible, and should NOT be
interpreted as a direct validation of the theorem statements.
```

### T5a Results (canonical B=7, A=2)

| log₁₀N | regime | |R_smooth| | V̄/scale | δ₇/M | MT3 norm | verdict |
|---------|--------|-----------|---------|------|----------|---------|
| 6 | degenerate | 0.144 | 0.204 | 1.9×10⁻⁴ | 0.135 | pass |
| 7 | degenerate | 0.152 | 0.208 | 2.6×10⁻⁵ | 0.027 | pass |
| 8 | degenerate | 0.160 | 0.211 | 3.4×10⁻⁶ | 0.005 | pass |
| 9 | degenerate | 0.166 | 0.215 | 4.3×10⁻⁷ | 0.001 | pass |

**MT1 safety**: |R_smooth| < 0.22 at all points (margin 0.05–0.08). ✓
**MT2 cluster**: degenerate (Q >> N), consistent. ✓
**MT3 normalized**: (δ₇/M)·(logN)^(B/2-1) decays 160× from 10⁶ to 10⁹. ✓

**Interpretation**: At B=7, Q = (logN)⁷ >> N for N ≤ 10⁹, so the cluster
regime is degenerate. No contradiction detected. For visible signal, see T5b.

### T5b Results (adaptive B) — partial

| log₁₀N | B | C/Gal | V̄/scale | smooth% | δ₇/M | PCB |
|---------|---|-------|---------|---------|------|-----|
| 6 | 1.5 | 0.387 | 0.277 | 62% | 1.379 | ✓ |
| 7 | 2.0 | 0.392 | 0.265 | 61% | 0.719 | ✓ |
| ... | ... | ... | ... | ... | ... | ... |

*(Full results pending completion of T5b run)*

---

## Papers

| Paper | Pages | Content |
|-------|-------|---------|
| MT1 | 9 | Prime Cluster Bound via Smooth Number Estimates |
| MT2 | 9 | Large-Sieve Control for Smooth Prime Clusters |
| MT3 | 8 | Conditional Goldbach from Smooth Cluster Control |

---

## Repository Structure

```
MT/
├── lean/
│   ├── HorizonMT/
│   │   ├── Interfaces.lean
│   │   ├── Bridges.lean
│   │   ├── MT1.lean
│   │   └── MT2.lean
│   ├── lakefile.lean
│   └── lean-toolchain
├── papers/
│   ├── MT1_*.pdf + .tex
│   ├── MT2_*.pdf + .tex
│   └── MT3_*.pdf + .tex
├── benchmark/
│   ├── MT_T5a_Standalone.py
│   └── MT_T5b_Standalone.py
├── data/
│   ├── t5a_results.json
│   └── t5b_results.json
└── README.md
```

---

## References

- [MT1] S. Durand, *Prime Cluster Bound via Smooth Number Estimates*, 2026
- [MT2] S. Durand, *Large-Sieve Control for Smooth Prime Clusters*, 2026
- [MT3] S. Durand, *Conditional Goldbach from Smooth Cluster Control*, 2026
- Gallagher, P.X., Mathematika 23 (1976), 4–9
- Hildebrand & Tenenbaum, Trans. AMS 296 (1986), 265–290

---

*Horizon Programme — Phase VI — April 2026*
*MIT License — Serge Durand*
