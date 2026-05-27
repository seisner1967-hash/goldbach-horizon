# Horizon Goldbach

Lean 4 formal specification programme for a conditional architecture around the
binary Goldbach conjecture.

This repository does **not** claim an unconditional proof of Goldbach. Its goal
is narrower and auditable: decompose the proof architecture into Lean-checked
modules, prove the finite/combinatorial layer, and expose the remaining
analytic work as named local infrastructure obligations.

## Current Focus: TS15--TS25

The current sprint chain lives under:

```text
TS/Goldbach/Strong/
  TS15/
  TS16/
  TS17/
  TS18/
  TS19/
  TS20/
  TS21/
  TS22/
  TS23/
  TS24/
  TS25/
```

Status summary:

| Sprint | Object | Status | Meaning |
| --- | --- | --- | --- |
| TS15 | Short-interval reduction | `interface_compiled` | typed Lean interface for the local analytic residue |
| TS16 | Combinatorial discharge | `repo_committed` | finite counting lemma proved unconditionally |
| TS17 | Mellin-Jackson projection | `repo_committed_relative` | reduced to Mellin/Fourier infrastructure |
| TS18 | Short-interval second moment | `repo_committed_relative` | reduced to character bridge and large sieve infrastructure |
| TS19 | OTSA residual bound | `repo_committed_relative` | reduced to spectral, trace, and Mellin-tail controls |
| TS20 | Synthesis manuscript | documentation | final ledger and project roadmap |
| TS21 | Short-interval constant budget | `repo_committed_relative` | transports explicit constants such as Brun-Titchmarsh `K = 20` |
| TS22 | Energy scale renormalization | `repo_committed_relative` | makes the short-interval normalization scale explicit |
| TS23 | OTSA scale propagation | `repo_committed_relative` | transports TS22 scales into the OTSA residual ledger |
| TS24 | Closed-form scale bridge | `repo_committed` | proves the ceiling-budget scale is dominated by a padded closed form |
| TS25 | Padded-scale OTSA feasibility | `repo_committed_relative` | specializes OTSA propagation to the TS24 padded scale |

## What Is Proved

TS16 proves the finite combinatorial comparison:

```lean
TS16.Goldbach.pair_count_le_energy
```

This removes the previous local counting obligation from TS15. The proof uses
only finite sets, products, sigma finsets, and cardinality comparison: close
pairs are injected into energetic triples.

TS17, TS18, and TS19 are relative discharges. They do not hide assumptions as
global axioms; instead they pass the remaining analytic inputs as explicit
structures.

TS21 adds a budgeted version of the short-interval second-moment interface:

```lean
TS21.Goldbach.Problem_E1K
TS21.Goldbach.ShortIntervalPrimeSecondMomentK
TS21.Goldbach.BrunTitchmarshShortInterval
TS21.Goldbach.BrunTitchmarshLocalWindowBudget
```

This lets later threshold computations carry a concrete constant, currently
`K = 20`, instead of forcing the TS18-style estimate into the rigid `C <= 1`
shape too early. TS21 also records the scale-correct local-window transport:
a uniform bound `shortPrimeLocalCount x Q n <= B` implies
`shortPrimeEnergy x Q <= (x+1) * B^2`.

TS22 generalizes the downstream target by introducing:

```lean
TS22.Goldbach.ShortIntervalScale
TS22.Goldbach.Problem_E1Scale
TS22.Goldbach.brunTitchmarshClosedFormScale
TS22.Goldbach.BrunTitchmarshNatIntervalBound
TS22.Goldbach.ScaledLargeSieveInfrastructure
```

This keeps the raw TS15 energy intact while allowing Brun-Titchmarsh and large
sieve inputs to use their natural normalization scales. TS22 also provides an
interval bridge from a future natural-number Brun-Titchmarsh theorem to the
local window budget used by TS21, and a scale-aware large-sieve discharge:

```lean
TS18.Goldbach.DirichletCharacterBridge
  + TS22.Goldbach.ScaledLargeSieveInfrastructure S
  => TS22.Goldbach.Problem_E1Scale S K
```

TS23 connects the TS22 scale layer to the TS19 OTSA residual ledger:

```lean
TS22.Goldbach.Problem_E1Scale S K
  + TS23.Goldbach.ScaleToOTSAControl S
  + scaled OTSA coupling
  + TS23.Goldbach.ScaledOTSAAdmissible
  => TS19.OTSA.OTSAResidualBound R
```

TS24 closes the arithmetic scale-domination layer for Brun-Titchmarsh budgets:

```lean
TS22.Goldbach.BrunTitchmarshNatIntervalBound
  => TS24.Goldbach.Problem_E1Scale_from_natIntervalBound_paddedClosedForm
```

The padded closed form keeps the unavoidable `+1` loss from `Nat.ceil`
explicit, so no unproved rounding claim is smuggled into the closed-form scale.

TS25 packages the padded-scale OTSA entry point:

```lean
TS22.Goldbach.BrunTitchmarshNatIntervalBound
  + TS23.Goldbach.ScaleToOTSAControl
      TS24.Goldbach.brunTitchmarshPaddedClosedFormScale
  + TS23.Goldbach.ScaledOTSAAdmissible
  + local OTSA coupling
  => TS19.OTSA.OTSAResidualBound R
```

## Remaining Analytic Infrastructure

The final TS20 ledger names the remaining analytic obligations:

| Obligation | Role |
| --- | --- |
| `MellinFourierNormBridge` | logarithmic Mellin/Fourier norm bridge |
| `FourierTailInfrastructure` | Plancherel tail estimate |
| `DirichletCharacterBridge` | character orthogonality and bridge error |
| `LargeSieveInfrastructure` | local large-sieve estimate with `C <= 1` |
| `BrunTitchmarshLocalWindowBudget` | pointwise short-window prime count budget |
| `BrunTitchmarshShortInterval` | stronger threshold-form short-interval budget, currently `K = 20` |
| `BrunTitchmarshScaleBridge` | domination of the exact integer window-budget scale by a chosen closed-form scale |
| `BrunTitchmarshNatIntervalBound` | natural-interval prime-count Brun-Titchmarsh theorem |
| `ScaledLargeSieveInfrastructure` | large-sieve estimate targeting an explicit `ShortIntervalScale` |
| `ScaleToOTSAControl` | analytic cost of carrying a TS22 scale into OTSA |
| `ScaledOTSAAdmissible` | local numerical threshold for scaled OTSA constants |
| `PaddedScaleAnalyticInfrastructure` | TS25 package for the padded scale, interval BT, and OTSA admissibility |
| `KernelSpectralControl` | OTSA spectral-kernel control |
| `TraceContributionControl` | OTSA trace/pole control |
| `MellinTailDecay` | OTSA Mellin-tail decay |
| `OTSACouplingHypothesis` | residual coupling inequality |

These are the objects that must be instantiated by genuine analytic proofs to
turn the relative architecture into an unconditional formal proof route.

## Build

The repository uses Lean 4.15.0 / Mathlib v4.15.0.

Typical build for the current sprint chain:

```powershell
lake build TS.Goldbach.Strong.TS16.CombinatorialDischarge `
  TS.Goldbach.Strong.TS17.MellinJacksonDischarge `
  TS.Goldbach.Strong.TS18.SecondMomentDischarge `
  TS.Goldbach.Strong.TS19.OTSAResidualDischarge `
  TS.Goldbach.Strong.TS21.SecondMomentBudgetDischarge `
  TS.Goldbach.Strong.TS22.BrunTitchmarshScaleDischarge
```

Build all TS15--TS22 targets:

```powershell
lake build TS.Goldbach.Strong.TS15.ShortIntervalSecondMoment `
  TS.Goldbach.Strong.TS15.ProblemE1ShortIntervals `
  TS.Goldbach.Strong.TS15.PCB_Q1_Discharge `
  TS.Goldbach.Strong.TS15.MellinJacksonFourier `
  TS.Goldbach.Strong.TS15.OTSAResidualDecomposition `
  TS.Goldbach.Strong.TS16.CombinatorialDischarge `
  TS.Goldbach.Strong.TS17.MellinJacksonDischarge `
  TS.Goldbach.Strong.TS18.SecondMomentDischarge `
  TS.Goldbach.Strong.TS19.OTSAResidualDischarge `
  TS.Goldbach.Strong.TS21.ShortIntervalBudget `
  TS.Goldbach.Strong.TS21.BrunTitchmarshShortInterval `
  TS.Goldbach.Strong.TS21.BrunTitchmarshEnergyDischarge `
  TS.Goldbach.Strong.TS21.ThresholdComputation `
  TS.Goldbach.Strong.TS21.SecondMomentBudgetDischarge `
  TS.Goldbach.Strong.TS22.EnergyScale `
  TS.Goldbach.Strong.TS22.BrunTitchmarshScaleDischarge `
  TS.Goldbach.Strong.TS22.ClosedFormScales `
  TS.Goldbach.Strong.TS22.BrunTitchmarshIntervalBridge `
  TS.Goldbach.Strong.TS22.ScaledLargeSieveDischarge `
  TS.Goldbach.Strong.TS23.OTSAScalePropagation `
  TS.Goldbach.Strong.TS24.ClosedFormScaleBridge `
  TS.Goldbach.Strong.TS25.PaddedScaleOTSAFeasibility
```

## Audit

Audited scope:

```text
TS/Goldbach/Strong/TS15
TS/Goldbach/Strong/TS16
TS/Goldbach/Strong/TS17
TS/Goldbach/Strong/TS18
TS/Goldbach/Strong/TS19
TS/Goldbach/Strong/TS21
TS/Goldbach/Strong/TS22
TS/Goldbach/Strong/TS23
TS/Goldbach/Strong/TS24
TS/Goldbach/Strong/TS25
```

Audit commands:

```powershell
rg -n "s[o]rry" TS\Goldbach\Strong\TS15 TS\Goldbach\Strong\TS16 TS\Goldbach\Strong\TS17 TS\Goldbach\Strong\TS18 TS\Goldbach\Strong\TS19 TS\Goldbach\Strong\TS21 TS\Goldbach\Strong\TS22 TS\Goldbach\Strong\TS23 TS\Goldbach\Strong\TS24 TS\Goldbach\Strong\TS25
rg -n "a[x]iom" TS\Goldbach\Strong\TS15 TS\Goldbach\Strong\TS16 TS\Goldbach\Strong\TS17 TS\Goldbach\Strong\TS18 TS\Goldbach\Strong\TS19 TS\Goldbach\Strong\TS21 TS\Goldbach\Strong\TS22 TS\Goldbach\Strong\TS23 TS\Goldbach\Strong\TS24 TS\Goldbach\Strong\TS25
```

Expected result: no matches.

## TS20 Manuscript

The synthesis document is available at:

```text
TS/Goldbach/Strong/TS20/TS20_Horizon_Goldbach_Synthesis.tex
```

It summarizes TS15--TS19 and records the final analytic infrastructure ledger.
It is written for XeLaTeX because it uses `fontspec`.

## Repository Note

The root project also contains older Horizon/Goldbach modules. Some older
areas may have their own independent audit status. The sprint chain documented
above is specifically the audited `TS/Goldbach/Strong/TS15`--`TS25` layer.
