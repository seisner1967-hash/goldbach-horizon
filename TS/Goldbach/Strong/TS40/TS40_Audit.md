# TS40 - Fourier Tail Roadmap

## Status

TS40 records the high-frequency Fourier-tail infrastructure needed by the TS17
Mellin-Jackson layer.

Status: `repo_committed_relative`.

TS40 does not prove Plancherel, the Fourier derivative rule, Sobolev decay, or
the final Fourier-tail estimate. It exposes them as local analytic
infrastructure obligations.

TS40 completes the roadmap of the harmonic TS17 front. It does not complete all
remaining analytic obligations in the repository: Brun-Titchmarsh/Selberg,
Dirichlet character bridges, large sieve inputs, and OTSA analytic constants
remain explicitly listed elsewhere.

## Lean Files

- `FourierTailRoadmap.lean`:
  - defines `FourierTailInfrastructure`;
  - keeps the Fourier transform abstract pending Mathlib API normalization;
  - keeps the Sobolev derivative representative abstract;
  - records Plancherel as `snorm` preservation;
  - records derivative-control as a roadmap marker;
  - records the high-frequency tail estimate;
  - defines `FourierTailTarget`;
  - proves `FourierTailTarget.of_infrastructure`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS40.FourierTailRoadmap

rg -n "s[o]rry" TS\Goldbach\Strong\TS40
rg -n "a[x]iom" TS\Goldbach\Strong\TS40
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS40-F1 | `FourierTailInfrastructure` | `analytic_infrastructure_obligation` | Plancherel + Sobolev tail contract |
| TS40-F2 | `FourierTailTarget` | `repo_committed_relative` | target proposition for the Fourier-tail side |
| TS40-F3 | `FourierTailTarget.of_infrastructure` | `repo_committed_relative` | supplied infrastructure discharges the roadmap target |

