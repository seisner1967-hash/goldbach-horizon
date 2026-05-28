# TS41 - Fourier API Probe

## Status

TS41 records the Mathlib Fourier-normalization interface needed before
instantiating the TS40 Fourier-tail roadmap with concrete Fourier objects.

Status: `repo_committed_relative`.

TS41 does not prove Plancherel, the Fourier derivative rule, Sobolev decay, or
the high-frequency tail bound. It fixes the future normalization slots and
constants needed before a concrete `FourierTailInfrastructure` proof is
attempted.

## Lean Files

- `FourierAPIProbe.lean`:
  - defines `FourierAPINormalizationLedger`;
  - records an abstract Fourier transform choice;
  - records an abstract Sobolev derivative representative;
  - records positive Plancherel and derivative-multiplier normalization
    constants;
  - defines `FourierAPINormalizationTarget`;
  - proves `FourierAPINormalizationTarget.of_ledger`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS41.FourierAPIProbe

rg -n "s[o]rry" TS\Goldbach\Strong\TS41
rg -n "a[x]iom" TS\Goldbach\Strong\TS41
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS41-F1 | `FourierAPINormalizationLedger` | `analytic_infrastructure_obligation` | Fourier API and normalization package |
| TS41-F2 | `FourierAPINormalizationTarget` | `repo_committed_relative` | target proposition for future concrete API binding |
| TS41-F3 | `FourierAPINormalizationTarget.of_ledger` | `repo_committed_relative` | supplied ledger discharges the TS41 target |
