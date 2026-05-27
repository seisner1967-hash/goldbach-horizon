# TS21 - Short-Interval Budget

## Status

TS21 introduces an explicit constant budget for the short-interval second
moment. It does not claim a full formal proof of Brun-Titchmarsh. Instead, it
packages the Brun-Titchmarsh consequence as a local analytic obligation and
proves the Lean plumbing that transports the resulting constant through the
TS15/TS18 short-interval layer.

Status: `repo_committed_relative`.

## Lean Files

- `ShortIntervalBudget.lean`:
  - defines `shortIntervalBase`;
  - defines the budgeted target `Problem_E1K K`;
  - defines `ShortIntervalPrimeSecondMomentK`;
  - proves monotonicity in the transported constant.
- `BrunTitchmarshShortInterval.lean`:
  - defines the explicit Brun-Titchmarsh budget constant `20`;
  - defines the local obligation `BrunTitchmarshShortInterval`;
  - instantiates `ShortIntervalPrimeSecondMomentK` from that obligation.
- `ThresholdComputation.lean`:
  - defines the default allowed TS21 constant `KAllowedTS21 = 20`;
  - proves the Brun-Titchmarsh budget is admissible for that threshold.
- `SecondMomentBudgetDischarge.lean`:
  - defines a budgeted large-sieve infrastructure;
  - proves the TS18-style discharge with an arbitrary explicit constant `K`;
  - promotes it to any allowed threshold `KAllowed` once `K <= KAllowed`.

## Ledger

| ID | Object | Previous Status | TS21 Status |
|----|--------|-----------------|-------------|
| TS21-BT1 | `BrunTitchmarshShortInterval` | absent | `analytic_infrastructure_obligation` |
| TS21-K1 | `ShortIntervalPrimeSecondMomentK` | absent | `repo_committed_relative` |
| TS21-K2 | `Problem_E1K` monotonicity | absent | `repo_committed` |
| TS21-LS1 | `LargeSieveBudgetInfrastructure` | TS18 required `C <= 1` | budgeted constant transport |
| TS21-T1 | `KAllowedTS21` | absent | explicit threshold input |

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS21.ShortIntervalBudget `
  TS.Goldbach.Strong.TS21.BrunTitchmarshShortInterval `
  TS.Goldbach.Strong.TS21.ThresholdComputation `
  TS.Goldbach.Strong.TS21.SecondMomentBudgetDischarge

rg -n "s[o]rry" TS\Goldbach\Strong\TS21
rg -n "a[x]iom" TS\Goldbach\Strong\TS21
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Conclusion

TS21 relaxes the rigid TS18 downstream requirement `C <= 1` into an explicit
budgeted interface. The analytic task is now:

```text
BrunTitchmarshShortInterval
  => ShortIntervalPrimeSecondMomentK with K = 20
  => Problem_E1K 20
```

The value `20` can later be replaced by a sharper constant without changing the
downstream Lean architecture.
