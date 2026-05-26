# TS18 - Relative Short-Interval Second Moment Discharge

## Status

TS18 promotes `ShortIntervalPrimeSecondMoment` from `analytic_open_problem`
to `repo_committed_relative`.

It does not claim a complete proof of the large sieve, Bombieri-Vinogradov, or
the Dirichlet-character bridge. Instead, those ingredients are isolated as
explicit local structures.

## Lean Files

- `DirichletCharacterBridge.lean`
  - stores `characterSecondMoment`;
  - stores `characterBridgeError`;
  - defines `DirichletCharacterBridge`.
- `LargeSieveInfrastructure.lean`
  - defines `LargeSieveInfrastructure`;
  - stores the constant `C`, its positivity, and `C <= 1`;
  - packages the selected modulus and the normalized large-sieve bound.
- `SecondMomentDischarge.lean`
  - defines `secondMomentInstance`;
  - proves `secondMomentInstance_C_le_one`;
  - proves `Problem_E1_from_TS18`.

## Ledger

| ID | Object | Previous Status | TS18 Status | Comment |
| --- | --- | --- | --- | --- |
| TS18-G38 | `ShortIntervalPrimeSecondMoment` | `analytic_open_problem` | `repo_committed_relative` | proved relative to two analytic infrastructures |
| TS18-B1 | `DirichletCharacterBridge` | absent | `analytic_infrastructure_obligation` | character orthogonality and bridge error |
| TS18-B2 | `LargeSieveInfrastructure` | absent | `analytic_infrastructure_obligation` | large sieve plus normalization |
| TS18-C1 | TS16 combinatorial discharge | `repo_committed` | unchanged | combinatorial debt remains closed |
| TS18-G40 | TS17 Mellin-Jackson discharge | `repo_committed_relative` | unchanged | harmonic debt remains localized |

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS18.DirichletCharacterBridge `
  TS.Goldbach.Strong.TS18.LargeSieveInfrastructure `
  TS.Goldbach.Strong.TS18.SecondMomentDischarge

rg -n "s[o]rry" TS\Goldbach\Strong\TS18
rg -n "a[x]iom" TS\Goldbach\Strong\TS18
```

Expected result:

```text
0 unresolved placeholders
0 global assumptions
```

## Conclusion

After TS18:

```text
ShortIntervalPrimeSecondMoment =
  DirichletCharacterBridge
  + LargeSieveInfrastructure
  => ShortIntervalPrimeSecondMoment
```

The final analytic work is not erased, but it is now named, local, and
connected to the existing TS15 downstream theorem.
