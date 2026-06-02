# TS83 - Mellin Tail Final API Gap Ledger

## Status

TS83 closes the Mellin-tail front architecturally. It records that the remaining
`Cm <= 1` work is no longer local triangle-spline calculus, but a final set of
API-level contracts:

- the TS82 Sobolev-slot recognition contract;
- the TS54 compatible Plancherel/L2 `snorm` contract;
- the TS51 Fourier-tail comparison package, tied to the same TS41 ledger.

Status: `repo_committed_relative`.

TS83 does not prove Plancherel, does not instantiate a concrete Sobolev API,
and does not prove the final Fourier-tail inequality. It proves that a
compatible package of those final contracts mechanically yields the TS51
Fourier-tail comparison target, the TS42 triangle-spline tail target, and the
TS33 Mellin-tail majorant contract `Cm <= 1`.

## Lean Files

- `MellinTailFinalAPIGapLedger.lean`:
  - defines `MellinTailFinalAPIGapLedger`;
  - defines `mellinTailFinalAPIGapLedger`;
  - defines `MellinTailFinalAPIContracts`;
  - defines `sobolevSlotAssembly_of_recognitionContract`;
  - defines `sobolevAgreementInfrastructure_of_recognitionContract`;
  - defines `triangleSplineFourierTailComparisonInputs_of_finalAPIContracts`;
  - defines `MellinTailFinalAPIGapLedgerTarget`;
  - defines `MellinTailFinalAPIContractsTarget`;
  - proves `mellinTailFinalAPIGapLedgerTarget`;
  - proves `sobolevSlotRecognitionContractTarget_of_finalAPIContractsTarget`;
  - proves `fourierPlancherelL2Target_of_finalAPIContractsTarget`;
  - proves `triangleSplineFourierTailComparisonTarget_of_finalAPIContractsTarget`;
  - proves `triangleSplineTailTarget_of_finalAPIContractsTarget`;
  - proves `mellinTailContractTarget_of_finalAPIContractsTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS83.MellinTailFinalAPIGapLedger

rg -n "s[o]rry" TS\Goldbach\Strong\TS83
rg -n "a[x]iom" TS\Goldbach\Strong\TS83
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS83-G1 | `MellinTailFinalAPIGapLedger` | `repo_committed` | records Sobolev, Plancherel, and Fourier-tail final API gaps |
| TS83-C1 | `MellinTailFinalAPIContracts` | `analytic_infrastructure_obligation` | compatible final API contracts for `Cm <= 1` |
| TS83-P1 | `triangleSplineFourierTailComparisonTarget_of_finalAPIContractsTarget` | `repo_committed_relative` | final contracts imply TS51 |
| TS83-P2 | `triangleSplineTailTarget_of_finalAPIContractsTarget` | `repo_committed_relative` | final contracts imply TS42 |
| TS83-P3 | `mellinTailContractTarget_of_finalAPIContractsTarget` | `repo_committed_relative` | final contracts imply TS33 `Cm <= 1` |

## Conclusion

TS83 marks the triangle-spline Mellin-tail route as architecturally complete:
all internal spline analysis is proved, and the remaining work is isolated in
named external API bindings.
