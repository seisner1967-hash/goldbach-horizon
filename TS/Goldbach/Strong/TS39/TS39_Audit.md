# TS39 - Mellin-Fourier Lp Isometry

## Status

TS39 defines the final mathematical specification for the Mellin-Fourier `L²`
isometry.

Status: `repo_committed_relative`.

TS39 does not construct the `LinearIsometryEquiv`. It records the exact target:
an isometric linear equivalence between `L²(muWeighted sigma)` and
`L²(volume)` whose forward and inverse maps agree a.e. with `TsigmaFun` and
`TsigmaInvFun`.

## Lean Files

- `MellinFourierLpIsometry.lean`:
  - defines `MellinFourierLpIsometry`;
  - requires the forward isometry to agree a.e. with `TsigmaFun`;
  - requires the inverse isometry to agree a.e. with `TsigmaInvFun`;
  - defines `MellinFourierLpIsometryTarget`;
  - proves `weakTarget_of_isometryTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS39.MellinFourierLpIsometry

rg -n "s[o]rry" TS\Goldbach\Strong\TS39
rg -n "a[x]iom" TS\Goldbach\Strong\TS39
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS39-I1 | `MellinFourierLpIsometry` | `analytic_infrastructure_obligation` | final `L²` isometry specification tied to `TsigmaFun`/`TsigmaInvFun` |
| TS39-I2 | `MellinFourierLpIsometryTarget` | `analytic_infrastructure_obligation` | fixed-`sigma` target proposition |
| TS39-I3 | `weakTarget_of_isometryTarget` | `repo_committed_relative` | final spec implies the weaker TS36 existence target |

## Conclusion

TS39 marks the end of the architectural mapping for the Mellin-Fourier norm
bridge (`TS17-B1`). The construction path is now split across TS34, TS35, TS36,
TS37, TS38, and this final specification.

