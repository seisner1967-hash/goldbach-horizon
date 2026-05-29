# TS52 - Fourier Mathlib API Binding Roadmap

## Status

TS52 prepares the binding layer between the TS41 Fourier normalization ledger
and Mathlib's concrete Fourier API.

Status: `repo_committed_relative`.

TS52 does not prove Plancherel, the Fourier derivative rule, Sobolev agreement,
or the concrete high-frequency tail estimate. It records the local binding
obligations that must be instantiated after the exact Mathlib Fourier symbols
and normalization constants have been checked.

## Lean Files

- `FourierMathlibAPIBinding.lean`:
  - defines `MathlibFourierAPIBinding`;
  - defines `MathlibFourierAPIBindingTarget`;
  - proves that a binding package yields both the TS52 target and the
    underlying TS41 normalization target.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS52.FourierMathlibAPIBinding

rg -n "s[o]rry" TS\Goldbach\Strong\TS52
rg -n "a[x]iom" TS\Goldbach\Strong\TS52
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS52-B1 | `MathlibFourierAPIBinding` | `analytic_infrastructure_obligation` | binding layer from TS41 Fourier slots to future Mathlib theorem instances |
| TS52-B2 | `MathlibFourierAPIBindingTarget` | `repo_committed_relative` | target proposition for the binding step |
| TS52-B3 | `FourierAPINormalizationTarget_of_binding` | `repo_committed_relative` | a binding package supplies the TS41 normalization target |

## Conclusion

TS52 is intentionally a roadmap, not a concrete Fourier proof. It keeps the
normalization and theorem-binding work explicit before any commitment to a
specific `fourierIntegral`, Plancherel theorem, derivative multiplier, or
high-frequency tail proof.
