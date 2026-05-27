# TS27 - OTSA Constant Register

## Status

TS27 records rational OTSA constant candidates in a labelled register and adds a
non-final smoke-test certificate.

Status: `repo_committed_relative`.

It does not certify the spectral, trace, Mellin-tail, scale-transfer, coupling,
or Goldbach theorems. The smoke-test constants are placeholders for checking the
TS26 rational pipeline.

## Lean Files

- `OTSAConstantRegister.lean`:
  - defines `OTSAConstantRegister`;
  - defines smoke-test rational constants;
  - defines `OTSACert_smoke_test`;
  - defines `OTSARegister_smoke_test`;
  - proves `smoke_test_scaledOTSAAdmissible`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS27.OTSAConstantRegister

rg -n "s[o]rry" TS\Goldbach\Strong\TS27
rg -n "a[x]iom" TS\Goldbach\Strong\TS27
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
|----|--------|--------|---------|
| TS27-R1 | `OTSAConstantRegister` | `repo_committed` | labelled register for rational OTSA constants |
| TS27-R2 | `OTSACert_smoke_test` | `smoke_test` | non-final rational pipeline test |
| TS27-R3 | `OTSARegister_smoke_test` | `smoke_test` | labelled non-final register entry |
| TS27-R4 | `smoke_test_scaledOTSAAdmissible` | `repo_committed_relative` | checks TS26-to-TS23 plumbing |

## Smoke-Test Constants

```text
Ck     = 3/50
Ct     = 1
Cm     = 1
Cscale = 1
```

These values are intentionally not a final OTSA certificate. They only verify
that rational majorants can be registered and converted into
`ScaledOTSAAdmissible`.
