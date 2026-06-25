# TS203 Audit - Truncated Haar Transport

## Scope

TS203 supplies the first concrete analytic ingredient for the TS202 Wall 0
contract.  It proves the compact finite-endpoint Haar transport identity

```lean
integral_{log epsilon}^{log X} F (exp u) du =
  integral_epsilon^X F x / x dx
```

for continuous real test functions on a positive interval `[epsilon, X]`.
This is the truncated `dx / x = du` identity obtained from the substitution
`x = exp u`.

## Main Declarations

- `TS203.Goldbach.exp_image_uIcc_log_subset_Icc`
- `TS203.Goldbach.continuousOn_div_id_on_exp_image_uIcc_log`
- `TS203.Goldbach.truncatedHaarTransport_interval`
- `TS203.Goldbach.truncatedHaarTransport_interval_symm`
- `TS203.Goldbach.TruncatedHaarTransportStatement`
- `TS203.Goldbach.truncatedHaarTransportStatement`
- `TS203.Goldbach.TruncatedHaarTransportEvidenceLedger`
- `TS203.Goldbach.truncatedHaarTransportEvidenceLedger`
- `TS203.Goldbach.TruncatedHaarTransportTarget`
- `TS203.Goldbach.truncatedHaarTransportTarget`

## What TS203 Proves

TS203 proves a genuine compact measure-transport theorem with real
`intervalIntegral`, not an abstract contract projection.  It uses Mathlib's
`intervalIntegral.integral_comp_mul_deriv'` with `Real.exp` and the derivative
`Real.exp`.

The proof stays in signed real integrals.  It does not use `lintegral` or
`ENNReal.ofReal`, avoiding any accidental loss of sign information.

## Non-Claims

TS203 does not prove:

- improper Haar transport as `epsilon -> 0+`;
- global Haar transport on `(0, infinity)`;
- Mellin/Fourier kernel compatibility;
- effective integrability for the improper passage;
- Plancherel;
- the Riemann-von Mangoldt explicit formula;
- zeta-zero summability;
- circle-method or Gallagher correlation;
- Goldbach.

TS203 also does not fabricate full `Wall0HaarMeasureTransportEvidence`; it
only supplies the truncated slot.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS203.TruncatedHaarTransport
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS203
git diff --check
git status --short
```
