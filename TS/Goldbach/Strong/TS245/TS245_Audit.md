# TS245 Audit - Cos-Square Improper Cutoff Assembly

## Scope

TS245 closes the cos-square cutoff route isolated in TS219.  It proves the
positive-half-line Haar-kernel integrability, identifies the product-filter
cutoff with the existing Lebesgue integral, executes the TS219 limiting
assembly, and obtains the value `pi/6`.

## Main Declarations

- `cosSquareHaarKernel_integrableOn_Ioi`
- `cosSquareHaarKernel_abs_le_quarter`
- `cosSquareHaarPartialIntegralZeroRight`
- `cosSquareImproperCutoffConvergence`
- `cosSquareTripleIPPCutoffAssembly`
- `cosSquareTripleIPPCutoffBridge`
- `cosSquareTripleIPPCutoffEvidence`
- `cosSquareImproperIntegralValue`
- `CosSquareImproperCutoffAssemblyLedger`
- `cosSquareImproperCutoffAssemblyTarget`

## What Is Proved

TS218 proves global integrability of the canonical sinc-fourth kernel and the
positive-half-line identity

```text
canonicalSincFourthKernel u = 4 * cosSquareHaarKernel (2*u).
```

TS245 transports this integrability through multiplication by `2` and removes
the nonzero scalar factor `4`.  This proves that `cosSquareHaarKernel` is
integrable on `(0, +infinity)`.

For the cutoff convergence, the upper partial integral converges to the
Lebesgue integral by `intervalIntegral_tendsto_integral_Ioi`.  At the lower
endpoint, the TS224 fourth-order remainder estimate gives

```text
|cosSquareHaarKernel x| <= 1/4
```

for `x > 0`, hence the integral on `[0, eps]` tends to zero.  The finite
decomposition

```text
int_eps^T Haar = int_0^T Haar - int_0^eps Haar
```

then proves `TS219.Goldbach.CosSquareImproperCutoffConvergenceStatement` on
the product cutoff filter.

Finally, TS221 supplies the finite triple-IPP identity, TS224 supplies boundary
vanishing, and TS244 supplies the third-derivative cutoff value `pi`.  Their
limits give a second limit `pi/6` for the Haar cutoff integrals.  Uniqueness of
limits identifies the Lebesgue integral with `pi/6`, proving

```lean
TS213.Goldbach.CosSquareIntegralValueStatement
```

## Non-Claims

TS245 does not prove the canonical sinc-fourth value, Plancherel evidence, the
explicit formula input, Gallagher, or Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS245.CosSquareImproperCutoffAssembly
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS245
git diff --check
```

## Expected Audit Result

The build succeeds.  The TS245 directory contains no placeholder proofs, no
forbidden declarations, and no non-ASCII characters.  `git diff --check`
reports no whitespace errors.
