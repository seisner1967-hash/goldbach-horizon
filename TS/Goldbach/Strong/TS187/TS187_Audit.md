# TS187 Audit - Analytic Frontier Transform Compatibility Ledger

## Scope

TS187 records the analytic frontier after TS186.  It prevents supporting-cleanup
drift by naming the real remaining walls as local contract and evidence types.

The central new wall is Wall 0: Mellin/Fourier compatibility.  Classical
explicit formulae use Mellin and Dirichlet-series language, while the recent
triangle-spline work built a real Fourier identity.  A future proof must justify
the logarithmic coordinate change `x = exp u`, the measure transport
`dx / x = du`, and the compatibility of kernels, analytic continuation, and
inversion.

## Main Declarations

- `TS187.Goldbach.MellinFourierDiffeomorphismContract`
- `TS187.Goldbach.MellinFourierDiffeomorphismEvidence`
- `TS187.Goldbach.AnalyticFrontierContracts`
- `TS187.Goldbach.AnalyticFrontierEvidence`
- `TS187.Goldbach.AnalyticFrontierTransformCompatibilityLedger`
- `TS187.Goldbach.analyticFrontierTransformCompatibilityLedger`
- `TS187.Goldbach.AnalyticFrontierTransformCompatibilityTarget`
- `TS187.Goldbach.analyticFrontierTransformCompatibilityTarget`

## What TS187 Proves Or Records

TS187 proves only the structural target that the analytic frontier has been
registered as explicit local types.  It records:

- Wall 0: Mellin/Fourier logarithmic coordinate compatibility.
- Wall 1: Plancherel L2 isometry.
- Wall 2: explicit-formula contour and residue theorem.
- Wall 3: zeta-zero summability or zero bounds.
- Wall 4: circle-method, Gallagher, or large-sieve correlation.

The ledger stores the contract and evidence types.  It does not populate an
`AnalyticFrontierEvidence` value.

## Non-Claims

TS187 does not prove:

- the Mellin/Fourier diffeomorphism;
- Plancherel;
- the contour explicit formula;
- zeta-zero summability;
- the Riemann hypothesis;
- Gallagher or circle-method correlation;
- Goldbach.

## Verification Commands

```powershell
lake env lean TS\Goldbach\Strong\TS187\AnalyticFrontierTransformCompatibilityLedger.lean
lake build TS.Goldbach.Strong.TS187.AnalyticFrontierTransformCompatibilityLedger
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS187
git diff --check
git status --short
```
