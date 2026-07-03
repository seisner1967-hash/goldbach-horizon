# TS219 Audit - Cos-Square Triple IPP Cutoff Reformulation

## Scope

TS219 corrects the triple-IPP side of the TS213 direct Dirichlet route.  The
old TS213 statement used a Lebesgue integral of

```text
(-2 * sin x + 4 * sin (2*x)) / x
```

over `(0, infinity)`.  That expression is Dirichlet-type and conditionally
convergent, so the final route must use cutoff limits rather than a raw
Lebesgue integral.

TS219 archives the old Lebesgue target as legacy and records the corrected
cutoff route: finite IPP on `[eps, T]`, explicit boundary terms, boundary
vanishing, cutoff value `pi` for the third-derivative kernel, and a fail-closed
assembly bridge to the TS213 cos-square value statement.

## Main Declarations

- `TS219.Goldbach.CosSquareTripleIPPReformulationStatus`
- `TS219.Goldbach.LegacyCosSquareTripleIPPLebesgueStatement`
- `TS219.Goldbach.cosSquareCutoffFilter`
- `TS219.Goldbach.cosSquareTripleIPPBoundaryTerm1`
- `TS219.Goldbach.cosSquareTripleIPPBoundaryTerm2`
- `TS219.Goldbach.cosSquareTripleIPPBoundaryTerm3`
- `TS219.Goldbach.boundaryJump`
- `TS219.Goldbach.cosSquareTripleIPPBoundarySum`
- `TS219.Goldbach.CosSquareImproperCutoffConvergenceStatement`
- `TS219.Goldbach.CosSquareFiniteTripleIPPStatement`
- `TS219.Goldbach.CosSquareBoundaryVanishingStatement`
- `TS219.Goldbach.CosSquareThirdDerivativeCutoffValueStatement`
- `TS219.Goldbach.CosSquareTripleIPPCutoffAssemblyStatement`
- `TS219.Goldbach.CosSquareTripleIPPCutoffBridge`
- `TS219.Goldbach.CosSquareTripleIPPCutoffEvidence`
- `TS219.Goldbach.CorrectedCosSquareTripleIPPTarget`
- `TS219.Goldbach.correctedCosSquareTripleIPPTarget_of_cutoffEvidence`
- `TS219.Goldbach.cosSquareIntegralValue_of_cutoffEvidence`
- `TS219.Goldbach.CosSquareTripleIPPCutoffReformulationLedger`
- `TS219.Goldbach.cosSquareTripleIPPCutoffReformulationLedger`
- `TS219.Goldbach.CosSquareTripleIPPCutoffReformulationTarget`
- `TS219.Goldbach.cosSquareTripleIPPCutoffReformulationTarget`

## What TS219 Proves

TS219 proves only routing and definitional facts:

```lean
CosSquareTripleIPPCutoffEvidence ->
  CorrectedCosSquareTripleIPPTarget

CosSquareTripleIPPCutoffEvidence ->
  TS213.Goldbach.CosSquareIntegralValueStatement
```

The second implication consumes an explicit
`CosSquareTripleIPPCutoffBridge` field.  TS219 does not prove that bridge; it
keeps the limiting assembly as a named future obligation.

TS219 also proves by `rfl` that the legacy target is exactly the old TS213
Lebesgue triple-IPP statement.

## Notes

`cosSquareCutoffFilter` uses `Filter.prod`.  Mathlib warns that this name is
deprecated in favor of a Unicode notation, but the explicit ASCII name is kept
in TS219 to preserve the sprint audit rule forbidding non-ASCII source text.

The cutoff value of the third-derivative kernel is correctly stated as `pi`,
not `pi/2`, since the formal Dirichlet combination is
`-2*(pi/2) + 4*(pi/2) = pi`.

## Non-Claims

TS219 does not prove:

- the finite triple IPP identity;
- boundary-term vanishing;
- the cutoff value of the third-derivative kernel;
- the cutoff assembly bridge;
- the Dirichlet cutoff or Abel value;
- the canonical `sinc^4` value;
- TS204 Plancherel evidence;
- the explicit formula;
- Gallagher or any circle-method estimate;
- Goldbach.

## Verification Commands

```text
lake env lean TS\Goldbach\Strong\TS219\CosSquareTripleIPPCutoffReformulation.lean
lake build TS.Goldbach.Strong.TS219.CosSquareTripleIPPCutoffReformulation
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS219
git diff --check
git status --short
```
