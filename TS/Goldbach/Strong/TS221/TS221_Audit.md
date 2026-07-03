# TS221 Audit - Cos-Square Finite Triple IPP Discharge

Status: repo_committed

## Scope

- `TS/Goldbach/Strong/TS221/CosSquareFiniteTripleIPPDischarge.lean`

## Build

- `lake env lean TS\Goldbach\Strong\TS221\CosSquareFiniteTripleIPPDischarge.lean`
- `lake build TS.Goldbach.Strong.TS221.CosSquareFiniteTripleIPPDischarge`

## What TS221 Proves

TS221 closes the finite compact part of the TS219 cutoff triple-IPP route.

It proves:

- `cosSquareIPPPrimitive_eq_boundaryTerms`
- `cosSquareIPPPrimitive_jump_eq_boundarySum`
- `cosSquareFiniteTripleIPP`

The main theorem discharges:

```lean
TS219.Goldbach.CosSquareFiniteTripleIPPStatement
```

The proof uses the TS220 local derivative identity for the explicit primitive,
proves continuity and interval integrability of the two kernels on the compact
positive interval `[eps, T]`, applies the finite-interval FTC, splits the
integral of the difference, and rewrites the primitive jump as the TS219
boundary sum.

## Non-Claims

TS221 does not prove boundary vanishing.
It does not prove the third-derivative cutoff value.
It does not prove the Dirichlet cutoff or Abel value.
It does not prove the canonical `sinc^4` value.
It does not prove Plancherel evidence, the explicit formula, Gallagher, or
Goldbach.

## Audit Commands

```powershell
lake env lean TS\Goldbach\Strong\TS221\CosSquareFiniteTripleIPPDischarge.lean
lake build TS.Goldbach.Strong.TS221.CosSquareFiniteTripleIPPDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS221
git diff --check
```

