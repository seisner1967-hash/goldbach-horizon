# TS222 Audit - Cos-Square Boundary Vanishing Reduction Bridge

## Scope

TS222 isolates the product-filter boundary-vanishing step remaining after the
finite triple IPP discharge in TS221.

The sprint defines the two one-variable primitive asymptotic obligations:

- `CosSquareIPPPrimitiveAtTopVanishingStatement`
- `CosSquareIPPPrimitiveZeroRightVanishingStatement`

and packages them as:

- `CosSquareIPPPrimitiveBoundaryLimitEvidence`

It then proves:

```lean
cosSquareBoundaryVanishing_of_primitiveLimits :
  CosSquareIPPPrimitiveBoundaryLimitEvidence ->
    TS219.Goldbach.CosSquareBoundaryVanishingStatement
```

The proof uses the TS221 identity

```lean
P(T) - P(eps) =
  TS219.Goldbach.cosSquareTripleIPPBoundarySum eps T
```

and composes the two one-variable limits with the two projections of the
product cutoff filter.

## Status

```text
repo_committed_relative
```

TS222 proves the reduction from primitive one-variable asymptotics to TS219
boundary vanishing.  It does not yet prove either primitive asymptotic.

## Files

```text
TS/Goldbach/Strong/TS222/CosSquareBoundaryVanishingReductionBridge.lean
TS/Goldbach/Strong/TS222/TS222_Audit.md
README.md
```

## Build

```powershell
lake build TS.Goldbach.Strong.TS222.CosSquareBoundaryVanishingReductionBridge
```

## Audit Commands

```powershell
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS222
git diff --check
```

## Non-Claims

TS222 does not prove:

- `P(T) -> 0` as `T -> +infty`;
- `P(eps) -> 0` as `eps -> 0+`;
- the unconditional TS219 boundary-vanishing evidence;
- the third-derivative cutoff value `pi`;
- Dirichlet cutoff or Abel convergence;
- the canonical `sinc^4` value;
- Plancherel evidence;
- the explicit formula;
- Gallagher;
- Goldbach.

## Result

TS222 reduces the boundary-vanishing problem to two local asymptotic estimates
for the explicit primitive constructed in TS220 and connected to the boundary
sum in TS221.  The remaining TS223/TS224-level work is to prove these
asymptotics and the third-derivative cutoff value.
