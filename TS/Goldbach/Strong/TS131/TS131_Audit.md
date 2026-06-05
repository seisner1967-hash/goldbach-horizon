# TS131 Audit - Selberg Finite Mobius Reconstruction Collapse

## Scope

TS131 adds:

```text
TS/Goldbach/Strong/TS131/SelbergFiniteMobiusReconstructionCollapse.lean
```

It opens the finite Mobius reconstruction identity isolated by TS130 and
reduces it to two local obligations:

1. an expansion/Fubini obligation from the reconstructed absorbed diagonal
   vector to a coefficient-collected side;
2. a local chain-coefficient collapse over finite divisor chains `d | m | e`.

The sprint is intentionally fail-closed: it does not claim the full finite
Mobius inversion proof, but it proves that these two exact obligations imply
the TS130 reconstruction identity.

## Concrete declarations

TS131 defines:

```lean
TS131.Goldbach.selbergMobiusReconstructionSupport
TS131.Goldbach.selbergMobiusChainCoefficient
TS131.Goldbach.selbergFiniteMobiusReconstructionExpandedSide
TS131.Goldbach.SelbergFiniteMobiusReconstructionExpansion
TS131.Goldbach.SelbergMobiusChainCoefficientCollapse
TS131.Goldbach.SelbergFiniteMobiusReconstructionCollapse
TS131.Goldbach.selbergFiniteMobiusReconstructionCollapse
TS131.Goldbach.selbergOptimalFiniteMobiusReconstructionCollapse
```

TS131 proves:

```lean
TS131.Goldbach.selbergSupport_delta_sum
TS131.Goldbach.selbergFiniteMobiusExpandedSide_eq_target_of_chainCollapse
TS131.Goldbach.selbergFiniteMobiusReconstructionIdentity_of_expansion_chainCollapse
TS131.Goldbach.optimalReconstructedWeight_denseSide_eq_optimal_budget_of_TS131_obligations
TS131.Goldbach.selbergFiniteMobiusReconstructionCollapseTarget
TS131.Goldbach.selbergOptimalWeightReconstructionTarget
```

## Meaning

The local coefficient is

```text
sum_m 1_{d | m} * 1_{m | e} * mu(e / m)
```

over the TS130 positive finite reconstruction support.  TS131 names the exact
delta collapse requirement:

```text
coefficient(d,e) = if d = e then 1 else 0.
```

It then proves that this delta collapse selects `Y d` from the finite support
sum, and that the combination of the expansion obligation plus this collapse
discharges:

```lean
TS130.Goldbach.SelbergFiniteMobiusReconstructionIdentity level Y
```

For the TS128 optimal diagonal vector, the same two local obligations imply
the exact dense-side value:

```text
TS110 dense side = 1 / TS122 denominator.
```

## What TS131 does not prove

TS131 does not yet prove:

- the concrete Fubini expansion from the TS130 reconstructed weights to the
  coefficient-collected side;
- the chain-coefficient Mobius delta collapse itself;
- the unconditional TS130 finite Mobius reconstruction identity;
- the Selberg interval majorant;
- Brun-Titchmarsh;
- the spectral trace package;
- the Mellin-tail package;
- any prime-counting estimate.

## Verification

Commands run:

```powershell
lake env lean TS/Goldbach/Strong/TS131/SelbergFiniteMobiusReconstructionCollapse.lean
lake build TS.Goldbach.Strong.TS131.SelbergFiniteMobiusReconstructionCollapse
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS131
git diff --check -- TS\Goldbach\Strong\TS131 README.md
```

Expected result:

- Lean file compiles.
- Lake target builds.
- No placeholder proof marker.
- No forbidden constant declaration.
- No non-ASCII characters in TS131.
- Diff whitespace check is clean.

## Status

```text
repo_committed_relative
```

The sprint is relative because the coefficient expansion and the local finite
Mobius chain collapse remain proposition-valued obligations.
