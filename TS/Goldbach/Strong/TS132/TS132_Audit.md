# TS132 Audit - Selberg Mobius Chain Coefficient Collapse Ledger

## Scope

TS132 adds:

```text
TS/Goldbach/Strong/TS132/SelbergMobiusChainCoefficientCollapseLedger.lean
```

It advances the TS131 local chain-coefficient obligation:

```text
sum_m 1_{d | m} * 1_{m | e} * mu(e / m)
```

by proving the two immediate cases and isolating the sole remaining
proper-divisor case.

## Concrete declarations

TS132 proves:

```lean
TS132.Goldbach.selbergMobiusRatCoefficient_one
TS132.Goldbach.selbergMobiusChainCoefficient_eq_zero_of_not_dvd
TS132.Goldbach.selbergMobiusChainCoefficient_eq_one_of_eq
TS132.Goldbach.selbergMobiusChainCoefficientCollapse_of_properDivisorCollapse
TS132.Goldbach.selbergFiniteMobiusReconstructionIdentity_of_expansion_properDivisorCollapse
TS132.Goldbach.selbergMobiusChainCoefficientCollapseLedgerTarget
TS132.Goldbach.selbergFiniteMobiusReconstructionCollapseTarget
```

TS132 defines:

```lean
TS132.Goldbach.SelbergMobiusProperDivisorChainCollapse
TS132.Goldbach.SelbergMobiusChainCoefficientCollapseLedger
TS132.Goldbach.selbergMobiusChainCoefficientCollapseLedger
TS132.Goldbach.SelbergMobiusChainCoefficientCollapseLedgerTarget
```

## Meaning

The diagonal coefficient is fully proved:

```text
coefficient(d,d) = 1
```

for `d` in the TS131 positive finite support. The proof uses finite
single-term selection and the fact that the rational Mobius coefficient at
`1` is `1`.

The non-divisibility case is also fully proved:

```text
not (d | e) -> coefficient(d,e) = 0.
```

Indeed, every nonzero term would require a chain `d | m | e`, which would
imply `d | e`.

Thus the full TS131 coefficient collapse is reduced to the proper-divisor
case:

```text
d | e, d != e -> coefficient(d,e) = 0.
```

This is the exact quotient-Mobius change-of-variables obligation left for the
next sprint.

## What TS132 does not prove

TS132 does not yet prove:

- the proper-divisor quotient Mobius collapse;
- the TS131 Fubini expansion into the coefficient-collected side;
- the unconditional TS130 finite Mobius reconstruction identity;
- the Selberg interval majorant;
- Brun-Titchmarsh;
- the spectral trace package;
- the Mellin-tail package;
- any prime-counting estimate.

## Verification

Commands run:

```powershell
lake env lean TS/Goldbach/Strong/TS132/SelbergMobiusChainCoefficientCollapseLedger.lean
lake build TS.Goldbach.Strong.TS132.SelbergMobiusChainCoefficientCollapseLedger
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS132
git diff --check -- TS\Goldbach\Strong\TS132 README.md
```

Expected result:

- Lean file compiles.
- Lake target builds.
- No placeholder proof marker.
- No forbidden constant declaration.
- No non-ASCII characters in TS132.
- Diff whitespace check is clean.

## Status

```text
repo_committed_relative
```

The sprint is relative because the proper-divisor quotient collapse and the
TS131 expansion obligation remain proposition-valued obligations.
