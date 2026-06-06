# TS134 Audit - Selberg Proper Divisor Quotient Reindexing Discharge

## Scope

TS134 adds:

```text
TS/Goldbach/Strong/TS134/SelbergProperDivisorQuotientReindexingDischarge.lean
```

It discharges the TS133 finite quotient reindexing obligation:

```text
chainCoefficient(d,e) =
  sum_{r | e/d} mu((e/d)/r)
```

for supported `d,e` with `d | e`.

## Concrete declarations

TS134 proves:

```lean
TS134.Goldbach.divisor_mem_reconstructionSupport_of_mem
TS134.Goldbach.selbergMobiusChainCoefficient_eq_filteredDivisorSum
TS134.Goldbach.quotientDivisorSum_eq_filteredDivisorSum
TS134.Goldbach.selbergMobiusProperDivisorQuotientReindexing
TS134.Goldbach.selbergMobiusProperDivisorChainCollapse
TS134.Goldbach.selbergMobiusChainCoefficientCollapse
TS134.Goldbach.selbergProperDivisorQuotientReindexingDischargeTarget
TS134.Goldbach.selbergProperDivisorMobiusChainCollapseTarget
```

TS134 defines:

```lean
TS134.Goldbach.SelbergProperDivisorQuotientReindexingDischarge
TS134.Goldbach.selbergProperDivisorQuotientReindexingDischarge
TS134.Goldbach.SelbergProperDivisorQuotientReindexingDischargeTarget
```

## Meaning

First, TS134 proves that any divisor of a supported positive `e` remains in
the TS130/TS131 positive reconstruction support. This permits the chain
coefficient sum over support to be replaced by the divisor sum:

```text
sum_{m in support} 1_{d | m} 1_{m | e} mu(e/m)
=
sum_{m | e, d | m} mu(e/m).
```

Second, TS134 reindexes the filtered divisor sum by the map:

```text
r -> d * r
```

from divisors of `e/d` to divisors `m` of `e` satisfying `d | m`. The proof
uses `Finset.sum_bij`, `Nat.dvd_div_iff_mul_dvd`, and
`Nat.mul_div_mul_comm`.

Thus the TS133 quotient reindexing obligation is proved unconditionally. As a
result, the TS132 proper-divisor chain collapse and the full TS131 chain
coefficient collapse are now available without a separate quotient-reindexing
hypothesis.

## What TS134 does not prove

TS134 does not yet prove:

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
lake env lean TS/Goldbach/Strong/TS134/SelbergProperDivisorQuotientReindexingDischarge.lean
lake build TS.Goldbach.Strong.TS134.SelbergProperDivisorQuotientReindexingDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS134
git diff --check -- TS\Goldbach\Strong\TS134 README.md
```

Expected result:

- Lean file compiles.
- Lake target builds.
- No placeholder proof marker.
- No forbidden constant declaration.
- No non-ASCII characters in TS134.
- Diff whitespace check is clean.

## Status

```text
repo_committed_relative
```

The sprint is relative because the TS131 Fubini expansion obligation remains
open.
