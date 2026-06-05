# TS133 Audit - Selberg Proper Divisor Mobius Chain Collapse

## Scope

TS133 adds:

```text
TS/Goldbach/Strong/TS133/SelbergProperDivisorMobiusChainCollapse.lean
```

It advances the proper-divisor case left by TS132:

```text
d | e, d != e -> chainCoefficient(d,e) = 0.
```

The sprint proves the quotient arithmetic and keeps the remaining finite
`m = d * r` reindexing as an exact local proposition.

## Concrete declarations

TS133 proves:

```lean
TS133.Goldbach.quotient_one_lt_of_proper_dvd
TS133.Goldbach.quotientMobiusDivisorSum_eq_zero_of_one_lt
TS133.Goldbach.selbergMobiusProperDivisorChainCollapse_of_quotientReindexing
TS133.Goldbach.selbergMobiusChainCoefficientCollapse_of_quotientReindexing
TS133.Goldbach.selbergFiniteMobiusReconstructionIdentity_of_expansion_quotientReindexing
TS133.Goldbach.selbergProperDivisorMobiusChainCollapseTarget
TS133.Goldbach.selbergMobiusChainCoefficientCollapseLedgerTarget
```

TS133 defines:

```lean
TS133.Goldbach.SelbergMobiusProperDivisorQuotientReindexing
TS133.Goldbach.SelbergProperDivisorMobiusChainCollapse
TS133.Goldbach.selbergProperDivisorMobiusChainCollapse
TS133.Goldbach.SelbergProperDivisorMobiusChainCollapseTarget
```

## Meaning

The quotient lemma proves that if `d` and `e` are positive, `d | e`, and
`d != e`, then:

```text
1 < e / d.
```

The quotient Mobius lemma proves:

```text
sum_{r | n} mu(n / r) = 0
```

for every `n > 1`, using `Nat.sum_div_divisors` and the TS105 Mobius-delta
identity.

Therefore, if the finite chain coefficient is reindexed as the quotient
divisor sum over `e / d`, the TS132 proper-divisor collapse follows
immediately. TS133 also proves that this quotient reindexing supplies the full
TS131 chain coefficient collapse, and together with the TS131 expansion
obligation supplies the TS130 finite reconstruction identity.

## What TS133 does not prove

TS133 does not yet prove:

- the finite quotient reindexing of the chain coefficient;
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
lake env lean TS/Goldbach/Strong/TS133/SelbergProperDivisorMobiusChainCollapse.lean
lake build TS.Goldbach.Strong.TS133.SelbergProperDivisorMobiusChainCollapse
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS133
git diff --check -- TS\Goldbach\Strong\TS133 README.md
```

Expected result:

- Lean file compiles.
- Lake target builds.
- No placeholder proof marker.
- No forbidden constant declaration.
- No non-ASCII characters in TS133.
- Diff whitespace check is clean.

## Status

```text
repo_committed_relative
```

The sprint is relative because the finite quotient reindexing and the TS131
expansion obligation remain proposition-valued obligations.
