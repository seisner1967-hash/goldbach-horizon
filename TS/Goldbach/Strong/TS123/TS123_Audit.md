# TS123 Audit - Selberg Jordan-Two Positivity Probe

## Status

`repo_committed_relative`

TS123 is a local positivity probe above the TS122 weighted-Cauchy optimization
layer. It does not prove the full multiplicative positivity of `J2`; instead
it proves that this single arithmetic input is enough to discharge the
denominator positivity required by TS122.

## Added file

```text
TS/Goldbach/Strong/TS123/SelbergJordanTwoPositivityProbe.lean
```

## Main declarations

```lean
TS123.Goldbach.selbergOptimizationSupport_eq_positive_support
TS123.Goldbach.selbergOptimizationSupport_eq_positive_range_filter
TS123.Goldbach.four_mem_selbergOptimizationSupport_of_level_ge_four
TS123.Goldbach.not_squarefree_four
TS123.Goldbach.one_mem_selbergOptimizationSupport
TS123.Goldbach.selbergMobiusRatCoefficient_one
TS123.Goldbach.SelbergJordanTwoPositiveOnSupport
TS123.Goldbach.SelbergOptimizationDenominatorPositive
TS123.Goldbach.selbergOptimizationDenominator_term_nonneg
TS123.Goldbach.selbergOptimizationDenominator_term_one_pos
TS123.Goldbach.selbergOptimizationDenominator_pos_of_jordanTwo_pos
TS123.Goldbach.selbergDiagonalEnergy_lower_bound_of_jordanTwo_pos
TS123.Goldbach.selbergOptimalDiagonalVectorCandidate
TS123.Goldbach.SelbergJordanTwoPositivityProbe
TS123.Goldbach.selbergJordanTwoPositivityProbe
TS123.Goldbach.SelbergJordanTwoPositivityProbeTarget
TS123.Goldbach.selbergJordanTwoPositivityProbeTarget
TS123.Goldbach.selbergDiagonalOptimizationTarget
```

## Concrete proofs

### TS123-R1: support reality check

TS123 records that the current TS122 support is the positive finite window:

```text
range(level + 1) filtered by 0 < d
```

not a squarefree-only support. The diagnostic is concrete: if `4 <= level`,
then `4` lies in the support, while `4` is not squarefree.

### TS123-R2: support nonemptiness at `1`

```lean
one_mem_selbergOptimizationSupport
```

proves that `1` is in the support whenever `0 < level`.

### TS123-R3: Mobius coefficient at `1`

```lean
selbergMobiusRatCoefficient_one
```

proves that the rational Mobius coefficient used by TS122 is `1` at `1`.

### TS123-R4: denominator positivity bridge

```lean
selbergOptimizationDenominator_pos_of_jordanTwo_pos
```

proves that, for `0 < level`, positivity of `J2` on the TS122 support implies
positivity of the TS122 optimization denominator.

### TS123-R5: constrained energy lower bound from only `J2` positivity

```lean
selbergDiagonalEnergy_lower_bound_of_jordanTwo_pos
```

combines TS122's Cauchy lower bound with TS123's denominator positivity bridge.

## Remaining obligations

TS123 does not yet prove:

- `J2(d) > 0` for every positive support index;
- the equality case / normalization of the optimal vector candidate;
- Selberg's sieve bound;
- Brun-Titchmarsh;
- any prime-count estimate.

Those are kept as explicit local obligations in
`SelbergJordanTwoPositivityProbe`.

## Verification commands

```powershell
lake env lean TS\Goldbach\Strong\TS123\SelbergJordanTwoPositivityProbe.lean
lake build TS.Goldbach.Strong.TS123.SelbergJordanTwoPositivityProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS123
git diff --check -- README.md TS\Goldbach\Strong\TS123\SelbergJordanTwoPositivityProbe.lean TS\Goldbach\Strong\TS123\TS123_Audit.md
```

## Verdict

TS123 keeps the next step honest. It proves the denominator positivity bridge
needed by TS122, while making explicit that the current support is positive
and bounded but not squarefree-only. The remaining hard arithmetic task is now
precisely the positivity of the Jordan-two coefficient on that support.
