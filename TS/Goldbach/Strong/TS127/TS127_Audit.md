# TS127 Audit - Selberg Jordan-Two Full Positivity Discharge

## Scope

TS127 closes the global positivity input for the corrected Selberg Jordan-two
coefficient.

The sprint combines:

```text
TS125: positivity of J2(p^k) for prime p and 0 < k
TS126: multiplicativity and the Nat.factorization product formula for J2
```

with finite-product positivity over `Rat`.

## Concrete Lean objects

The sprint adds:

```lean
TS127.Goldbach.selbergJordanTwoCoefficient_pos_of_pos
TS127.Goldbach.selbergJordanTwoPositiveOnPositiveNat
TS127.Goldbach.selbergJordanTwoPositiveOnSupport
TS127.Goldbach.selbergOptimizationDenominator_pos
TS127.Goldbach.selbergDiagonalEnergy_lower_bound
TS127.Goldbach.SelbergJordanTwoFullPositivityDischarge
TS127.Goldbach.selbergJordanTwoFullPositivityDischarge
TS127.Goldbach.SelbergJordanTwoFullPositivityDischargeTarget
TS127.Goldbach.selbergJordanTwoFullPositivityDischargeTarget
TS127.Goldbach.selbergJordanTwoMultiplicativityAPIProbeTarget
```

## What is proved

For every positive natural number `n`, TS127 proves:

```lean
0 < TS119.Goldbach.selbergJordanTwoCoefficient n
```

The proof rewrites `J2(n)` using the TS126 factorization formula:

```text
J2(n) = product over n.factorization of J2(p^k)
```

then unfolds `Finsupp.prod` to a product over the factorization support. For
each support entry, Mathlib gives `p.Prime` from `Nat.prime_of_mem_primeFactors`
and `0 < n.factorization p` from `Finsupp.mem_support_iff`. TS126 then supplies
the positivity of the corresponding prime-power coefficient.

TS127 also packages the consequences already wired by TS124:

```text
global J2 positivity
  -> supportwise J2 positivity
  -> TS122 denominator positivity
  -> constrained diagonal energy lower bound
```

## Remaining obligations

TS127 does not construct the optimal vector, prove the equality case in weighted
Cauchy, prove the Selberg sieve bound, discharge Brun-Titchmarsh, or address
the spectral trace and Mellin-tail terminal packages.

## Verification

Expected checks:

```text
lake build TS.Goldbach.Strong.TS127.SelbergJordanTwoFullPositivityDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS127
git diff --check -- README.md TS\Goldbach\Strong\TS127\SelbergJordanTwoFullPositivityDischarge.lean TS\Goldbach\Strong\TS127\TS127_Audit.md
```
