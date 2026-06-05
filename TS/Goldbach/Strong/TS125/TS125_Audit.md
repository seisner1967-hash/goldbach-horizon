# TS125 Audit - Selberg Jordan-Two Prime-Power Positivity Probe

## Scope

TS125 extends the TS124 local Jordan-two positivity facts from `1` and primes
to all positive prime powers. It is still not the full multiplicative
positivity theorem for all positive integers.

Lean file:

```text
TS/Goldbach/Strong/TS125/SelbergJordanTwoPrimePowerPositivityProbe.lean
```

## Main declarations

```lean
TS125.Goldbach.selbergJordanTwoCoefficient_prime_pow_succ
TS125.Goldbach.selbergJordanTwoCoefficient_pos_of_prime_pow_succ
TS125.Goldbach.selbergJordanTwoCoefficient_four
TS125.Goldbach.selbergJordanTwoCoefficient_four_pos
TS125.Goldbach.SelbergJordanTwoPositiveOnPrimePowers
TS125.Goldbach.selbergJordanTwoPositiveOnPrimePowers
TS125.Goldbach.SelbergJordanTwoPrimePowerPositivityProbe
TS125.Goldbach.selbergJordanTwoPrimePowerPositivityProbe
TS125.Goldbach.SelbergJordanTwoPrimePowerPositivityProbeTarget
TS125.Goldbach.selbergJordanTwoPrimePowerPositivityProbeTarget
TS125.Goldbach.selbergJordanTwoPositivityAPIProbeTarget
```

## Concrete proofs

TS125 proves the normalized positive-prime-power formula:

```text
J2(p^(k+1)) = p^(2*(k+1)) - p^(2*k)
```

for every prime `p` and every natural `k`. The proof uses the TS119 local
divisor-sum collapse twice, rewrites divisor sums of prime powers with
`Nat.sum_divisors_prime_pow`, isolates the final range term with
`Finset.sum_range_succ`, and normalizes exponents explicitly.

TS125 then proves:

```text
J2(p^(k+1)) > 0
```

by factoring

```text
p^(2*(k+1)) - p^(2*k) = p^(2*k) * (p^2 - 1)
```

over `Rat`.

The sprint also records the non-squarefree support diagnostic from TS123 in
coefficient form:

```text
J2(4) = 12
J2(4) > 0
```

## Remaining obligations

TS125 does not yet prove:

- multiplicativity of the local positivity result across coprime factors;
- full positive-integer positivity of `J2`;
- optimal vector normalization;
- equality in weighted Cauchy;
- Selberg's sieve bound;
- Brun-Titchmarsh;
- any prime-count estimate.

## Verification

Commands:

```powershell
lake env lean TS\Goldbach\Strong\TS125\SelbergJordanTwoPrimePowerPositivityProbe.lean
lake build TS.Goldbach.Strong.TS125.SelbergJordanTwoPrimePowerPositivityProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS125
git diff --check -- README.md TS\Goldbach\Strong\TS125\SelbergJordanTwoPrimePowerPositivityProbe.lean TS\Goldbach\Strong\TS125\TS125_Audit.md
```

Expected result: build succeeds; no forbidden proof placeholders and no
non-ASCII in TS125; diff check is clean.

## Status

```text
repo_committed_relative
```

TS125 is relative because the jump from prime powers to all positive integers
still requires the multiplicative positivity route.
