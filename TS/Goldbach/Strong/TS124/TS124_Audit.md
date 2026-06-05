# TS124 Audit - Selberg Jordan-Two Positivity API Probe

## Scope

TS124 starts the concrete positivity discharge above the TS123 denominator
bridge. It does not prove full multiplicative positivity of `J2`; instead, it
proves local arithmetic facts and packages the exact bridge from future global
positive-integer positivity to the TS122/TS123 optimization layer.

Lean file:

```text
TS/Goldbach/Strong/TS124/SelbergJordanTwoPositivityAPIProbe.lean
```

## Main declarations

```lean
TS124.Goldbach.selbergJordanTwoCoefficient_one
TS124.Goldbach.selbergJordanTwoCoefficient_prime
TS124.Goldbach.selbergJordanTwoCoefficient_pos_of_prime
TS124.Goldbach.SelbergJordanTwoPositiveOnPositiveNat
TS124.Goldbach.selbergJordanTwoPositiveOnSupport_of_positiveNat
TS124.Goldbach.selbergOptimizationDenominator_pos_of_positiveNat
TS124.Goldbach.selbergDiagonalEnergy_lower_bound_of_positiveNat
TS124.Goldbach.SelbergJordanTwoPositivityAPIProbe
TS124.Goldbach.selbergJordanTwoPositivityAPIProbe
TS124.Goldbach.SelbergJordanTwoPositivityAPIProbeTarget
TS124.Goldbach.selbergJordanTwoPositivityAPIProbeTarget
TS124.Goldbach.selbergJordanTwoPositivityProbeTarget
```

## Concrete proofs

TS124 proves the first local Jordan-two positivity facts:

```text
J2(1) = 1
J2(p) = p^2 - 1 for prime p
J2(p) > 0 for prime p
```

The prime calculation expands the Dirichlet convolution defining `J2`, rewrites
the antidiagonal convolution through `Nat.sum_divisorsAntidiagonal`, uses
`Nat.sum_divisors_prime_pow`, and then normalizes the two prime-power terms.

TS124 also introduces the global positivity input:

```lean
SelbergJordanTwoPositiveOnPositiveNat
```

and proves that this single future theorem implies:

```text
J2 positivity on the TS122 support,
positivity of the TS122 optimization denominator,
the constrained TS122 diagonal lower bound.
```

## Remaining obligations

TS124 does not yet prove:

- full positive-integer positivity of `J2`;
- the multiplicative/product formula for Jordan-two;
- optimal vector normalization;
- equality in weighted Cauchy;
- Selberg's sieve bound;
- Brun-Titchmarsh;
- any prime-count estimate.

## Verification

Commands:

```powershell
lake env lean TS\Goldbach\Strong\TS124\SelbergJordanTwoPositivityAPIProbe.lean
lake build TS.Goldbach.Strong.TS124.SelbergJordanTwoPositivityAPIProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS124
git diff --check -- README.md TS\Goldbach\Strong\TS124\SelbergJordanTwoPositivityAPIProbe.lean TS\Goldbach\Strong\TS124\TS124_Audit.md
```

Expected result: build succeeds; no forbidden proof placeholders and no
non-ASCII in TS124; diff check is clean.

## Status

```text
repo_committed_relative
```

TS124 is relative because the full positivity theorem
`forall d > 0, 0 < J2(d)` remains open. It gives concrete local positivity at
`1` and at primes, and it proves the exact bridge needed to feed TS123 once the
full positivity theorem is available.
