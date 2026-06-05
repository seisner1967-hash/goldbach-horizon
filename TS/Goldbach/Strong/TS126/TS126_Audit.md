# TS126 Audit - Selberg Jordan-Two Multiplicativity API Probe

## Scope

TS126 opens the multiplicative route from the TS125 prime-power positivity
facts toward the global positivity input used by TS124/TS123/TS122.

## Concrete Lean objects

The sprint adds:

```lean
TS126.Goldbach.selbergJordanTwoFunction_isMultiplicative
TS126.Goldbach.selbergJordanTwoCoefficient_mul_of_coprime
TS126.Goldbach.selbergJordanTwoCoefficient_factorization
TS126.Goldbach.selbergJordanTwoCoefficient_pos_of_prime_pow
TS126.Goldbach.SelbergJordanTwoPositiveOnPrimePowersFactorizationShape
TS126.Goldbach.selbergJordanTwoPositiveOnPrimePowersFactorizationShape
TS126.Goldbach.SelbergJordanTwoMultiplicativePositiveProductRoute
TS126.Goldbach.SelbergJordanTwoMultiplicativityAPIProbe
TS126.Goldbach.selbergJordanTwoMultiplicativityAPIProbe
TS126.Goldbach.SelbergJordanTwoMultiplicativityAPIProbeTarget
TS126.Goldbach.selbergJordanTwoMultiplicativityAPIProbeTarget
TS126.Goldbach.selbergJordanTwoPrimePowerPositivityProbeTarget
```

## What is proved

The corrected Jordan-two arithmetic function

```lean
TS119.Goldbach.selbergJordanTwoFunction
```

is multiplicative over `Rat`. The proof uses the multiplicativity of
`ArithmeticFunction.moebius`, transports it to `Rat` by `intCast`, and multiplies
it with `ArithmeticFunction.isMultiplicative_pow`.

The scalar coefficient then gets two concrete API bridges:

```text
J2(m*n) = J2(m) * J2(n)
```

for coprime `m,n`, and

```text
J2(n) = product over n.factorization of J2(p^k)
```

for `n != 0`, via `ArithmeticFunction.multiplicative_factorization`.

TS126 also rewrites the TS125 prime-power positivity result into the exponent
positive shape used by `Nat.factorization`:

```text
p prime and 0 < k imply 0 < J2(p^k).
```

## Remaining obligations

TS126 does not yet prove the finite-product positivity step over an arbitrary
positive integer. That next local step is recorded as

```lean
TS126.Goldbach.SelbergJordanTwoMultiplicativePositiveProductRoute
```

which is definitionally the global positive-integer `J2` input from TS124.

The optimal vector normalization, the Selberg sieve bound, Brun-Titchmarsh,
the spectral trace formula, and the Mellin-tail API contracts remain outside
this sprint.

## Verification

Expected checks:

```text
lake build TS.Goldbach.Strong.TS126.SelbergJordanTwoMultiplicativityAPIProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS126
git diff --check -- README.md TS\Goldbach\Strong\TS126\SelbergJordanTwoMultiplicativityAPIProbe.lean TS\Goldbach\Strong\TS126\TS126_Audit.md
```
