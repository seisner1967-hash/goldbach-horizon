# TS319 Audit - Nonresonant Discrete Logarithmic Phase Bound

## Scope

TS319 proves the unit-modulus and small-frequency parts of the TS318 phase
contract.  It certifies the exact logarithmic phase increments on a dyadic
window, reduces negative frequencies to positive ones by conjugation, and
inhabits the indexed TS318 contract with an unconditional height-dependent
constant.

The module deliberately distinguishes that coarse closure from a uniform
Kusmin-Landau estimate.  It does not claim a height-independent oscillatory
constant, close-pair smallness, a rational half-budget, RH, OTSA, or Goldbach.

## Main declarations

```lean
TS319.Goldbach.discreteLogPhase_norm_eq_one
TS319.Goldbach.discreteLogPhasePartialSum_norm_le_scale
TS319.Goldbach.discreteLogPhasePartialSum_neg_norm_eq

TS319.Goldbach.logarithmicPhaseIncrement
TS319.Goldbach.discreteLogPhase_succ_eq_mul_exp_increment
TS319.Goldbach.log_succ_div_self_bounds
TS319.Goldbach.logarithmicPhaseIncrement_succ_le
TS319.Goldbach.logarithmicPhaseIncrement_dyadic_bounds

TS319.Goldbach.coarseLogPhaseConstant
TS319.Goldbach.coarseNonresonantDiscreteLogPhasePartialSumBound
TS319.Goldbach.coarseWeightedKusminLandauKernelBound

TS319.Goldbach.OscillatoryDiscreteLogPhasePartialSumBoundStatement
TS319.Goldbach.UniformOscillatoryDiscreteLogPhasePartialSumBoundStatement
TS319.Goldbach.UniformNonresonantDiscreteLogPhasePartialSumBoundStatement
TS319.Goldbach.nonresonantBound_of_oscillatoryBound
```

## Small-frequency branch

For every positive natural scale, the pure logarithmic phase has norm one:

```text
norm (x^(I*t)) = 1.
```

The triangle inequality and the exact cardinality of `Ico X Y` therefore
give, whenever `X <= Y <= 2*X`,

```text
norm (sum x in Ico X Y, x^(I*t)) <= X.
```

If `abs(t) <= 1`, the safe TS318 decay weight is exactly one.  This closes
the slowly oscillating branch with constant one.

## Frequency symmetry

TS319 proves

```text
discreteLogPhase x (-t) = conj (discreteLogPhase x t)
```

and transports this identity through every finite partial sum.  Since complex
conjugation preserves the norm, the future sharp estimate only needs a direct
positive-frequency proof.

## Dyadic increment geometry

The consecutive phase increment is

```text
Delta_t(n) = t * log ((n+1)/n).
```

It is connected to the complex phase by the exact recurrence

```text
(n+1)^(I*t) = n^(I*t) * exp (I * Delta_t(n)).
```

For positive `n`, TS319 proves

```text
1/(n+1) <= log ((n+1)/n) <= 1/n.
```

For nonnegative frequency, the increments decrease with `n`.  Under
`X <= n < 2*X`, `1 < t <= 2*T`, and `4*T <= X`, they satisfy

```text
t/(2*X) <= Delta_t(n) <= 1/2.
```

This is the precise monotone nonresonant regime required by a discrete
Kusmin-Landau argument.  TS319 records the geometry without postulating the
generic oscillatory theorem.

## Coarse indexed closure

The TS318 contract is indexed by fixed `X` and `T`; it does not require its
constant to be uniform in height.  TS319 therefore proves it unconditionally
with

```text
coarseLogPhaseConstant(T) = max(1, 2*T).
```

Indeed, `abs(t) <= 2*T` implies

```text
X <= max(1,2*T) * X / max(1,abs(t)).
```

This also inhabits the TS317 pointwise weighted-kernel contract with constant
`4 * coarseLogPhaseConstant(T)`.  The result is a genuine finite bound, but it
does not provide the height-independent small constant needed downstream.

## Uniform oscillatory boundary

`OscillatoryDiscreteLogPhasePartialSumBoundStatement` isolates the branch
`1 < abs(t) <= 2*T`.  `nonresonantBound_of_oscillatoryBound` combines any such
estimate with the proved small-frequency branch, using constant `max(1,C)`.

The uniform versions quantify one constant over all compatible `X` and `T`.
They are defined and routed, but not inhabited.  This is the exact remaining
Kusmin-Landau obligation; no global axiom is introduced.

## Fail-closed boundary

The following remain open:

```text
UniformOscillatoryDiscreteLogPhasePartialSumBoundStatement
WeightedClosePairEnvelopeBoundStatement smallness
NormalizedTraceBudgetData with traceBudget <= 1/2
RH
OTSA
Goldbach
```

The coarse height-dependent inhabitant must not be reported as uniform
oscillatory smallness.

## Verification

```text
Targeted build: 3040/3040
Global build:   2664/2664
Lean placeholders (`sorry`, `axiom`, `opaque`, `admit`): none
Non-ASCII characters: none
git diff --check: clean
```
