# TS301 Audit - Anchored Macroscopic Xi Quotient

## Scope

TS301 replaces the circular moving-center minimum-modulus proposal by a
concrete finite quotient normalized at the fixed point `2`.

The construction is unconditional and uses no infinite Hadamard product.  It
does not claim a closed asymptotic rate for the anchored real-part envelope.

## Macroscopic finite quotient

For height `T`, the module uses the TS290 dyadic factorization at inner radius

```text
64 * (T + 4).
```

The resulting TS285 quotient has all selected singularities filled and is
analytic and nonzero on the full buffered analytic disk.  The centered control
ball

```text
closedBall 2 (16 * (T + 4))
```

is proved to lie inside that disk.  Thus the quotient is genuinely analytic
and nonzero on a macroscopic neighborhood containing both horizontal Perron
segments.

The anchor is quantitative: xi is nonzero at `2` by the zero-free half-plane
theorem.  No lower bound at a moving horizontal center is assumed.

## Anchored logarithm

TS279 supplies a holomorphic logarithm of the concrete macroscopic quotient.
TS301 centers it at the fixed anchor:

```text
L0(z) = L(z) - L(2).
```

It proves

```text
exp(L0(z)) = Q_T(z) / Q_T(2)
```

throughout the control ball.  The centering removes the additive branch
constant exactly.

The image of `Re L0` on the compact control ball is compact.  Its supremum,
enlarged by one and capped below by one, gives a concrete strict positive
real-part envelope.  This is a valid finite bound, not a closed asymptotic
formula.

## Borel-Caratheodory and local Cauchy data

The TS300 Schwarz-transform theorem is applied after translating the fixed
anchor to zero.  It yields a norm bound for `L0` throughout the macroscopic
interior.

Every finite-grid horizontal center is at distance at most `T + 5` from the
anchor.  Its Cauchy sphere has radius

```text
2 * (T + 4),
```

and lies in the half-radius control ball.  Consequently TS301 constructs
actual `LocalHolomorphicLogCauchyData` for the normalized macroscopic quotient
on both horizontal sides and proves

```text
|Q_T'/Q_T| <= 2 * anchoredEnvelope(T) / (2 * (T + 4)).
```

The normalization by the fixed value `Q_T(2)` does not alter the logarithmic
derivative.

## Exact finite bridge

The module defines two named finite sums:

```text
macroscopicFiniteZeroLogDerivativeSum(T,s)
heightFiniteZeroLogDerivativeSum(T,s)
```

and their explicit difference.  From the two exact factorizations it proves

```text
g_height'/g_height
  = Q_macro'/Q_macro
    + (macroFiniteSum - heightFiniteSum).
```

The sign is `+`.  Algebraically, the macroscopic polynomial contains the
height polynomial and the additional factors, so

```text
g_height = P_extra * Q_macro.
```

Top and bottom versions are instantiated at the actual TS299 finite-grid
height.  Their nonvanishing obligations are discharged from the finite-grid
zeta zero-free lemmas and the exact xi/zeta multiplier bridge.

## Logical hygiene

The following routes are not used:

- a local minimum-modulus deduction from an upper boundary bound;
- a claim that all nontrivial zeros lie on the critical line;
- an infinite Hadamard product;
- an anonymous quotient remainder.

## Open frontier

The following remain intentionally unproved:

- a closed `O(T * log(T + 2)^2)` bound for the anchored compact envelope;
- decay of the extra finite macroscopic/height correction;
- decay of the complete horizontal quotient contribution;
- the completion-correction rate;
- the fixed-left boundary estimate;
- completeness and evaluation of exceptional residues;
- Perron inversion and the meromorphic rectangle residue theorem;
- an infinite explicit formula;
- Gallagher, OTSA, or Goldbach.

The next quantitative step should replace the compact supremum by explicit
upper and lower finite-product estimates on a quantitatively clean
macroscopic boundary.  TS301 has already removed the moving-center
minimum-modulus obstruction from that task.

## Verification

- Direct Lean compilation passes without warnings.
- Target build passes: `3001/3001`.
- Global build passes: `2664/2664`.
- Source and audit are ASCII-only.
- No unchecked declaration placeholders occur in TS301.
