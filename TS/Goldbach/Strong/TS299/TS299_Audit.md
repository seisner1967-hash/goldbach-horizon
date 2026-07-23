# TS299 Audit - Finite-Grid Strong Height and Reciprocal-Load Bound

## Scope

TS299 replaces the arbitrary finite-avoidance height of TS296 by an explicit
finite-grid selection. It constructs a height in `(T,T+1)` with both a
positive closed separation from nearby zero ordinates and an effective
multiplicity-weighted reciprocal-load bound.

The proof is finite and unconditional. It uses the cumulative TS290 zero
count, but it does not assume a unit-interval zero-density estimate.

## Grid geometry

Let

```text
M_T = sum_{rho in nearbyConcreteZeros T} multiplicity(rho),
K_T = 4 * (M_T + 1).
```

TS299 places `K_T` equally spaced midpoints in `(T,T+1)` and sets

```text
delta_T = 1 / (4 * K_T).
```

For a fixed zero ordinate, two distinct grid points cannot both lie within
`delta_T`: their spacing is at least `1/K_T`, whereas two forbidden gaps
would give a distance below `2*delta_T = 1/(2*K_T)`. Therefore each nearby
zero forbids at most one grid index.

Since every concrete zero has positive multiplicity,

```text
card(badGridIndices T) <= card(nearbyConcreteZeros T) <= M_T.
```

Consequently at least half of the `K_T` indices are good. In particular the
good grid is nonempty.

## Harmonic kernel estimate

For every real ordinate `a`, TS299 proves the uniform finite estimate

```text
sum_{k < K} 1 / max(1/(4*K), |gridPoint(T,K,k) - a|)
  <= 8 * K * H_K.
```

The proof is split into `a <= T`, `T < a < T+1`, and `T+1 <= a`. In the
interior case, `floor(K*(a-T))` identifies the nearest grid index and reduces
the sum to

```text
sum_{k < K} 1 / (Nat.dist k j + 1) <= 2 * H_K.
```

No singular integral or Stieltjes argument is used.

## Averaged reciprocal load

On every good grid index, the truncated denominator equals the actual zero
height gap. Swapping the two finite sums and applying the harmonic estimate
gives

```text
sum_{k in goodGridIndices T} reciprocalZeroLoad(T,gridPoint k)
  <= M_T * 8 * K_T * H_(K_T).
```

Because `K_T <= 2 * card(goodGridIndices T)`, finite averaging selects a
concrete index satisfying

```text
reciprocalZeroLoad(T,finiteGridStrongTau T)
  <= 16 * M_T * H_(K_T).
```

The selected point simultaneously satisfies the exact gap
`finiteGridStrongDelta T = 1/(4*K_T)`.

## Contour routing

`finiteGridStrongPerronContourData` is a concrete
`TS294.QuantitativelyCleanPerronContourData`. The top and bottom sides are
zero-free by the concrete zero characterization from TS296 and the new grid
gap. The fixed left side reuses the unconditional TS296 functional-equation
argument.

Thus `finiteGridStrongCleanPerronContourExistence` inhabits the TS295 strong
clean-height contract with the exact grid separation and exact harmonic load
envelope.

## Closed TS290 envelopes

The natural nearby multiplicity mass is proved equal to
`TS270.concreteMultiplicityCountUpToHeight (T+2)`. TS290 therefore gives

```text
A(T) = xiGlobalLogLinearConstant * (T+2) * log(T+4),
M_T <= A(T).
```

Using `H_K <= 1 + log K`, TS299 obtains the closed load envelope

```text
finiteGridClosedLoadEnvelope(T)
  = 16 * A(T) * (1 + log(4 * (A(T) + 1))).
```

It also proves the closed separation rate

```text
finiteGridClosedDelta(T)
  = 1 / (16 * (A(T) + 1))
  <= finiteGridStrongDelta(T).
```

The theorem `finiteGridClosedStrongPerronContourExistence` populates the
TS295 contract directly with these two closed functions. This is the
expected coarse `T log(T)^2` reciprocal-load scale obtainable from the
cumulative TS290 count alone.

## Dependency hygiene

TS299 uses only finite grids, finite zero selections, the elementary harmonic
bound from Mathlib, the concrete TS296 zero characterization, and the TS290
global multiplicity count. It does not use RH, a local zero-density theorem,
an infinite Hadamard product, Borel-Caratheodory, or contour integration.

## Open frontier

The following remain intentionally unproved:

- an effective local logarithm sphere bound for the finite xi quotient;
- an effective rate for the xi/zeta completion correction;
- decay of the full integrated horizontal envelope;
- the fixed-left boundary estimate;
- completeness and evaluation of exceptional residues;
- Perron inversion and the meromorphic rectangle residue theorem;
- an infinite explicit formula;
- Gallagher, OTSA, or Goldbach.

## Verification

- Target build: `2995/2995`.
- Global build: `2664/2664`.
- No unchecked declaration placeholders in TS299.
- Source and audit are ASCII-only.
- Git whitespace validation is clean.
