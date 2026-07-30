# TS321 Audit - Weighted Shell Envelope Assembly

## Scope

TS321 decomposes the exact finite `weightedClosePairEnvelope` from TS317.  It
does not redefine that envelope and does not discard the TS316 coefficient
weights.  Every off-diagonal pair belongs either to the close regime
`gap <= 1` or to one unique shell `(k,k+1]` with `1 <= k < 2*T`.

The module separates two shell objects: coefficient mass without the gap
weight, and envelope mass with the exact TS317 weight.  This distinction makes
the identity and the subsequent `1/k` majorization explicit.

## Main declarations

```lean
TS321.Goldbach.zeroPairCoefficientMass
TS321.Goldbach.weightedNearPairCoefficientMass
TS321.Goldbach.weightedGapShellCoefficientMass
TS321.Goldbach.weightedGapShellEnvelopeMass

TS321.Goldbach.gapShellIndex
TS321.Goldbach.gapShellIndex_spec
TS321.Goldbach.gapShellIndex_mem
TS321.Goldbach.gapShellIndex_unique

TS321.Goldbach.weightedClosePairEnvelope_eq_near_add_envelopeShells
TS321.Goldbach.weightedGapShellEnvelopeMass_le_one_div_mul_coefficientMass
TS321.Goldbach.weightedClosePairEnvelope_le_coefficientShellAssembly

TS321.Goldbach.WeightedNearPairMassBoundStatement
TS321.Goldbach.WeightedPairShellCoefficientMassBoundStatement
TS321.Goldbach.weightedClosePairEnvelopeBound_of_local_coefficient_bounds
TS321.Goldbach.WeightedLocalShellBoundData
```

## Exact shell indexing

For every real gap greater than one, TS321 defines

```text
gapShellIndex(gap) = Nat.ceil(gap) - 1.
```

It proves

```text
gapShellIndex(gap) < gap <= gapShellIndex(gap) + 1.
```

This convention assigns an integral gap `n` to shell `(n-1,n]`, so no boundary
pair is lost or counted twice.  The TS318 height bound `gap <= 2*T` places the
index in `Finset.Ico 1 (2*T)`.  The nominal shell `k = 2*T` is necessarily
empty and is not included.

## Close regime

When `gap <= 1`, the TS317 safe weight is exactly

```text
1 / max(1,gap) = 1.
```

Thus the close contribution is the coefficient mass itself.  There is no
division by a zero gap and no minimal-spacing assumption.

## Shell partition

TS321 first proves the identity pair by pair and then applies finite Fubini to
obtain

```text
weightedClosePairEnvelope T
  = weightedNearPairCoefficientMass T
      + sum k in Ico 1 (2*T), weightedGapShellEnvelopeMass T k.
```

All sums remain over the concrete finite `truncatedZeroSet T` and its
off-diagonal `erase` sets.

## Correct shell weight

On shell `(k,k+1]`, with `1 <= k`, the gap satisfies `k < gap`.  Hence

```text
1 / max(1,gap) = 1/gap <= 1/k.
```

Termwise comparison gives

```text
weightedGapShellEnvelopeMass T k
  <= (1/k) * weightedGapShellCoefficientMass T k.
```

The complete assembly therefore uses `1/k`, not `1/(k+1)`.

## Local-to-global adapter

`WeightedNearPairMassBoundStatement` certifies a close-mass majorant.
`WeightedPairShellCoefficientMassBoundStatement` certifies the coefficient
mass in one shell.  From these inputs TS321 constructs the existing TS317
contract with majorant

```text
nearMajorant
  + sum k in Ico 1 (2*T), (1/k) * shellMajorant k.
```

`WeightedLocalShellBoundData` packages exactly these inputs for TS322.  Its
existence with numerically small fields is not claimed.

## Coarse unconditional bound

TS321 re-exports the already proved TS317 estimate

```text
weightedClosePairEnvelope T <= globalLinearSpectralMass ^ 2.
```

This majorant is uniform in `T`, but no claim is made that it is small enough
for the rational half-budget.

## Fail-closed boundary

The following remain open:

```text
effective near-pair coefficient-mass smallness
effective shell coefficient-mass smallness
rational majorants satisfying the TS181 half-budget
OTSA
Goldbach
```

No Montgomery conjecture, minimal zero spacing, linear independence of
logarithms, RH, or global axiom is introduced.

## Verification

```text
Targeted build: 3042/3042
Global build:   2664/2664
Lean placeholders (`sorry`, `axiom`, `opaque`, `admit`): none
Non-ASCII characters: none
git diff --check: clean
```
