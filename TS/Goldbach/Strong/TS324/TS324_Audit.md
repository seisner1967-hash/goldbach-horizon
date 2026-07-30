# TS324 Audit - Certified Zero-Cover Semantics

## Scope

TS324 introduces the semantic boundary between an untrusted rational zero-box
payload and the concrete finite zeta-zero truncation used by TS315--TS323.  It
defines an executable rational upper bound for the TS322 finite weighted core
and proves that every certified cover validates this bound.

The module does not check a payload, construct an analytic zero cover, import
an empirical zero table, or inhabit the TS323 half-budget certificate.

## Main declarations

```lean
TS324.Goldbach.RationalInterval
TS324.Goldbach.ZeroBoxPayload
TS324.Goldbach.ZeroCoverPayload
TS324.Goldbach.PayloadWellFormed

TS324.Goldbach.corePairWeight
TS324.Goldbach.rationalGapShellIndex
TS324.Goldbach.rationalCorePairWeight
TS324.Goldbach.intervalDistance
TS324.Goldbach.maximalCompatibleCoreWeight
TS324.Goldbach.computedCoreMajorant

TS324.Goldbach.zeroLiesInBox
TS324.Goldbach.boxCoefficientMass
TS324.Goldbach.CertifiedTruncatedZeroCover

TS324.Goldbach.finiteWeightedLocalCore_eq_weightedPairSum
TS324.Goldbach.finiteWeightedLocalCore_le_computedCoreMajorant

TS324.Goldbach.TS324Ledger
TS324.Goldbach.ts324Ledger
```

## Trust boundary

`RationalInterval`, `ZeroBoxPayload`, and `ZeroCoverPayload` contain data only.
They carry no proofs and are suitable for a later untrusted external
generator.  `PayloadWellFormed` records only rational interval validity and
nonnegative declared coefficient masses.

The analytic information is isolated in
`CertifiedTruncatedZeroCover H data`.  It states exactly:

```text
every zero in truncatedZeroSet H lies in at least one indexed box;
the exact TS316 coefficient mass in each box is at most its rational bound.
```

The box-mass condition depends on the true zeta zeros and remains outside the
future Boolean checker.  No field of the semantic cover contains the desired
finite-core conclusion.

## Exact core weight

The TS322 finite core uses the stepwise weight

```text
1                              when gap <= 1,
1 / (Nat.ceil gap - 1)         when gap > 1.
```

TS324 proves this weight is nonnegative and antitone.  It also proves that the
rational implementation using `Nat.ceil` on `Rat` casts exactly to the real
weight.  The theorem `finiteWeightedLocalCore_eq_weightedPairSum` rewrites the
TS321 near-plus-shell definition as the exact nested ordered-pair sum with
this weight.  No inequality or rational approximation occurs in this step.

## Interval geometry

For two ordinate intervals TS324 defines

```text
max 0 (max (J.lower - I.upper) (I.lower - J.upper)).
```

This rational quantity is proved to be a lower bound for the actual ordinate
gap of every two contained zeros.  Antitonicity therefore gives the correctly
oriented safe inequality

```text
actual core weight <= rational weight at the interval distance.
```

Only the lower gap endpoint is required.  No midpoint classification and no
upper gap endpoint enter the proof.

## Box overcount

For every ordered zero pair, coverage supplies at least one box for each
endpoint.  The actual pair term is bounded by the sum of all compatible
ordered box-pair terms.  After summing over zeros, finite Fubini reordering
factorizes each box block as

```text
boxCoefficientMass i * boxCoefficientMass j * boxWeight i j.
```

The semantic mass bounds then yield exactly the cast of
`computedCoreMajorant data`.  The box double sum is ordered, so no extra factor
two is introduced.  Its diagonal terms deliberately use the full square of a
box mass and hence dominate all distinct internal zero pairs.

Box disjointness is not needed for soundness: overlaps merely add positive
terms and weaken the numerical bound.  A future checker may impose
disjointness as a data-quality policy.

## Fail-closed boundary

TS324 does not provide:

```text
a Boolean payload checker;
an inhabitant of CertifiedTruncatedZeroCover;
a concrete empirical zero dataset;
a claimed rational core majorant beyond the computed box sum;
an inhabitant of TS323.CertifiedRationalTraceBudgetData;
an unconditional half-budget, OTSA, or Goldbach theorem.
```

The next intended split is:

```text
TS325  executable payload checker and declared-majorant reflection
TS326  analytic validation of zero coverage and completeness
TS327  attempted concrete TS323 certificate habitation
```

## Verification

```text
Targeted build: 3044/3044
Global build:   2664/2664
Lean placeholders (`sorry`, `axiom`, `opaque`, `admit`): none
Non-ASCII characters: none
git diff --check: clean
```
