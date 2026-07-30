# TS325 Audit - Executable Payload Budget Checker

## Scope

TS325 closes the decidable checker front for the proof-free TS324 rational
zero-box payload.  It checks interval validity, nonnegative declared box
masses, and the comparison of the executable `computedCoreMajorant` with a
declared rational majorant.  It proves an exact reflection theorem and routes a
successful check, conditionally on the independent TS324 analytic cover, to a
real upper bound for the finite TS322 core.

The module does not inspect concrete zeta zeros, decide analytic coverage,
construct box-mass certificates, or claim that any declared majorant is small
enough for the TS323 half-budget.

## Main declarations

```lean
TS325.Goldbach.checkRationalInterval
TS325.Goldbach.checkZeroBoxPayload
TS325.Goldbach.checkPayloadWellFormed
TS325.Goldbach.checkRationalInterval_iff
TS325.Goldbach.checkZeroBoxPayload_iff
TS325.Goldbach.checkPayloadWellFormed_iff
TS325.Goldbach.payloadWellFormedDecidable

TS325.Goldbach.checkPayloadBudget
TS325.Goldbach.PayloadBudgetClaim
TS325.Goldbach.checkPayloadBudgetClaim
TS325.Goldbach.checkPayloadBudget_iff
TS325.Goldbach.checkPayloadBudgetClaim_iff

TS325.Goldbach.finiteWeightedLocalCore_le_of_check
TS325.Goldbach.finiteWeightedLocalCore_le_of_claim_check

TS325.Goldbach.TS325Ledger
TS325.Goldbach.ts325Ledger
```

## Structural reflection

Every rational proposition is converted explicitly through `decide`.  The
array checker validates exactly the three fields of `TS324.PayloadWellFormed`:

```text
real interval lower <= upper;
imaginary interval lower <= upper;
0 <= coefficientMassUpper.
```

The theorem `checkPayloadWellFormed_iff` proves equivalence with the TS324
proposition and supports a local `Decidable` instance.  No decidability
instance is introduced for `CertifiedTruncatedZeroCover`.

## Declared-majorant reflection

The complete executable check is

```text
checkPayloadWellFormed data
  && decide (computedCoreMajorant data <= declared).
```

Consequently `checkPayloadBudget_iff` reflects exactly

```text
PayloadWellFormed data
  /\ computedCoreMajorant data <= declared.
```

`PayloadBudgetClaim` contains only the raw payload and the declared rational
bound.  It stores no duplicate Boolean flag and cannot become inconsistent
with a separately stored checker result.

## Conditional semantic routing

Given a successful Boolean check and
`CertifiedTruncatedZeroCover H data`, TS324 yields

```text
finiteWeightedLocalCore H <= computedCoreMajorant data.
```

The reflected rational comparison is cast to `Real` and closes

```text
finiteWeightedLocalCore H <= declared.
```

The analytic cover remains an explicit theorem argument.  The Boolean checker
does not construct, inspect, or decide it.

## Fail-closed boundary

TS325 does not provide:

```text
an inhabitant or a Decidable instance for CertifiedTruncatedZeroCover;
an analytic zero-coverage or completeness argument;
a concrete empirical zero dataset;
a proof that a checked majorant is numerically useful;
an inhabitant of TS323.CertifiedRationalTraceBudgetData;
an unconditional half-budget, OTSA, or Goldbach theorem.
```

In particular, executability does not imply that the current constants permit
a trace budget at most one half.  That remains a quantitative analytic and
certification question.

The next intended split is:

```text
TS326  analytic validation of zero coverage and box coefficient masses
TS327  attempted concrete TS323 certificate habitation
```

## Verification

```text
Targeted build: 3045/3045
Global build:   2664/2664
Lean placeholders (`sorry`, `axiom`, `opaque`, `admit`): none
Non-ASCII characters: none
git diff --check: clean
```
