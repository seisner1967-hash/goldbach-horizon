# TS326 Audit - Zero-Count Saturation Cover

## Scope

TS326 reduces the analytic TS324 zero-cover obligation to independent global
and local multiplicity-count certificates. An exact global count, disjoint
box-local lower counts, and saturation force exhaustive coverage of the finite
zero truncation. A separate rational ordinate allocation converts the derived
total multiplicity bound in every box into the TS324 coefficient-mass bound.

The module does not evaluate the Riemann zeta function, prove a Turing count,
construct local sign-change certificates, import empirical zeros, or claim
that the resulting TS324 core majorant can satisfy the TS323 half-budget.

## Main declarations

```lean
TS326.Goldbach.concreteZeroMultiplicity
TS326.Goldbach.truncatedMultiplicityMass
TS326.Goldbach.boxMultiplicityTerm
TS326.Goldbach.boxMultiplicityMass

TS326.Goldbach.CertifiedGlobalZeroCount
TS326.Goldbach.CertifiedLocalZeroCountLower
TS326.Goldbach.CertifiedZeroCountSaturation

TS326.Goldbach.CertifiedZeroCountSaturation.sum_boxMultiplicityMass_eq_total
TS326.Goldbach.CertifiedZeroCountSaturation.boxMultiplicityMass_eq_localCount
TS326.Goldbach.CertifiedZeroCountSaturation.boxMultiplicityMass_le_payloadUpper
TS326.Goldbach.CertifiedZeroCountSaturation.covers_of_countSaturation

TS326.Goldbach.intervalAbsLower
TS326.Goldbach.intervalAbsLower_cast_le_abs
TS326.Goldbach.CertifiedCoefficientMassAllocation
TS326.Goldbach.zeroCoefficientMagnitude_le_multiplicity_div_lower
TS326.Goldbach.boxCoefficientMass_le_multiplicity_div_lower
TS326.Goldbach.coefficientMassValid_of_countSaturation
TS326.Goldbach.certifiedTruncatedZeroCover_of_countSaturation

TS326.Goldbach.TS326Ledger
TS326.Goldbach.zeroCountSaturationCoverLedger
```

## Count saturation

`truncatedMultiplicityMass H` is the exact sum of the concrete TS264 analytic
multiplicity over `TS315.truncatedZeroSet H`. The local mass in a box is the
same sum restricted by `TS324.zeroLiesInBox`.

The independent certificates state:

```text
truncatedMultiplicityMass H = N;
localCount i <= boxMultiplicityMass H box_i;
sum_i localCount i = N.
```

`CertifiedZeroCountSaturation` additionally requires that different boxes do
not share a true truncated zero and that `localCount i` is bounded by the
payload field `multiplicityUpper`. Here `multiplicityUpper` means total
multiplicity in the box, not the maximum multiplicity of one zero.

Disjointness gives

```text
sum_i boxMultiplicityMass H box_i <= truncatedMultiplicityMass H.
```

The local lower bounds and saturation give the reverse inequality, so both
sums are equal. Equality also forces every box mass to equal its local lower
count. If a truncated zero were missing from all boxes, its strictly positive
TS264 multiplicity would make the box sum strictly smaller than the global
sum. This contradiction proves `covers_of_countSaturation` without storing or
assuming the TS324 coverage conclusion.

The saturation certificate is a data structure in `Type`, rather than a
`Prop` structure, because it carries the witnesses `N` and `localCount`.
`CertifiedGlobalZeroCount` and `CertifiedLocalZeroCountLower` remain separate
propositions and must be inhabited by later analytic certificates.

## Coefficient-mass allocation

For an imaginary interval `[a,b]`, TS326 defines the computable rational bound

```text
intervalAbsLower = max 0 (max a (-b)).
```

Every ordinate in the interval has absolute value at least this quantity. If
the lower bound `u` is positive, TS269's universal denominator estimate gives

```text
zeroCoefficientMagnitude rho <= multiplicity rho / u^2.
```

Summing inside a box and using the saturated multiplicity bound yields

```text
boxCoefficientMass H box_i
  <= multiplicityUpper_i / u_i^2.
```

`CertifiedCoefficientMassAllocation` requires the entirely rational final
comparison

```text
multiplicityUpper_i / u_i^2 <= coefficientMassUpper_i.
```

It follows that every TS324 `coefficientMassValid` field is inhabited. Together
with saturation coverage this constructs
`CertifiedTruncatedZeroCover H data`.

Boxes whose imaginary interval meets zero cannot satisfy the positive-lower
condition and must be refined or handled by a separate future certificate.

## Fail-closed boundary

TS326 does not provide:

```text
an inhabitant of CertifiedGlobalZeroCount;
an inhabitant of CertifiedLocalZeroCountLower;
an inhabitant of CertifiedCoefficientMassAllocation for concrete payload data;
a zeta evaluator, Turing-method checker, or argument-principle checker;
an empirical zero payload;
a proof that a checked core majorant is numerically small;
an inhabitant of TS323.CertifiedRationalTraceBudgetData;
an unconditional half-budget, OTSA, or Goldbach theorem.
```

The next intended sprint is:

```text
TS327  attempted habitation of the analytic count inputs and the concrete
       TS323 rational trace-budget certificate
```

A classical count `N(T)` is commonly stated for positive ordinates, whereas
`truncatedMultiplicityMass H` uses the symmetric TS315 truncation. Any TS327
adapter from positive-ordinate data must therefore prove the conjugation
correspondence, rule out ordinate zero in the truncation, and account for the
resulting multiplicity factor explicitly.

## Verification

```text
Targeted build: 3046/3046
Global build:   2664/2664
Lean placeholders (sorry, axiom, opaque, admit): none
Non-ASCII characters: none
git diff --check: clean
```
