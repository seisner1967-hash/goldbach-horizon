# TS256 Audit - Riemann Zeta Zero Truncated Contribution

## Scope

TS256 defines a finite, scale-dependent zero-contribution interface connecting
the TS185 Riemann-zeta zero API contract to the TS255 named zero function.

## Main Declarations

- `ZeroTruncationHeightFunction`
- `ZeroSpectralSummand`
- `RiemannZetaZeroTruncationData`
- `truncation_mem_nontrivialRiemannZetaZero`
- `ts93ZeroFamilyLedger_of_truncation`
- `zetaZeroTruncatedComplexSum`
- `zetaZeroTruncatedRealContribution`
- `truncatedZeroContributionFunction`
- `TruncatedZeroSumRealityStatement`
- `TruncatedZeroContributionIdentificationStatement`
- `truncatedZeroContributionFunction_identification`
- `decomposedObligations_of_truncatedZeroContribution`
- `fullyCorrectedCoreEvidence_of_truncatedZeroContribution`
- `RiemannZetaZeroTruncatedContributionLedger`
- `riemannZetaZeroTruncatedContributionTarget`

## Finite Truncation

For every natural scale, `RiemannZetaZeroTruncationData C` stores a
nonnegative height and a `Finset Complex`.  The finite set contains exactly the
zeros selected by `C.zeroSet` whose imaginary parts lie below that height.

The contract is an input type.  TS256 does not construct such a finite set or
prove local finiteness of the Riemann-zeta zeros.

## Finite Sum

`zetaZeroTruncatedComplexSum` sums an abstract spectral summand over the finite
set and multiplies each term by the TS185 multiplicity.  Keeping the summand
abstract avoids fixing an unverified Mellin normalization.

The TS255 zero function is the real part of this finite complex sum.  Reality
of the full sum is retained as the separate
`TruncatedZeroSumRealityStatement`; taking the real part does not discharge
that future symmetry obligation.

## Routing

TS256 constructs TS255 decomposed obligations and the TS253 fully corrected
core when the named identity and both bounds are supplied for the truncated
zero function and a separately named residual function.

The ledger stores the real truncation-to-TS93, truncation-to-zero-function, and
truncation-to-decomposed-obligations constructors.

## Non-Claims

TS256 does not construct the TS185 zero API contract or finite truncation,
define the concrete spectral summand or an infinite zero sum, prove local
finiteness, reality, a zero-density estimate, the explicit-formula identity,
either bound, RH, Gallagher evidence, either OTSA bridge, or Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS256.RiemannZetaZeroTruncatedContribution
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS256
git diff --check
```

## Expected Audit Result

The build succeeds.  The TS256 directory contains no placeholder proofs, no
forbidden declarations, and no non-ASCII characters.  `git diff --check`
reports no whitespace errors.
