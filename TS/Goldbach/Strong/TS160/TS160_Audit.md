# TS160 Audit - Selberg Phi Denominator Candidate

## Status

`repo_committed`

TS160 instantiates the first arithmetic candidate after the TS159 refactor
interface.  It does not replace TS122 and does not prove a Brun-Titchmarsh
comparison.  It only tests the natural `phi` denominator:

```text
D_phi(level) = sum_{1 <= d <= level} mu(d)^2 / phi(d)
```

and proves that this candidate escapes the TS154 `D < 2` obstruction.

## New definitions

```lean
TS160.Goldbach.selbergPhiDenominatorSummand
TS160.Goldbach.selbergPhiDenominator
TS160.Goldbach.selbergPhiRequiredGrowth
```

The candidate keeps the Mobius-square support through the existing TS122
`selbergMobiusRatCoefficient`, but replaces the Jordan-two denominator by
`Nat.totient`.

## Main results

TS160 proves:

```lean
TS160.Goldbach.selbergPhiDenominator_pos
TS160.Goldbach.selbergPhiDenominator_three_gt_two
TS160.Goldbach.selbergPhiDenominator_escapes_two_cap
TS160.Goldbach.selbergPhiDenominator_satisfies_TS159_interface
```

The key finite computation is:

```text
D_phi(3) = 1/phi(1) + 1/phi(2) + 1/phi(3)
         = 1 + 1 + 1/2
         = 5/2 > 2.
```

Thus the candidate is not trapped by the old TS154 cap.

## Interface realization

TS160 defines a prototype required-growth curve:

```text
requiredGrowth(level) = 2 if 3 <= level, otherwise 1.
```

It then constructs:

```lean
TS160.Goldbach.selbergPhiGrowingDenominatorData
```

as a `TS159.Goldbach.SelbergGrowingDenominatorData`, and proves the TS159
data-satisfaction predicate for the phi denominator.

## Ledger

The sprint packages the result in:

```lean
TS160.Goldbach.SelbergPhiDenominatorCandidateLedger
TS160.Goldbach.selbergPhiDenominatorCandidateLedger
TS160.Goldbach.SelbergPhiDenominatorCandidateTarget
TS160.Goldbach.selbergPhiDenominatorCandidateTarget
```

## Scope

TS160 does not prove logarithmic growth, does not prove the TS159
`RefactoredSelbergBTComparisonRoute`, and does not reconnect the candidate to
TS22.  It only establishes that the `phi` candidate is a plausible arithmetic
replacement that crosses the old barrier.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS160.SelbergPhiDenominatorCandidate
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS160
git diff --check -- README.md TS\Goldbach\Strong\TS160
```

Expected result: build succeeds, no audit matches, and no whitespace errors.
