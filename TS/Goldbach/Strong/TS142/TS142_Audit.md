# TS142 Audit

## Scope

TS142 adds the exact fractional decomposition of the TS141 lcm multiplicity
count.  For each pair `(d1,d2)`, it defines

```text
multiplicity = intervalLength / lcm(d1,d2) + error
```

as an exact rational identity and inserts this identity into the full TS141
pair-first double sum.

## Concrete proofs

```text
TS142.Goldbach.lcmMultiplicity_eq_TS141
TS142.Goldbach.lcmMultiplicity_eq_main_add_error
TS142.Goldbach.selbergConcreteSquareMajorantRat_eq_fractionalExpansion
TS142.Goldbach.selbergFractionalMainTerm_eq_intervalLength_mul_denseSide
TS142.Goldbach.selbergFractionalMainTerm_eq_optimalBudget
TS142.Goldbach.lcmMultiplicityFractionalDecompositionTarget
```

The first four results are unconditional finite identities.  The fifth uses
the explicitly named lcm dense-side budget input.  The final target packages
the decomposition once the two genuine estimates are supplied.

## Remaining inputs

```text
TS142.Goldbach.LCMMultiplicityErrorBound
TS142.Goldbach.SelbergLCMDenseSideExactBudget
```

The error bound is the interval arithmetic statement that the discrepancy
from `intervalLength / lcm` has absolute value at most one.

The dense-side budget is deliberately separate from TS136: TS136 proves an
exact budget for the `gcd/lcm` kernel, while the TS142 main term has kernel
`1/lcm`.  No identification between these two forms is assumed silently.

TS142 does not prove an asymptotic estimate for the optimization denominator,
an aggregate error bound, or the Brun-Titchmarsh budget comparison.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS142.LCMMultiplicityFractionalDecomposition
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS142
git diff --check
```

Expected result: build succeeds and the audit searches return no matches.
