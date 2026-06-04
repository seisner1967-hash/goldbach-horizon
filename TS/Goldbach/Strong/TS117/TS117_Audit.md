# TS117 Audit - Selberg Diagonal Coefficient Calculation Ledger

## Status

`repo_committed`

TS117 performs the first calculation audit below the TS116 gcd-coefficient
kernel-match layer. It introduces a standard Mobius-square/totient diagonal
coefficient candidate as an explicit local slot and proves its normalization at
`d = 1`.

The main result is a structural obstruction for the current TS109--TS116
diagonal interface: no coefficient depending only on `Nat.gcd m n` can match
the canonical dense `gcd(m,n)/lcm(m,n)` kernel for all pairs. The proof uses
the concrete pairs `(2,4)` and `(2,6)`, which have the same gcd but different
lcm values and therefore different dense-kernel values.

This sprint does not prove the Selberg coefficient calculation, does not close
the dense-to-diagonal identity, and does not prove the square-sum majorant,
Selberg's sieve, Brun-Titchmarsh, interval majorant, budget comparison, or any
prime-count estimate. Instead it formally diagnoses that the diagonal
normalization must be refined before the TS116 compatibility can be discharged.

## File

```text
TS/Goldbach/Strong/TS117/SelbergDiagonalCoefficientCalculationLedger.lean
```

## Key declarations

```lean
TS117.Goldbach.selbergMobiusSquareTotientCoefficient
TS117.Goldbach.selbergMobiusSquareTotientCoefficient_one
TS117.Goldbach.selbergMobiusSquareTotientGcdCoefficient
TS117.Goldbach.selbergMobiusSquareTotientGcdCoefficient_eq_filter_sum
TS117.Goldbach.canonicalKernel_two_four
TS117.Goldbach.canonicalKernel_two_six
TS117.Goldbach.canonicalKernel_two_four_ne_two_six
TS117.Goldbach.no_gcd_only_coefficient_matches_canonicalKernel
TS117.Goldbach.no_selbergGcdCoefficientKernelCompatibility
TS117.Goldbach.SelbergDiagonalCoefficientCalculation
TS117.Goldbach.selbergDiagonalCoefficientCalculation
TS117.Goldbach.SelbergDiagonalCoefficientCalculationTarget
TS117.Goldbach.selbergDiagonalCoefficientCalculationTarget
TS117.Goldbach.selbergGcdCoefficientKernelMatchTarget
```

## Proof summary

The theorem

```lean
TS117.Goldbach.selbergMobiusSquareTotientCoefficient_one
```

proves that the candidate Mobius-square/totient coefficient is normalized at
`d = 1`.

The theorems

```lean
TS117.Goldbach.canonicalKernel_two_four
TS117.Goldbach.canonicalKernel_two_six
TS117.Goldbach.canonicalKernel_two_four_ne_two_six
```

compute two canonical dense-kernel values:

```text
K(2,4) = 1/2
K(2,6) = 1/3
```

even though both pairs have gcd `2`.

The theorem

```lean
TS117.Goldbach.no_gcd_only_coefficient_matches_canonicalKernel
```

proves that no one-variable coefficient `coefficient (Nat.gcd m n)` can match
the canonical `gcd/lcm` kernel for all pairs.

The theorem

```lean
TS117.Goldbach.no_selbergGcdCoefficientKernelCompatibility
```

specializes that obstruction to the current TS116 compatibility obligation.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS117.SelbergDiagonalCoefficientCalculationLedger
rg -n "s[o]rry" TS\Goldbach\Strong\TS117
rg -n "a[x]iom" TS\Goldbach\Strong\TS117
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS117
git diff --check -- README.md TS\Goldbach\Strong\TS117\SelbergDiagonalCoefficientCalculationLedger.lean TS\Goldbach\Strong\TS117\TS117_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS117-R1 | `selbergMobiusSquareTotientCoefficient_one` | `repo_committed` | proves normalization of the candidate coefficient at `d = 1` |
| TS117-R2 | `canonicalKernel_two_four` | `repo_committed` | computes `K(2,4) = 1/2` |
| TS117-R3 | `canonicalKernel_two_six` | `repo_committed` | computes `K(2,6) = 1/3` |
| TS117-R4 | `canonicalKernel_two_four_ne_two_six` | `repo_committed` | proves the two kernel values differ |
| TS117-R5 | `no_gcd_only_coefficient_matches_canonicalKernel` | `repo_committed` | proves the canonical kernel is not a function of gcd alone |
| TS117-R6 | `no_selbergGcdCoefficientKernelCompatibility` | `repo_committed` | proves the current TS116 compatibility cannot be discharged as stated |
| TS117-I1 | `SelbergDiagonalCoefficientCalculation` | `repo_committed` | packages the coefficient candidate and the obstruction diagnosis |
| TS117-T1 | `selbergGcdCoefficientKernelMatchTarget` | `repo_committed_relative` | keeps the TS116 layer available while identifying the needed refinement |

## Remaining work

The next arithmetic step is not to push the current TS116 compatibility harder.
It is to refine the diagonal change of variables so that the local coefficient
retains the pair- or lcm-sensitive normalization needed to match the canonical
`gcd/lcm` kernel. Only after that interface correction can the Mobius
coefficient calculation be used to close the dense-to-diagonal Selberg
identity.
