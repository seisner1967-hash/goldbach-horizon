# TS271 Audit - Height-Shell Partial Summation

## Scope

TS271 introduces exact finite shells `(A, B]`, proves their multiplicity-count
increments, bounds each shell's reciprocal-square residual mass, proves a
generic finite Abel identity, and transports every future global multiplicity
count bound to an amortized finite shell estimate.

## Proof route

1. Define `zerosUpToHeight B \ zerosUpToHeight A` and characterize membership.
2. Prove finite-height selections monotone and split their multiplicity sums.
3. Cast the exact natural shell increment into a real subtraction identity.
4. Use the positive lower shell height to bound every reciprocal-square term.
5. Sum the local bound and identify the shell multiplicity count.
6. Prove finite Abel summation by induction on `Finset.range K`.
7. Prove reciprocal-square weights nonnegative and decreasing on every positive
   monotone height chain.
8. Apply Abel summation to the exact concrete multiplicity counts.
9. Replace these counts by any TS270 global multiplicity-counting bound.

## Proved

- exact `(A, B]` shells with explicit boundary convention
- monotonicity of concrete finite-height zero selections
- exact natural and real shell-count increment identities
- local reciprocal-square shell bound
- generic finite Abel summation identity and inequality
- exact concrete multiplicity-count partial summation
- amortized finite shell estimate under every future global count bound

## Non-claims

- no concrete chain is proved to cover the complete TS269 high selection
- the boundary at `abs rho.im = 1` is not assembled
- no dyadic index existence theorem is used
- no effective multiplicity count or `N(T)` asymptotic is proved
- no zero-density theorem or infinite shell convergence is proved
- no global weighted zero summability is proved
- no explicit-formula identity, residual bound, or Gallagher estimate is proved
- Goldbach is not claimed

## Verification

```powershell
lake build TS.Goldbach.Strong.TS271.HeightShellPartialSummation
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS271
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS271
git diff --check
```
