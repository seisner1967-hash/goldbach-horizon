# TS290 Audit - Riemann Xi Log-Linear Zero Counting

## Scope

TS290 turns the closed theta-Mellin growth estimate of TS289 into an
unconditional log-linear multiplicity count for the concrete nontrivial zeta
zeros of TS264--TS265.  It then constructs the actual TS270 global counting
contract with the TS273 safe log-linear envelope.

## Constant-ratio Jensen geometry

The original TS283 construction uses the ambient radius `r + 3`.  Its
averaging radius is separated from `r`, but the quotient of radii tends to
one, so its Jensen logarithmic denominator is not uniformly positive.

TS290 therefore rebuilds the exact finite-zero geometry with ambient radius
`4 * r`.  The same finite maximum barrier gives radii satisfying

```text
r < averagingRadius < analyticRadius < 4 * r
2 * r <= averagingRadius
```

and exact inner/factor zero selections with a zero-free closed collar.  Hence

```text
log (averagingRadius / r) >= log 2 >= 1 / 2.
```

This constant-ratio geometry, rather than the existence-oriented `r + 3`
geometry, is what yields a log-linear count.

## Zeta-xi multiplicity bridge

On the critical strip, TS290 proves the local identity

```text
riemannXiCandidate = xiZetaLocalMultiplier * riemannZeta,
```

where the multiplier is analytic and nonzero.  The reciprocal completed-zeta
Gamma factor needed for this identity is exposed through new ASCII aliases in
the TS282 bridge.  Local normal forms and `AnalyticAt.order_eq_nat_iff` then
give the exact equality

```text
concreteRiemannZetaMultiplicity rho =
  riemannXiCandidateMultiplicity rho
```

for every concrete nontrivial zeta zero.  Thus no multiplicity is lost when
the TS265 height selection is embedded into the xi Jensen disk.

## Closed log-linear estimate

TS290 routes the TS289 boundary majorant through the new buffered xi data and
proves elementary bounds for its logarithmic budget.  It defines

```text
xiDyadicLogLinearConstant =
  28 + 4 * completedZetaThetaTailConstant

xiGlobalLogLinearConstant =
  4 * xiDyadicLogLinearConstant
```

and proves, for every real `T >= 1`,

```text
concreteMultiplicityCountUpToHeight T <=
  xiGlobalLogLinearConstant * T * log (T + 2).
```

The proof uses the disk with inner radius `2 * T`, which contains the TS265
height truncation because every concrete zero lies in the critical strip.

## TS270 and TS273 routing

The large-height estimate above is packaged as

```text
xiLargeHeightLogLinearMultiplicityCountEstimate
```

and TS273 supplies the safe extension below height one.  The final definition

```text
xiGlobalMultiplicityCountingBoundContract
```

is a concrete, unconditional
`TS270.Goldbach.GlobalMultiplicityCountingBoundContract` for
`TS273.Goldbach.logLinearMultiplicityCountEnvelope
xiGlobalLogLinearConstant`.

## Unicode bridge exception

The TS290 source and this audit are ASCII-only.  The locked Mathlib API uses
Unicode identifiers for `completedRiemannZetaZero` and the real Gamma factor.
Their six unavoidable occurrences remain confined to
`TS282/CompletedRiemannZetaZeroBridge.lean`, which exposes ASCII aliases to
TS290.

## Non-claims

TS290 does not prove a Riemann-von-Mangoldt asymptotic or its leading
constant, an infinite zero sum, the explicit formula, Gallagher, an OTSA
bridge, or Goldbach.

## Verification

Canonical build target:

```powershell
lake build TS.Goldbach.Strong.TS290.RiemannXiLogLinearZeroCounting
```

Static checks:

```powershell
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS290 TS\Goldbach\Strong\TS282\CompletedRiemannZetaZeroBridge.lean
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS290
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS282\CompletedRiemannZetaZeroBridge.lean
git diff --check
```

Expected result: the build succeeds; the incomplete-declaration and TS290
ASCII scans print no matches; the TS282 bridge scan prints exactly the six
documented Mathlib identifier lines; and `git diff --check` is clean.
