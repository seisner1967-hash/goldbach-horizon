# TS282 Audit - Riemann Xi Candidate and Buffered Specification

## Scope

TS282 defines the correct Riemann xi candidate from Mathlib's entire additive
regularization of completed zeta.  It then specifies the exact finite zero
geometry and quotient assembly required to instantiate the TS275 buffered
Jensen pipeline.

## Correct xi normalization

The regularized function itself is not xi.  TS282 defines

```text
riemannXiCandidate(s) =
  (s * (s - 1) * completedRiemannZetaZero(s) + 1) / 2.
```

The module proves:

```text
riemannXiCandidate_entire
riemannXiCandidate_zero
riemannXiCandidate_one
riemannXiCandidate_zero_ne_zero
riemannXiCandidate_one_sub
riemannXiCandidate_eq_completedRiemannZeta_mul
```

The last theorem identifies the candidate away from `0` and `1` with
`s * (s - 1) * completedRiemannZeta(s) / 2`.

## Exact fail-closed interfaces

`XiFiniteZeroFactorizationSpec` uses the real TS275
`JensenDiskConfiguration`.  It records inner and factor `Finset`s, a common
positive multiplicity, complete zero membership on the analytic closed ball,
and a local analytic normal form at every selected zero.  No placeholder type
or `True` is used for geometry.

The module proves that this specification produces a genuine
`JensenFactorZeroData`, including noncoincidence of every factor zero with the
center, derived from `xi(0) = 1/2`.

`XiBufferedQuotientAssembly` is the remaining analytic construction: an
analytic nonvanishing quotient with the exact finite factorization on the
buffered closed ball.  Any supplied assembly becomes a genuine
`BufferedJensenFactorizationData`, and TS280 immediately yields the canonical
finite Jensen boundary estimate and multiplicity-count quotient.

## Unicode bridge exception

The locked Mathlib API spells three declarations with the Unicode
subscript-zero character.  `CompletedRiemannZetaZeroBridge.lean` contains the
only three unavoidable non-ASCII occurrences and exposes ASCII aliases.  The
main TS282 module and this audit are ASCII-only.  This exception is explicit
and mechanically limited to the three Mathlib identifier references.

## Non-claims

TS282 does not construct the finite xi zero sets, prove local normal forms,
select a zero-free collar, assemble the quotient, prove the xi/zeta zero
correspondence, prove effective xi growth, prove a zero-counting estimate,
prove the explicit formula, prove Gallagher, close an OTSA bridge, or claim
Goldbach.

## Verification

Canonical build target:

```powershell
lake build TS.Goldbach.Strong.TS282.RiemannXiCandidateBufferedSpec
```

Static checks:

```powershell
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS282
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS282\RiemannXiCandidateBufferedSpec.lean TS\Goldbach\Strong\TS282\TS282_Audit.md
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS282\CompletedRiemannZetaZeroBridge.lean
git diff --check
```

Expected result: the build succeeds, the incomplete-declaration and main-file
ASCII scans print no matches, and the bridge scan prints exactly the three
documented Mathlib identifier lines.
