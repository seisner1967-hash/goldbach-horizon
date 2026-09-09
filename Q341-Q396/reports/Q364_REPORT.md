# Q364 - Riemann-Siegel Auxiliary Entire Extension

Date: 2026-08-20

## Verdict

```text
Q364_HALF_INTEGER_LOCAL_ISOLATION_PASS
Q364_DSLOPE_FACTORIZATION_PASS
Q364_DENOMINATOR_DSLOPE_LOCAL_NONZERO_PASS
Q364_LOCAL_REMOVABLE_SINGULARITY_PASS
Q364_LOCAL_HOLOMORPHIC_EXTENSION_PASS
Q364_GLOBAL_ENTIRE_FUNCTION_PASS
Q364_AUXILIARY_F_ENTIRE_PASS
Q364_QUOTIENT_AGREEMENT_PASS
Q364_DERIVATIVE_INTERFACE_PASS
Q364_DIRECT_BUILD_PASS
Q364_AXIOM_AUDIT_PASS
```

Q364 is closed. Bridge A remains open.

## Timing

```text
T0                 : 2026-08-20T14:27:54.7583401+02:00
proof freeze       : 2026-08-20T14:39:34.3445199+02:00
required freeze    : 2026-08-20T17:12:54.7583401+02:00
absolute deadline  : 2026-08-20T17:27:54.7583401+02:00
```

All source development finished before the required freeze.

## Baseline

```text
HEAD        : 433e29eff1d9da2bc5937bb82bf5df3a2d59c08f
origin/main : 433e29eff1d9da2bc5937bb82bf5df3a2d59c08f
worktree    : detached
Lean        : 4.15.0
Mathlib     : 9837ca9d65d9de6fad1ef4381750ca688774e608
```

Q362 and Q363 archive and manifest hashes matched the mandate. Both dependency
manifests replayed 21/21.

## Formal construction

`LocalIsolation.lean` proves that distinct half-integers are separated by at
least one. Consequently, a unit ball around `halfInteger n` contains no other
zero of `publishedFDenominator`.

`DSlopeFactorization.lean` defines

```lean
localDslopeModel c z :=
  dslope publishedFNumerator c z /
    dslope publishedFDenominator c z
```

and proves that it equals the published quotient away from the center. The
simple-zero theorem from Q362 and continuity of `dslope` prove that its
denominator is locally nonzero. The model is analytic at every half-integer.

`EntireExtension.lean` defines exactly the mandated global function:

```lean
riemannSiegelF z :=
  if publishedFDenominator z = 0 then
    deriv publishedFNumerator z / deriv publishedFDenominator z
  else
    publishedFQuotient z
```

Near a half-integer this function is eventually equal to the analytic
divided-slope model. At ordinary points it is locally equal to the published
quotient. Lean therefore proves:

```lean
riemannSiegelF_differentiable : Differentiable Complex riemannSiegelF
riemannSiegelF_analyticAt (z) : AnalyticAt Complex riemannSiegelF z
riemannSiegelF_contDiff        : ContDiff Complex top riemannSiegelF
```

The quotient agreement and half-integer value are explicit theorems. The safe
derivative interface is `riemannSiegelFDeriv j z = iteratedDeriv j
riemannSiegelF z` and is exposed only after the global analyticity proof.

## Build and trust audit

```text
Direct source replay : 5/5 PASS
Lake aggregate       : 6/6 PASS
Source files         : 5
Source lines         : 201
Forbidden scan       : empty
git diff --check     : empty for the local lakefile change
Terminal axioms      : propext, Classical.choice, Quot.sound
```

One post-freeze invocation of the `lake` shim failed before Lean started with a
transient Schannel SSL credential error. The same unit was immediately replayed
successfully, followed by a clean 5/5 direct replay. This was an infrastructure
incident and did not affect any proof result.

## Scope boundary

```text
Q364                         : CLOSED
Q365_RS_COEFFICIENTS         : READY / NOT_STARTED
RIEMANN_SIEGEL_DECOMPOSITION : OPEN
ARIAS_REMAINDER              : OPEN
BRIDGE_A                     : OPEN
CARRIER_MEMBERSHIP           : UNPROVED
TS340_UNCONDITIONAL          : OPEN_FROZEN
```

No Riemann-Siegel coefficient, decomposition theorem, Arias remainder,
dyadic checker, production bracket, or Q365 work was started.

## Git governance

No branch, commit, push, pull request, merge, or tag was created. The only
lakefile change is the local `lean_lib Q364Probe` entry needed for the build.
The worktree remains detached and `HEAD = origin/main = 433e29e`.
