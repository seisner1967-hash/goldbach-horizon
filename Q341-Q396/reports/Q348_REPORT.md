# Q348 - Theta-Mellin Robust Sign Pilot

Date: 2026-08-12

## Verdict

```text
Q348_Q347_CONTRACT_REPAIR_PASS
Q347_FULL_BINDING_DIRECT_COMPILE_PASS
Q348_THETA_MELLIN_REDUCTION_PASS
Q348_EXPLICIT_THETA_TAIL_PASS
Q348_THETA_KERNEL_EXPANSION_PASS
Q348_QUADRATURE_REDUCTION_PASS
Q348_FIRST_ROBUST_SIGN_PAIR_PASS      : NOT_OBTAINED
A_INSTANCE_SIGN_PASS_[14,15]          : NOT_OBTAINED
QUADRATURE_SEMANTIC_LEAF              : MISSING
BRIDGE_A                              : OPEN
CARRIER_MEMBERSHIP                    : UNPROVED
TS340_UNCONDITIONAL                   : OPEN_FROZEN
Q349                                  : NOT_LAUNCHED
```

Q348 closes the exact analytic reduction to a theta-Mellin integral, but it
does not close Bridge A.  No theorem in the package asserts either numerical
integral enclosure.

## Governance

- Start: `2026-08-12T11:51:17.0023977+02:00`
- Deadline: `2026-08-12T13:51:17.0023977+02:00`
- Proof and axiom audit completed before the deadline.
- The source folder and manifest were frozen at `13:12:15`, before the
  deadline. The first ZIP round-trip call was interrupted; archive creation
  resumed at `14:05:06` as documentation-only work, with no proof, build, or
  Git operation after the deadline.
- Detached baseline: `433e29eff1d9da2bc5937bb82bf5df3a2d59c08f`
- `origin/main`: same SHA throughout the audit.
- No branch, commit, push, PR, merge, tag, or permanent module was created.

## Q347 repairs

The obsolete import in `AnalyticLeafBoundary.lean` was replaced by
`CheckedArithmeticCertificate`.  The external binding now requires the
sufficient refinement contract

```text
checkedOutput membership -> serializedOutput membership
```

instead of equality of the checked and serialized intervals.  Two stale sign
helpers were replaced by direct cast-and-order proofs.  The pair constructors
in `FirstBracketCertificateBoundary.lean` were corrected from product syntax
to conjunction syntax.  Both repaired files compile directly.

## Compiled mathematical results

### Exact theta-Mellin identity

`completedRiemannZeta0_critical_eq_thetaMellin` unfolds Mathlib's existing
definition of `completedRiemannZeta₀` as the Mellin transform of the modified
Hurwitz-even kernel.  The pole correction then gives

```text
completedRiemannZeta(1/2 + it)
  = criticalThetaMellinIntegral(t) / 2
      - (1/(1/2+it) + 1/(1/2-it)).
```

The correction is proved exactly equal to the positive real number

```text
1 / (t^2 + 1/4).
```

In particular it is `4/785` at `t = 14` and `4/901` at `t = 15`.

### Real carrier reduction

The project carrier is proved equal to

```text
Re(criticalThetaMellinIntegral t) / 2 - 1 / (t^2 + 1/4).
```

Together with the positive Gamma norm from Q343, strict signs of this real
quantity are equivalent to strict signs of `normalizedHardyZ`.

### Explicit theta tail and kernel expansion

`thetaTail_norm_le` reuses Mathlib's proved Hurwitz-kernel estimate:

```text
||F_nat 0 (N+1) x||
  <= exp(-pi (N+1)^2 x) / (1 - exp(-pi x)),  x > 0.
```

For `x > 1`, the modified kernel at parameter zero is also proved exactly
equal to the positive theta series

```text
sum n, 2 * exp(-pi * (n+1)^2 * x).
```

This removes Gamma and phase conventions from the future numerical leaf.

### Exact quadrature targets

The robust completed-carrier targets are:

```text
t = 14 : [-3/10^6, -1/10^6]
t = 15 : [ 5/10^6,  7/10^6]
```

The corresponding unscaled Mellin-integral targets are proved sufficient:

```text
t = 14 : [8/785 - 6/10^6, 8/785 - 2/10^6]
t = 15 : [8/901 + 10/10^6, 8/901 + 14/10^6].
```

If both integral memberships are supplied, the compiled theorem
`normalizedHardyZ_robust_sign_pair_of_quadrature` yields

```text
normalizedHardyZ 14 < 0 /\ 0 < normalizedHardyZ 15.
```

Neither membership is constructed in Q348.

## Compilation and axioms

The pinned toolchain executable was invoked directly because `lake` attempted
a remote Mathlib URL refresh and failed with the known Windows SSL credential
error.  With the already completed local cache, all seven targeted source
checks succeeded.  The final compile log records every invocation.

All terminal Q348 theorems audited by `#print axioms` depend only on:

```text
propext
Classical.choice
Quot.sound
```

The source scan found no `sorry`, `admit`, specialized `axiom`, `opaque`,
`Float`, `native_decide`, or `Lean.ofReduceBool` outside the audit command
itself.

## Exact remaining leaf

```lean
FourteenQuadratureEnclosure
FifteenQuadratureEnclosure
```

These are the only uninhabited assumptions needed for the robust sign pair.
Mathlib supplies the analytic definition and theta tail bounds, but no proved
numerical quadrature engine for the oscillatory complex Mellin integral.
Consequently:

```text
Q348_REDUCTION_PASS does not imply BRIDGE_A_CLOSED.
```

The next legitimate research target is a verified quadrature checker for the
theta-Mellin integrand (including certified `exp`, `log`, and `cos` ranges),
or the production Riemann-Siegel leaf.  No next sprint is launched here.
