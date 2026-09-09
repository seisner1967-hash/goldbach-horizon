# Q352 - Folded Theta C2 and Second-Derivative Bound

Date: 2026-08-12  
Baseline: `433e29eff1d9da2bc5937bb82bf5df3a2d59c08f`  
Lean: 4.15.0  
Mathlib: `9837ca9d65d9de6fad1ef4381750ca688774e608`

## Verdict

```text
Q352_FOLDED_INTEGRAND_C2_PASS
Q352_TERM_SECOND_DERIVATIVE_FORMULA_PASS
Q352_TERM_UNIFORM_MAJORANT_PASS
Q352_GEOMETRIC_SERIES_BOUND_PASS
Q352_SECOND_DERIVATIVE_LE_25_PASS
Q352_Q351_8192_SPECIALIZATION_PASS
Q352_CONCRETE_TRAPEZOIDAL_SUM_NOT_OBTAINED
Q348_SIGN_LEAVES_UNINHABITED
BRIDGE_A_OPEN
CARRIER_MEMBERSHIP_UNPROVED
TS340_UNCONDITIONAL_OPEN_FROZEN
```

## Compiled results

The folded theta integrand is C2 on the compact interval:

```lean
theorem criticalThetaFoldedIntegrand_contDiffOn_two (t : Real) :
    ContDiffOn Real 2
      (Q349Probe.criticalThetaFoldedIntegrand t) (Set.Icc 0 2)
```

For every `|t| <= 15`, its second derivative within `[0,2]` is uniformly bounded,
including the conventional zero value outside the closed set:

```lean
theorem criticalThetaFoldedIntegrand_secondDerivative_le_twentyFive
    {t : Real} (ht : |t| <= 15) (u : Real) :
    |iteratedDerivWithin 2
      (Q349Probe.criticalThetaFoldedIntegrand t) (Set.Icc 0 2) u| <= 25
```

The Q351 connector can therefore be instantiated with `zeta = 25` and
`N = 8192`:

```lean
theorem criticalThetaMellin_re_sub_trapezoidal_8192_le
    {t : Real} (ht : |t| <= 15) :
    |(Q348Probe.criticalThetaMellinIntegral t).re -
        Q351Probe.trapezoidalIntegral
          (Q349Probe.criticalThetaFoldedIntegrand t) 8192 0 2| <=
      (1 : Real) / 4000000
```

The exact intermediate error is

```text
49024733 / 196608000000000 < 1 / 4000000.
```

## Proof architecture

1. Jacobi theta holomorphy gives smoothness of
   `u -> thetaPositiveSeries (exp u)` without differentiating a `tsum` merely
   for regularity.
2. A separate locally uniform majorant justifies differentiating the explicit
   theta series twice and identifies the exact second derivative termwise.
3. Each term is reduced monotonically to `u = 0` and bounded by
   `(2213/4) * m^4 * 23^(-m^2)`.
4. The first term is isolated. For `m >= 2`, the remainder is bounded by a
   geometric series of ratio `16/529`.
5. Lean verifies the final rational estimate
   `26677715/1085508 < 25`.

The estimate `exp (-pi) <= 1/23` is proved internally using the finite Taylor
lower bound for `exp 3.14` and `3.14 < pi`; no numerical oracle is used.

## Build and trust audit

```text
lake build Q352Probe: 3075/3075 PASS
Q352 diagnostics: no warnings; informational tactic suggestions only
Terminal axioms: propext, Classical.choice, Quot.sound
```

The forbidden-token scan found no `sorry`, `admit`, specialized `axiom`,
`opaque`, `native_decide`, `Lean.ofReduceBool`, or `Float`. The only textual
occurrences of `axioms` are the three intentional `#print axioms` audit lines.

## Fail-closed boundary

Q352 does not compute the 8192-panel trapezoidal sum. It introduces no
certified enclosures for `pi`, `exp`, `cos`, or theta values and proves no sign
at `t = 14`, `t = 15`, or any Q343 bracket endpoint. Consequently Bridge A,
carrier membership, the Q348 sign leaves, and unconditional TS340 remain open.

## Governance

The work was performed in a detached disposable worktree. `HEAD` and
`origin/main` both remain at `433e29e`. No branch, commit, push, pull request,
merge, tag, or permanent Goldbach module was created.
