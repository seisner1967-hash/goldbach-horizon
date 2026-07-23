# TS303 Audit - Closed Anchored Macroscopic Envelope

## Scope

TS303 closes the quantitative rate of the anchored macroscopic quotient from
TS301.  It uses a new outer circle, not the unquantified zero-free collar of
the TS290 factorization.  The resulting envelope is deliberately quadratic;
this coarse rate is already sufficient for fixed-scale horizontal decay.

## Quantitative outer geometry

Write

```text
r(T) = 64*(T+4),
R(T) = 8*r(T).
```

Every factor root selected by `xiMacroscopicSpec(T)` lies in the analytic
disk and therefore satisfies

```text
norm rho < 4*r(T).
```

On `norm z = R(T)`, reverse triangle inequalities give

```text
norm(z-rho) >= 4*r(T),
norm(2-rho) <= 4*r(T)+2.
```

Consequently the finite zero polynomial satisfies

```text
norm(P_T(2)/P_T(z))
  <= (1 + 1/(2*r(T)))^M(T),
```

where `M(T)` is the exact selected multiplicity mass.

## Boundary quotient bound

The global TS285 factorization is used at both `z` and the fixed anchor `2`:

```text
Q_T(z)/Q_T(2)
  = (xi(z)/xi(2)) * (P_T(2)/P_T(z)).
```

The polynomial is nonzero on the outer circle, and its anchor value is
nonzero because `xi(2)` is nonzero.  TS289 bounds the xi factor.  This yields
the positive closed boundary majorant

```text
B(T) = XiMajorant(R(T))/norm(xi(2))
       * (1 + 1/(2*r(T)))^M(T).
```

No minimum-modulus estimate at a moving point is used.

## Maximum-modulus transport

The quotient `Q_T` is entire by TS285, hence so is `Q_T/Q_T(2)`.  Mathlib's
maximum-modulus theorem transports the bound on `norm z = R(T)` to the full
outer closed ball.  The anchored TS301 control ball is proved to be a subset
of that ball.

## Closed real-part rate

Taking logarithms separates three finite costs:

```text
log B(T)
  = log XiMajorant(R(T))
    - log norm(xi(2))
    + M(T)*log(1 + 1/(2*r(T))).
```

TS303 proves:

- `log XiMajorant(R) <= (R+3)*log(R+2) + C_theta`;
- the anchor contribution is a fixed nonnegative constant;
- `M(T)*log(1+1/(2*r(T)))` is bounded through the TS302/TS290 count.

For formal robustness, `log y <= y-1` absorbs the remaining logarithms into
the explicit quadratic envelope

```text
E(T) = K_closed*(T+4)^2,
```

with

```text
K_closed = 263171 + C_theta + anchorCost + 514*C_dyadic.
```

This is intentionally weaker than the expected `O(T log T)` bound, but it is
closed, unconditional, and sufficient downstream.

## Cauchy and horizontal decay

On the TS301 control ball,

```text
Re anchoredLog_T(z) < E(T).
```

The centered Borel-Caratheodory theorem from TS300 and the existing local
Cauchy radius `2*(T+4)` give

```text
norm(Q_T'/Q_T) <= K_closed*(T+4)
```

at every point of both finite-grid horizontal segments.  After multiplication
by the quadratic Mellin kernel and the exact width `7/2`, the closed quotient
component tends to zero for every fixed arithmetic scale `x`.

## Logical hygiene

The proof does not use:

- a moving-center minimum-modulus estimate;
- a local zero-density estimate;
- RH or a critical-line assertion;
- an infinite Hadamard product;
- the unquantified TS290 zero-free collar.

## Open frontier

The following remain intentionally unproved:

- a sharper `O(T log T)` anchored envelope;
- the completion-correction rate from TS297;
- decay of the complete horizontal Perron integrand;
- the fixed-left boundary estimate;
- completeness and evaluation of exceptional residues;
- Perron inversion and the meromorphic rectangle residue theorem;
- an infinite explicit formula;
- Gallagher, OTSA, or Goldbach.

The natural next target is the archimedean completion correction.  The zero
load, finite macroscopic correction, and anchored quotient components now all
have independent fixed-scale decay theorems.

## Verification

- Direct Lean compilation passes.
- Source and audit are ASCII-only.
- No unchecked declaration placeholders occur in TS303.
