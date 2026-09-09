# Q365 - exact Riemann-Siegel coefficients

Date: 2026-08-20

Verdict: `Q365_CLOSED`

## Statuses

```text
Q365_PRIMARY_COEFFICIENT_PROVENANCE_PASS
Q365_INDEX_CONVENTION_PASS
Q365_DERIVATIVE_INDEX_BOUND_PASS
Q365_D_COEFFICIENT_RECURRENCE_PASS
Q365_D_COEFFICIENT_SUPPORT_PASS
Q365_CK_PRIMARY_DEFINITION_PASS
Q365_CK_DERIVATIVE_BINDING_PASS
Q365_SMALL_K_SYMBOLIC_REPLAY_PASS
Q365_FINITE_COEFFICIENT_SUM_PASS
Q365_DIRECT_BUILD_PASS
Q365_AXIOM_AUDIT_PASS
```

The proof was frozen at `15:30:15+02:00`, 1892.365 seconds after T0 and well
before both the provenance gate and the required development freeze.

## Primary provenance

The definitions are fixed in `Q365_PRIMARY_COEFFICIENT_SPEC.md` from:

- J. Arias de Reyna, *High Precision Computation of Riemann's Zeta Function
  by the Riemann-Siegel Formula, I*, Math. Comp. 80 (2011), equations (39),
  (2.4), and (2.5);
- the author-supplied TeX source of *High Precision Computation ... II*,
  arXiv `2201.00342v1`, sections 3.6 and 3.17.

The latter source gives the initial conditions, the regular recurrence, the
exceptional `3*k = 2*j` recurrence, support, and published low-order values.
FLINT was used only as an implementation cross-check.

## Construction

`rsDRow` is structurally recursive in the outer order. It implements:

```text
d_0^(0) = 1
d_j^(0) = 0 for j != 0
d_j^(k) = 0 for 2*j > 3*k
```

For `m = 3*k - 2*j > 0`, it uses the solved primary recurrence. When `m = 0`,
it uses the finite same-row factorial sum, never division by zero. Negative
lags are represented by `rsDLag`, which returns zero.

`rsCCoeff` is the exact finite formula

```text
1 / pi^(2*k) * sum_j
  (pi / (2*i))^j * d_j^(k) * riemannSiegelFDeriv (3*k-2*j) p.
```

The derivative is therefore the interface to the entire function proved in
Q364, not an independent table.

`riemannSiegelFiniteCoefficientSum` is exactly

```text
sum (k = 0 .. K) (rsCCoeff sigma k p / a^k).
```

No relation to zeta or `normalizedHardyZ` is asserted in Q365.

## Terminal signatures

```lean
rsDCoeff_recurrence (sigma : Rat) (k j : Nat)
    (h : 2 * j < 3 * (k + 1)) :
  rsDCoeff sigma (k + 1) j =
    rsDCoeff sigma k j / (4 * (3 * (k + 1) - 2 * j)) +
    (1 - 2 * sigma) * rsDLag (rsDCoeff sigma k) j 1 /
      (2 * (3 * (k + 1) - 2 * j)) -
    (3 * (k + 1) - 2 * j + 1) * rsDLag (rsDCoeff sigma k) j 2

rsDCoeff_support (sigma : Rat) (k j : Nat)
    (h : 3 * k < 2 * j) :
  rsDCoeff sigma k j = 0

rsDCoeff_top_primary (sigma : Rat) (k j : Nat)
    (h : 2 * j = 3 * (k + 1)) :
  rsDCoeff sigma (k + 1) j =
    -sum (r = 0 .. j-1)
      ((-1)^(j-r) * rsDCoeff sigma (k + 1) r * rsDTopFactor (j-r))

rsCCoeff_eq_primary_formula (sigma : Rat) (k : Nat) (p : Complex) :
  rsCCoeff sigma k p =
    1 / pi^(2*k) * sum (j = 0 .. floor(3*k/2))
      ((pi / (2*I))^j * (rsDCoeff sigma k j) *
        Q364Probe.riemannSiegelFDeriv (3*k-2*j) p)

rsCCoeff_derivative_index_le (k j : Nat) :
  3 * k - 2 * j <= 3 * k

riemannSiegelFiniteCoefficientSum_wellFormed
    (sigma : Rat) (K : Nat) (a p : Complex) (_ha : a != 0) :
  riemannSiegelFiniteCoefficientSum sigma K a p =
    sum (k = 0 .. K) (rsCCoeff sigma k p / a^k)
```

The machine-extracted Unicode signatures are retained in
`Q365Logs/direct_build.log` and `Q365Logs/lake_build.log`.

## Symbolic replay

Lean reduces exactly the critical-line rows `k = 0,1,2,3`. In particular:

```text
k=0 : 1
k=1 : 1/12, 0
k=2 : 1/288, 0, -1/4, -1/12
k=3 : 1/10368, 0, -1/30, -1/144, 1/2
```

These values are consequences of the recurrence, not an imported table.

## Audit

```text
Direct Lean 4.15 replay : PASS 8/8
Pinned Lake aggregate  : PASS 13/13
Forbidden scan         : EMPTY
git diff --check       : EMPTY
Axioms                 : propext, Classical.choice, Quot.sound
```

The Elan/Lake shim intermittently failed before Lean with a Schannel SSL
credential error. Calling the pinned `lean.exe` and `lake.exe` binaries
directly produced complete successful replays.

## Governance and frontier

```text
Q365_RS_COEFFICIENTS         : CLOSED
Q366_RS_DECOMPOSITION        : READY / NOT_STARTED
RIEMANN_SIEGEL_DECOMPOSITION : OPEN
ARIAS_REMAINDER              : OPEN
BRIDGE_A                     : OPEN
CARRIER_MEMBERSHIP           : UNPROVED
TS340_UNCONDITIONAL          : OPEN_FROZEN
```

No branch, commit, push, pull request, merge, tag, or modification of `main`
was performed.
