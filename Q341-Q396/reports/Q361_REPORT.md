# Q361 Report - Analytic Riemann--Siegel Kernel

## Verdict

```text
Q361_ANALYTIC_DEPENDENCY_AUDIT_PASS
Q361_PARAMETER_SPINE_BUILD_PASS
Q361_AXIOM_AUDIT_PASS
Q361_THEOREM_SPINE_PARTIAL
Q361_CANONICAL_THEOREM_SPINE_PASS  : NOT_OBTAINED
Q361_RIEMANN_SIEGEL_FORMULA_PASS   : NOT_OBTAINED
Q361_ARIAS_REMAINDER_DEPENDENCY_GAP
Q361_B_NOT_ATTEMPTED_ORDER_GATE
Q361_CHECKER_NOT_ATTEMPTED
```

Q361 stopped early and fail-closed during phase A.  The strict phase order
forbids phases B through E because the canonical Riemann--Siegel theorem was
not proved.

## What compiled

`Q361Probe.ParameterSpine` formalizes the general parameters

```text
a(t) = sqrt(t/(2*pi))
N(t) = floor(a(t))
p(t) = 1 + 2*(N(t)-a(t))
```

and the explicit critical-line envelope used by Q360.  Lean proves

```text
0 < t -> 0 < a(t)
N(t) <= a(t) < N(t)+1
0 < t -> -1 < p(t) <= 1
0 <= ariasRawRemainderBound(t,K)
0 <= explicitAriasBound(t,K)
```

The source contains no `normalizedHardyZ` sign import, no Arb proof object,
and no remainder defined by subtraction.

The direct Lean 4.15 build and `#print axioms` audit pass.  Every compiled
theorem depends only on

```text
propext, Classical.choice, Quot.sound
```

## Why phase A did not pass

The missing object is not interval arithmetic.  It is the analytic theorem
that connects the canonical Hardy carrier to the Riemann--Siegel saddle
expansion.

The finite correction requires an auxiliary entire function `F`, derivatives
through order `3*K`, the `d_j^(k)` recurrence and the coefficients `C_k(p)`.
The quotient used computationally by FLINT has removable singularities at
half-integers.  Defining it as an ordinary quotient and applying Mathlib's
`iteratedDeriv` would be unsound for this purpose, because derivatives at
nondifferentiable points default to zero.  A holomorphic extension and its
agreement with the published function must be proved first.

Beyond that local issue, pinned Mathlib has no theorem deriving the exact
Riemann--Siegel decomposition from zeta, and no theorem proving Arias de
Reyna's explicit remainder estimate.  The closest libraries provide zeta's
Dirichlet series, continuation and functional equation, Cauchy integrals,
removable singularities and Taylor series.  They do not provide the required
contour deformation or saddle-point remainder estimates.

Defining

```text
remainder := normalizedHardyZ - finitePart
```

would make the equality tautological and would leave the bound completely
unproved.  Q361 deliberately did not do this.

## Source-level correction recorded

The Q359 correction remains:

```text
ctx.cap = 10 exposes derivative indices 0..9
the expansion needs derivatives through index 3*K
Q359 reliable only for K <= 3
Q359 K=4..30 incomplete
Q359 fail-closed verdict unchanged
```

Q361 also distinguishes the exact theorem-level critical-line constant
`1/2` from FLINT's rounded `mag_t` execution.  The source implementation can
round that branch to `4/7`; Q360 used the sharper mathematical theorem
expression.  This does not invalidate its external routing role, but the
distinction must be explicit in any future formal proof.

## Infrastructure note

The Mathlib `.olean` cache was initially absent.  The standard `lake exe
cache get` path failed while fetching an independent ProofWidgets release.
Running the already-built official cache executable restored 5826 cached
files.  No cold Mathlib build was counted.  A broad local Lake target was
stopped when it selected the entire TS graph; the two Q361 files were then
compiled directly and successfully.

## Governance

```text
Development stopped before freeze : YES
Q361-B started                    : NO
Q361-C/D/E started                : NO
Q362 started                      : NO
Git permanent operation          : NONE
BRIDGE_A                          : OPEN
CARRIER_MEMBERSHIP                : UNPROVED
TS340_UNCONDITIONAL               : OPEN_FROZEN
```

The exact missing theorem and its dependencies are recorded in
`Q361_ANALYTIC_DEPENDENCY_MAP.md`.  A future continuation should begin from a
readable primary statement of Arias de Reyna's theorem and formalize the
auxiliary entire function before attempting numerical certificate plumbing.
