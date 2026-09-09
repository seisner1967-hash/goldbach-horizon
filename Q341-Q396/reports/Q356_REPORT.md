# Q356 — Parametric dyadic 16-panel pilot

## Fail-closed verdict

```text
Q356_CANONICAL_FLINT_EXPORT_PASS
Q356_SIGNED_OUTWARD_DYADIC_REPLAY_PASS
Q356_PARAMETRIC_EXP_COS_CHECKER_PASS
Q356_UNIFORM_THETA_TAIL_PASS
Q356_EXACT_ZERO_ENDPOINT_EXPRESSION_PASS
Q356_17_NODE_REPLAY_PASS
Q356_16_PANEL_TRAPEZOIDAL_AGGREGATION_PASS
Q356_Q349_NOMINAL_BINDING_NOT_REPLAYED_BASELINE_UNAVAILABLE
Q356_STRONG_END_TO_END_Q349_BINDING_NOT_OBTAINED
```

Q356 closes the autonomous computational pilot. It does not claim the maximal
end-to-end Q349 verdict because the required Git object and the Q349--Q351
source modules were not supplied to this execution environment.

## Q356-A — canonical FLINT export

`Q356Generator/generate.py` uses python-flint 0.8.0 at 320-bit working
precision and emits only signed integer endpoints with common denominator
`2^192`. The payload contains the exact grid metadata `u_k = k/4096`, nodes
`k=0..16`, and an append-only arithmetic trace.

The external generator is untrusted. The replay checks the payload digest,
the grid indices, all fixed-precision operations, several adversarial signed
multiplications, every exact rational Taylor inclusion, and both final pilot
trapezoids. Regeneration is byte-for-byte reproducible.

Multiplication uses mathematical floor on the lower endpoint and ceiling on
the upper endpoint. The fourth theta power appears only as `sq(q)` followed by
`sq(q2)`.

## Q356-B — parametric checker

Lean reconstructs

```text
u_k              = k / 4096
exp argument      = u_k
quarter argument  = u_k / 4
cos14 argument    = 7 u_k
cos15 argument    = 15 u_k / 2
negative argument = -pi * exp(u_k)
```

The dyadic checker converts integer endpoints to exact rational intervals and
accepts a rounded multiplication only when the exact four-corner rational
product is included in the candidate interval. `checkMul_sound` proves the
signed outward-rounding contract independently of the exporter.

Finite Taylor proofs use degrees 20 and 18 for the small positive exponential
leaves, 14 even cosine terms, and degree 72 uniformly on the reconstructed
negative exponential input interval.

## Q356-C/D — uniform tail and zero endpoint

Lean proves one tail enclosure for every `u >= 0` (hence in particular for
`u in [0,2]`):

```text
thetaTail 2 (exp u) in [0, 2^-40].
```

The proof is calibrated at the worst case `exp u >= 1`. The `k=0` certificate
uses exact leaves `exp(0)=1`, `exp(0/4)=1`, and both cosine values equal to one;
only `exp(-pi)` is Taylor-checked on its certified input interval. Thus `k=0`
has a specialized computational path but no alternate endpoint semantics.

## Q356-E — 16 panels

Five generated Lean checkpoint modules compile independently. They prove the
arithmetic and analytic leaf checks for all 17 nodes. The replay then proves
membership for the two semantic node expressions and aggregates with half
weights at `k=0` and `k=16`, followed by the exact step `1/4096`.

The resulting dyadic trapezoid boxes are approximately:

```text
t=14: [0.0006713826695614567, 0.0006713826695756727]
t=15: [0.0006713703013901811, 0.0006713703014043968]
widths: about 1.42e-14
```

These are only the first 16 panels, not the 8192-panel Q353 sums and not sign
certificates.

## Trust audit

- Direct Lean 4.15.0 autonomous build: PASS 18/18.
- Checkpoint blocks: PASS 5/5.
- Terminal axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No `sorry`, `admit`, specialized `axiom`, `opaque`, `Float`, `unsafe`,
  `native_decide`, or `Lean.ofReduceBool` in Q356 Lean sources.
- No Riemann--Siegel implementation.

## Baseline boundary

The mandated Goldbach object is `433e29eff1d9da2bc5937bb82bf5df3a2d59c08f`.
The only supplied bundle ends at `6dc620aaf058b802089d2039d6c03b83025b677e`
and does not contain that object. The uploaded archives include Q348 and
Q352--Q355, but not the Q349--Q351 source modules or compiled objects.

`Q356Probe/AnalyticBinding.lean` therefore remains source-only. Its attempted
compilation fails immediately and specifically at the missing module prefix
`Q349Probe`. No substitute definition was introduced and no end-to-end Q349
PASS is claimed.

## Frozen boundary

```text
Q356_STRONG_END_TO_END_Q349_BINDING : NOT_OBTAINED
Q357_FIRST_128_PANEL_BLOCK          : NOT_STARTED
Q353_8192_NODE_SUM                  : NOT_OBTAINED
Q348_SIGN_LEAVES                    : UNINHABITED
BRIDGE_A                            : OPEN
CARRIER_MEMBERSHIP                  : UNPROVED
TS340_UNCONDITIONAL                 : OPEN_FROZEN
```
