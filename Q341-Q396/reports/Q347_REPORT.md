# Q347 — Bridge A dyadic-certificate research sprint

Date: 2026-08-12  
Required Goldbach baseline: `433e29eff1d9da2bc5937bb82bf5df3a2d59c08f`  
Available architecture baseline: `6dc620aaf058b802089d2039d6c03b83025b677e`  
Required Lean: 4.15.0  
Required Mathlib: `9837ca9d65d9de6fad1ef4381750ca688774e608`

## Verdict

```text
Q347_ARCHITECTURE_PARTIAL
Q347_BASELINE_BINDING_PENDING
Q347_BUILD_NOT_RUN_ENVIRONMENT_MISSING
Q347_ARITHMETIC_CERTIFICATE_SOURCE_DRAFTED_UNCOMPILED
Q347_SPECIAL_FUNCTION_ANALYTIC_LEAF_MISSING
Q347_REAL_CERTIFICATE_REPLAY_NOT_OBTAINED
Q347_FIRST_BRACKET_SIGN_NOT_OBTAINED
BRIDGE_A_OPEN
CARRIER_MEMBERSHIP_UNPROVED
MUR4_OPEN_REDUCED_TO_ANALYTIC_LEAF
TS340_UNCONDITIONAL_OPEN_FROZEN
Q348_NOT_LAUNCHED
```

The two-hour authorization was treated as a maximum.  Research started at
`2026-08-12T08:03:54+02:00`, with deadline
`2026-08-12T10:03:54+02:00`.  It stopped early and fail-closed after the
available environment made both baseline binding and Lean replay impossible.
No missing build or external numerical result is promoted to a proof.

## 1. Integrity and environment

The required Q346 baseline object `433e29e...` is absent from the available
Git bundle.  The available bundle ends at `6dc620a...` and is used only in a
detached architecture lab.  It cannot establish Q346-baseline compatibility.

The Q346 manifest supplied with the inputs is present and its SHA-256 is the
pinned value `6bf3565046beb5a006c8286eaeb5f423a95f44654a7e4eae527549e8c90c06c3`.
The Q343 first-bracket certificate JSON and its serialized endpoint balls are
not present, so no genuine bracket instance can be replayed.

The repository pins Lean 4.15.0 and the required Mathlib commit, but the
container has no `lean`, `lake`, `elan`, Mathlib source, or compiled Mathlib
cache.  Consequently:

- no new Lean file was compiled;
- no `#print axioms` result exists for the Q347 drafts;
- no first-sign theorem exists;
- the drafts remain outside the Goldbach source tree.

## 2. What the sprint did establish

### Existing exact arithmetic substrate

The available Goldbach history contains `Goldbach/IntervalArith.lean`, an
exact rational interval layer with membership-correctness theorems for point
intervals, negation, addition, subtraction, four-corner multiplication,
positive-denominator division, squaring, and interfaces for square-root and
logarithm enclosures.  A textual source audit found no proof hole or declared
axiom in that file.  This is a historical/source result only because its build
could not be replayed here.

### Proof-carrying certificate boundary

`Q347Probe/ArithmeticCertificate.lean` drafts a small inductive certificate
language over that exact interval layer.  Its intended soundness theorem says
that Lean reconstructs interval membership from checked analytic leaves;
strict endpoint exclusion then yields the sign.  The generator and parser are
therefore outside the mathematical trust boundary.

`Q347Probe/AnalyticLeafBoundary.lean` separates two facts which must never be
conflated:

1. the replayed interval contains the exact mathematical carrier value;
2. the replayed interval is identical to the serialized external output.

No inhabitant of either analytic-leaf structure was constructed.  Interface
definitions alone do not close bridge A.

## 3. External tool audit

### `girving/interval`

The project supplies conservative software floating-point intervals, complex
boxes, elementary transcendental operations, `sincos`, and a generic
Euler–Maclaurin layer.  These are relevant building blocks.  Two restrictions
are decisive:

- current upstream targets Lean 4.27.0-rc1 rather than Goldbach's Lean 4.15.0;
- its current Gamma file gives an effective Stirling expansion for **real
  log-Gamma at positive real arguments**, not a complex Gamma enclosure at
  `1/4 + i*t/2`.

The pinned commit `f4a3231...` could not be materialized in this environment,
so compatibility with Lean 4.15.0 remains untested.

### DSLean

DSLean demonstrates typed translation of external certificates into Lean and
Gappa-backed reconstruction.  It does not provide a zeta, complex Gamma, or
Hardy-Z enclosure theorem, and current upstream also targets Lean 4.27.0.  Its
architecture is useful after an analytic trace exists; it does not supply that
trace.

### FLINT/Arb

FLINT documents Arb values as rigorous balls and provides Hardy-Z evaluation.
That is strong evidence about the external computation, but a final Arb ball
is not a Lean proof that Mathlib's exact `riemannZeta` or the project carrier
belongs to the interval.  The Q343–Q346 inputs contain no operation-level
special-function trace with checked truncation remainders.

A targeted search found no primary Lean source already formalizing the
Riemann–Siegel formula with an explicit numerical remainder suitable for this
replay.  This search is not a proof of global nonexistence; it records what was
available to the sprint.

## 4. Exact remaining lock

For one exact dyadic endpoint `t0`, bridge A still needs a constructed theorem
of the following semantic shape:

```lean
AnalyticLeaf Q343Probe.normalizedHardyZ t0
```

or a corresponding `BoundExternalLeaf` that also proves equality with the
serialized FLINT interval.  The missing proof must unfold a specified finite
Hardy-Z algorithm and prove every rounding and truncation remainder.

For the first sign only, the narrowest current engineering candidate is a
direct Riemann–Siegel certificate over real interval operations:

1. recover the exact Q343 first-bracket endpoints and balls;
2. materialize the pinned `girving/interval` commit and port only the required
   `log`, square-root, and `sincos` slice to Lean 4.15;
3. prove a Riemann–Siegel identity and explicit remainder enclosure at the
   selected endpoint;
4. replay all dyadic operations in Lean;
5. prove final-interval equality and strict zero exclusion.

The fallback route is a complex Euler–Maclaurin zeta evaluator plus a separate
complex Gamma/log-Gamma enclosure.  It has a broader dependency surface.  The
recommendation above is an engineering inference; only a compiled one-point
prototype can validate it.

## 5. Boundary and governance

The arithmetic certificate draft reduces mur 4 to a named analytic obligation,
but it does not discharge that obligation.  Bridge B remains closed by Q346;
bridge A and carrier membership remain open.  No branch, commit, push, pull
request, merge, tag, permanent Goldbach module, or Q348 work was created.

## Primary references

- FLINT Arb real-number semantics: https://flintlib.org/doc/arb.html
- FLINT real/complex-number documentation index: https://flintlib.org/doc/index_arb.html
- `girving/interval`: https://github.com/girving/interval
- `girving/interval` Euler–Maclaurin subtree: https://github.com/girving/interval/tree/main/Interval/EulerMaclaurin
- `girving/interval` real log-Gamma source: https://github.com/girving/interval/blob/main/Interval/EulerMaclaurin/Gamma.lean
- `girving/interval` conservative `sincos` source: https://github.com/girving/interval/blob/main/Interval/Interval/Sincos.lean
- DSLean: https://github.com/taterowney/DSLean

