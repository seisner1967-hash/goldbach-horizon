# Q354 - Flat checked transcendental replay

## Verdict

```text
Q354_FLAT_INSTRUCTION_FORMAT_PASS
Q354_FLAT_BLOCK_SOUNDNESS_PASS
Q354_CHECKED_SUBSET_SERIALIZED_PASS
Q354_FINITE_TAYLOR_REMAINDER_PASS
Q354_TIGHT_COS_LEAVES_PASS
Q354_SINGLE_NODE_TRACE_CHECK_PASS
Q354_TRUE_ANALYTIC_NODE_MEMBERSHIP_PASS
Q354_SINGLE_NODE_REPLAY_PASS
Q354_16_NODE_STRETCH_NOT_ATTEMPTED
```

The maximal permitted single-node verdict is obtained. Lean proves that the
serialized final registers contain the complete mathematical folded theta
integrand at `u = 1`, for both `t = 14` and `t = 15`:

```lean
singleNode14_serialized_register_true_membership
singleNode15_serialized_register_true_membership
```

These theorems include the infinite theta tail through the existing analytic
majorant. They do not merely certify the two-term SSA expression.

## Flat replay architecture

The Q353 dependent trace was replaced by:

- a flat `Array FlatInstr`;
- dynamic `Nat` register references checked by `Array.get?`;
- `Option` failure on every invalid reference or unsupported operation;
- rational interval inclusion checks;
- a proved semantic register invariant;
- four blocks of five instructions, each compiled independently.

A monolithic flat fold still exhausted elaboration resources. Segmenting it
and proving each instruction checkpoint locally reduced the concrete replay
to a stable build while preserving global register indices.

## Finite Taylor leaf

`TightTaylor.lean` proves a finite Taylor remainder from
`Complex.exp_bound'`, then pairs the complex terms into a real even cosine
polynomial. The kernel proves the following rational enclosures:

```text
cos(7)    in [0.7539022543, 0.7539022544]
cos(15/2) in [0.3466353178, 0.3466353179]
```

The large complex normalization initially timed out. The successful proof
uses a real polynomial checkpoint with 20 and 22 terms respectively.

## True analytic membership

The final serialized boxes are `[-24, 24]`. Independently of the truncated
SSA expression, Lean proves the stronger uniform estimate

```text
abs (criticalThetaFoldedIntegrand t 1) <= 12.
```

The proof uses the complete theta-series majorant, `exp(1/4) <= 3`, and
`exp(-pi * exp(1)) <= 1/2`, all derived analytically without a numerical
oracle. This gives the two actual terminal memberships required by the Q354
mandate.

## Trust audit

- Lean 4.15.0 direct compilation: PASS.
- Selected terminal axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- No `sorry`, `admit`, specialized `axiom`, `opaque`, `Float`,
  `native_decide`, or `Lean.ofReduceBool` in Q354 sources.
- No Riemann-Siegel implementation.
- No branch, commit, push, PR, merge, tag, or modification of `main`.

## Fail-closed boundary

```text
BRIDGE_A                     : OPEN
CARRIER_MEMBERSHIP           : UNPROVED
Q348_SIGN_LEAVES             : UNINHABITED
Q353_8192_NODE_SUM           : NOT_OBTAINED
Q354_16_NODE_STRETCH         : NOT_ATTEMPTED
TS340_UNCONDITIONAL          : OPEN_FROZEN
```

Q354 certifies one real analytic quadrature node, not a sign of the full
integral and not the 8193-node trapezoidal sum. Bridge A therefore remains
open exactly as required.
