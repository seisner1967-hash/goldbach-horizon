# Q392 / RS20H: canonical transform prefactor certified

Classification: POST_DEADLINE_USER_AUTHORIZED continuation of Q392.
Original four-hour timebox: OVERRUN. No new timebox or milestone is claimed.

## Result and limits

Two further actual finite atoms are certified without residual premises:

```lean
Q392Prefactor.finiteAtom_four_certified :
  certifiedTransformReBox.mem (Q392Probe.finiteAtomValue 4)

Q392Prefactor.finiteAtom_five_certified :
  certifiedTransformImBox.mem (Q392Probe.finiteAtomValue 5)
```

Together with the frozen Gamma/Dirichlet checkpoint, this gives six of eight
actual finite atom memberships at the single endpoint
`751937898017/1073741824`, K=63, ell=10.

The new widths, computed exactly from the Lean interval definitions, are:

| Component | Width (decimal rendering) | Lean upper bound |
| --- | --- | --- |
| Transform real part | 6.1574133063799153765995615e-18 | 1/10^17 |
| Transform imaginary part | 6.1585371700174297465025305e-18 | 1/10^17 |

These theorems do NOT assert membership in the older, narrower candidate
intervals. The new replay explicitly uses the new certified boxes.

## Exact reduction

Write t for the exact endpoint, r=sqrt(t^2+1/4), and set

```text
lambda = 1/(2*(r+t))
L      = log(abs xi) = (log r - log 2 - log pi)/2
theta  = -arctan lambda
E      = -L/2 + t*theta + 1/4
phi    = -theta/2 - t*L + t/2
```

`requestedTransformFactor_eq` proves the identity

```text
requestedTransformFactor = (-i/2) * exp(E) * exp(i*phi).
```

It uses the canonical Q384 coordinate squares, the exact coordinate product,
the positive-real-part branch of the complex logarithm, and Q380's independent
prefactor definition. There is no replacement prefactor and no numerical
identification with an unrelated expression.

## Certificates

The generators use only rational arithmetic and integer square roots:

- a 28-decimal rational enclosure of r, checked by squaring in Lean;
- two reduced logarithm endpoint certificates, with finite Taylor error;
- two arctangent endpoint certificates, using alternating-series bounds;
- a certified reduction of phi by -207 full turns;
- 40-term exponential polynomials, with explicit norm errors;
- exact interval multiplication and extraction of real/imaginary components.

All generated candidates acquire mathematical meaning only through their
compiled membership theorems. No external transcendental evaluator is trusted.
The three generators reproduce eleven generated Lean files byte-for-byte.

## Six-atom replay

`sixCertifiedAtomsCandidate_check` verifies the rational arithmetic expression
through the existing Q347/Q368 checker. Its candidate output, including Q391's
actual remainder radius `1/400000000000000000000000000000`, is approximately

```text
[1.8855174682945956200e-13, 1.8915581061120010466e-13].
```

Its positivity is a rational fact, NOT an unconditional Hardy sign theorem.
The semantic endpoint theorem retains exactly

```lean
Q392Prefactor.remainingCoefficientMemberships
```

as a premise for atoms 6 and 7. The axiom/dependency audit checks both that the
six proved atom theorems have no binders and that this premise remains on the
terminal theorem.

## Open leaf

Atoms 6 and 7 are the components of `requestedCoefficientFactor`, involving
the canonical Q365 coefficient sum and derivatives of Q364's entire auxiliary
function through order 189. This checkpoint does not certify those derivatives
or either coefficient component. Their old candidate boxes remain untrusted.

```text
ACTUAL_FINITE_ATOMS               : 6/8 CERTIFIED
COEFFICIENT_ATOMS_6_AND_7          : UNPROVED
CANONICAL_ENDPOINT_MEMBERSHIP     : CONDITIONAL_ONLY
CANONICAL_ENDPOINT_SIGN           : CONDITIONAL_ONLY
CARRIER_MEMBERSHIP                : UNPROVED
PRODUCTION_BRACKET                : NOT_OBTAINED
BRIDGE_A                         : OPEN
TS340_UNCONDITIONAL               : OPEN_FROZEN
```

Even a future completed endpoint does not discharge the historical Bridge A
contract. The original first bracket has different endpoints, and the family,
counting, and saturation obligations recorded in `Q392_BRIDGE_A_SPEC.md` remain.

## Verification and preservation

Exact build counts, dependency audits, hashes, and times are recorded in
`Q392_PREFACTOR_STATUS.json` and `Q392PrefactorResearch/VERIFICATION.json`.
The production source scan excludes forbidden shortcuts. Allowed axioms are
only `propext`, `Classical.choice`, and `Quot.sound`.

No global Lake rebuild is claimed. The direct Lean 4.15 checks use the existing
pinned Mathlib cache. No permanent Git operation occurred. HEAD and origin/main
remain at `433e29eff1d9da2bc5937bb82bf5df3a2d59c08f`.
The pre-existing tracked additions in `lakefile.lean` are preserved; the working
tree is not falsely described as Git-clean.

Both prior Q392 packages and their 65-entry and 1569-entry manifests are
checked unchanged. This is a separate checkpoint, not a revision of either.
