# Q392 / RS20H continuation: four certified finite atoms

Classification: POST_DEADLINE_USER_AUTHORIZED. Original Q392 timebox: OVERRUN.
Proof checkpoint: 2026-09-08. This does not replace the immutable initial Q392 package.

## Verdict

```text
GAMMA_PHASE_TRUE_COMPONENTS       : CERTIFIED (atoms 0, 1)
DIRICHLET_TRUE_COMPONENTS         : CERTIFIED (atoms 2, 3)
FINITE_ATOM_MEMBERSHIPS           : 4 / 8
FOUR_ATOM_CONDITIONAL_REPLAY      : PASS
CANONICAL_ENDPOINT               : CONDITIONAL_ONLY
CARRIER_MEMBERSHIP               : UNPROVED
BRIDGE_A                         : OPEN
TS340_UNCONDITIONAL              : OPEN_FROZEN
```

All four memberships concern `Q392Probe.finiteAtomValue`, at the unchanged
endpoint `751937898017/1073741824`, with `K=63`, `ell=10`.

## Unconditional results

`GammaPhaseCertifiedAtoms.lean` proves:

```lean
finiteAtom_zero_certified : certifiedGammaReBox.mem (Q392Probe.finiteAtomValue 0)
finiteAtom_one_certified  : certifiedGammaImBox.mem (Q392Probe.finiteAtomValue 1)
```

The actual normalized Gamma phase is approximated through the convergent Euler
Gamma sequence, with an explicitly checked logarithmic correction. A generic
phase-error bound `65536/N^9` is proved for `N >= 1` and positive real part.
At `N=512` this is `2^-65`, approximately `2.71e-20`. This is a phase bound,
not a relative-error theorem for an unrestricted Gamma approximation.

The 513 logarithms of the finite Euler sum are certified in 33 blocks, joined
by a balanced tree. One additional logarithm supplies the corrected endpoint.
Real logarithms, exact rational correction arithmetic, a reduction by 207 full
turns, and a finite exponential Taylor remainder complete the proof.
Each final Gamma component interval has width exactly `2201/10^20 = 2.201e-17`.

`DirichletCertifiedAtoms.lean` proves:

```lean
finiteAtom_two_certified   : certifiedDirichletReBox.mem (Q392Probe.finiteAtomValue 2)
finiteAtom_three_certified : certifiedDirichletImBox.mem (Q392Probe.finiteAtomValue 3)
```

All ten terms of the canonical `Int` interval `[1,10]` are certified separately.
An exact identity separates `1/sqrt(n)` from the phase `-t0*log(n)`. Rational
square comparisons certify the amplitudes; reduced real logarithms and a
40-term exponential polynomial certify the phases. Both summed component
widths are about `2.0088e-16`, with a proved upper bound `1e-15`.

## Conditional endpoint, not a sign theorem

The new rational boxes are deliberately wider than the old 192-bit candidate
boxes. No membership in those old narrow boxes is claimed for atoms 0 through 3.

`PartialAtomReplay.lean` consumes the four new memberships and retains:

```lean
remainingFourAtomMemberships :=
  forall n, 4 <= n -> n < 8 ->
    (Q392Probe.candidateAtomBox n).mem (Q392Probe.finiteAtomValue n)
```

The Q347/Q368 arithmetic check passes, using exactly the Q391 remainder radius
`1/400000000000000000000000000000`. Its candidate output is positive, approximately
`[1.88559323262521e-13, 1.89148606149045e-13]`. These numbers are NOT an unconditional
enclosure of Hardy Z: both the endpoint membership and positivity theorem still
take `remainingFourAtomMemberships` as an explicit premise.

The remaining work is to certify the real and imaginary components of
`requestedTransformFactor` and `requestedCoefficientFactor`, preserving the
source-2024 convention `sigma=0`. A future change to their boxes must be replayed.
No endpoint, production bracket, carrier membership, or historical Bridge A
contract has been closed by this continuation.

## Verification

- Lean 4.15.0; Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608`.
- Production import closure: 74/74 direct builds, matching current source hashes.
- Axiom audit: 13/13 selected terminal and structural declarations; only
  `propext`, `Classical.choice`, `Quot.sound`.
- Transitive dependency audit: 57,359 constants; rejected semantic dependencies: none.
- The four atom theorems have no residual premises. The endpoint premise is checked to remain present.
- Forbidden scan over all continuation proof sources: EMPTY.
- Eight rational-generator commands replay byte-identically; 587 Lean source files unchanged.
- The 587 files include alternative per-node generated sources. They are NOT all claimed as
  separately compiled modules; the certified production import closure is the 74-module set.
- Historical import-source inventory: 693 files.
- Original Q392 manifest: 65/65 unchanged. Original archive SHA-256 remains
  `9701836b2e7c47751e1f87b0b305e6f71f31b450dd85aa10927762bdbe16c0d4`.
- `HEAD = origin/main = 433e29eff1d9da2bc5937bb82bf5df3a2d59c08f`.
- No permanent Git operation. Pre-existing additions to `lakefile.lean` remain;
  the worktree is not described as Git-clean.

Exact build records and the dependency audit are retained in the continuation package.
No fresh global Lake rebuild or cold Mathlib rebuild is claimed.
