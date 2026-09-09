# Q392 / RS20H: partial finite-atom and arithmetic replay

## Verdict

**Q392_PARTIAL_FAIL_CLOSED. BRIDGE_A remains OPEN.**

The original four-hour timebox expired on 2026-09-06. Subsequent work is
`POST_DEADLINE_USER_AUTHORIZED`, following the user's explicit continuation
requests. The original T0 and deadline are unchanged. This package is a partial
replay overlay, not a claim to have met the original schedule or closed an endpoint.

## Proven in Lean

1. `requestedFiniteExpr_value_eq_canonical` binds an explicit eight-component
   ring expression to the actual Q390 finite part at t0, K=63, ell=10, with the
   Q384 source-2024 coefficient convention. It has no atom-membership premise.
2. `requestedGammaPhase_norm = 1`, six coarse component enclosures, and exact
   default zero values for unused atom indices. These are genuine mathematical
   bounds but are too wide to support the candidate sign proof.
3. `candidate_arithmetic_check`: the serialized candidate interval is exactly
   the result of Q347 rational interval arithmetic. The arithmetic certificate
   uses the actual finite expression, not the historical synthetic stress value.
4. `candidate_radius_matches_Q391`: the certificate uses the sharp radius
   1/400000000000000000000000000000, rather than imposing the old 1e-14 radius.
5. `candidate_output_lo_pos`: the **rational candidate output** has positive
   lower endpoint after adding that radius. This is NOT a Hardy sign theorem.

The compiled source list, audit results and actual build counts are recorded in
Q392_BUILD_SUMMARY.txt and Q392BuildLogs/verification.json. The audit scans
production sources, checks declared axioms, and traverses actual proof/type
constants. Imported-but-unused modules are not treated as proof dependencies.

## Conditional only

`requested_endpoint_mem_of_candidate_atoms`,
`requested_leaf_of_candidate_atoms`, and
`requested_endpoint_positive_of_candidate_atoms` all retain precisely:

```lean
(hAtom : forall n,
  (Q392Probe.candidateAtomBox n).mem (Q392Probe.finiteAtomValue n))
```

No value of this hypothesis was constructed. In particular, there is no
unconditional concrete endpoint, no strict Hardy sign, and no concrete
historical AnalyticLeaf in this package. The earlier abstract sharp connector
also remains conditional, as its name and full printed signature specify.

## External diagnostic only

The reproducible generator evaluates the true eight subexpressions at 4096 and
8192 working bits using full input balls. Its d recurrence is computed with
exact Python rationals. It exports eight outward candidate intervals on a
2^-192 grid. The two computations overlap at every atom and at the finite sum.

Numerical estimate of the finite part: about 1.8885503675660488e-13.
The independent numerical Hardy reference agrees, with an estimated difference
about 2.43904e-76. Neither numerical output is used as a mathematical proof.
Lean validates only the subsequent rational arithmetic on the exported numbers.

## Exact remaining work

The immediate open obligation is the eight narrow memberships `hAtom` above.
The first is an effective enclosure of the normalized complex Gamma phase.
Unit norm does not supply its angle. Q346 fixes the phase convention but gives
no numerical certificate for this t0. The inspected pinned Gamma APIs provide
qualitative convergence and identities; a suitable effective bound was not
constructed in this continuation. This is not a proof of impossibility.

The remaining components require tight Dirichlet and prefactor evaluations and
effective evaluation of the finite coefficient factor, including derivatives
up to order 189 or an exactly equivalent certified integral route. The six
coarse intervals proved here cannot be substituted for the exported tight ones.

The reduced error from Q391 solves the remainder budget, not these finite-atom
obligations. No external ball, unchecked code execution, target-defined atom,
or new residual semantic witness was presented as a discharged premise.

## Historical contract audit

See Q392_BRIDGE_A_SPEC.md and the compiled Q392_CONTRACT_AUDIT.txt. The first
production bracket requires two specified intervals at two specified rational
endpoints near 14.1347, neither equal to t0. The H=1000 consumer requires a
649-bracket family and two Turing multiplicity bounds. TS329 has separate
global/local count certificates and saturation conditions. Q392 supplies none
of those production or counting objects and introduces no weakened Bridge A
predicate. `CARRIER_MEMBERSHIP` and `TS340_UNCONDITIONAL` remain unchanged.

## Governance and replay

The initial preflight checked the immutable Q391 archive (SHA-256
81fdcfe0e966983aa6e110d51a3c0addccd98392424717db7a7e441d834b752c), its closure
manifest (7656f7b8a581d68e002fbb7077984df0c23eee91c98950f16f54667d21262700),
81 manifest entries, the pinned Mathlib revision and Git refs.

No commit, push, branch change, reset, checkout or destructive cleanup occurred.
The historical worktree was already dirty. The only tracked-file change in this
campaign is one additional `lean_lib Q392Probe` line in the existing lakefile;
its pre-Q392 content is preserved under Q392Research. Historical proof sources
and archives were not rewritten. Consequently the old manifest's lakefile entry
describes the old overlay, not the deliberately extended current lakefile.

The initial specialist agents stopped on usage limits. No usage reset or
external service was purchased. The contract audit and most implementation
therefore occurred during the local post-deadline continuation. Corrected
build/audit setup failures are disclosed in Q392_PROGRESS_LEDGER.md.

Replay requires the restored canonical Q343-Q391 source/cache environment,
Lean 4.15.0, and Mathlib 9837ca9d65d9de6fad1ef4381750ca688774e608. It is not
a standalone Mathlib distribution. This overlay contains all Q392 sources,
new/modified configuration, generators, exact candidate numbers and audits.
The historical import-source manifest records the local dependency graph.

Run `Q392Research/verify.ps1` in the restored project. Candidate regeneration
uses the bundled Python runtime and the existing .q358-python/python-flint 0.8.0
installation; no regeneration is needed to replay the serialized Lean numbers.
The package verifier performs a fresh safe ZIP extraction and byte/hash replay.
Its archive-hash attestation is external to the immutable ZIP.

## Unchanged frontier

```text
Q392_CANONICAL_FINITE_PART_BINDING : PROVEN_IN_LEAN
Q392_CANDIDATE_ARITHMETIC_REPLAY  : PROVEN_IN_LEAN
Q392_TIGHT_ATOM_MEMBERSHIPS      : NOT_OBTAINED
Q392_CANONICAL_ENDPOINT          : CONDITIONAL_ONLY
Q392_CANONICAL_HARDY_SIGN        : NOT_OBTAINED
CARRIER_MEMBERSHIP              : UNPROVED
BRIDGE_A                        : OPEN
TS340_UNCONDITIONAL              : OPEN_FROZEN
```
