# Q376 — Source side decay and parallel deformation

Date: 2026-08-22  
Baseline: `433e29eff1d9da2bc5937bb82bf5df3a2d59c08f`  
Verdict: `Q376_ANALYTIC_PARTIAL_FAIL_CLOSED`

## Proven in Lean

- Exact affine geometry, orientation, transverse endpoints and tangents.
- Pole and principal-log branch avoidance throughout every intermediate strip.
- Uniform Gaussian/cosine side bounds for every `OuterContourRegime`; this
  covers the central, lower and upper constructors.
- Vanishing right and left transverse integrals for the regular primary `g`,
  every finite polynomial, and their exact difference.
- Exact Cauchy identity on every truncated rectangle.
- Passage to complete-line integrals under integrability and side-decay.
- Unconditional parallel deformation for `sourcePrimaryGRegular` minus an
  arbitrary finite polynomial, then for the named primary finite polynomial.

Principal compiled theorems:

```lean
sourceFiniteTaylorDifference_right_boundary_tendsto_zero
sourceFiniteTaylorDifference_left_boundary_tendsto_zero
source_truncated_rectangle_identity
source_parallel_line_deformation_of_integrable
sourceFiniteTaylorDifference_parallel_deformation_closed
sourcePrimaryFiniteTaylor_parallel_deformation_closed
```

## Conditional boundary

`SourcePrimaryRemainderOnFinalLine` isolates the remaining pointwise theorem:

```text
sourcePrimaryGRegular tau z - sourcePrimaryFiniteTaylorPolynomial K tau at z
  = sourceRgK K tau z (1/2) phi
```

Lean proves that an inhabitant of this structure is sufficient for the full
outer-contour binding and for equality with `sourceRSRemainder`. No inhabitant
is constructed or claimed.

## Not obtained

```text
Q376_SOURCE_RGK_SIDE_DECAY_PASS              : NOT_OBTAINED
Q376_SOURCE_REMAINDER_PARALLEL_DEFORMATION   : NOT_OBTAINED
Q376_PARALLEL_LINE_DEFORMATION_PASS          : NOT_CLAIMED_FOR_SOURCE_RGK
Q376                                         : PARTIAL
```

The reason is precise: the source first defines the Taylor remainder
analytically and only later identifies it with the independent line integral
`sourceRgK` by a change of variables and an inner contour deformation. The
local Cauchy series is insufficient on the whole unbounded outer line because
its disk condition is not uniform there.

## Audit

```text
Direct Lean builds : PASS 22/22
Aggregate Lake     : PASS 2287/2287
Axioms             : propext, Classical.choice, Quot.sound
Forbidden scan     : EMPTY
git diff --check   : PASS
HEAD = origin/main : 433e29e
```

The worktree contains many accepted untracked artifacts from earlier pilots;
it is not described as clean. No permanent Git operation was performed.
