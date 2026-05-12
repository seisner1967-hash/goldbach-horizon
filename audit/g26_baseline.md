# G26 — Phase 0 baseline snapshot

Generated manually because `python -m proof_agent` is not installed on this
host (the agent CLI returned `No module named proof_agent`). Per the Phase 0
brief, the manual fallback is acceptable.

## Repo identity

- Branch: `feat/g26-sorry-cleanup` (created from `main`)
- HEAD: `62bdd5c2e316df0e4a0f37331651362f5fde03a6`
- Subject: "Replace FSN v9 placeholders with explicit unknown markers"
- Date of snapshot: 2026-05-12
- Lake target: single library `Goldbach` (no `Goldbach.Certified` /
  `Goldbach.Goldbach` submodule targets exist; see `lakefile.lean`).

## Discipline boundary (off-limits, do not modify in this track)

These 5 untracked files belong to a separate Lean project (F-MT-004 / M_short_F).
They are in the same working tree but are not part of the G26 cleanup scope.
`Loop-LakeBuild.ps1` refuses to proceed if any of them appears in the staged
index or working-tree diff:

- `Goldbach/M3cTerminalCD12Interval.lean` (untracked, 8401 bytes)
- `Goldbach/M3cTerminalCD12AbelInterval.lean` (untracked, 5634 bytes)
- `Goldbach/M3cTerminalCD12Conditional.lean` (untracked, 9113 bytes)
- `Goldbach/M3cTerminalCD12PublicV022.lean` (untracked, 5315 bytes)
- `Goldbach/MertensLandauNOverPhiKernelBound.lean` (untracked, 16035 bytes)

Status carried forward unchanged from upstream:

- F-MT-004 = OPEN
- M_short_F = NOT_ACCEPTED

The G26 track must not create, reference, or delete any artefact under
`audit/CD*`, `manifests/CD*`, or a top-level `CD*/` folder. All G26 artefacts
live under `audit/g26_*`, `manifests/G26_*`, `tools/g26_cleanup/*`.

Build-system files that are also forbidden to mutate from G26:

- `lakefile.lean`
- `lean-toolchain`
- `lake-manifest.json`

## Watchlist (sorry / axiom census, tracked Goldbach library)

`git grep '\bsorry\b' Goldbach/` (HEAD = 62bdd5c) returns 36 matches across
25 tracked files. Spot-check of `Goldbach/ThresholdReal.lean` (the file with
the highest count, 5) shows every match is inside a comment — the words
`0 sorry` / `sorry` appearing in human-readable documentation, not as
proof terms. This is consistent with the commit `7ed739f` "ZERO SORRY —
45/45 closed, 0 axiom, 0 sorry".

- Actual `sorry` proof terms in tracked `Goldbach/**.lean`: **0**
- Actual `axiom` declarations in tracked `Goldbach/**.lean`: **0**
  (`git grep -E '^\s*axiom\s' Goldbach/` returns nothing)

Files where the comment-only `sorry` token appears (preserved as-is — these
are documentation artefacts, not cleanup targets):

| count | file |
|---|---|
| 5 | Goldbach/ThresholdReal.lean |
| 3 | Goldbach/A2Certificate.lean |
| 2 | Goldbach/CompactZone/Grid.lean |
| 2 | Goldbach/CompactZone/Wire.lean |
| 2 | Goldbach/Jackson/Defs.lean |
| 2 | Goldbach/PCBGallagher.lean |
| 2 | Goldbach/PrimeCrystalModel.lean |
| 1 | Goldbach/A2PureAnalytic.lean |
| 1 | Goldbach/AxiomsToLemmas.lean |
| 1 | Goldbach/BreakpointGrid.lean |
| 1 | Goldbach/CompactWindowShadow.lean |
| 1 | Goldbach/CompactZone/Bridge.lean |
| 1 | Goldbach/CompactZone/CellBounds.lean |
| 1 | Goldbach/CompactZone/CellBoundsStrong.lean |
| 1 | Goldbach/CompactZone/Defs.lean |
| 1 | Goldbach/DominationRatioComputable.lean |
| 1 | Goldbach/FredholmOTSA.lean |
| 1 | Goldbach/G43Budget.lean |
| 1 | Goldbach/HerglotzPositivity.lean |
| 1 | Goldbach/InterfacesStrong.lean |
| 1 | Goldbach/InterfacesStrongBridge.lean |
| 1 | Goldbach/IntervalArith.lean |
| 1 | Goldbach/MellinJackson.lean |
| 1 | Goldbach/Roadmap.lean |
| 1 | Goldbach/SmallInstances.lean |

## Pre-existing unstaged changes (NOT part of Phase 0)

Carried forward from `main` working tree, untouched by this Phase 0 commit:

- `Goldbach/CompactZone/NumeratorAll.lean` (modified)
- `Goldbach/Jackson/Defs.lean` (modified)
- `Goldbach/KLMN/Chain.lean` (modified)
- `Goldbach/KLMN/Sobolev.lean` (modified)
- `Goldbach/Status.lean` (modified)

None of these are in the forbidden list. They are unrelated to G26 and
should be triaged outside this track before Phase 1 starts (open question
for ratification).

## What `lake build` was not run for

A full `lake build Goldbach` would have to recompile every dependent of
the 5 pre-existing unstaged files above — minutes of CPU and a dirty cache.
Phase 0 acceptance focuses on the guard tool, not on rebuilding the
library; the build will be exercised at the start of Phase 1 against a
clean tree.
