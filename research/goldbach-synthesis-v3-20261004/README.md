# Goldbach engineering freeze and Synthesis V3

This snapshot closes the engineering session on 4 October 2026. It preserves
every file under `Goldbach_Parity_20261002`, including Lean sources, independent
compiler and axiom receipts, build scripts, native binaries, numerical receipts,
logs, unsuccessful attempts, research notes, and the new manuscript.

The manuscript and minimal arXiv source package are available in
[the V3 publication folder](../../publications/2026-10-goldbach-synthesis-v3/).
The previous V2 publication is preserved unchanged.

## Proof boundary

- The retained engineering tally is 88 modules and 1,488 auxiliary declarations,
  including definitions. It is not a count of 1,488 new theorems about Goldbach.
- The exact Mellin module passed independently with 30 declarations:
  24 theorems and 6 definitions, without recovery or custom proof axioms.
- The exact rational scalar test passed at `N=100000000`, `a=1/N`, `H=10^11`.
  This verifies a rational majorant smaller than `10^-6`; the complete Lean
  interface from the Mellin tails to the Goldbach coefficient remains uncompiled.
- Two native executables were built. The final native coefficient check ended
  at its hard time limit without a verdict; no coefficient value is claimed.
- The last Lean batch failed at the reflection rewrite. Its geometric successor
  was not invoked. The repaired tail source is preserved as uncompiled source.
- The signed estimate for `D_N` and the research win condition remain open.

## Exact preservation and restoration

`ARCHIVE_MANIFEST.json` lists every original file, byte count, SHA-256 and storage
location. Ordinary files are directly readable under `workspace/`. Original
files too large for GitHub are stored losslessly under `payloads/`, either as
deterministic gzip or as unchanged compressed data, split into parts of at most
48 MiB. Identical oversized payloads share stored parts. No original file is
omitted.

The subtree disables Git text conversion. Historic Windows paths inside receipts
remain historic evidence; they are not silently rewritten for publication.

From the repository root, verify every reconstructed original byte stream:

```console
python scripts/restore_goldbach_v3.py research/goldbach-synthesis-v3-20261004
```

Restore the complete original research tree into a chosen directory:

```console
python scripts/restore_goldbach_v3.py research/goldbach-synthesis-v3-20261004 --output RESTORE_DIRECTORY
```

The script verifies hashes and refuses to replace a differing existing file.
It supports extended paths on Windows. For Git checkout on Windows, use
`git config core.longpaths true` if needed.

Archive integrity is a byte-preservation check. It does not add mathematical
proofs, turn failed attempts into successful ones, or rerun historical tests.

The minimal theory restart instructions are in
`workspace/Goldbach_Parity_20261002/synthesis_v3/HANDOFF_THEORY_V3.txt`.
