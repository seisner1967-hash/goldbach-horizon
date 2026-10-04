# Numerical addendum for Synthesis V3.1

This archive preserves all 47 files from `Goldbach_Numerical_20261004` as
frozen on 4 October 2026: operational C++ checker source and executable,
Python launch and audit scripts, the corrected Windows job controller,
execution receipts, logs, the initial stopped attempt, two complete sets of
the three payload files, the numerical verdict and the concise addendum.
Original byte streams total 988,288,691 bytes. No source file was omitted.

The fresh producer and independent checker both completed with exit code 0
at `N=100000000`, `K=134217728`. The recorded CRT coefficient, direct
canonical A32 coefficient and independent B40 coefficient agree exactly:

```text
14616354094337692277256326339388864358034646
```

The normalized coefficient is
`175937962.6753246171932162576862099326930458013955734680521890163404618`.
The observed A32/B40 difference is zero; the joint quantization comparison
radius is `4.440892142909547146941529534764364885748854559143088343048421854199551E-8`.
The producer elapsed native time was 1098.219 seconds and the checker elapsed
native time was 1659.281 seconds. These values are documented in the retained
JSON receipts. Their parent monitor times are recorded separately.

These results validate a finite arithmetic computation. They do not validate
the uncompiled Mellin truncation-to-coefficient interface, a native-to-Lean
refinement, a spectral hypothesis, the sign of D_N, or Goldbach's conjecture.
No new theoretical or Lean research was performed for this addendum.

## Archive verification and restoration

`ARCHIVE_MANIFEST.json` records every original path, byte count and SHA-256.
Ordinary files are stored under `workspace/Goldbach_Numerical_20261004/`.
The two 400,000,020-byte copies of `factors.bin` have the same SHA-256 and share
one lossless gzip payload, split into parts of at most 48 MiB under `payloads/`.
The subtree's `.gitattributes` disables Git text conversion.

The archive schema retains the name `GOLDBACH_V3_BYTE_EXACT_RESEARCH_ARCHIVE`
because the existing generic V3 archival and restoration scripts were reused.
This is the new operational numerical snapshot, not a modification of the
earlier V3 engineering freeze. Historic absolute Windows paths in receipts
remain unchanged evidence.

From the repository root, verify every reconstructed original byte stream
without rerunning the native calculation:

```console
python scripts/restore_goldbach_v3.py research/goldbach-numerical-20261004
```

Restore the numerical workspace into a chosen directory:

```console
python scripts/restore_goldbach_v3.py research/goldbach-numerical-20261004 --output RESTORE_DIRECTORY
```

The unchanged historical producer executable used in this run is already
preserved by the companion V3 engineering snapshot at
`research/goldbach-synthesis-v3-20261004/workspace/Goldbach_Parity_20261002/round22/role4/circle_native_revision02/build-final04/producer_dit22.exe`.
Its SHA-256 is
`44d2d571a0190f7dbbb975225559d16a012693bda4197738e6311c14892cadb0`.
Restore the V3 snapshot into the same output directory to recover that producer
and the surrounding historical sources:

```console
python scripts/restore_goldbach_v3.py research/goldbach-synthesis-v3-20261004 --output RESTORE_DIRECTORY
```

Verification checks archival byte integrity. Scientific evidence is contained
in `numerical_verdict.json`, the native stdout and the execution receipts.
