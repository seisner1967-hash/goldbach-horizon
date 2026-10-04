# Closed component attempt — technical failure, no numerical PASS

The unique authorized THERMAL_COMPONENT_AUX22 attempt started
2026-10-03T10:06:52.935732UTC and finished10:10:21.151549UTC, exit1.
Token0836684068fe4c5da140a88078ef1359. The actor was ROLE6 and the child
command used the frozen Python -B -X utf8 runtime. All27PREEXEC copies
preceded rawSTART. The25bound source/input/runtime files and gate/preparation
remained unchanged. The sole attempt is consumed and will never be replayed.

The exact exception is `ValueError: Exceeds the limit (4300 digits) for
integer string conversion`. `component_bank22.py:141` calls
`thermal_kernel22.py:99`, exporting `E_function` through
`thermal_dyadic22.py:47`, where `str(q.numerator)` fails. Repeated exact
Fraction radius propagation admits increasing power-of-two denominators.
This is a representation/serialization defect; the exception does not
identify a false Gamma, EM, DFT or thermal identity and does not locate a
parity deduction. It also prevents a completed bank result from existing.

The log has15Gamma case progress lines, and the actual child wrote15sqrt
certificates. Neither constitutes a partial PASS: case outcomes remained in
process memory and were not preserved in a completed result. The independent
checker at the end was not reached. All numerical layers of this bank remain
UNRESOLVED/NO_COMPLETED_RESULT, with noH1/coefficientN/D_N/WIN claim.

Raw files remain in `actual_component22`: actual_START.json, actual.log,
component_sqrt_certificates22.jsonl, PREEXEC_captures.json,
POSTEXEC_integrity.json and actual_receipt.json. ReceiptFULL2a6c38,
STARTFULL8ee9d7, PREEXECFULL44eab4, POSTFULL19233f, logFULL67b1e1,
certificatesFULLb93fc7. The source/paper audit by ROLE4 is separate
07c877 and concerns only the independent integral and its closed remainder.

A new SOURCE revision01 may round each radius outward onto the2^-512 grid
and carry the radius-round contribution, preserving its mathematical
enclosure while bounding representation size. This is a new source/contract
iteration requiring a new freeze and a distinct root gate. No existing
binding is changed, no runtime integer-string setting is patched, and no
old partial phase value is reused as an oracle.
