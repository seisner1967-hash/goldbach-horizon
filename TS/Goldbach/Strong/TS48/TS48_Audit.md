# TS48 - Bounded Support Snorm Lemma

## Status

TS48 proves the generic bounded-support `snorm` lemma used by TS47.

Status: `repo_committed`.

The proof compares a bounded supported function with the indicator of its
support, applies Mathlib's indicator-function `eLpNorm` estimate, and closes
the remaining `ENNReal` bound by showing `sqrt(2) <= 2`.

TS48 does not prove Sobolev agreement, Plancherel, or Fourier-tail decay.

## Lean Files

- `BoundedSupportSnormLemma.lean`:
  - defines `BoundedSupportSnormTarget`;
  - proves `boundedSupportSnormLemma`;
  - proves `boundedSupportSnormTarget`;
  - proves `triangleSplineDerivativeSnormTarget`.

## Audit Commands

```powershell
lake build TS.Goldbach.Strong.TS48.BoundedSupportSnormLemma

rg -n "s[o]rry" TS\Goldbach\Strong\TS48
rg -n "a[x]iom" TS\Goldbach\Strong\TS48
```

Expected result: 0 `s[o]rry`, 0 `a[x]iom`.

## Ledger

| ID | Object | Status | Comment |
| --- | --- | --- | --- |
| TS48-N1 | `BoundedSupportSnormTarget` | `repo_committed` | target proposition for the generic lemma |
| TS48-N2 | `boundedSupportSnormLemma` | `repo_committed` | proves the generic bounded-support `snorm <= 2` estimate |
| TS48-N3 | `boundedSupportSnormTarget` | `repo_committed` | concrete witness for the TS48 target |
| TS48-N4 | `triangleSplineDerivativeSnormTarget` | `repo_committed` | discharges the TS45 triangle-spline derivative `snorm` target |

## Conclusion

TS48 closes the generic `snorm` bridge introduced in TS47. The triangle-spline
derivative norm route now has a concrete Lean witness, leaving Sobolev
agreement and Fourier-tail decay for later sprints.
