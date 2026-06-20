# TS184 Audit - Triangle Spline Von Mangoldt API Probe

## Scope

TS184 probes Mathlib's von Mangoldt API and binds it to the TS183 finite
weighted-sum interface.

The new Lean file is:

```text
TS/Goldbach/Strong/TS184/TriangleSplineVonMangoldtAPIProbe.lean
```

## Mathlib API identified

TS184 imports:

```lean
import Mathlib.NumberTheory.VonMangoldt
```

The probe stabilizes these symbols:

```text
ArithmeticFunction.vonMangoldt : ArithmeticFunction Real
ArithmeticFunction.vonMangoldt_nonneg
```

The sprint defines:

```lean
mathlibVonMangoldtWeight : Nat -> Real
```

by applying Mathlib's `ArithmeticFunction.vonMangoldt` as a plain natural
number weight.  The Mathlib nonnegativity theorem supplies the exact field
required by the TS183 `VonMangoldtWeightContract`.

## Proved content

TS184 proves:

```lean
mathlibVonMangoldtWeight_nonneg
mathlibVonMangoldtWeightContract
triangleSplineMathlibVonMangoldtWeightedSum_eq_generic
triangleSplineMathlibVonMangoldtWeightedSum_nonneg
triangleSplineMathlibVonMangoldtWeightedSum_range_eq_of_le
triangleSplineMathlibVonMangoldtWeightedSum_affine
triangleSplineVonMangoldtAPIProbeTarget
```

The concrete smoothed von Mangoldt sum inherits the TS183 finite-range,
range-extension, affine-support, and nonnegativity properties.

## Non-claims

TS184 does not prove:

```text
prime-number estimates
the explicit formula
zeta-zero construction
zeta-zero summability
Plancherel
Goldbach
```

## Verification protocol

Run:

```powershell
lake env lean TS\Goldbach\Strong\TS184\TriangleSplineVonMangoldtAPIProbe.lean
lake build TS.Goldbach.Strong.TS184.TriangleSplineVonMangoldtAPIProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS184
git diff --check
git status --short
```

Expected result:

```text
Lean file compiles
Lake target builds
No forbidden proof placeholders
No global assumption declarations
No non-ASCII characters in TS184
No whitespace errors
```

## Verdict

TS184 turns the TS183 local von Mangoldt contract into a concrete Mathlib API
binding while keeping all analytic-number-theory claims outside the sprint.
