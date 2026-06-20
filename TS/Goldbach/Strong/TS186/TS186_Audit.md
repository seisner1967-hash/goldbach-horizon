# TS186 Audit - Triangle Spline Main Term Normalization Bridge

## Scope

TS186 packages the triangle-spline origin value for future explicit-formula
main-term use.

The new Lean file is:

```text
TS/Goldbach/Strong/TS186/TriangleSplineMainTermNormalizationBridge.lean
```

## Proved content

TS186 proves and records:

```lean
TriangleSplineMainTermNormalizationStatement
triangleSplineMainTermNormalization
TriangleSplineScaledMainTermStatement
triangleSplineScaledMainTerm
TriangleSplineDiscreteWeightAtZeroStatement
triangleSplineDiscreteWeightAtZero
TriangleSplineDiscreteScaledMainTermStatement
triangleSplineDiscreteScaledMainTerm
triangleSplineMainTermNormalizationTarget
```

The continuous origin value is supplied by the existing TS162 theorem:

```lean
TS162.Goldbach.triangleSpline_zero
```

The discrete origin value is supplied by the TS182 affine formula at `n = 0`
for positive scales.

## Mathematical meaning

TS186 normalizes the future explicit-formula main term:

```text
X * triangleSpline(0) = X
X * triangleSplineDiscreteWeight X 0 = X    for 0 < X
```

This is a local bridge only.  It does not assemble the explicit formula.

## Non-claims

TS186 does not prove:

```text
the explicit formula
zeta-zero summability
Plancherel
a sieve-trace comparison
Goldbach
```

## Verification protocol

Run:

```powershell
lake env lean TS\Goldbach\Strong\TS186\TriangleSplineMainTermNormalizationBridge.lean
lake build TS.Goldbach.Strong.TS186.TriangleSplineMainTermNormalizationBridge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS186
git diff --check
git status --short
```

Expected result:

```text
Lean file compiles
Lake target builds
No forbidden proof placeholders
No global assumption declarations
No non-ASCII characters in TS186
No whitespace errors
```

## Verdict

TS186 closes the main-term normalization bridge while leaving the explicit
formula and the sieve-trace comparison as future local contracts.
