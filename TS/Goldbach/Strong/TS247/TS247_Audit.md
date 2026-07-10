# TS247 Audit - Triangle Spline Plancherel Evidence Assembly

## Scope

TS247 consumes the canonical sinc-fourth value proved in TS246 and assembles
the concrete triangle-spline Plancherel evidence required by TS204.

The ledger carries the evidence term itself, not a boolean or `True` marker.

## Main Declarations

- `triangleSplinePlancherelEvidence`
- `triangleSplinePlancherelIsometry`
- `triangleSplinePlancherelEnergyTransport`
- `triangleSplineSincL2EnergyValue`
- `TriangleSplinePlancherelEvidenceAssemblyLedger`
- `triangleSplinePlancherelEvidenceAssemblyTarget`

## What Is Proved

TS246 proves the canonical scalar input

```lean
TS209.Goldbach.CanonicalSincFourthIntegralValueStatement
```

TS209 transports this through the TS208 scalar spectral reduction and builds

```lean
TS204.Goldbach.TriangleSplinePlancherelInputEvidence
  TS204.Goldbach.triangleSplinePlancherelInputContract
```

TS247 instantiates that bridge and extracts the specialized isometry

```lean
TS174.Goldbach.TriangleSplinePlancherelIsometryStatement
```

as well as the exact spectral energy value

```text
triangleSplineSincL2Energy = ENNReal.ofReal (sqrt (2/3)).
```

## Non-Claims

TS247 proves the triangle-spline specialization needed by TS204.  It does not
prove a general Plancherel theorem for arbitrary functions.  It does not prove
the effective explicit formula input, Gallagher, or Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS247.TriangleSplinePlancherelEvidenceAssembly
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS247
git diff --check
```

## Expected Audit Result

The build succeeds.  The TS247 directory contains no placeholder proofs, no
forbidden declarations, and no non-ASCII characters.  `git diff --check`
reports no whitespace errors.
