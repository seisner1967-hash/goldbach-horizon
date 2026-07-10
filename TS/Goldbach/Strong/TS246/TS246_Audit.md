# TS246 Audit - Canonical Sinc-Fourth Assembly

## Scope

TS246 transports the TS245 cos-square value through the scaling and evenness
identities already proved in TS218.  It closes the canonical TS209 full-line
sinc-fourth scalar statement.

## Main Declarations

- `canonicalSincFourthIntegralValue`
- `CanonicalSincFourthAssemblyLedger`
- `canonicalSincFourthAssemblyLedger`
- `CanonicalSincFourthAssemblyTarget`
- `canonicalSincFourthAssemblyTarget`

## What Is Proved

TS245 proves

```text
cosSquareImproperIntegral = pi/6.
```

TS218 proves

```text
halfLineCanonicalSincFourthIntegral = 2 * cosSquareImproperIntegral
fullLineCanonicalSincFourthIntegral = 2 * halfLineCanonicalSincFourthIntegral.
```

The TS213 algebraic assembly therefore gives

```text
fullLineCanonicalSincFourthIntegral = 2*pi/3.
```

This is exactly

```lean
TS209.Goldbach.CanonicalSincFourthIntegralValueStatement
```

## Consequence Frontier

TS209 already proves that the canonical value supplies

```lean
TS204.Goldbach.TriangleSplinePlancherelInputEvidence
  TS204.Goldbach.triangleSplinePlancherelInputContract
```

TS246 records this implication but leaves the concrete evidence assembly to
the next sprint.

## Non-Claims

TS246 does not assemble the concrete TS204 Plancherel evidence.  It does not
prove the explicit formula input, Gallagher, or Goldbach.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS246.CanonicalSincFourthAssembly
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS246
git diff --check
```

## Expected Audit Result

The build succeeds.  The TS246 directory contains no placeholder proofs, no
forbidden declarations, and no non-ASCII characters.  `git diff --check`
reports no whitespace errors.
