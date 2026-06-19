# TS174 Audit - Triangle Spline Plancherel Interface Probe

## Sprint Scope

TS174 probes the L2/Plancherel interface after the TS173 pointwise Fourier
identification theorem.

This sprint names the concrete `eLpNorm` quantities for:

- the complexified triangle spline;
- Mathlib's Fourier integral of that spline;
- the pi-scale squared-sinc candidate from TS166.

It proves that TS173 transports the Fourier-side `eLpNorm` to the sinc-side
`eLpNorm`, and that any supplied concrete Plancherel isometry for the triangle
spline immediately yields equality between the squared-sinc L2 energy and the
time-side triangle-spline L2 energy.

## Main Declarations

- `TS174.Goldbach.triangleSplineTimeL2Energy`
- `TS174.Goldbach.triangleSplineFourierL2Energy`
- `TS174.Goldbach.triangleSplineSincL2Energy`
- `TS174.Goldbach.TriangleSplinePlancherelIsometryStatement`
- `TS174.Goldbach.triangleSplineFourierL2Energy_eq_sincL2Energy`
- `TS174.Goldbach.triangleSplineSincL2Energy_eq_timeL2Energy_of_plancherel`
- `TS174.Goldbach.TriangleSplinePlancherelInterfaceProbeLedger`
- `TS174.Goldbach.triangleSplinePlancherelInterfaceProbeLedger`
- `TS174.Goldbach.TriangleSplinePlancherelInterfaceProbeTarget`
- `TS174.Goldbach.triangleSplinePlancherelInterfaceProbeTarget`

## What Is Proved

TS174 proves the exact consumption bridge:

```lean
TS174.Goldbach.triangleSplineFourierL2Energy_eq_sincL2Energy
```

by applying `eLpNorm_congr_ae` to the pointwise Fourier identity from TS173.
It also proves:

```lean
TS174.Goldbach.triangleSplineSincL2Energy_eq_timeL2Energy_of_plancherel
```

which says that a future concrete Plancherel isometry for the triangle spline
is immediately consumable by the squared-sinc spectral side.

## Explicit Non-Claims

TS174 does not prove:

- the concrete Plancherel isometry;
- L2 finiteness of the squared-sinc candidate;
- the Riemann-von Mangoldt explicit formula;
- any Goldbach theorem.

## Verification

```powershell
lake build TS.Goldbach.Strong.TS174.TriangleSplinePlancherelInterfaceProbe
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS174
git diff --check
```

Expected result: build succeeds, no `s[o]rry`, no `a[x]iom`, no non-ASCII, and
no whitespace errors.

## Status

`repo_committed`
