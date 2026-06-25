# TS205 Audit - Final Analytic Inputs to OTSA Routing Bridge

## Scope

TS205 connects the TS204 final analytic input specification to the TS200
non-circular OTSA interface.  It defines an adapter type saying that final
triangle-spline analytic evidence can populate a chosen package of five TS200
OTSA input contracts.

The sprint is deliberately conditional.  It does not create analytic evidence,
does not prove any OTSA input, and does not create an unconditional Goldbach
ledger.

## Main Declarations

- `TS205.Goldbach.FinalAnalyticToOTSAInputBridge`
- `TS205.Goldbach.otsaInputEvidence_of_finalAnalyticEvidence`
- `TS205.Goldbach.binaryGoldbach_of_finalAnalyticBridge`
- `TS205.Goldbach.FinalAnalyticToOTSARoutingBridgeLedger`
- `TS205.Goldbach.finalAnalyticToOTSARoutingBridgeLedger`
- `TS205.Goldbach.FinalAnalyticToOTSARoutingBridgeTarget`
- `TS205.Goldbach.finalAnalyticToOTSARoutingBridgeTarget`

## What TS205 Proves

TS205 proves a routing theorem:

```lean
binaryGoldbach_of_finalAnalyticBridge
```

The theorem says that if:

- final analytic evidence for a TS204 contract bundle is supplied;
- a bridge turns that evidence into the five TS200 OTSA input slots;
- a TS200 `OTSAConclusionBridge` is supplied;

then `TS200.Goldbach.BinaryGoldbachStatement` follows by the TS200 interface.

## Non-Claims

TS205 does not prove:

- Plancherel;
- the effective explicit formula;
- zero-contribution bounds;
- residual bounds;
- Gallagher or large-sieve comparison;
- any TS200 OTSA input;
- the TS200 conclusion bridge;
- Goldbach.

TS205 also does not store a field of type
`TS200.Goldbach.BinaryGoldbachStatement` in its concrete ledger.  The Goldbach
statement remains conditional on supplied evidence and a supplied conclusion
bridge.

## Verification Commands

```powershell
lake build TS.Goldbach.Strong.TS205.FinalAnalyticInputsToOTSARoutingBridge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS205
git diff --check
git status --short
```
