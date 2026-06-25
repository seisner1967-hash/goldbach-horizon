# TS200 Audit - OTSA Non-Circular Consumption Interface

## Scope

TS200 prevents a circular final Goldbach interface.  TS199 named future OTSA
consumption slots, including a dashboard slot called
`conditional_goldbach_statement`.  That is useful for governance, but it should
not be consumed as an input to a final theorem.

TS200 defines a new non-circular interface where the inputs are only:

- trace constant bound;
- Mellin-tail bound;
- replacement sieve budget;
- final OTSA inequality;
- combinatorial reduction.

The binary Goldbach statement is defined separately as the output of a future
`OTSAConclusionBridge`.

## Main declarations

- `TS200.Goldbach.BinaryGoldbachStatement`
- `TS200.Goldbach.OTSAInputContracts`
- `TS200.Goldbach.OTSAInputEvidence`
- `TS200.Goldbach.OTSAConclusionBridge`
- `TS200.Goldbach.binaryGoldbach_of_otsaConclusionBridge`
- `TS200.Goldbach.OTSANonCircularConsumptionLedger`
- `TS200.Goldbach.otsaNonCircularConsumptionLedger`
- `TS200.Goldbach.OTSANonCircularConsumptionTarget`
- `TS200.Goldbach.otsaNonCircularConsumptionTarget`

## What is proved

TS200 proves only the routing theorem:

```lean
theorem binaryGoldbach_of_otsaConclusionBridge
    (contracts : OTSAInputContracts)
    (evidence : OTSAInputEvidence contracts)
    (bridge : OTSAConclusionBridge contracts) :
    BinaryGoldbachStatement
```

The proof simply applies `bridge.conclusion_from_inputs evidence`.  This is
intentional: it verifies the non-circular data flow, where Goldbach is the
output of the bridge and not a field in the input evidence.

## Non-claims

TS200 does not prove:

- any OTSA input contract;
- a trace constant bound;
- a Mellin-tail bound;
- a replacement sieve budget;
- the final OTSA inequality;
- the combinatorial reduction;
- Plancherel;
- the explicit formula;
- zeta-zero summability;
- circle-method or Gallagher correlation;
- Goldbach.

## Verification commands

```powershell
lake build TS.Goldbach.Strong.TS200.OTSANonCircularConsumptionInterface
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS200
git diff --check
git status --short
```
