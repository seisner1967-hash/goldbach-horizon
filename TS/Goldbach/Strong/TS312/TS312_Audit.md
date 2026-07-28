# TS312 Audit: Post-Wall-2 Effective Formula Contract Discharge

## Scope

TS312 is an interface-only consolidation sprint.  It imports the analytic
results proved in TS292 and TS311 and records them in the six-field TS204
effective explicit-formula contract.  It introduces no new contour estimate,
zero-counting argument, residue calculation, or special-value evaluation.

Main file:

```text
TS/Goldbach/Strong/TS312/PostWall2EffectiveFormulaContractDischarge.lean
```

## Main declarations

```lean
TS312.Goldbach.TS181TraceBudgetAdapterData
TS312.Goldbach.TS181TraceBudgetAdapterData.toTS181Contracts
TS312.Goldbach.explicitFormulaTraceBridgeTarget_of_adapter

TS312.Goldbach.postWall2ExplicitFormulaEffectiveInputContract
TS312.Goldbach.postWall2ExplicitFormulaEffectiveInputEvidence
TS312.Goldbach.PostWall2EffectiveFormulaContractDischargeTarget
TS312.Goldbach.postWall2EffectiveFormulaContractDischargeTarget

TS312.Goldbach.PostWall2EffectiveFormulaStatus
TS312.Goldbach.postWall2EffectiveFormulaStatus
TS312.Goldbach.TS312Ledger
TS312.Goldbach.ts312Ledger
```

## TS204 discharge

The TS204 interface is parametric: its six fields are propositions rather
than a preselected analytic formula.  TS312 instantiates them as follows.

| TS204 field | Concrete TS312 content |
| --- | --- |
| `explicit_formula_identity_statement` | TS311 developed complex and real infinite identities |
| `main_term_identification_statement` | `triangleSplinePerronMainTerm x = x / 2` |
| `zero_contribution_bound_statement` | TS292 absolute norm summability and effective tail |
| `residual_bound_statement` | TS311 componentwise contour residual bound |
| `effective_constants_statement` | nonnegative spectral tail constant and tail rate tending to zero |
| `compatibility_with_ts181_blueprint_statement` | conditional TS181 adapter theorem |

The resulting evidence object inhabits every field with a concrete theorem:

```lean
postWall2ExplicitFormulaEffectiveInputEvidence :
  TS204.Goldbach.TriangleSplineExplicitFormulaEffectiveInputEvidence
    postWall2ExplicitFormulaEffectiveInputContract
```

Therefore Wall 2 is visible through the high-level TS204 interface, not only
through the local TS311 theorem names.

## Spectral summability status

The new post-Wall-2 status records the complete norm-summability theorem

```lean
TS292.Goldbach.infiniteZeroSpectralTerm_norm_summable
```

and the closed tail estimate

```text
norm (Z_infinite(x) - Z_T(x))
  <= max(1,x) * C_tail * logarithmicTailRate(T).
```

The tail constant is nonnegative and the rate tends to zero.  This closes the
spectral summability component without reopening the TS290 counting argument.

## Exact TS181 boundary

TS181 requires data that do not follow from the complex explicit identity:

* a TS93 zero-family ledger;
* nonnegative rational TS95 zero and residual contributions;
* a positive rational trace budget;
* a proof that the budget is at most `1 / 2`;
* a comparison of the rational total with that budget.

`TS181TraceBudgetAdapterData` names exactly these missing inputs.  TS312 proves

```lean
TS181TraceBudgetAdapterData ->
  TS95.Goldbach.ExplicitFormulaTraceBridgeTarget
```

by routing the data through the existing TS181 theorem.  TS312 does not prove
that `TS181TraceBudgetAdapterData` is inhabited.  Consequently neither the
rational packaging nor the half-budget is claimed.

## Strategic dashboard discipline

TS199 is imported but not edited.  Its ledger remains the historical state
explicitly documented as "after TS198".  `PostWall2EffectiveFormulaStatus`
embeds that value and records the later TS292/TS311 evidence separately.

Current status:

| Front | Status after TS312 |
| --- | --- |
| Wall 2 effective explicit formula | closed |
| Wall 3 spectral summability and tail | closed |
| TS181 rational trace packaging | open |
| TS181 trace budget at most one half | open |
| Gallagher / Wall 4 | open |
| OTSA | not proved |
| Goldbach | not claimed |

## Claim boundary

TS312 does not prove:

* a rational encoding of the TS311 complex terms;
* the TS181 trace budget bound;
* a Gallagher variance estimate;
* OTSA;
* Goldbach;
* a closed form for `riemannZeta` logarithmic derivatives at `0` or `-1`.

## Verification commands

```powershell
lake env lean TS\Goldbach\Strong\TS312\PostWall2EffectiveFormulaContractDischarge.lean
lake build TS.Goldbach.Strong.TS312.PostWall2EffectiveFormulaContractDischarge
lake build
rg -n "s[o]rry|a[x]iom|o[p]aque|a[d]mit|[^\x00-\x7F]" TS\Goldbach\Strong\TS312
git diff --check
git status --short
```

Verified build results:

```text
Targeted build: 3033/3033
Global build:   2664/2664
```

The module is intended to preserve strict ASCII and to contain no `s[o]rry`,
`a[x]iom`, `o[p]aque`, or `a[d]mit` declaration.
