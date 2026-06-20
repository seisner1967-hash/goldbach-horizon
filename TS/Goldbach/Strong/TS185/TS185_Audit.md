# TS185 Audit - Explicit Formula Zeta Zero Family Ledger

## Scope

TS185 opens the right-hand zero-family vocabulary for the explicit-formula
front after TS184 made the finite von Mangoldt side concrete.

The new Lean file is:

```text
TS/Goldbach/Strong/TS185/ExplicitFormulaZetaZeroFamilyLedger.lean
```

## Mathlib API identified

TS185 imports:

```lean
import Mathlib.NumberTheory.LSeries.RiemannZeta
```

The probe stabilizes these symbols:

```text
riemannZeta
riemannZeta_neg_two_mul_nat_add_one
RiemannHypothesis
```

Only `riemannZeta` and the trivial-zero theorem are consumed.  The Mathlib
`RiemannHypothesis` proposition is recorded as an available symbol but is not
used as an assumption.

## Proved content

TS185 defines:

```lean
mathlibRiemannZetaFunction
riemannZetaZeroPredicate
criticalStripPredicate
nontrivialRiemannZetaZeroPredicate
RiemannZetaZeroFamilyAPIBindingContract
zetaZeroFamilyLedger_of_apiContract
```

It proves:

```lean
riemannZetaZeroPredicate_trivial_neg_two_mul_nat_add_one
zetaZeroFamilyLedgerTarget_of_apiContract
zetaZeroFamilyTarget_of_apiContract
explicitFormulaZetaZeroFamilyTarget
```

The key bridge is conditional and local: a future
`RiemannZetaZeroFamilyAPIBindingContract` supplies the existing TS93
`ZetaZeroFamilyLedger`, and therefore the TS92 zero-family target.  TS185 does
not populate that contract.

## Non-claims

TS185 does not prove:

```text
construction of all zeta zeros
zeta-zero summability
the explicit formula
the Riemann hypothesis
Plancherel
Goldbach
```

## Verification protocol

Run:

```powershell
lake env lean TS\Goldbach\Strong\TS185\ExplicitFormulaZetaZeroFamilyLedger.lean
lake build TS.Goldbach.Strong.TS185.ExplicitFormulaZetaZeroFamilyLedger
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS185
git diff --check
git status --short
```

Expected result:

```text
Lean file compiles
Lake target builds
No forbidden proof placeholders
No global assumption declarations
No non-ASCII characters in TS185
No whitespace errors
```

## Verdict

TS185 builds the typed zero-family API bridge needed by TS181/TS95 while
leaving every analytic theorem about nontrivial zeta zeros as a local future
contract.
