# TS105 Audit - Mobius Delta Identity Discharge

## Status

`repo_committed`

TS105 proves the concrete Mobius-delta divisor-sum identity using the current
Mathlib arithmetic-function API located in TS104.

This sprint does not prove the full TS103 Mobius inversion infrastructure,
gcd/lcm kernel algebra, Selberg's sieve, Brun-Titchmarsh, or any prime-count
estimate.

## File

```text
TS/Goldbach/Strong/TS105/MobiusDeltaIdentityDischarge.lean
```

## Key declarations

```lean
TS105.Goldbach.mathlibMoebiusDivisorSum_eq_delta
TS105.Goldbach.mathlibArithmeticDelta_eq_ite
TS105.Goldbach.mathlibMoebiusDivisorSum_eq_ite
TS105.Goldbach.mobiusConcreteBinding_divisorSum_mobius_eq_delta
TS105.Goldbach.MobiusConcreteDeltaDischarge
TS105.Goldbach.mobiusConcreteDeltaDischarge
TS105.Goldbach.mobiusDeltaIdentity_of_concreteDeltaDischarge
TS105.Goldbach.MobiusConcreteDeltaDischargeTarget
TS105.Goldbach.mobiusConcreteDeltaDischargeTarget
TS105.Goldbach.mobiusDeltaIdentityTarget_of_concreteDeltaDischargeTarget
TS105.Goldbach.mobiusDeltaIdentityTarget
TS105.Goldbach.mobiusConcreteBindingTarget
```

## Proof summary

The theorem

```lean
TS105.Goldbach.mathlibMoebiusDivisorSum_eq_delta
```

evaluates Mathlib's bundled theorem

```lean
ArithmeticFunction.coe_moebius_mul_coe_zeta
```

at a natural number `n`, then rewrites the product with

```lean
ArithmeticFunction.coe_mul_zeta_apply
```

to identify the product `(moebius * zeta) n` with the finite divisor sum of
`moebius`. The right-hand side is Mathlib's arithmetic-function unit, exposed
by TS104 as `mathlibArithmeticDelta`.

## Build and audit commands

```powershell
lake build TS.Goldbach.Strong.TS105.MobiusDeltaIdentityDischarge
rg -n "s[o]rry" TS\Goldbach\Strong\TS105
rg -n "a[x]iom" TS\Goldbach\Strong\TS105
rg -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS105
git diff --check -- README.md TS\Goldbach\Strong\TS105\MobiusDeltaIdentityDischarge.lean TS\Goldbach\Strong\TS105\TS105_Audit.md
```

Expected result: build succeeds and all `rg` checks return no matches.

## Ledger

| Item | Declaration | Status | Meaning |
| --- | --- | --- | --- |
| TS105-D1 | `mathlibMoebiusDivisorSum_eq_delta` | `repo_committed` | proves the Mathlib Mobius divisor sum equals the arithmetic delta |
| TS105-D2 | `mathlibMoebiusDivisorSum_eq_ite` | `repo_committed` | exposes the same identity as `if n = 1 then 1 else 0` |
| TS105-D3 | `mobiusConcreteBinding_divisorSum_mobius_eq_delta` | `repo_committed` | transports the identity to the concrete TS104 binding |
| TS105-T1 | `MobiusConcreteDeltaDischargeTarget` | `repo_committed` | packages the proved concrete delta identity |
| TS105-T2 | `mobiusDeltaIdentityTarget` | `repo_committed` | supplies the TS103 Mobius-delta target |

## Remaining work

TS105 closes the Mobius-delta divisor-sum bridge only. The remaining
arithmetic front still needs the gcd/lcm kernel algebra, quadratic-kernel
extraction, Selberg interval majorant, Selberg sieve bound, and budget
comparison that feed Brun-Titchmarsh.
