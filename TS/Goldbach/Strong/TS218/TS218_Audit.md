# TS218 Audit - Sinc-Fourth Scaling and Evenness Discharge

## Scope

TS218 discharges the two elementary TS213 scalar obligations that are
independent of the Dirichlet value and the improper triple integration by
parts:

- the half-line scaling identity from the substitution `x = 2*u`;
- the full-line evenness identity for the canonical `sinc^4` kernel.

The scaling proof combines the pointwise identity
`canonicalSincFourthKernel u = 4 * cosSquareHaarKernel (2*u)` on `0 < u`
with Mathlib's `integral_comp_mul_left_Ioi` change of variables.  The evenness
proof derives global integrability of the canonical kernel from TS178 and the
TS209 pi-scaling relation, then splits the full-line integral and maps the
non-positive half by `x -> -x`.

## Main Declarations

- `TS218.Goldbach.canonicalSincFourthKernel_even`
- `TS218.Goldbach.one_sub_cos_two_mul_eq_two_sin_sq`
- `TS218.Goldbach.canonicalSincFourthKernel_scaling_pointwise`
- `TS218.Goldbach.halfLineSincFourthScaling`
- `TS218.Goldbach.canonicalSincFourthKernel_integrable`
- `TS218.Goldbach.fullLineSincFourthEvenness`
- `TS218.Goldbach.SincFourthScalingEvennessDischargeLedger`
- `TS218.Goldbach.sincFourthScalingEvennessDischargeLedger`
- `TS218.Goldbach.SincFourthScalingEvennessDischargeTarget`
- `TS218.Goldbach.sincFourthScalingEvennessDischargeTarget`

## What TS218 Proves

TS218 proves the two TS213 statements:

```lean
TS213.Goldbach.HalfLineSincFourthScalingStatement
TS213.Goldbach.FullLineSincFourthEvennessStatement
```

It also proves the supporting integrability theorem:

```lean
Integrable
  TS213.Goldbach.canonicalSincFourthKernel
  (volume : Measure Real)
```

This integrability is recovered from TS178's pi-scaled spectral integrability
through the TS209 scaling identity.

## Non-Claims

TS218 does not prove:

- the Dirichlet cutoff value;
- the Dirichlet Abel value;
- the old TS213 Lebesgue Dirichlet statement;
- improper triple integration by parts;
- the canonical `sinc^4` value;
- TS204 Plancherel evidence;
- the explicit formula;
- Gallagher or any circle-method estimate;
- Goldbach.

## Verification Commands

```text
lake env lean TS\Goldbach\Strong\TS218\SincFourthScalingEvennessDischarge.lean
lake build TS.Goldbach.Strong.TS218.SincFourthScalingEvennessDischarge
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS218
git diff --check
git status --short
```
