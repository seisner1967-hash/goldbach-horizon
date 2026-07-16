# TS287 Audit - Riemann Xi Growth API Probe

## Scope

TS287 probes the locked Gamma and Riemann-zeta APIs and installs the first
explicit growth substitution point downstream of the TS286 master API.

The primary route uses the entire regularized function
`TS282.Goldbach.completedRiemannZetaZero`.  It deliberately does not request a
global bound for Gamma separated from zeta, because Gamma has poles on the
circles under consideration and the completed expression carries the needed
cancellations.

## Locked API findings

The module confirms and reexports:

* `Complex.differentiableAt_Gamma` away from the nonpositive integers;
* `Complex.Gamma_eq_integral` when the real part is positive;
* `zeta_eq_tsum_one_div_nat_cpow` only when `1 < re s`;
* the entire regularized completed-zeta function already bridged by TS282.

No directly consumable uniform complex Stirling inequality or critical-strip
zeta growth theorem is used.

## Proved elementary bounds

On `abs z = R` with `0 <= R`, TS287 proves:

```text
abs(z - 1) <= R + 1,
abs(z * (z - 1)) <= R * (R + 1).
```

For any supplied completed-zeta circle bound `abs LambdaZero(z) <= A(R)`, it
then proves the exact affine estimate:

```text
abs xi(z) <= max 1 ((R * (R + 1) * A(R) + 1) / 2).
```

## Jensen routing

The explicit xi majorant fills a genuine
`BoundaryNormOnAveragingSphereStatement` for the concrete TS285
factorization.  TS279 and TS274 then yield:

```text
xi_finiteJensenBoundaryEstimate_explicit
xi_zero_count_le_explicit_completedZeta_majorant
```

Thus no downstream Jensen proof must be revisited when a future sprint
constructs the function `A`.

## Non-claims

TS287 does not prove a complex Stirling bound, a critical-strip zeta bound,
effective completed-zeta growth, a concrete quantitative zero-counting
asymptotic, the explicit formula, Gallagher, an OTSA bridge, or Goldbach.

## Verification

Canonical build target:

```powershell
lake build TS.Goldbach.Strong.TS287.RiemannXiGrowthAPIProbe
```

Static checks:

```powershell
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS287
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS287
git diff --check
```

Expected result: the build succeeds and all scans print no matches.
