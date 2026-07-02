# TS213 Audit - Canonical Sinc-Fourth Direct Dirichlet Route

## Scope

TS213 records the direct non-Plancherel route to the canonical scalar identity
isolated by TS209:

```lean
TS209.Goldbach.CanonicalSincFourthIntegralValueStatement
```

The sprint defines the scalar objects needed by the classical Dirichlet/IPP
proof:

- `cosSquareRemainder x = (1 - cos x)^2`
- the positive-half-line kernel `(1 - cos x)^2 / x^4`
- the Dirichlet sine kernel `sin (a*x) / x`
- the expected third-derivative kernel
  `(-2 * sin x + 4 * sin (2*x)) / x`
- the half-line and full-line canonical `sinc^4` integrals

It then states the concrete future obligations:

- the third-derivative formula for `(1 - cos x)^2`;
- the Dirichlet sine integral on the positive half-line;
- the improper triple integration-by-parts identity;
- the scaling identity from `x = 2*u`;
- the evenness identity reducing the full-line integral to the half-line.

## Main Declarations

- `TS213.Goldbach.cosSquareRemainder`
- `TS213.Goldbach.cosSquareHaarKernel`
- `TS213.Goldbach.sineDirichletKernel`
- `TS213.Goldbach.cosSquareThirdDerivativeKernel`
- `TS213.Goldbach.CanonicalSincFourthDirectDirichletRouteEvidence`
- `TS213.Goldbach.canonicalSincFourthIntegral_of_cosSquareValue_scaling_evenness`
- `TS213.Goldbach.canonicalSincFourthIntegral_of_directDirichletRoute`
- `TS213.Goldbach.triangleSplinePlancherelEvidence_of_directDirichletRoute`
- `TS213.Goldbach.CanonicalSincFourthDirectDirichletRouteLedger`
- `TS213.Goldbach.canonicalSincFourthDirectDirichletRouteLedger`
- `TS213.Goldbach.CanonicalSincFourthDirectDirichletRouteLedgerTarget`
- `TS213.Goldbach.canonicalSincFourthDirectDirichletRouteLedgerTarget`

## What TS213 Proves

TS213 proves the routing theorem:

```lean
CanonicalSincFourthDirectDirichletRouteEvidence ->
  TS209.Goldbach.CanonicalSincFourthIntegralValueStatement
```

and then routes the same evidence through TS209 and TS208 to obtain:

```lean
TS204.Goldbach.TriangleSplinePlancherelInputEvidence
  TS204.Goldbach.triangleSplinePlancherelInputContract
```

The only numerical assembly performed in TS213 is the scalar algebra:

```text
cos-square integral = pi / 6
half-line sinc^4   = 2 * cos-square integral
full-line sinc^4   = 2 * half-line sinc^4
------------------------------------------------
full-line sinc^4   = 2 * pi / 3
```

## Non-Claims

TS213 does not prove:

- the Dirichlet sine integral;
- the improper triple integration-by-parts identity;
- the scaling identity from `x = 2*u`;
- the evenness identity;
- the canonical `sinc^4` value unconditionally;
- Plancherel or Parseval;
- the explicit formula;
- Gallagher or large-sieve comparison;
- Goldbach.

## Verification Commands

```powershell
lake env lean TS\Goldbach\Strong\TS213\CanonicalSincFourthDirectDirichletRoute.lean
lake build TS.Goldbach.Strong.TS213.CanonicalSincFourthDirectDirichletRoute
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS213
git diff --check
git status --short
```
