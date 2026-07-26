# TS306 Audit: Exceptional Residue Inventory

## Scope

TS306 constructs the concrete exceptional residue inventory for the TS293
triangle-spline Perron integrand. The inventory contains exactly the two
Mellin-kernel poles `s = 0` and `s = -1`. The pole `s = 1` remains outside this
Finset because TS293 already records it separately as the main term `x / 2`.

The module certifies the listed local principal parts. It does not claim that
these certificates alone prove a global meromorphic residue theorem or an
exhaustive singularity classification.

## Generic local construction

`localSimplePoleData_of_analytic` packages an analytic numerator `H` into a
`TS293.PerronLocalResidueData` for `H(z)/(z-p)`.

The regular part is the divided difference `dslope H p`. Analyticity follows
from the shifted power series of `H`, and on the punctured neighborhood the
identity

```text
H(z)/(z-p) = H(p)/(z-p) + dslope H p z
```

is proved exactly. No global residue API is used.

## Local analytic data

The module defines

```text
negZetaLogDerivative(z) = -zeta'(z)/zeta(z).
```

It proves this function analytic at `0` and `-1` from:

- analyticity of zeta away from `1`;
- `zeta(0) = -1/2`;
- `zeta(-1) = -1/12`, evaluated through Mathlib's Bernoulli formula.

For positive `x`, complex exponentiation `x^z` is entire. Therefore the two
analytic numerators are:

```text
H0(z)  = (-zeta'(z)/zeta(z)) * x^z / (z+1)
Hm1(z) = (-zeta'(z)/zeta(z)) * x^z / z.
```

The Perron integrand is rewritten exactly as `H0(z)/z` and
`Hm1(z)/(z+1)` respectively.

## Certified residues

`zeroPerronLocalResidueData` certifies

```text
Res(Fx, 0) = -zeta'(0)/zeta(0).
```

`negOnePerronLocalResidueData` certifies

```text
Res(Fx, -1) = x^(-1) * zeta'(-1)/zeta(-1).
```

The second constant is already concrete. No external contract for the value
of `zeta'(-1)/zeta(-1)` is introduced. The optional classical simplification
`-zeta'(0)/zeta(0) = -log(2*pi)` is not proved in the locked API and is not
needed for the inventory.

## Exact inventory and main-term separation

`perronExceptionalPoles` is definitionally `{0, -1}`.

`concreteExceptionalResidueInventory` proves both points lie in every
admissible `TS293.PerronRectangle`, using only its fields
`left < -1 < 1 < right` and `0 < tau`.

`MainTermSeparatedExceptionalInventory` records:

- the exact exceptional Finset;
- `(1 : Complex)` is not a member.

This prevents the main pole from being silently added to the exceptional
contribution. TS293 continues to supply `x / 2` separately.

## Exact contribution and routing

`concreteExceptionalResidueContribution_eq_inv` proves

```text
exceptionalContribution(x)
  = -zeta'(0)/zeta(0)
    + x^(-1) * zeta'(-1)/zeta(-1).
```

`concreteExceptionalResidueBound` is the sum of the norms of these two
terms. `concreteExceptionalResidueBoundData` populates the TS298 exceptional
residue bound interface for the canonical strong-height rectangle. The bound
is independent of the contour height.

## Open classification statement

`ExceptionalInventoryCompletenessStatement` names the remaining global
classification obligation: inside the rectangle, after excluding the main
pole and zeta zeros, every non-analytic point of the Perron integrand belongs
to the exceptional Finset.

This statement is deliberately not used to build the local inventory. It
belongs with the later meromorphic rectangle theorem.

## Non-claims

TS306 does not prove:

- `-zeta'(0)/zeta(0) = -log(2*pi)`;
- exhaustive classification of all singularities in the rectangle;
- the logarithmic archimedean input still exposed by TS305;
- Perron inversion;
- the meromorphic rectangle residue theorem;
- an infinite explicit formula;
- Gallagher, OTSA, or Goldbach.

## Hygiene

The module is finite and local. It introduces no Hadamard product, RH,
zero-density assumption, `sorry`, `axiom`, `opaque`, or `admit` declaration.
