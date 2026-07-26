# TS305 Audit: Fixed Left Boundary Convergence and Closed Residual

## Scope

TS305 separates the fixed left Perron boundary from the horizontal sides.
The left integral does not tend to zero as the height grows. It converges to
a genuine improper integral, and only the symmetric truncation residual tends
to zero.

The module is fail-closed. The locked Mathlib revision has no complex digamma
or Stirling estimate strong enough to prove the required logarithmic Gamma
rate. That rate is exposed by `FixedLeftArchimedeanBoundData`; it is not hidden
in a generic zeta bound or asserted as proved.

## Unconditional results

### Fixed geometry and kernel

- `fixedLeftPoint t` is the line `re(s) = -3/2`.
- `fixedLeftReflectedPoint t = 1 - fixedLeftPoint t` has real part `5/2`.
- Neither `s` nor `s + 1` vanishes on the fixed left line.
- `triangleSplineMellinKernel_fixedLeft_norm_le` proves
  `norm(kernel(s)) <= 2 / (1 + t^2)`.
- `nat_cpow_fixedLeftPoint_norm` identifies the arithmetic scale exactly as
  `x^(-3/2)`.

### Functional-equation reduction

- `zetaLeftReflectionFactor` is the explicit factor in Mathlib's
  `riemannZeta_one_sub` identity.
- Its differentiability and nonvanishing at the reflected points are proved.
- `fixedLeftReflectedVonMangoldtMass` is finite by absolute convergence of the
  von Mangoldt L-series on `re(s) = 5/2`.
- `neg_riemannZeta_logDerivative_fixedLeft_eq_reflection_sub_LSeries` proves
  the exact identity

  ```text
  -zeta'(s)/zeta(s)
    = reflectionCorrection(1-s) - L_vonMangoldt(1-s).
  ```

Thus the zeta part on the reflected right line is closed. The only remaining
analytic input is the logarithmic rate of the explicit archimedean factor.

### Integrability and limit

- `fixedLeftLogKernel_integrable` proves integrability of
  `(1 + log(abs(t)+2)) / (1+t^2)` by domination with an integrable Japanese
  bracket of exponent `-3/2`.
- `FixedLeftArchimedeanBoundData.toLogDerivativeBoundData` adds the fixed
  Dirichlet mass to the archimedean constant and yields the complete left-line
  logarithmic derivative bound.
- `fixedLeftIntegrand_integrable` proves absolute integrability of the Perron
  integrand for every positive arithmetic scale.
- `fixedLeftBoundaryLimit` is the full upward-oriented vertical integral.
- `fixedLeftBoundaryTruncation_tendsto` proves convergence of symmetric finite
  truncations to that limit.
- `fixedLeftBoundaryResidual_strongHeight_tendsto_zero_of_archimedean` proves
  convergence of the residual along the strong heights.

### Routing

- `fixedLeftBoundaryLimit_norm_le` gives a height-independent
  `O(x^(-3/2))` bound.
- `fixedLeftBoundaryTruncation_norm_le` gives the same bound for every
  nonnegative finite height.
- `perronLeftForwardIntegral_eq_fixedLeftBoundaryTruncation` checks the TS293
  orientation and parameterization exactly.
- `fixedLeftSideBoundData_of_archimedean` populates the TS298 left-side
  interface from the sole archimedean input.

## Open analytic statement

The following statement is not proved in TS305:

```text
norm(reflectionCorrection(5/2-it))
  <= C_arch * (1 + log(abs(t)+2)).
```

It requires a targeted logarithmic estimate for the complex Gamma factor.
The weaker linear completion estimate from TS304 is insufficient here because
it would leave a non-integrable `1/abs(t)` majorant after multiplication by the
quadratic Mellin kernel.

The sharp explicit truncation rate `O((log(T)+1)/T)` is also not claimed.
TS305 proves convergence through absolute integrability.

## Non-claims

TS305 does not prove:

- the archimedean logarithmic rate above;
- that the fixed left limit is zero;
- the exceptional residue inventory at `s = 0` and `s = -1`;
- Perron inversion;
- the meromorphic rectangle residue theorem;
- an infinite explicit formula;
- Gallagher, OTSA, or Goldbach.

## Dependency hygiene

The proof uses only finite functional-equation algebra, absolute convergence on
`re(s) = 5/2`, elementary fixed-line geometry, and standard Bochner integral
convergence. It introduces no Hadamard product, zero-density hypothesis, RH,
`sorry`, `axiom`, or `opaque` declaration.
