# TS310 Audit - Scalar Mellin-Perron Inversion

## Scope

TS310 closes Mellin-Perron inversion for the triangle-spline kernel and routes
it into the finite rectangle residue identity of TS309. The implementation is
split into:

- `ScalarMellinInversion.lean`: scalar kernel inversion by finite rectangles;
- `ScalarMellinPerronInversion.lean`: von Mangoldt Tonelli exchange, arithmetic
  identification, Perron inversion, and the truncated explicit identity.

## Proved results

### Scalar kernel

For `0 < y` and `1 < c`, TS310 proves

```text
integral_R y^(c+it) / ((c+it)(c+1+it)) dt
  = 2*pi*(1-y^(-1))  if 1 < y,
  = 0                 if 0 < y <= 1.
```

The proof uses finite rectangles. For `y > 1` it closes to the left and uses
the residues `1` at `0` and `-y^(-1)` at `-1`. For `0 < y < 1` it closes to
the right and crosses no pole. The case `y = 1` keeps the quadratic kernel
intact and is proved from an absolutely integrable `1/(t^2+r^2)` majorant.

### Tonelli exchange

On `re(s) = c > 1`, each von Mangoldt term is dominated by

```text
norm(LSeries.term vM c n) * x^c / (1+t^2).
```

The L-series norm sequence is summable and the Cauchy kernel is integrable.
`integral_tsum_of_summable_integral_norm` therefore gives the exact exchange
between the natural-number `tsum` and the full real-line integral.

### Arithmetic identification

The `n = 0` term is isolated before forming `x/n`. For `n > 0`, the scalar
kernel is evaluated at `y = x/n`, giving

```text
vonMangoldt(n) * (1 - n/x)  if n < x,
0                           otherwise.
```

The resulting `tsum` is reduced exactly to `Finset.range x` and identified
with `TS184.triangleSplineMathlibVonMangoldtWeightedSum`.

### Final contracts

The following outputs are unconditional:

```text
triangleSplinePerronInversion
triangleSplinePerronInversionStatement
canonical_truncatedPerronExplicitIdentity_complex
canonical_truncatedPerronExplicitIdentity
```

In particular, `TriangleSplinePerronInversionStatement` from TS293 is inhabited,
and its combination with
`TS309.canonical_triangleSplineRectangleResidueStatement` yields the canonical
finite-height explicit identity.

## Fail-closed boundary

TS310 does not prove:

- convergence of the complete contour residual as the height tends to infinity;
- the infinite explicit formula;
- Gallagher's estimate;
- the OTSA bridge;
- Goldbach.

The left vertical boundary has a generally nonzero limiting contribution, so a
future infinite-height assembly must retain that limit rather than silently
discarding it.

## Integrity checks

- no `sorry`, `axiom`, `opaque`, or `admit` is introduced;
- no Riemann Hypothesis or zero-density hypothesis is used;
- no general Mellin or Fourier inversion theorem is imported;
- no circular use of Perron inversion occurs in the scalar proof.

## Build verification

- targeted: `lake build TS.Goldbach.Strong.TS310.ScalarMellinPerronInversion`
  completed at `3031/3031`;
- global: `lake build` completed at `2664/2664`;
- source scan over the TS310 Lean files found no unchecked placeholder.
