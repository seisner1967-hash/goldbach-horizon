# TS278 Audit - Holomorphic Primitive on a Ball Backport

## Scope

TS278 backports the open-ball primitive theorem that is absent from the
locked Mathlib revision.  It specializes the later Mathlib construction to
complex-valued functions, which is exactly the form needed for the future
logarithmic derivative `g' / g` route from TS277.

The primitive is defined by an axis-parallel wedge integral from the center
of the ball.  The proof uses only APIs available in the locked revision:
interval-integral differentiation, continuity on a ball, convexity, and
Cauchy-Goursat on rectangles.

## Proof route

1. Define the horizontal-then-vertical wedge integral.
2. Prove its sum with the reverse wedge is the boundary integral of the
   associated rectangle.
3. Deduce rectangle conservativity from complex differentiability and the
   locked Cauchy-Goursat theorem.
4. Prove the horizontal and vertical segments used locally remain in the
   open ball.
5. Show conservativity identifies a nearby difference of center-based wedge
   integrals with the local wedge from the evaluation point.
6. Differentiate the horizontal interval integral up to a little-o error.
7. Bound the vertical interval-integral error by continuity and the imaginary
   coordinate estimate.
8. Combine both errors to prove that the wedge integral has derivative `f`.
9. Package the resulting primitive for every complex-differentiable function
   on an open ball.

## Main result

```text
HolomorphicPrimitiveOnBallStatement:
  every f : Complex -> Complex differentiable on ball c r
  has a primitive on ball c r.
```

The concrete theorem is:

```text
differentiableOn_holomorphicExactOn_ball
```

## Boundary of the sprint

TS278 proves the primitive only on an open ball.  TS277 requires an analytic
logarithm on a closed buffered disk.  A later sprint must use compactness and
the local analytic and nonvanishing neighborhoods of the quotient to obtain
a slightly larger open ball, apply TS278 to `g' / g`, and normalize and
exponentiate the resulting primitive.

## Non-claims

- no uniform extension beyond a closed analytic ball is proved
- no primitive of a concrete logarithmic derivative is constructed
- no buffered TS277 holomorphic logarithm is constructed
- no complete Jensen theorem or concrete Riemann xi function is supplied
- no effective zeta zero-counting estimate is proved
- no explicit-formula identity, Gallagher estimate, or OTSA bridge is proved
- Goldbach is not claimed

## Verification

```powershell
lake build TS.Goldbach.Strong.TS278.HolomorphicPrimitiveOnBallBackport
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS278
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS278
git diff --check
```
