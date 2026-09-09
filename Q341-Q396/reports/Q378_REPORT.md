# Q378 / RS6H - Local circle-to-line germ

Date: 2026-08-24  
Verdict: `RS6H_ANALYTIC_PARTIAL_FAIL_CLOSED`

## Proven in Lean

The local contour geometry was normalized by an explicit Cayley map. Lean proves:

- the nested transformed Cauchy circle lies strictly inside the final source line;
- both poles are inside the explicit inner Cayley circle;
- the principal logarithm cut is avoided throughout the closed annulus;
- the Cayley pullback extends continuously at the compactified point at infinity;
- it is holomorphic on the open annulus;
- Cauchy's annulus theorem identifies the outer unit-circle integral with the inner concentric-circle integral.

The outer reparametrization is closed completely. The exact Cayley coordinate is strictly increasing, tends to `-infinity` at `0+` and to `+infinity` at `(2*pi)-`, and the transformed line integrand is integrable. Consequently:

```lean
Q378Probe.sourceCayley_complete_outer_transport
```

constructs an unconditional `SourceCayleyOuterParameterTransport`.

For the inner boundary, Lean now proves that the actual Q377 path is the explicit Blaschke map

```text
-i*q*(v+i*q)/(1-i*q*v),  q = 2-sqrt(3),  |v|=1,
```

that its denominator never vanishes, and that its angular derivative has the form

```text
i * omega(theta) * path(theta),  omega(theta) > 0.
```

In particular the actual inner Cayley path is regular and positively oriented.

## Exact open leaf

The remaining obligation is the global one-period reparametrization theorem for this positive Blaschke path: construct a real angular lift whose total increment is exactly `2*pi`, then apply interval substitution to identify the induced path integral with the canonical inner `circleIntegral`.

This is strictly stronger than the already proved set equality and pointwise positive orientation. No uninhabited transport witness was introduced.

Therefore the following remain unproved:

```text
Q378_INNER_CIRCLE_PARAMETER_TRANSPORT : NOT_OBTAINED
Q378_LOCAL_CIRCLE_LINE_GERM           : NOT_OBTAINED
SourcePrimaryRemainderOnFinalLine      : OPEN
Q374_SOURCE_RSFORMULA                  : OPEN
BRIDGE_A                               : OPEN
```

## Trust and governance

- Aggregate build: `2356/2356 PASS`.
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- Forbidden scan: empty.
- `HEAD = origin/main = 433e29e`.
- No branch, commit, push, PR, merge or tag.
- Development frozen before the four-hour deadline.

