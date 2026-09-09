# RS3H-II Final Report

## Classification

```text
RS3H2_ANALYTIC_PARTIAL_FAIL_CLOSED
ORIGINAL_TIMEBOX_CLOSEOUT : INCOMPLETE / DEADLINE_EXPIRED
POST_DEADLINE_CONTINUATION: TECHNICAL_VERIFICATION_ONLY
```

RS3H-II substantially closes the elementary geometry, branch, integrability,
finite-rectangle, and denominator-coercivity infrastructure required by the
primary-source Riemann-Siegel remainder. It does not prove `RSformula`, the Arias
remainder estimate, or any theorem about a production endpoint.

## Timebox

```text
T0              : 2026-08-20T18:38:16.9326729+02:00
RESEARCH_FREEZE : 2026-08-20T21:28:16.9326729+02:00
DEADLINE        : 2026-08-20T21:38:16.9326729+02:00
POST-DEADLINE CONTINUATION : 2026-08-22, explicitly requested by user
```

The last theorem completed after the interruption is separately labeled in
Q370_REPORT.md. No post-deadline work changes the original timebox verdict.

## Technical achievements

### Q369

- exact affine geometry and injectivity of both source contours;
- exact central/lower/upper `gamma` regimes and pole avoidance;
- principal-log branch avoidance and denominator nonvanishing;
- absolute integrability of the true inner `Rg_(K+1)` integrand for all `K`;
- exact double-kernel/measurability spine;
- product-majorant and Fubini theorems with explicit semantic premises;
- Cauchy on truncated rectangles;
- targeted affine parallel-line deformation from explicit side decay.

### Q370

- exact combined source exponent and Gaussian reduction;
- residual and Cauchy-prefactor factorization;
- integrable polynomial-Gaussian outer majorant and rational inner majorant;
- uniform positive lower bound for the outer cosine denominator (post-deadline);
- isolation of `SourceFRealGap` as the remaining deep harmonic leaf.

## Exact frontier

```text
Q369_SOURCE_RSFORMULA                    : OPEN
Q369_AUXILIARY_TO_ZETA                  : OPEN
Q369_CRITICAL_PHASE_TRANSPORT           : OPEN
Q369_NORMALIZED_HARDY_Z_DECOMPOSITION   : OPEN
Q370_SOURCE_F_REAL_GAP                   : OPEN
Q370_ARIAS_RAW_REMAINDER_BOUND          : OPEN
Q370_EXPLICIT_ARIAS_BOUND               : OPEN
Q371_CANONICAL_RS_ENDPOINT              : NOT_ATTEMPTED (gated)
Q372_FIRST_RS_RS_PRODUCTION_BRACKET     : NOT_ATTEMPTED (gated)
BRIDGE_A                                : OPEN
CARRIER_MEMBERSHIP                      : UNPROVED
TS340_UNCONDITIONAL                     : OPEN_FROZEN
```

## Trust audit

Representative terminal theorems and definitions depend only on:

```text
propext
Classical.choice
Quot.sound
```

The forbidden-token scan over Q369/Q370 is empty. Arb/FLINT values are not used
as proof. No remainder is defined by subtraction and no Q358 sign theorem is
imported to establish Riemann-Siegel.

## Git

```text
HEAD        : 433e29eff1d9da2bc5937bb82bf5df3a2d59c08f
origin/main : 433e29eff1d9da2bc5937bb82bf5df3a2d59c08f
branch      : detached
commit/push/PR/merge/tag : none
```
