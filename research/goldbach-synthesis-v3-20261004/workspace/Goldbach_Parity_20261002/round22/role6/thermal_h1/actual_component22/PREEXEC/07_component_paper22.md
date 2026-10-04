# Component bank15.3 — sources to review, no execution

This is a new evaluator-component contract, not the thermalH1 identity bank.
N=100000000 is a context label. Neither the full arithmetic trace, the two
vertical integrals, Arch, nor the globalH1 residual is evaluated here.
Historical G0 and Gamma outputs are not inputs or numerical oracles.
The previous outward arithmetic source is acknowledged as READONLY ground
rule provenance; the new512-bit primitives, EM and Stirling routes are new
sources. No Python import, syntax probe, numerical invocation or Lean call
has been made while preparing them.

## Closed Gamma producer and independent phase reference

The fixed phase catalogue is sigma={1,3/2,2}, gamma={0,-3,3,-23,23}, all15
cases before filters. Producer Gamma uses w=s+64, the holomorphic right
half-plane Log(w),32 Stirling terms, and recurrence by all64 factors.
After including the32nd term, the log remainder is the negative periodic
B64 integral. Re w>=64+1/4, even on the1/16 derivative disk Re w>63;
the conservative bounds are4/(63*6^64) and16 times that for psi. See the
primary [Johansson formula and remainder convention](https://arxiv.org/pdf/2109.08392),
equations21–23:31 terms plus R32 differs from32 terms plus the periodic-only
remainder. The source preserves that distinction.

The source does not exponentiate logGamma(w) outside its primitive domain.
It chooses an exact integer k from the rational midpoint of ReL/log2,
retains the complete log2 enclosure in L-k log2, checks its real box inside
[-2,2], evaluates the new exponential there, rescales by exact2^k, and
divides by the full64-factor complex product. Arbitrary size integers
carry that scaling; there is no floating underflow or unstated stability
assumption. The final complex width is constructed and checked <=2^-81.

The independent reference imports no Stirling evaluator: it uses
Gamma(s)=integral_R exp(s v-exp v)dv. Range[-64,6], step1/32, halfcell1/64,
degree24,2240cells/case,33600total. With P0=1,
P(k+1)(t)=(s-t)Pk(t)+tPk'(t), the coefficient recurrence is
a(k+1,j)=(s+j)a(k,j)-a(k,j-1). The finite sum of even derivative polynomials
is integrated before each24-step Horner evaluation. This exact linearity
reduces the reference to806400 complex Horner products plus one final
amplitude product per cell; it changes neither remainder nor catalogue.

On a complex v-disk radius1/4, t=exp(Re v)>0,
|exp(sv-exp v)| <= (t+t²)exp(-t/2)exp(23/4)
<10*3^6<2^13, using sigma in[1,2], |gamma|<=23, cos1/4>=1/2.
Therefore the Cauchy error is exactly bounded by
70*2^13*(1/16)^25/(1-1/16). The left tail is <=exp(-64)<=(3/8)^64,
from exp1>=8/3. For the right tail exp6>=256 and sigma<=2 give
integral_R^infty t exp(-t)dt=(R+1)exp(-R)<=257*2^-256.
The actual reference rounding width must be <=2^-120. The complete
reference width divided by its certified norm lower bound must be <=1/1024.
This last guard is only informativeness; validity is supplied by the
integral, Cauchy remainder, tails and outward evaluation. Norm reflection
formulas are extra independent checks, never substitutes for complex phase.

Four further Gamma cases sigma={5/16,43/16}, gamma={-100,100} exercise the
expanded contour domain and actual width. The M=2^13 reference does not
apply to those four cases. They have no independent phase-validation claim.
No point in these finite catalogues validates all204800 thermal nodes.

## EM, derivative and real precision propagation

M128/K64 is differentiated analytically. The fixed base domain is
Re s in[-7/8,2], |Im s|<=401/4. Its1/16 Cauchy expansion is
Re s in[-15/16,33/16], |Im s|<=1605/16. This explicitly keeps Re s>-1.
On that expansion all128 Pochhammer factors have norm<230, and the
Bernoulli Fourier bound supplies the closed conservative remainder
4*128²/126*(230/768)^128<2^-182. Differentiation on the1/16 disk bounds
the derivative remainder by2^-178. The source never differentiates a
point Gamma or a finite difference without a remainder.

The source stores (s)_j/128^j directly. Its derivative step is
Dnext=D*(s+j)/128+P/128. Small EM coefficients are applied to these
normalized products, avoiding a huge Pochhammer followed by cancellation.
Both finite value and derivative boxes still carry every outward round.
At the declared nodes their constructed widths, and the subsequent A'/A
widths, must meet2^-81. A quotient requires a positive actual denominator
norm lower bound; this is not a free zero-free numerical premise.

The special-value references [DLMF25.6](https://dlmf.nist.gov/25.6) give
zeta(0)=-1/2, zeta(2)=pi²/6 and zeta'(0)=-log(2pi)/2. They are evaluated
using new ground primitives, not EM. Eight additional EM log-derivative
points near the contour disk extremes are width guards without an
independent value claim. Psi(1) and gammaEuler are prepared for futureH1,
but are not asserted validated by this particular catalogue.

## DFT, orientation, alias and four budgets

Vertical kernel: m128,Rc3/16,halfcell1/8,degree64. Every j visited.
For s=s0+i v, each even coefficient k is integrated with
(-1)^(k/2)*2*r^(k+1)/(k+1), divided by2pi; this is i^k, not1.
Real kernel: m96,Rc1/8,halfcell1/32,degree32, no i^k.
Cases verticaldegrees0,1,2,3,4,16,32,64 and realdegrees0,1,2,31,32
are checked against exact polynomial integrals. Roots, positions and
weights are new complete boxes; their midpoint points carry L1 norm radii.
For sample p, errors ef,ep and weight w with error ew, a product records
(|w|+ew)ef, (|w|+ew)ep, |p|ew, and the exact dyadic product round,
as four separate fields. No category is assigned a free tolerance.

At exponent m, discrete quadrature aliases z^m onto its constant term.
The source independently compares the result to2*r*Rc^m (divided by2pi
vertically), while requiring disjointness from the true polynomial integral.
These two alias cases demonstrate a nonzero paid alias. They are not
reported as exact integration at arbitrary degree or alias-free FFT.

Mutations:15 complex Gamma rotations by i,2 zeta sign changes,1 zeta'
sign change,1 missing-i^k change:19. All must be disjoint from their own
independent reference. An overlapping mutation is UNRESOLVED, not false.

## Fixed cost, checker, protocol and remaining obligations

44 result cases:15phase+4Gammawidth+2EMconstants+8EMwidth+13polynomials
+2aliases.15 square-root certificates support reference norm lower bounds.
EM makes10 new127-power catalogues (1270 powers). Gamma producer calls19.
All33,600 reference cells and every DFT node must be visited. These are
fixed source counts, not measured timings or a runtime promise.

The independent checker imports only Fraction and emitted intervals. It
rechecks catalogues, special-value/phase/norm overlap, mutation disjointness,
actual width guards and the no-global-credit fields. It does not replace
analytic proof of the primitive/rest formulas and does not use a PASS oracle.

The metadata preparation may freeze sources and runtime bytes. Only a
distinct root gate, bound to the exact preparation SHA and all bindings,
can permit one actual attempt. PREEXEC copies precede rawSTART; an atomic
actual directory consumes the sole attempt even on failure. POSTEXEC
hashes, log, result, sqrt JSONL and receipt are preserved without retry.
Global thermal H1, arithmetic trace, boundary nonannulation, actual allzero
trace, coefficientN, D_N and WIN remain OPEN and receive no credit here.
