# Gamma rotated-Laplace auxiliary, source preparation

This is a new bank, independent of the completed Epstein bank. All 21 samples
are fixed before any mask: sigma in {1,3/2,2}, gamma in {0,+1,-1,+10,-10,+100,-100}.
N=100000000 is a scale label only. No primes, zeta zeros, heat correlation,
Weil trace, coefficient N, D_N or victory are computed by this bank.

## Actual mathematical quantity and independent route

Put z=sigma+i*gamma, theta=sign(gamma)*pi/4, with sign(0)=+1,
and c=exp(i*theta). The complex-rate Laplace identity, with the principal
power of c and positive-real powers of x, yields

    Gamma(z)=exp(i*theta*z) I(z,c),
    I(z,c)=integral_R exp(z*v-c*exp(v)) dv.

Thus W=exp(pi*abs(gamma)/4)*abs(Gamma(z))=abs(I(z,c)). The bank evaluates
the genuine rotated complex integral. It also reconstructs a rectangle for
Gamma from exp(-pi*abs(gamma)/4)*exp(i*sigma*theta)*I. It never compares a
claimed upper bound with an identical copy of that upper bound.

The source-only Lean input is GammaPrerequisites22.lean,
SHA8bcfef577be2dbf3412646bd7938fe3d929dc0efdd4d1d7c29149ff6102ed7a0.
Its complex Laplace identity and whole-strip H2 theorem are separate Lean
obligations; this document reports no compilation. The integral representation
is also supported by [NIST DLMF 5.9.1](https://dlmf.nist.gov/5.9.E1).

The independent reference uses [NIST DLMF 5.4.3 and 5.4.4](https://dlmf.nist.gov/5.4)
and Gamma recurrence. For g=abs(gamma)>0, put q=exp(-2*pi*g), v=exp(-pi*g/2).
Factored formulas, which avoid large sinh/cosh intermediates, are

    W_1^2       = 2*pi*g*v/(1-q),
    W_2^2       = (1+g^2)*W_1^2,
    W_(3/2)^2   = 2*pi*(g^2+1/4)*v/(1+q).

At g=0 the references are 1, 1, and pi/4 respectively. The half-strip reference
formula is regular at zero. No division by g or sinh(0) is evaluated. The two
routes share only certified elementary constants/primitives, not Gamma values.
These reflection identities are external analytic obligations, visible in
the result and not inferred from finite sample overlap.

## Closed continuous quadrature and tail budget

Let G(v)=exp(z*v-c*exp(v)), an entire function of the complex variable v.
On a complex disc of radius1/8 about any real center, abs(Im v)<=1/8 gives
abs(theta+Im v)<=pi/4+1/8<pi/3. Hence the cosine is at least1/2. With
u=exp(Re v)>0, sigma in[1,2], and abs(gamma)<=100,

    abs(G(v)) <= exp(100/8)*(u+u^2)*exp(-u/2) < 2^26.

For example exp(u/2)>=u/2 and >=u^2/8 bound the two peaks by2 and8;
18*3^13<2^26 is a convenient looser integer bound. Cauchy bounds the Taylor
coefficients by2^26*8^k. No branch of a noninteger power is used in G(v).

The interval[-32,6] is divided into9728 cells of width1/256, radius1/512.
The exact integral of each Taylor polynomial of degree12 is retained, including
all even coefficients. The omitted Taylor remainder has geometric ratio1/64.
Integrating its norm over the total length38 yields the exact rational budget

    E_quad = 38*64/(63*2^52).

For v<-32, damping has norm at most1, so the integral is at most
exp(-32*sigma)/sigma <= exp(-32) <=(3/8)^32, using exp(1)>=8/3.
For v>6 substitute x=exp(v). Since sigma-1 is in[0,1], x^(sigma-1)<=x
when x>=1 and Re(c)>=1/2. With R=exp(6)>256,

    integral_R^infinity x*exp(-x/2) dx=(2R+4)*exp(-R/2)
       <=516*exp(-128)<=516/2^128.

The closed complex disk radius is

    E_analytic=E_quad+(3/8)^32+516/2^128.

This disk is enclosed by adding E_analytic to both sides of each component
rectangle. The corresponding norm enclosure therefore remains rigorous.
Observed interval widths are kept separately from these analytic tails.
ROLE4 accepted these Cauchy and tail derivations on paper; no numerical run
was involved in this acceptance.

## Fresh exact arithmetic and primitive budgets

The elementary integer-endpoint rules are adapted, with explicit provenance,
from READONLY role6/interval22.py SHA6e29ec2c7fb5d8e1eba796f3d863fb4c95db5b2bb5cf9671a9fb80d6469df588.
The new module has a768-bit grid. It does not import G0 code, use G0 results,
replay its producer, alter its grid, or read its certificates. All inputs are
integers/Fractions, and an AST guard prohibits float/complex literals and
float/complex/Gamma API calls. Multiplication, division and rational scaling
round outward on this grid. Square treats intervals crossing zero correctly.
Every square root checks integer-square inequalities and writes a certificate.

Pi uses Machin's identity16*atan(1/5)-4*atan(1/239), with256 alternating terms
per arctangent and the next absolute term as a remainder. Its resulting width
must be<=128*2^-768, with3<pi<4. This is a direct series evaluation, not a
stored approximation. Square-root-two uses integer-square certificates.

Exp's frozen domain is[-1024,16]. Exact dyadic reduction first reaches
abs(base)<=1/16 before grid rounding; a guard confirms abs(base)<=1/8.
Taylor degree128 in Horner form has remainder<=2/8^129. The enclosure is then
squared at most14 times. Positivity permits intersection with[0,infinity).
For sin/cos the frozen domain is[-4096,4096]. An exact integer period is
chosen using rational midpoints; subtraction uses the whole pi enclosure.
The residual must lie in[-4,4]. Each128-term Taylor polynomial is evaluated
with factorial-ratio Horner steps. A common absolute tail is

    2*4^257/256! < 2^-380,

since256!>=128^128. Range intersection with[-1,1] uses a proved fact about
the real functions. No midpoint is substituted for an interval input.

For each exp/sin/cos result the source checks the closed width contract

    width_out <= 2^48*(width_in+2^-768)+2^-300.

This is a conservative enclosure-width guard, not an additional assumed
rounding error. Enclosure validity comes from outward integer operations and
explicit series tails. Failure of this guard is an arithmetic-budget failure,
never a mathematical refutation of Gamma. For exp, polynomial sensitivity on
the base is<2; squaring accumulation is bounded by2^14 times exp(16)<2^26.
For sin/cos, the absolute Taylor majorant is at most exp(4)<81, and the period
uncertainty contributes fewer than2^16 grid units. These estimates fit2^48.
The explicit series tails are below2^-380, leaving margin for the2^-300 term.

The exact cell polynomial is constructed from

    P_0=1, P_(k+1)=(z-w)P_k+w*P'_k,
    coefficient_(k+1,j)=(z+j)*coefficient_(k,j)-coefficient_(k,j-1).

Its even Taylor weights2*r^(k+1)/(k+1)! multiply exact rational complex
coefficients before their conversion to intervals. Quantizing a tiny weight
first would destroy the error budget. The combined degree12 polynomial
requires only12 complex Horner multiplications per cell and sample.

A deliberately loose propagation check explains the frozen component width
cap2^-80. Primitive guards with exact centers imply width(exp(v))<2^-299,
width(c*exp(v))<2^-298 and widths of amplitudes/phases' sine/cosine<2^-249.
Amplitudes are<2^21, so each G component has width<2^-226. For k<=12,
the sum of absolute P_k coefficients is<=128^k; abs(w)_1<=2^11.
After exact Taylor weights, the combined polynomial magnitude is<2^104.
Its coefficient rounding and derivative propagation give component width
<2^-180 (a bound2^116 times the w width plus2^160 grid units suffices).
Multiplication by G and summation of fewer than2^14 cells therefore yield
width<2^-96, within the looser enforced2^-80 cap. Each actual component width
is still reported and checked; it is never replaced by this estimate.

## Discrimination, resources and limits

The normalized absolute tolerance is fixed at1/100000000. A case passes only
when the actual integral/reference norm intervals intersect, their maximum
endpoint distance is within tolerance, the arithmetic width cap holds, and
the integral norm upper bound is<=2. Disjoint rigorous enclosures are reported
separately from unresolved overlap or an inadequate width.

The mutation omits exp(-pi*g/4) during Gamma reconstruction. Exactly12 cases
with abs(gamma) in{1,10} are declared applicable before execution. Their wrong
normalized norm is exp(pi*g/4)*abs(I); a detection requires both disjointness
from the reflection reference and a norm lower bound>2. Other gamma cases
are not counted as detected mutation tests. In particular the normalized
values at abs(gamma)=100 fall below the absolute tolerance: a zero mutation
is not discriminated there and the output explicitly flags that limitation.

The source loop evaluates all9728 cells in all21 cases. Within this single new
attempt, exp(v) is shared across cases, three amplitudes across each sigma,
and seven trigonometric pairs across each gamma. Negative-gamma integrals
are evaluated with their signed phases, not copied from positive outputs.
There are38912 grid exp calls and68096 paired grid sin/cos calls, plus the
small reference/reconstruction calls. The polynomial requires21*9728*12
complex multiplications. All counts are expressions from source loops;
there is no empirical runtime estimate or imported PASS. Grid caches do not
persist across attempts. No array of primes or zero table is allocated.

The first bank may yield GAMMA_ROTATED_LAPLACE_AUX_PASS, UNRESOLVED, or
COUNTEREXAMPLE_ENCLOSURES_DISJOINT under the explicitly stated analytic
obligations. Finite samples never prove whole-strip H2. No status credits the
Weil real trace, its complete zero count, the global coefficient atN, or D_N.
Those layers need distinct producers, contracts and gates.
