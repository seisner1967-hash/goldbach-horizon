# Rational alpha+1 upper construction when the Goldbach graph has no loop

This is a universal paper construction for the **no-loop calibration case**.
It is not a universal upper theorem for all Goldbach graphs: the loop extension
remains unproved here. It concerns only D_pi(N), whose prime-count constant and
Boolean pinning already reject it as a candidate for a uniform Goldbach proof.
No theorem about a viable candidate family is claimed.

Let the prime graph have k disjoint nonloop pairs and s isolated prime vertices,
with k>=1 and no loop. Put t=2k+s and alpha=k+s, and set m=alpha+1. Over Q, use
prime variables only at first and define

 S=sum_prime X_p,
 T=sum_(nonloop pairs {p,q}) X_p X_q,
 L=S-t, and g=2T.

The ordinary degree of S is one and of T is two. Treat formal S,T temporarily
as indeterminates of weights one and two. Define the rational polynomial

 Phi_m(S,T) = [z^m] (1+z)^S exp(T H(z)),
 H(z)=log(1+2z)-2log(1+z)
     =sum_(j>=2) (-1)^(j+1)(2^j-2) z^j/j.

Only coefficients through z^m are needed. Thus no analytic convergence or
continuous transform enters: these are finite formal-power-series calculations
over Q. The binomial expansion (1+z)^S has coefficient
C(S,j)=S(S-1)...(S-j+1)/j!, a polynomial of degree j. Since H starts in degree two,
the coefficient of T^a in Phi_m has S-degree at most m-2a. Therefore Phi_m has
weighted degree at most m and ordinary degree at most m after substituting S,T.

At a Boolean assignment, let u be the number of pairs with both endpoints one,
v the number with exactly one endpoint one, and w the number of selected
isolates. Then T=u and S=2u+v+w, so

 (1+z)^S exp(T H(z)) = (1+2z)^u (1+z)^(v+w).

This is also the value of the ordinary polynomial in z

 product_pairs (1+z(X_p+X_q)) * product_isolates (1+z X_p),

whose z-degree is at most k+s=alpha. Consequently Phi_m vanishes at every
Boolean point, because m=alpha+1. This proves Phi_m lies in the Boolean ideal.
Its ordinary degree is at most m, so ordinary division by X_p^2-X_p supplies
Boolean multipliers whose products also have degree at most m.

At T=0, Phi_m(S,0)=C(S,m). Define

 Q_m(S,T)=(Phi_m(S,T)-C(S,m))/T.

This is a polynomial, of weighted degree at most m-2. Set c=C(t,m), which is a
nonzero positive rational integer because m<=t when k>=1. Define

 A(S)=(1-C(S,m)/c)/(S-t),
 B(S,T)=-Q_m(S,T)/(2c).

The numerator of A vanishes at S=t, so A is a polynomial of degree at most m-1.
B has weighted degree at most m-2. These definitions give the **ordinary**
polynomial identity

 1 - A(S)(S-t) - B(S,T)(2T) = Phi_m(S,T)/c.

The right side is in the Boolean ideal and has degree at most m. Therefore
division produces U_p with

 1 = A L + B g + sum_prime U_p (X_p^2-X_p),

of standard total degree at most m=alpha+1. Multilinearly reducing A and B first
is optional and preserves their degree bounds; any correction remains in the
same Boolean ideal with the same total-degree bound.

To restore all coordinates 0..N, write

 L_full=L_prime+sum_nonprime X_c,
 g_N=g_prime+sum_nonprime X_c H_c,

where each H_c is linear and each nonprime term of g is assigned to one of its
nonprime factors. Choose C_c=-A-B H_c. The displayed prime-ring identity then
becomes

 1 = A L_full+B g_N+sum_prime U_p (X_p^2-X_p)+sum_nonprime C_c X_c.

The added products still have degree at most alpha+1. Together with the general
restriction lower bound, this proves exact rational degree alpha+1 for every
no-loop D_pi graph with at least one edge, once the paper argument is verified.

## Loop distinction and finite rational checks

With a loop, the original generator contains X_l^2. The Boolean quotient replaces
this by X_l, but a B*g product still counts the original degree two. The above
construction cannot silently replace the loop by another nonloop pair. For an
arbitrary graph consisting of one loop and no isolates, alpha=0 but the minimum
standard degree is 2, not alpha+1=1: with L=X-1 and g=X^2,
1=X^2-(X+1)(X-1). A degree-one identity cannot include g or a Boolean generator,
and any remaining multiple of L vanishes at X=1. Thus a proof for all
matching-plus-loop graphs would be false. Goldbach graphs have prime 2 isolated
whenever N>4, so that example
do not refute the desired all-N Goldbach calibration upper bound. A rigorous
extension exploiting the isolated vertex is still an open obligation here.

`scripts/rational_upper.py` performs exact rational linear algebra at the 26
recorded even N=10..60, searches only the requested candidate degree alpha+1,
and expands successful multipliers. The output includes exact rational orbit
coefficients and a deterministic ordinary lift, checked by polynomial coefficient
comparison. These finite successes must not be used to assert a general loop
upper bound. Existing finite-field degree artifacts are not modified.
