# General loop upper extension: BLOCKED after three paper attempts

The rational restriction lower bound is now Judge-verified in the main project.
The universal no-loop upper construction is given separately in UPPER_NO_LOOP.md.
All 26 finite rational upper cases have succeeded, including their loop cases,
but they do not close the following general obligation:

 For every Goldbach matching graph with one loop and at least one isolated
 vertex, construct a D_pi rational certificate of standard degree alpha+1.

No proof of this universal loop statement is claimed. After three paper attempts,
work shifted to the completed no-loop construction and exact finite rational
certificates. This is a blocked upper extension, not a route-wide DEAD declaration.

1. Directly extending the no-loop generating function adds a factor
   (1+2z)^(-X_loop/2). Omitting it silently treats the loop as a nonloop edge.
   Its contributions have to be retained, and the resulting vanishing relation
   does not immediately specialize to a constant modulo L and g.
2. Pairing the loop with an isolated vertex makes the linear-factor count equal
   alpha, but changes its quadratic edge product from X_loop to
   X_loop*X_isolate. The resulting relation uses a different generator and is
   not an upper certificate for the original g. This generator substitution is
   rejected as an incomplete argument.
3. Two vanishing relations after removing the loop and one isolate reduce the
   problem to an explicit four-by-four rational determinant. It is nonzero in
   sampled parameters, but a proof that it never vanishes has not been supplied.

For a concrete continuation of attempt 3, let k be the number of nonloop pairs,
s>=1 the number of isolates, t=2k+s+1, and alpha=k+s. Write x for the loop and y
for a chosen isolate. The remaining linear-factor product has z-degree alpha-1.
In the Boolean quotient, S is the total prime count and g=2T+x. Therefore its
coefficients of orders alpha and alpha+1 vanish and are represented by

 Phi_j(S,g,x,y) = [z^j](1+z)^(S-g-y)(1+2z)^((g-x)/2).

After reducing x^2=x and y^2=y, these coefficients are polynomials over Q of
weighted degree at most j (S,x,y have weight1 and g weight2). The weight claim
follows because log(1+2z)-2log(1+z) begins at order2, and each x or y factor
introduced by its Boolean exponential begins at order1.

At S=t,g=0 define

 h_j(x,y)=[z^j](1+z)^(t-y)(1+2z)^(-x/2), for x,y in {0,1}.

A sufficient condition for a degree-alpha+1 identity is that the four equations

 (ell_0+ell_x*x+ell_y*y) h_alpha(x,y) + c h_(alpha+1)(x,y) = 1

have rational coefficients ell_0,ell_x,ell_y,c. A nonsingular coefficient matrix
gives such coefficients. The resulting combination of the two vanishing Phi
relations equals one modulo S-t,g,x^2-x,y^2-y; weighted division then has the
required degree bounds. This route still needs a general determinant argument,
including k=0 and any zero h entries. Finite nonsingularity alone is insufficient.

The Goldbach graph restriction matters: arbitrary matching-plus-loop graphs with
no isolates can fail degree alpha+1. A single loop has alpha=0 but standard minimum
degree2, as shown by 1=X^2-(X+1)(X-1). For even N>4, prime2 is isolated because
N-2 is even and greater than2. This eliminates that elementary counterexample,
but it does not itself prove the remaining loop upper statement.
