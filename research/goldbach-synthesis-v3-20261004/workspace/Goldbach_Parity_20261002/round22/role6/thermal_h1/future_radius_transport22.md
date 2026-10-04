# Future fullH1 radius representation — SOURCE correction, not component credit

The frozen component sources use exact Fraction propagation for polynomial
evaluation. Exactness encloses the object, but denominators can grow by up
to512bits per multiplication. At high degree, decimal serialization may hit
the runtime limit of4300digits. This static risk was identified while the
sole authorized component attempt was running. It is not an observed failure
until the actual log says so, and is not a mathematical disproof of H1.
The frozen25bindings are preserved; no second component attempt is made.

The future all800-cell unit-modulus powers must instead keep each radius
on the outward512-bit grid. Let p approximate z, q approximate a true
unit-modulus step, errors e and eq, and |z|<=U. After the rounded Gaussian
point product, the exact candidate radius is
(1+eq)e+Ueq+r_product. Define e_next=ceil(2^512*candidate)/2^512.
The new extra rounding satisfies0<=r_radius<2^-512. Nearest rounding of
the two product coordinates has norm error at most2^-512. Their sum is
therefore <=2*2^-512, checked from exact integers. The already selected
closed bound2e0+1600(Ueq+2*2^-512) remains valid for799updates with
eq<=2^-200, using(1+eq)^800<=2. No free stability premise is added.

A future contractive primal exponential recurrence uses the same mechanism,
the true step q=exp(-1/Y) in(0,1), U=1, and at most999999updates. Its closed
bound is2e0+2X(eq+2*2^-512), with X=1000000 and eq<=2^-200. The exact
radius grid bounds the size of all subsequent rational numerators and
denominators independently of the iteration count. It changes representation
conservatively and retains the radius-round contribution explicitly.

These new sources have no imports or evaluations yet. They must receive a
future source freeze, review and distinct gate before use. They do not
repair, replay or grant a PASS to the component attempt now in progress.
