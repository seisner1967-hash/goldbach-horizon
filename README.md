# Horizon Goldbach

Lean 4 formal specification programme for a conditional architecture around the
binary Goldbach conjecture.

This repository does **not** claim an unconditional proof of Goldbach. Its goal
is narrower and auditable: decompose the proof architecture into Lean-checked
modules, prove the finite/combinatorial layer, and expose the remaining
analytic work as named local infrastructure obligations.

## Current Focus: TS15--TS284

The current sprint chain lives under:

```text
TS/Goldbach/Strong/
  TS15/
  TS16/
  TS17/
  TS18/
  TS19/
  TS20/
  TS21/
  TS22/
  TS23/
  TS24/
  TS25/
  TS26/
  TS27/
  TS28/
  TS29/
  TS30/
  TS31/
  TS32/
  TS33/
  TS34/
  TS35/
  TS36/
  TS37/
  TS38/
  TS39/
  TS40/
  TS41/
  TS42/
  TS43/
  TS44/
  TS45/
  TS46/
  TS47/
  TS48/
  TS49/
  TS50/
  TS51/
  TS52/
  TS53/
  TS54/
  TS55/
  TS56/
  TS57/
  TS58/
  TS59/
  TS60/
  TS61/
  TS62/
  TS63/
  TS64/
  TS65/
  TS66/
  TS67/
  TS68/
  TS69/
  TS70/
  TS71/
  TS72/
  TS73/
  TS74/
  TS75/
  TS76/
  TS77/
  TS78/
  TS79/
  TS80/
  TS81/
  TS82/
  TS83/
  TS84/
  TS85/
  TS86/
  TS87/
  TS88/
  TS89/
  TS90/
  TS91/
  TS92/
  TS93/
  TS94/
  TS95/
  TS96/
  TS97/
  TS98/
  TS99/
  TS100/
  TS101/
  TS102/
  TS103/
  TS104/
  TS105/
  TS106/
  TS107/
  TS108/
  TS109/
  TS110/
  TS111/
  TS112/
  TS113/
  TS114/
  TS115/
  TS116/
  TS117/
  TS118/
  TS119/
  TS120/
  TS121/
  TS122/
  TS123/
  TS124/
  TS125/
  TS126/
  TS127/
  TS128/
  TS129/
  TS130/
  TS131/
  TS132/
  TS133/
  TS134/
  TS135/
  TS136/
  TS137/
  TS138/
  TS139/
  TS140/
  TS141/
  TS142/
  TS143/
  TS144/
  TS145/
  TS146/
  TS147/
  TS148/
  TS149/
  TS150/
  TS151/
  TS152/
  TS153/
  TS154/
  TS155/
  TS156/
  TS157/
  TS158/
  TS159/
  TS160/
  TS161/
  TS162/
  TS163/
  TS164/
  TS165/
  TS166/
  TS167/
  TS168/
  TS169/
  TS170/
  TS171/
  TS172/
  TS173/
  TS174/
  TS175/
  TS176/
  TS177/
  TS178/
  TS179/
  TS180/
  TS181/
  TS182/
  TS183/
  TS184/
  TS185/
  TS186/
  TS187/
  TS188/
  TS189/
  TS190/
  TS191/
  TS192/
  TS193/
  TS194/
  TS195/
  TS196/
  TS197/
  TS198/
  TS199/
  TS200/
  TS201/
  TS202/
  TS203/
  TS204/
  TS205/
  TS206/
  TS207/
  TS208/
  TS209/
  TS210/
  TS211/
  TS212/
  TS213/
  TS214/
  TS215/
  TS216/
  TS217/
  TS218/
  TS219/
  TS220/
  TS221/
  TS222/
  TS223/
  TS224/
  TS225/
  TS226/
  TS227/
  TS228/
  TS229/
  TS230/
  TS231/
  TS232/
  TS233/
  TS234/
  TS235/
  TS236/
  TS237/
  TS238/
  TS239/
  TS240/
  TS241/
  TS242/
  TS243/
  TS244/
  TS245/
  TS246/
  TS247/
  TS248/
  TS249/
  TS250/
  TS251/
  TS252/
  TS253/
  TS254/
  TS255/
  TS256/
  TS257/
  TS258/
  TS259/
  TS260/
  TS261/
  TS262/
  TS263/
  TS264/
  TS265/
  TS266/
  TS267/
  TS268/
  TS269/
  TS270/
  TS271/
  TS272/
  TS273/
  TS274/
  TS275/
  TS276/
  TS277/
  TS278/
  TS279/
  TS280/
  TS281/
  TS282/
  TS283/
  TS284/
```

Status summary:

| Sprint | Object | Status | Meaning |
| --- | --- | --- | --- |
| TS15 | Short-interval reduction | `interface_compiled` | typed Lean interface for the local analytic residue |
| TS16 | Combinatorial discharge | `repo_committed` | finite counting lemma proved unconditionally |
| TS17 | Mellin-Jackson projection | `repo_committed_relative` | reduced to Mellin/Fourier infrastructure |
| TS18 | Short-interval second moment | `repo_committed_relative` | reduced to character bridge and large sieve infrastructure |
| TS19 | OTSA residual bound | `repo_committed_relative` | reduced to spectral, trace, and Mellin-tail controls |
| TS20 | Synthesis manuscript | documentation | final ledger and project roadmap |
| TS21 | Short-interval constant budget | `repo_committed_relative` | transports explicit constants such as Brun-Titchmarsh `K = 20` |
| TS22 | Energy scale renormalization | `repo_committed_relative` | makes the short-interval normalization scale explicit |
| TS23 | OTSA scale propagation | `repo_committed_relative` | transports TS22 scales into the OTSA residual ledger |
| TS24 | Closed-form scale bridge | `repo_committed` | proves the ceiling-budget scale is dominated by a padded closed form |
| TS25 | Padded-scale OTSA feasibility | `repo_committed_relative` | specializes OTSA propagation to the TS24 padded scale |
| TS26 | OTSA numerical feasibility | `repo_committed_relative` | converts rational OTSA certificates into scaled admissibility |
| TS27 | OTSA constant register | `repo_committed_relative` | registers non-final rational OTSA smoke-test constants |
| TS28 | OTSA constants candidate | `repo_committed_relative` | adds a typed-status candidate-v0 OTSA register |
| TS29 | OTSA constant provenance | `repo_committed_relative` | records provenance status for OTSA rational bounds |
| TS30 | Brun-Titchmarsh Selberg roadmap | `repo_committed_relative` | decomposes BT into Selberg majorant and budget comparison |
| TS31 | OTSA asymptotic majorants | `repo_committed_relative` | records candidate-v1 rational majorants and provenance gaps |
| TS32 | OTSA trace majorant roadmap | `repo_committed_relative` | records the conditional trace target `Ct <= 1/2` |
| TS33 | OTSA final majorants roadmap | `repo_committed_relative` | replaces final raw placeholders by Mellin-tail and scale-transfer contracts |
| TS34 | Mellin-Fourier measure transport | `repo_committed_relative` | isolates a.e. transport under weighted, restricted, exp, and log measures |
| TS35 | Mellin-Fourier AEEqFun transport | `repo_committed_relative` | descends `TsigmaFun` and `TsigmaInvFun` through the a.e. quotient layer |
| TS36 | Mellin-Fourier L2 isometry roadmap | `repo_committed_relative` | packages the remaining `Lp`-level inputs for the future isometry |
| TS37 | Mellin-Fourier Lp norm inputs | `repo_committed_relative` | isolates `Memℒp` and `snorm` preservation for the future isometry |
| TS38 | Mellin-Fourier Lp linearity inputs | `repo_committed_relative` | isolates a.e. additivity and scalar compatibility for the future isometry |
| TS39 | Mellin-Fourier Lp isometry spec | `repo_committed_relative` | specifies the final `LinearIsometryEquiv` and its a.e. representative behaviour |
| TS40 | Fourier tail roadmap | `repo_committed_relative` | records Plancherel, derivative-control, and high-frequency tail obligations |
| TS41 | Fourier API probe | `repo_committed_relative` | records Fourier API normalization slots before concrete Mathlib binding |
| TS42 | Mellin tail spline roadmap | `repo_committed_relative` | records the triangle-spline route to the `Cm <= 1` Mellin-tail contract |
| TS43 | Triangle spline pointwise facts | `repo_committed` | proves elementary branch values and the pointwise derivative bound |
| TS44 | Triangle spline measurability and support | `repo_committed` | proves measurability and support containment for the derivative representative |
| TS45 | Triangle spline derivative snorm roadmap | `repo_committed_relative` | packages TS43/TS44 inputs and isolates the derivative `snorm <= 2` obligation |
| TS46 | Triangle spline support measure | `repo_committed` | proves the Lebesgue measure of `[-1, 1]` is exactly `2` |
| TS47 | Triangle spline snorm discharge bridge | `repo_committed_relative` | reduces the derivative `snorm <= 2` estimate to a generic bounded-support lemma |
| TS48 | Bounded-support snorm lemma | `repo_committed` | proves the generic bounded-support `snorm` lemma and discharges the TS45 triangle derivative target |
| TS49 | Triangle spline Sobolev agreement | `repo_committed_relative` | isolates agreement between the TS41 Sobolev derivative slot and `triangleSplineDeriv` |
| TS50 | Triangle spline tail assembly | `repo_committed_relative` | assembles TS48 norm control and TS49 Sobolev agreement into the TS42 spline-tail route |
| TS51 | Triangle spline Fourier-tail comparison | `repo_committed_relative` | replaces the TS50 tail marker by an explicit high-frequency `snorm <= 1` comparison package |
| TS52 | Fourier Mathlib API binding roadmap | `repo_committed_relative` | records the binding layer between TS41 normalization slots and future Mathlib Fourier theorem instances |
| TS53 | Fourier concrete symbols probe | `repo_committed_relative` | checks `Real.fourierIntegral`, its inverse, kernel formulas, and the derivative-rule symbol |
| TS54 | Fourier Plancherel L2 gap ledger | `repo_committed_relative` | records the missing compatible `snorm`/L2 Plancherel contract after TS53 |
| TS55 | Triangle spline Sobolev agreement ledger | `repo_committed_relative` | decomposes the TS49 weak-derivative agreement into local Sobolev-side obligations |
| TS56 | Triangle spline branch formulae | `repo_committed` | proves the affine branch formulae for `triangleSpline` and its vanishing outside `[-1, 1]` |
| TS57 | Triangle spline classical branch derivatives | `repo_committed` | proves classical derivatives on `(-1, 0)` and `(0, 1)` and agreement with `triangleSplineDeriv` |
| TS58 | Triangle spline boundary and exterior control | `repo_committed` | proves exterior derivative `0`, exterior agreement with `triangleSplineDeriv`, and nullity of the corner set |
| TS59 | Triangle spline off-corner classical derivative | `repo_committed` | proves the pointwise derivative agreement away from `{ -1, 0, 1 }` |
| TS60 | Triangle spline a.e. classical derivative | `repo_committed` | lifts TS59 through the null corner set to prove a.e. derivative agreement |
| TS61 | Triangle spline distributional derivative ledger | `repo_committed_relative` | records the weak-derivative identity contract and the TS60 a.e. input package |
| TS62 | Triangle spline test-function API probe | `repo_committed_relative` | binds the TS61 abstract test-function API to a concrete C1 compact-support package |
| TS63 | Triangle spline concrete distributional contract | `repo_committed_relative` | specializes the TS61 weak-derivative contract to the concrete TS62 test-function API |
| TS64 | Triangle spline IPP integrability inputs | `repo_committed_relative` | isolates the two Bochner-integrability inputs needed before proving the TS63 IPP identity |
| TS65 | Triangle spline IPP integrability discharge | `repo_committed` | proves the two TS64 Bochner-integrability inputs for the concrete TS62 test-function API |
| TS66 | Triangle spline IPP product support restriction | `repo_committed` | proves the two concrete IPP products vanish outside `[-1, 1]` |
| TS67 | Triangle spline IPP integral restriction | `repo_committed_relative` | fixes the integral-level restriction contract from global `volume` to `volume.restrict (Icc (-1) 1)` |
| TS68 | Triangle spline IPP integral restriction proof | `repo_committed` | proves the two TS67 integral-restriction equalities using TS66 support restriction |
| TS69 | Triangle spline IPP branch split | `repo_committed_relative` | fixes the branchwise split contract over `Icc (-1) 0` and `Ioc 0 1` |
| TS70 | Triangle spline IPP branch split proof | `repo_committed` | proves the TS69 branchwise split using disjoint restricted measures |
| TS71 | Triangle spline IPP right branch closed bridge | `repo_committed_relative` | fixes the bridge contract from `Ioc 0 1` to `Icc 0 1` |
| TS72 | Triangle spline IPP right branch closed bridge proof | `repo_committed` | proves the TS71 closed-right-branch bridge using the null endpoint |
| TS73 | Triangle spline IPP affine branch contract | `repo_committed_relative` | fixes the two local affine IPP identities on the closed branches |
| TS74 | Triangle spline IPP recombination from affine branches | `repo_committed_relative` | proves TS73 affine branch IPP is sufficient for the concrete TS63 contract |
| TS75 | Triangle spline IPP interval-integral bridge | `repo_committed_relative` | fixes the API bridge from restricted branch measures to directed interval integrals |
| TS76 | Triangle spline IPP interval-integral bridge proof | `repo_committed` | proves the TS75 bridge from restricted branch measures to directed interval integrals |
| TS77 | Triangle spline IPP affine branch proof | `repo_committed` | proves the two TS73 local affine integration-by-parts identities |
| TS78 | Triangle spline concrete distributional discharge | `repo_committed` | combines TS74 and TS77 to discharge the concrete TS63 weak-derivative contract |
| TS79 | Triangle spline distributional derivative discharge | `repo_committed` | lifts the concrete TS63 weak-derivative contract to the abstract TS61 distributional target |
| TS80 | Triangle spline Sobolev slot assembly | `repo_committed_relative` | packages TS60 and TS79, and isolates the exact TS41 Sobolev-slot agreement still needed for TS49/TS55 |
| TS81 | Triangle spline Sobolev slot API binding | `repo_committed_relative` | isolates the final TS41 API binding whose proof would close TS80, TS55, and TS49 |
| TS82 | Triangle spline Sobolev API reality probe | `repo_committed_relative` | records the current Mathlib Sobolev API gap and defines the recognition contract feeding TS81 |
| TS83 | Mellin-tail final API gap ledger | `repo_committed_relative` | packages the final Sobolev, Plancherel, and Fourier-tail API contracts needed for `Cm <= 1` |
| TS84 | Scale-transfer majorant roadmap | `repo_committed_relative` | opens the `Cscale <= 2` front and packages the final scale-transfer API contracts feeding TS33/TS25 |
| TS85 | Scale-transfer variance ledger | `repo_committed_relative` | decomposes the TS84 scale-transfer contract into a Gallagher-style variance-transfer obligation |
| TS86 | Grand-sieve variance roadmap | `repo_committed_relative` | decomposes the TS85 Gallagher contract into Farey-spacing and dual large-sieve variance obligations |
| TS87 | Farey spacing roadmap | `repo_committed_relative` | decomposes the TS86 Farey infrastructure into rational-point separation, covering, and counting contracts |
| TS88 | Farey separation proof | `repo_committed` | proves the classical `1 / (q q')` separation contract for TS87 Farey points |
| TS89 | Farey counting proof | `repo_committed` | proves a concrete finite counting bound and discharges the TS87 counting target |
| TS90 | Farey covering proof | `repo_committed` | discharges the current TS87 covering marker and completes the Farey-spacing package |
| TS91 | Dual large-sieve variance bound proof | `repo_committed` | discharges the current TS86 dual large-sieve contract and closes the scale-transfer API route |
| TS92 | Spectral trace roadmap | `repo_committed_relative` | decomposes the `Ct <= 1/2` trace front into kernel, zeta-zero, and explicit-formula contracts |
| TS93 | Zeta zero family ledger | `repo_committed_relative` | refines the TS92 zero-family component into zero-set, multiplicity, strip, conjugation, and symmetry obligations |
| TS94 | Trace kernel spectral data ledger | `repo_committed_relative` | refines the TS92 kernel component into kernel, spectral-weight, normalization, positivity, decay, and convergence obligations |
| TS95 | Explicit formula trace bridge ledger | `repo_committed_relative` | refines the TS92 explicit-formula component into zero contribution, residual terms, trace budget, and bridge obligations |
| TS96 | Spectral trace majorant discharge | `repo_committed_relative` | assembles a TS95 explicit-formula ledger into the TS92/TS32 spectral trace majorant route |
| TS97 | Brun-Titchmarsh final input ledger | `repo_committed_relative` | isolates the exact TS22 natural-interval Brun-Titchmarsh input feeding the TS84/TS25 final assembly |
| TS98 | Final three-obligation assembly | `repo_committed_relative` | packages the TS97, TS95, and TS83 final inputs as the root dashboard feeding TS84/TS25 |
| TS99 | Selberg sieve weight ledger | `repo_committed_relative` | refines the TS97 arithmetic input into Selberg weights, majorant, sieve, and budget obligations feeding TS30/TS98 |
| TS100 | Selberg quadratic form ledger | `repo_committed_relative` | refines the TS99 Selberg-weight front into divisor-algebra, quadratic-kernel, diagonalization, and budget obligations feeding TS99/TS98 |
| TS101 | Selberg divisor algebra ledger | `repo_committed_relative` | refines the TS100 quadratic-form front into divisor weights, convolution, gcd/lcm algebra, and Mobius-inversion obligations feeding TS100/TS99 |
| TS102 | Horizon root assembly | `repo_committed_relative` | packages TS101, TS95, and TS83 terminal inputs into TS98, TS84, TS25, and candidate-v3 OTSA root surfaces |
| TS103 | Mobius inversion ledger | `repo_committed_relative` | refines the TS101 divisor-algebra front into divisor-sum, convolution, Mobius-delta, and gcd/lcm-kernel obligations feeding TS101/TS100 |
| TS104 | Mobius Mathlib API probe | `repo_committed_relative` | locates Mathlib's `ArithmeticFunction.moebius`, zeta inverse theorem, divisor sums, and convolution bridge feeding TS103 |
| TS105 | Mobius delta identity discharge | `repo_committed` | proves the Mathlib Mobius divisor-sum delta identity and supplies the TS103 Mobius-delta target |
| TS106 | Divisor kernel algebra ledger | `repo_committed_relative` | proves the canonical rational gcd/lcm product identity and packages the remaining divisor-kernel route feeding TS103 |
| TS107 | Selberg quadratic kernel extraction ledger | `repo_committed_relative` | proves symmetry of the canonical rational `gcd/lcm` kernel and supplies the TS106 extraction target |
| TS108 | Selberg quadratic form expansion ledger | `repo_committed_relative` | defines the finite Selberg quadratic double sum and proves the index-swapped expansion from TS107 symmetry |
| TS109 | Selberg quadratic diagonalization ledger | `repo_committed_relative` | defines the finite diagonal change-of-variables and diagonal square-sum side feeding TS108 |
| TS110 | Selberg dense-to-diagonal identity ledger | `repo_committed_relative` | names the dense-equals-diagonal Selberg identity as a proposition-valued obligation feeding TS109 |
| TS111 | Selberg dense-to-diagonal reindexing ledger | `repo_committed_relative` | expands the TS109 diagonal square side to a finite triple sum and packages the remaining reindexing obligations feeding TS110 |
| TS112 | Selberg Mobius collapse ledger | `repo_committed_relative` | rewrites the TS111 pair divisor filters as a single gcd filter and packages the remaining Mobius collapse obligations feeding TS111 |
| TS113 | Selberg finite Fubini reindexing ledger | `repo_committed_relative` | reorders the TS112 gcd-filtered triple sum into pair-first order and isolates the inner gcd-divisor sum feeding TS112 |
| TS114 | Selberg inner gcd-divisor collapse ledger | `repo_committed_relative` | factors the TS113 inner gcd-divisor sum and proves the conditional dense-side match from a local kernel coefficient identity |
| TS115 | Selberg Mobius coefficient ledger | `repo_committed_relative` | reduces the TS114 local coefficient to a one-variable gcd coefficient and isolates the coefficient-to-kernel match obligation |
| TS116 | Selberg gcd coefficient kernel-match ledger | `repo_committed_relative` | exposes the diagonal coefficient formula and isolates the exact compatibility needed to match the TS107 `gcd/lcm` kernel |
| TS117 | Selberg diagonal coefficient calculation ledger | `repo_committed` | proves the current gcd-only coefficient shape cannot match the pair-dependent `gcd/lcm` kernel and records the needed diagonal refinement |
| TS118 | Selberg lcm absorption bridge | `repo_committed` | proves the original `gcd/lcm` dense side equals the absorbed-weight gcd-square dense side |
| TS119 | Selberg Jordan-two gcd-square diagonalization ledger | `repo_committed_relative` | proves the local `J2` divisor-sum collapse and packages the corrected gcd-square diagonal side |
| TS120 | Selberg gcd-square global reindexing ledger | `repo_committed_relative` | expands and reorders the corrected Jordan-two diagonal side into pair-first local-coefficient form |
| TS121 | Selberg Jordan-two finite-support collapse | `repo_committed` | proves the finite-support collapse and closes the corrected dense-to-diagonal identity with absorbed weights |
| TS122 | Selberg diagonal optimization ledger | `repo_committed_relative` | proves finite weighted Cauchy for the corrected Jordan-two diagonal energy and isolates the remaining positivity/optimal-vector inputs |
| TS123 | Selberg Jordan-two positivity probe | `repo_committed_relative` | proves denominator positivity from supportwise `J2` positivity and records the current support is positive-bounded, not squarefree-only |
| TS124 | Selberg Jordan-two positivity API probe | `repo_committed_relative` | proves `J2(1) = 1`, `J2(p) = p^2 - 1`, prime positivity, and the bridge from global `J2` positivity to the TS123/TS122 lower bound |
| TS125 | Selberg Jordan-two prime-power positivity probe | `repo_committed_relative` | proves `J2(p^(k+1)) = p^(2*(k+1)) - p^(2*k)`, prime-power positivity, and the concrete non-squarefree value `J2(4) = 12` |
| TS126 | Selberg Jordan-two multiplicativity API probe | `repo_committed_relative` | proves multiplicativity of `J2`, exposes the `Nat.factorization` product formula, and rewrites prime-power positivity in factorization shape |
| TS127 | Selberg Jordan-two full positivity discharge | `repo_committed` | proves `J2(n) > 0` for every positive natural number and feeds the TS123/TS122 denominator and energy lower-bound route |
| TS128 | Selberg optimal vector normalization | `repo_committed` | proves the finite optimal vector satisfies the Mobius constraint and attains energy `1 / D` for the TS122 weighted Cauchy problem |
| TS129 | Selberg diagonal budget majorant ledger | `repo_committed_relative` | proves the dense side is the diagonal energy of the absorbed vector and packages the remaining interval sieve-majorant step |
| TS130 | Selberg optimal weight reconstruction ledger | `repo_committed_relative` | defines reconstructed original weights from a diagonal vector, proves support facts, and isolates the finite Mobius reconstruction identity |
| TS131 | Selberg finite Mobius reconstruction collapse | `repo_committed_relative` | names the finite chain coefficient, proves delta selection, and shows expansion plus coefficient collapse implies the TS130 reconstruction identity |
| TS132 | Selberg Mobius chain coefficient collapse ledger | `repo_committed_relative` | proves the diagonal and non-divisor chain-coefficient cases and reduces the remaining collapse to the proper-divisor quotient case |
| TS133 | Selberg proper-divisor Mobius chain collapse | `repo_committed_relative` | proves the quotient is greater than one and the quotient Mobius sum is zero, reducing the proper-divisor collapse to finite quotient reindexing |
| TS134 | Selberg proper-divisor quotient reindexing discharge | `repo_committed_relative` | proves the finite quotient reindexing by `r -> d*r`, closing the TS132/TS133 chain-coefficient collapse under only the TS131 expansion obligation |
| TS135 | Selberg finite Mobius reconstruction expansion discharge | `repo_committed` | proves the TS131 finite Fubini expansion and combines it with TS134 to close the TS130 finite reconstruction identity and optimal dense budget |
| TS136 | Selberg interval majorant ledger | `repo_committed_relative` | packages the TS135 optimal weights as the TS99 Selberg weight ledger and bridges supplied TS30 interval majorant data to TS99/TS97 |
| TS137 | Concrete Selberg interval majorant interface | `repo_committed_relative` | names the concrete interval majorant data and proof fields that instantiate TS30 and feed TS136/TS99/TS97 |
| TS138 | Concrete Selberg interval majorant formulation | `repo_committed_relative` | instantiates the TS137 data side with the finite Selberg square majorant built from TS136 optimal weights |
| TS139 | Concrete Selberg interval sieve theorem ledger | `repo_committed_relative` | proves the finite counting bridge from pointwise prime square lower bounds to the TS138 interval sieve bound |
| TS140 | Large prime admissibility | `repo_committed_relative` | proves the TS139 pointwise prime square lower bound when every interval prime is larger than the Selberg support level |
| TS141 | Concrete Selberg square majorant expansion | `repo_committed_relative` | expands the TS138 square majorant into pair-first lcm form with interval multiple counts |
| TS142 | LCM multiplicity fractional decomposition | `repo_committed_relative` | splits each TS141 lcm multiple count into its rational interval-length main term and exact remainder, then inserts the split into the full square majorant |
| TS143 | LCM multiplicity error-bound discharge | `repo_committed` | proves that every positive lcm multiple count differs from its rational interval-length main term by absolute value at most one |
| TS144 | LCM dense-side budget refactor | `repo_committed_relative` | records the `1/lcm` versus `gcd/lcm` kernel obstruction and replaces the unsupported exact-budget route by a sufficient upper bound through gcd/totient diagonalization and `totient <= J2` |
| TS145 | Euler totient diagonalization and Jordan domination | `repo_committed` | proves the gcd-kernel diagonalization by Euler's totient, proves `totient <= J2` globally, and closes the corrected LCM dense-side `1 / D` upper budget for positive levels |
| TS146 | Weighted LCM error aggregation | `repo_committed` | aggregates the TS143 local errors into `|E| <= (sum |lambda|)^2` and combines this with TS145 to bound the concrete square majorant by `intervalLength / D + (sum |lambda|)^2` |
| TS147 | Selberg optimal weight explicit formula | `repo_committed` | unfolds the reconstructed weights, proves `|lambda(m)| <= m * sum_{m|d}|Y(d)|`, reindexes the resulting finite `L1` envelope by divisors, and feeds that envelope into the TS146 square-majorant bound |
| TS148 | Selberg divisor-envelope polynomial bound | `repo_committed` | identifies the positive support with `Icc 1 level`, proves `|Y(d)| <= 1 / D` and divisor mass `<= level^2`, and obtains the explicit bound `divisorEnvelope <= level^3 / D` |
| TS149 | Selberg divisor-envelope Jordan refinement | `repo_committed` | proves `sigma_1(n) <= J2(n)`, identifies the supported divisor mass with `sigma_1(d)`, and improves the bounds to `divisorEnvelope <= level / D` and `squareMajorant <= intervalLength / D + (level / D)^2` |
| TS150 | Refined Selberg budget scale interface | `repo_committed_relative` | packages the TS149 rational bound, proves the monotone `Nat.ceil` bridge to the TS138 natural majorant, and reduces the remaining BT comparison to `ceil(refinedBudget) <= brunTitchmarshCeilBudget` |
| TS151 | Dependent Selberg scale split interface | `repo_committed_relative` | proves the fixed-level TS140/TS150 admissibility package is uninhabited because it includes `n = 0`, then replaces it by a level depending on `(x,Q)` plus separate finite-head and late-window inputs that construct the exact TS22 and TS97 objects |
| TS152 | Finite-head prime interval budget reduction | `repo_committed_relative` | proves `primeIntervalCard n h <= h+1`, reduces every head window `n <= level(x,Q)` to the cumulative count on `[0, level(x,Q)+h]`, and supplies two explicit constructors for the TS151 finite-head package |
| TS153 | Dependent Selberg budget feasibility probe | `repo_committed_relative` | splits the refined budget into principal and quadratic terms, proves each is necessarily below the TS22 ceiling, and extracts the exact requirement `(intervalScale+1)/BTceil <= D(level)` from any dependent scale comparison |
| TS154 | Selberg denominator upper-bound obstruction probe | `repo_committed` | rewrites `D(level)` as a squarefree reciprocal-Jordan sum, dominates it by a telescoping finite Euler product, proves `D(level) <= 2*level/(level+1) < 2` for positive levels, and rules out any dependent comparison whose TS153 threshold is at least `2` |
| TS155 | Brun-Titchmarsh threshold obstruction geometry | `repo_committed` | proves the exact equivalence between the TS153 threshold obstruction and `0 < BTceil` together with `2*BTceil <= intervalScale+1`, then proves every successful dependent comparison requires the strict opposite inequality |
| TS156 | Brun-Titchmarsh threshold evaluation | `repo_committed_relative` | evaluates the exact TS22 ceiling, proves the TS155 obstruction from `intervalScale >= 2` and `Real.log(Q+1) >= 16`, and specializes this finite criterion to `Q = (Nat.log 2 x)^2` |
| TS157 | Goldbach-scale eventual obstruction | `repo_committed` | proves the TS156 finite regime for every `x >= 2^3000` using a certified bound on `Real.exp 16` and `2*n^2 <= 2^n`, then rules out every dependent TS150 comparison throughout that tail |
| TS158 | Selberg/Brun-Titchmarsh obstruction closure ledger | `repo_committed` | packages TS153--TS157 into one terminal ledger naming the affected TS150 route, the formal causes, the threshold `2^3000`, and the eventual no-comparison theorem |
| TS159 | Selberg denominator refactor interface | `repo_committed` | opens the post-obstruction interface for replacement denominators, defines the abstract growing-denominator route, and proves the current TS122/Jordan-two denominator cannot satisfy any positive-level growth requirement reaching `2` |
| TS160 | Selberg phi denominator candidate | `repo_committed` | defines the prototype denominator `sum mu(d)^2 / phi(d)`, proves positivity, proves `D_phi(3) = 5/2 > 2`, and realizes the TS159 growing-denominator data interface for a finite prototype growth curve |
| TS161 | Phi pre-mortem and spectral pivot ledger | `repo_committed` | proves the TS149-style absorption `sigma_1 <= phi` is false already at `2`, archives TS160 as a useful probe rather than a completed repair, and opens the TS94/TS95 spectral-pivot front |
| TS162 | Triangle spline trace-kernel instantiation | `repo_committed` | packages the TS42 triangle spline as a concrete TS94 trace kernel, proves pointwise nonnegativity, value at the origin, and unit-support vanishing, while leaving Plancherel and the explicit formula as TS95-side obligations |
| TS163 | Triangle spline Fourier-weight candidate ledger | `repo_committed` | replaces the TS162 zero spectral-weight placeholder by a nonnegative squared-sinc candidate, packages the resulting TS94 kernel ledger, and keeps Fourier identification, Plancherel, and the explicit formula as explicit future obligations |
| TS164 | Triangle spline Fourier normalization probe | `repo_committed` | introduces a scale-parametrized squared-sinc family, proves scale-independent nonnegativity and zero-frequency normalization, shows TS163 is the unit-scale case, and keeps the Mathlib Fourier normalization constant open |
| TS165 | Triangle spline Mathlib Fourier scale ledger | `repo_committed` | probes Mathlib's real Fourier API, records the `-2*pi*x*xi` forward-kernel convention, selects the TS164 pi-scale contract, and still makes no Fourier identity, Plancherel, or explicit-formula claim |
| TS166 | Triangle spline Fourier identification reduction | `repo_committed` | defines the exact compiled Fourier-identification statement between Mathlib's Fourier integral of the complexified TS42 triangle spline and the TS165 pi-scale squared-sinc candidate, then reduces the future proof to convolution and branch-integration routes without claiming the identity |
| TS167 | Triangle spline convolution-route probe | `repo_committed` | defines the centered box, its complex lift, the manual box self-convolution, and the non-squared scaled sinc, then proves the spatial-convolution, box-Fourier, and Fourier-exchange statements would imply the TS166 Fourier target |
| TS168 | Triangle spline branch-integral route probe | `repo_committed` | defines the affine branch Fourier integrals over `[-1,0]` and `[0,1]`, gives their intended closed forms, and proves branch split plus branch evaluations plus closed-form recombination would imply the TS166 Fourier target |
| TS169 | Triangle spline branch closed-form recombination | `repo_committed` | proves the two TS168 branch closed forms recombine to the TS166 pi-scale squared-sinc target, while leaving the branch split and branch integral evaluations open |
| TS170 | Triangle spline right branch integral evaluation | `repo_committed` | proves the TS168 right branch integral evaluation over `[0,1]` by splitting zero and nonzero frequency, using a direct affine integral at zero and an explicit elementary primitive plus FTC away from zero |
| TS171 | Triangle spline left branch integral evaluation | `repo_committed` | proves the TS168 left branch integral evaluation over `[-1,0]` by mirroring TS170 with the affine branch `1+x`, an explicit elementary primitive, and FTC away from zero |
| TS172 | Triangle spline Fourier branch split | `repo_committed` | proves the TS168 global Fourier branch split by converting `Real.fourierIntegral` to the explicit global kernel integral, restricting to the spline support, splitting `[-1,1]` at `0`, and identifying the two affine branch integrals |
| TS173 | Triangle spline Fourier identification discharge | `repo_committed` | assembles the TS168 branch route from the four TS169--TS172 discharged obligations and proves the TS166 pointwise Fourier identification for the triangle spline |
| TS174 | Triangle spline Plancherel interface probe | `repo_committed` | names the triangle-spline, Fourier-side, and squared-sinc `eLpNorm` quantities, proves TS173 transports the Fourier `eLpNorm` to the sinc `eLpNorm`, and records the concrete Plancherel isometry as a future input |
| TS175 | Triangle spline spatial L2 energy evaluation | `repo_committed` | evaluates the elementary spatial square-energy integral of the triangle spline as `2/3`, splitting at `0` and using the TS56 affine branch formulae |
| TS176 | Triangle spline time L2 eLpNorm bridge | `repo_committed` | lifts the TS175 interval square-energy constant to the global Lebesgue square-energy of the real and complexified triangle spline, while leaving the final `eLpNorm` value and Plancherel as future obligations |
| TS177 | Triangle spline time eLpNorm value | `repo_committed` | converts the TS176 global complex square-energy identity into the exact TS174 time-side `eLpNorm` value `ENNReal.ofReal (Real.sqrt (2 / 3))`, while still leaving Plancherel and spectral sinc integrability open |
| TS178 | Triangle spline sinc spectral integrability | `repo_committed` | proves the TS174 pi-scale squared-sinc spectral `eLpNorm` is finite by dominating the weight with `2 * (1 / (1 + xi ^ 2))`, while still leaving Plancherel and the exact spectral norm value open |
| TS179 | Triangle spline Plancherel API probe | `repo_committed` | records the local Mathlib Plancherel API reality check and proves that a supplied TS174 Plancherel isometry gives the exact spectral value `ENNReal.ofReal (Real.sqrt (2 / 3))` |
| TS180 | Triangle spline TS94 kernel evidence ledger | `repo_committed` | packages the TS162 kernel, TS163 sinc-square weight, TS173 Fourier identity, TS177 time L2 value, TS178 spectral finiteness, and TS179 conditional Plancherel consumption as TS94-side evidence without claiming zeta-zero summability or the explicit formula |
| TS181 | Explicit formula trace blueprint | `repo_committed` | opens the TS95 front by naming the local zeta-zero, residual, trace-budget, and bridge contracts that turn the TS180 kernel evidence into a concrete explicit-formula ledger, without proving the explicit formula |
| TS182 | Triangle spline discrete sieve-trace bridge | `repo_committed` | defines the discrete smoothing weight `triangleSpline(n / X)`, proves its affine formula for `n <= X`, proves vanishing for `X <= n`, and records this as the first bridge from the continuous kernel to natural-number sums |
| TS183 | Triangle spline finite weighted prime-sum interface | `repo_committed` | turns the TS182 pointwise weight into a finite generic arithmetic sum, proves range-extension invariance, affine rewriting, and nonnegativity for nonnegative weights, then names a local von Mangoldt weight contract |
| TS184 | Triangle spline Von Mangoldt API probe | `repo_committed` | binds Mathlib's `ArithmeticFunction.vonMangoldt` to the TS183 contract and inherits nonnegativity, range-extension, and affine-support properties |
| TS185 | Explicit formula zeta zero family ledger | `repo_committed_relative` | probes Mathlib's `riemannZeta` and `riemannZeta_neg_two_mul_nat_add_one`, defines local nontrivial-zero predicate and API binding contract, and wires the contract conditionally into the TS93 zero-family ledger |
| TS186 | Triangle spline main-term normalization bridge | `repo_committed` | reuses the TS162 origin value `triangleSpline 0 = 1`, proves `X * triangleSpline 0 = X`, and normalizes the discrete origin weight for positive scales without proving the explicit formula |
| TS187 | Analytic frontier transform compatibility ledger | `repo_committed_relative` | names five analytic walls as local contract/evidence types: Wall 0 Mellin/Fourier logarithmic coordinate compatibility, Wall 1 Plancherel, Wall 2 contour explicit formula, Wall 3 zeta-zero summability, Wall 4 circle-method/Gallagher correlation; no wall is populated |
| TS188 | Triangle spline analytic Wall 1 Plancherel contract bridge | `repo_committed_relative` | wires the TS187 Wall 1 Plancherel obligation to the concrete TS174 Plancherel isometry statement and proves that supplying this evidence activates the TS179 spectral-energy transport; Plancherel itself remains unproved |
| TS189 | Logarithmic pullback Mellin Fourier interface | `repo_committed` | proves the algebraic logarithmic pullback under `x = exp u`, including log/exp round trips, triangle-spline support, affine form, and nonnegativity; keeps the measure transport `dx / x = du` and Mellin-as-Fourier equivalence as unproved Wall 0 contracts |
| TS190 | Triangle spline critical-line amplitude | `repo_committed` | specializes the TS189 amplitude to `c = 1/2`, proves nonnegativity, vanishing past `exp u >= X`, and the affine form `(1 - exp u / X) * exp(u/2)` on the support; the critical-line choice is a functional specialization, not an RH claim |
| TS191 | Critical-line amplitude energy primitive | `repo_committed_relative` | proves the support-side square expansion of the TS190 critical amplitude and evaluates the natural primitive at `log X` as `X / 3`, while keeping the improper lower-tail integral as a local contract |
| TS192 | Critical-line primitive lower-tail limit | `repo_committed` | proves that the TS191 energy primitive tends to `0` as `u -> -infty`, completing the lower-tail boundary value; the full improper-integral/FTC bridge remains separate |
| TS193 | Critical-line truncated FTC energy bridge | `repo_committed` | proves the derivative of the TS191 primitive, the finite-interval FTC identity for the expanded density, and convergence of the truncated integrals to `X / 3`; the full improper-integral object remains separate |
| TS194 | Critical-line actual amplitude energy bridge | `repo_committed` | proves that the truncated integrals of the actual TS190 critical-line amplitude squared agree eventually with the TS193 expanded-density integrals and therefore tend to `X / 3`; the standalone improper-integral object remains separate |
| TS195 | Critical-line actual improper energy object | `repo_committed` | packages the TS194 truncated actual-amplitude convergence as a named limit-based energy object with value `X / 3`, and consumes the local TS194 object contract without defining a general Lebesgue improper integral |
| TS196 | Critical-line compact change-of-variables probe | `repo_committed` | proves the compact set-integral change of variables `x = exp u` for the actual critical-line energy density, using Mathlib's one-dimensional Jacobian theorem; the full Wall 0 improper and Mellin/Fourier transports remain unproved |
| TS197 | Critical-line x-side interval convergence bridge | `repo_committed` | transfers the TS194 truncated-energy limit through the compact TS196 change of variables, proving that the x-side compact energies with lower endpoint `exp a` tend to `X / 3` as `a -> -infty`; the x-side improper object and full Wall 0 transports remain unproved |
| TS198 | Critical-line x-side improper energy object | `repo_committed` | packages the TS197 x-side convergence as a named limit-based energy object with value `X / 3`, records the equivalent `b -> 0+` convergence certificate, and consumes the local TS197 object contract without defining a general Lebesgue improper integral |
| TS199 | OTSA strategic dashboard synthesis | `repo_committed` | collects the post-TS198 sieve, critical-energy, and analytic-wall status into one governance ledger, proves the u-side and x-side energy scalars agree because both are `X / 3`, and records that trace, Mellin-tail, sieve-budget, final OTSA, and Goldbach obligations remain unproved |
| TS200 | OTSA non-circular consumption interface | `repo_committed_relative` | refactors the final OTSA interface so Goldbach is an output of a future conclusion bridge, not an input contract; registers trace, Mellin-tail, sieve-budget, final-inequality, and combinatorial-reduction obligations without proving them |
| TS201 | Strategic decision ledger | `repo_committed_relative` | records the post-TS200 open fronts and fixes the next recommended target as Wall 0 measure transport, while explicitly keeping all analytic walls, sieve replacement, bundle generation, OTSA inputs, and Goldbach unproved |
| TS202 | Wall 0 measure transport bridge | `repo_committed_relative` | refines the selected Wall 0 target into Haar measure-transport contract and evidence types, records the TS196 compact change of variables and TS198 x-side energy `X / 3` as available inputs, and keeps full Haar transport and Mellin/Fourier compatibility unproved |
| TS203 | Truncated Haar transport | `repo_committed` | proves the compact finite-endpoint Haar transport identity `int_{log epsilon}^{log X} F(exp u) du = int_epsilon^X F(x)/x dx` for continuous real test functions on positive intervals, populating only the truncated Wall 0 slot while leaving improper/global transport and Mellin/Fourier compatibility open |
| TS204 | Final analytic inputs specification | `repo_committed_relative` | defines contract/evidence types for the three final analytic input families: triangle-spline Plancherel, effective explicit formula, and Gallagher/large-sieve comparison; records TS188 conditional Plancherel transport and TS203 truncated Haar transport while leaving all final analytic evidence and Goldbach unproved |
| TS205 | Final analytic inputs to OTSA routing bridge | `repo_committed_relative` | defines the non-circular adapter from TS204 final analytic evidence to the five TS200 OTSA input slots and proves that, given this adapter plus a TS200 conclusion bridge, `BinaryGoldbachStatement` follows; no analytic input, OTSA slot, conclusion bridge, or Goldbach theorem is proved |
| TS206 | Explicit formula effective statement | `repo_committed_relative` | makes the Wall 2 effective explicit-formula target concrete for the TS184 triangle-spline von Mangoldt sum by defining main-term, zero-contribution, residual, effective-constant, and TS181-compatibility statements; no formula, bound, constants package, TS204 evidence, OTSA input, or Goldbach theorem is proved |
| TS207 | Naive Haar energy divergence obstruction | `repo_committed` | proves that the naive Haar-weighted square energy of the triangle spline dominates a logarithmically divergent comparison integral near zero; this blocks the false route from the TS198 `dx` energy `X / 3` to a Haar `dx/x` energy claim |
| TS208 | Triangle spline Plancherel evidence probe | `repo_committed_relative` | reduces the concrete Wall 1 Plancherel input to the direct scalar `sinc^4` identity `integral triangleSplineSincRealWeight^2 = 2/3`; if that identity is supplied, TS208 proves the spectral `eLpNorm` value, the TS174 Plancherel statement, and the TS204 Plancherel input evidence |
| TS209 | Triangle spline sinc-fourth scale reduction | `repo_committed_relative` | removes the Wall 1 normalization ambiguity by proving that the canonical unscaled scalar identity `integral canonicalSincSq^2 = (2*pi)/3` implies the TS208 pi-scaled identity `integral triangleSplineSincRealWeight^2 = 2/3`, and therefore would populate the TS204 Plancherel evidence |
| TS210 | Box convolution triangle evidence | `repo_committed` | proves the TS167 spatial convolution statement by evaluating the manual self-convolution of the centered unit box: the overlap length is zero outside `[-1, 1]`, `1 + x` on `[-1, 0]`, and `1 - x` on `[0, 1]`, matching the TS56 triangle-spline branches after complex coercion |
| TS211 | Box Fourier evaluation | `repo_committed` | proves the TS167 box Fourier evaluation statement directly: Mathlib's Fourier transform of the centered unit box equals the non-squared pi-scaled sinc profile, by reducing the global integral to `[-1/2, 1/2]` and evaluating the zero and nonzero frequency cases with `integral_exp_mul_complex` |
| TS212 | Box Fourier convolution exchange | `repo_committed` | proves the TS167 specialized Fourier-convolution exchange statement for the centered unit box by comparing both sides with closed forms: TS210 rewrites the self-convolution as the triangle spline, TS173 evaluates the triangle Fourier transform, TS211 evaluates the box Fourier transform, and TS167 squares sinc into squared-sinc |
| TS213 | Canonical sinc-fourth direct Dirichlet route | `repo_committed_relative` | defines the non-Plancherel scalar Dirichlet/IPP route to the TS209 canonical `sinc^4` value, and proves that the derivative formula, Dirichlet sine integral, triple IPP, scaling, and evenness obligations would imply both the canonical identity and the TS204 Plancherel input evidence |
| TS214 | Cos-square third derivative formula discharge | `repo_committed` | proves the first TS213 scalar obligation by calculating the first, second, and third derivatives of `(1 - cos x)^2`, obtaining the required formula `-2 * sin x + 4 * sin (2*x)` for the triple-IPP route |
| TS215 | Dirichlet sine integral API probe | `repo_committed_relative` | probes the positive-half-line Dirichlet sine integral API: records that no ready-made `sin x / x` value was located locally, proves Mathlib's `integral_comp_mul_left_Ioi` scaling API is available, and reduces the TS213 Dirichlet slot to a unit-frequency value plus positive-frequency scaling |
| TS216 | Dirichlet unit-frequency value probe | `repo_committed_relative` | focuses the TS215 unit-frequency side: identifies the frequency-one kernel as `sin x / x`, records the current Lebesgue target, and names cutoff-improper and Abel-regularized targets without claiming the Dirichlet value |
| TS217 | Dirichlet improper reformulation bridge | `repo_committed_relative` | archives the old Lebesgue Dirichlet target as legacy, promotes cutoff-improper and Abel-regularized formulations as the official future targets, and defines cutoff/Abel evidence wrappers without proving either route |
| TS218 | Sinc-fourth scaling and evenness discharge | `repo_committed` | discharges the two elementary TS213 scalar obligations independent of Dirichlet and triple IPP: the half-line scaling identity from `x = 2*u`, the full-line evenness identity, and the supporting global integrability of the canonical `sinc^4` kernel via TS178 and TS209 |
| TS219 | Cos-square triple IPP cutoff reformulation | `repo_committed_relative` | archives the old TS213 Lebesgue triple-IPP statement as legacy and replaces it with a cutoff route: finite IPP on `[eps, T]`, explicit boundary terms, boundary vanishing, third-derivative cutoff value `pi`, and an explicit fail-closed assembly bridge |
| TS220 | Cos-square IPP primitive derivative bridge | `repo_committed_relative` | proves the local derivative identity for the explicit primitive behind the finite triple-IPP route: for `x != 0`, `P'(x) = cosSquareHaarKernel x - (1/6) * cosSquareThirdDerivativeKernel x`; finite IPP, primitive-jump boundary matching, boundary vanishing, and cutoff values remain open |
| TS221 | Cos-square finite triple IPP discharge | `repo_committed` | proves the TS219 finite cutoff triple-IPP statement by identifying the TS220 primitive with the three TS219 boundary terms, applying the finite-interval FTC on `[eps, T]`, splitting the integral of `Haar - (1/6)*Deriv3`, and rewriting the primitive jump as the boundary sum |
| TS222 | Cos-square boundary vanishing reduction bridge | `repo_committed_relative` | reduces the TS219 product-filter boundary vanishing statement to the two one-variable asymptotic estimates `P(T) -> 0` at `+infty` and `P(eps) -> 0` as `eps -> 0+`, using the TS221 identity `P(T)-P(eps)=boundarySum eps T`; the asymptotic estimates themselves remain open |
| TS223 | Cos-square IPP primitive atTop asymptotic | `repo_committed` | proves the first TS222 primitive asymptotic, `P(T) -> 0` as `T -> +infty`, by bounding the three trigonometric coefficients in the TS220 primitive and multiplying them by `x^(-3)`, `x^(-2)`, and `x^(-1)`; the zero-right asymptotic and full boundary vanishing remain open |
| TS224 | Cos-square IPP primitive zero-right asymptotic | `repo_committed` | proves the second TS222 primitive asymptotic, `P(eps) -> 0` as `eps -> 0+`, using local bounds `|f| <= x^4/4`, `|f'| <= x^3`, `|f''| <= 3*x^2`, and `|P(x)| <= (3/4)*x`; combines TS223 and TS224 through TS222 to prove TS219 boundary vanishing |
| TS225 | Third-derivative cutoff value reduction | `repo_committed_relative` | reduces the TS219 third-derivative cutoff value to product-filter Dirichlet cutoff values at frequencies `1` and `2`; proves the pointwise kernel decomposition and the `-2*(pi/2)+4*(pi/2)=pi` Tendsto combination, while leaving finite linearization and Dirichlet convergence as explicit future obligations |
| TS226 | Third-derivative finite linearization discharge | `repo_committed` | proves the compact interval-integral algebra left open by TS225: eventually on the TS219 cutoff filter, `int cosSquareThirdDerivativeKernel = -2*int sineDirichletKernel 1 + 4*int sineDirichletKernel 2`; Dirichlet product-filter convergence remains open |
| TS227 | Dirichlet product-cutoff scaling reduction | `repo_committed_relative` | proves that every positive-frequency product-filter Dirichlet cutoff value follows from the unit-frequency value, by scaling `(eps, T)` to `(a*eps, a*T)` and proving the finite interval change of variables; the unit-frequency Dirichlet cutoff value remains open |
| TS228 | Dirichlet product-cutoff partial-integral bridge | `repo_committed_relative` | reduces the single unit-frequency product-filter Dirichlet value to the one-sided partial-integral limit `int_0^T sin x / x -> pi/2`; proves the finite decomposition `int_eps^T = F(T)-F(eps)`, the bound `|F(eps)| <= |eps|`, and the lower-end limit `F(eps) -> 0`; the atTop Dirichlet value remains open |
| TS229 | Dirichlet exponential regularization setup | `repo_committed_relative` | prepares the Abel route by defining the damped unit Dirichlet kernel and target evaluation, proves the scalar limit `pi/2 - arctan b -> pi/2` as `b -> 0+`, and routes future Abel evidence to the TS228 atTop target, TS227 unit cutoff value, and TS219 third-derivative cutoff value; the damped integral evaluation and Abel-to-cutoff bridge remain open |
| TS230 | Damped Dirichlet evaluation reduction | `repo_committed_relative` | refines the TS229 Abel route by proving the scalar arctangent tail `int_b^A 1/(1+s^2) ds -> pi/2 - arctan b` as `A -> +infty`, and reduces the damped Dirichlet evaluation target to the Laplace sine transform plus a Fubini/arctangent bridge; those two analytic inputs remain open |
| TS231 | Laplace sine transform discharge | `repo_committed` | proves the TS230 Laplace sine transform input by an explicit primitive for `exp(-s*x) * sin x`, finite-interval FTC, and exponential boundary decay for `s > 0`; the Fubini/arctangent bridge and Abel-to-cutoff bridge remain open |
| TS232 | Damped Dirichlet Fubini bridge reduction | `repo_committed_relative` | records the corrected interval-integral Fubini route after TS231, restates the TS229 damped partial-integral target, isolates compact Fubini, uniform boundary, damped-difference, and auxiliary high-damping obligations, and proves that a future TS230 Fubini bridge plus TS231 supplies the damped evaluation target; the Fubini bridge and Abel-to-cutoff bridge remain open |
| TS233 | Compact Fubini identity discharge | `repo_committed` | proves the TS232 compact Fubini identity on `[b, A] x [0, T]` by a parameter primitive, rectangle integrability, Fubini swap, and interval-integral rewrites; uniform boundary, damped-difference, auxiliary damping, Abel-to-cutoff, and final Dirichlet cutoff value remain open |
| TS234 | Laplace boundary uniform limit discharge | `repo_committed` | proves the TS232 uniform vanishing of the integrated TS231 boundary term over compact parameter intervals `[b, A]`, by bounding the kernel by a constant multiple of `exp(-b*T)` and squeezing the interval integral to zero; damped-difference, auxiliary damping, corrected Fubini execution, Abel-to-cutoff, and final Dirichlet cutoff value remain open |
| TS235 | Damped difference atTop discharge | `repo_committed` | proves the TS232 damped-difference limit by integrating the TS231 finite Laplace formula over `[b, A]`, using the TS230 arctangent primitive, applying the TS234 boundary limit, and rewriting by the TS233 compact Fubini identity eventually on `atTop`; auxiliary damping, corrected Fubini execution, Abel-to-cutoff, and final Dirichlet cutoff value remain open |
| TS236 | Auxiliary damping uniform bound discharge | `repo_committed` | proves the TS232 high-damping estimate `|dampedPartialIntegral A T| <= 1 / A` for `0 < A` and `0 <= T` by dominating the damped Dirichlet kernel by `exp((-A)*x)`, evaluating the finite exponential majorant integral, and using `exp((-A)*T) <= 1`; corrected Fubini execution, damped evaluation, Abel-to-cutoff, and final Dirichlet cutoff value remain open |
| TS237 | Corrected Fubini execution assembly | `repo_committed` | proves the TS232 corrected Fubini execution statement by combining TS233--TS236, then derives the TS230 Fubini bridge and the TS229 damped Dirichlet evaluation target; the Abel-to-cutoff bridge and final ordinary Dirichlet cutoff value remain open |
| TS238 | Abel-to-cutoff bridge frontier | `repo_committed_relative` | records that TS237 proves the damped Abel evaluation and TS229 proves the scalar Abel limit, exposes the remaining Abel-to-cutoff bridge as the unique Tauberian input, and proves that supplying this bridge activates TS228, TS227, and the TS219 third-derivative cutoff value; the bridge itself and final ordinary Dirichlet cutoff value remain open |
| TS239 | Dirichlet cutoff API and direct route probe | `repo_committed_relative` | records a bounded probe of the locked Mathlib cutoff API, notes that `Real.sinc` and a direct Dirichlet cutoff theorem were not located in the probed modules, defines a local `normalizedSinc` surrogate, proves its interval integrals agree with the TS228 repository partial integrals, and exposes the direct tail-bound route as the next fallback target; the cutoff value, Abel-to-cutoff bridge, cos-square value, sinc-fourth value, Plancherel, and Goldbach remain open |
| TS240 | Dirichlet tail bound discharge | `repo_committed` | proves the TS239 quantitative direct-route fallback `|F(U)-F(T)| <= 2/T` for `0 < T <= U` by applying FTC to the primitive `-cos x / x`, evaluating `int_T^U x^-2 dx = 1/T - 1/U`, and using `|cos x| <= 1`; Cauchy convergence, the cutoff value, Abel-to-cutoff bridge, cos-square value, sinc-fourth value, Plancherel, and Goldbach remain open |
| TS241 | Dirichlet cutoff Cauchy convergence discharge | `repo_committed` | uses the TS240 tail bound to prove that the unit Dirichlet partial integral is a Cauchy sequence along `atTop`, extracts a canonical real cutoff limit by completeness of `Real`, and proves convergence to that limit; the value `pi/2`, Abel identification, Abel-to-cutoff bridge, cos-square value, sinc-fourth value, Plancherel, and Goldbach remain open |
| TS242 | Dirichlet Abel summation identity discharge | `repo_committed` | proves the finite Abel summation identity `D_b(T) = exp(-b*T)*F(T) + b*int_0^T exp(-b*x)*F(x) dx` for `0 < b` and `0 <= T`, proves continuity/Lipschitz support for `F`, and proves `exp(-b*T)*F(T) -> 0` from TS241 convergence plus exponential decay; the value `pi/2`, Abel identification, Abel-to-cutoff bridge, cos-square value, sinc-fourth value, Plancherel, and Goldbach remain open |
| TS243 | Dirichlet cutoff Abel final-value identification | `repo_committed` | proves the local Abel final-value theorem for the already convergent TS241 cutoff partial integral, identifies `dirichletCutoffLimit = pi/2`, proves the TS228 unit one-sided cutoff target, and closes the TS229/TS238 Abel-to-cutoff bridge; cos-square value, sinc-fourth value, Plancherel, and Goldbach remain open |
| TS244 | Dirichlet product-cutoff and third-derivative discharge | `repo_committed` | applies TS243 through the TS228 product-filter bridge and TS227 positive-frequency scaling, proves the product-cutoff value `pi/2` for every positive Dirichlet frequency, and closes the TS219 third-derivative cutoff value `pi`; improper cutoff convergence, TS219 cutoff assembly, cos-square value, sinc-fourth value, Plancherel, and Goldbach remain open |
| TS245 | Cos-square improper cutoff assembly | `repo_committed` | transports TS218 integrability to the cos-square Haar kernel, proves the TS219 product-filter cutoff convergence to the Lebesgue half-line integral, combines TS221 finite IPP, TS224 boundary vanishing, and TS244 residual value `pi`, and proves `cosSquareImproperIntegral = pi/6`; sinc-fourth value, Plancherel, and Goldbach remain open |
| TS246 | Canonical sinc-fourth assembly | `repo_committed` | applies the TS213 algebraic assembly to the TS245 value `cosSquareImproperIntegral = pi/6` and the TS218 scaling/evenness identities, proving the TS209 canonical full-line value `2*pi/3`; concrete TS204 Plancherel evidence, the explicit formula, Gallagher, and Goldbach remain open |
| TS247 | Triangle-spline Plancherel evidence assembly | `repo_committed` | consumes the TS246 canonical sinc-fourth value through the TS209/TS208 bridge, constructs the concrete TS204 triangle-spline Plancherel evidence, proves the specialized TS174 isometry, and exposes the exact pi-scaled spectral energy; a general Plancherel theorem, the explicit formula, Gallagher, and Goldbach remain open |
| TS248 | Wall 1 final analytic input consumption | `repo_committed` | fixes the TS204 Plancherel contract to the concrete TS247 evidence, reduces final analytic evidence construction to the effective explicit-formula and Gallagher evidence families, specializes the reduction to the TS206 contract family, and composes supplied remaining evidence through TS205 into TS200 OTSA inputs and the separate conditional conclusion bridge; the explicit formula, Gallagher, both OTSA bridges, and Goldbach remain open |
| TS249 | Effective explicit-formula constants discharge | `repo_committed` | constructs a flexible TS206 constants family from nonnegative `NNReal` constants and a positive-by-construction lower scale, proves constants admissibility, packages the remaining four analytic fields as core evidence, and routes core plus TS181 compatibility and Gallagher through TS248; the explicit-formula identity and bounds, TS181 compatibility, Gallagher, both OTSA bridges, and Goldbach remain open |
| TS250 | Explicit-formula structural compatibility discharge | `repo_committed` | audits the exact TS206 compatibility proposition, constructs a minimal TS181 inhabitant, closes that structural field, and reduces TS206 evidence to the four analytic core fields; the sprint explicitly records that effective TS206-to-TS181 alignment and an actual zeta-zero family are not encoded by the current compatibility type |
| TS251 | Explicit-formula main-term contract obstruction | `repo_committed` | constructs shifted explicit-formula data satisfying the current TS206 identity while changing the main term, proves that the universal main-term identification field is false for every admissible constants package, proves the TS249 core evidence uninhabited, and defines a corrected joint identity-and-main-term witness target; the corrected contract is not yet installed |
| TS252 | Corrected explicit-formula contract installation | `repo_committed` | installs a parallel TS204 contract whose identity and main-term slots share the TS251 existential witness, retains the TS206 zero and residual bound shapes, constructs corrected evidence, and routes corrected core plus Gallagher through TS248; TS206 remains unchanged and no bridge to its impossible contract is claimed |
| TS253 | Explicit-formula bounds contract obstruction | `repo_committed` | constructs identity- and main-term-preserving data that exceed each retained TS206 majorant, proves both universal bound statements false at every positive lower scale, proves the TS251 corrected core and TS252 corrected evidence uninhabited for admissible constants, and defines a fully corrected single-witness formula target; the fully corrected contract is not yet installed |
| TS254 | Fully corrected explicit-formula contract installation | `repo_committed` | installs a parallel TS204 contract whose four analytic slots are definitionally the same TS253 single-witness statement, constructs generic and TS249/TS250-specialized evidence routes through the TS248 Wall 1 bundle, and leaves the full analytic witness, Gallagher, both OTSA bridges, and Goldbach explicitly open; TS206 and TS252 remain unchanged |
| TS255 | Fully corrected explicit-formula analytic decomposition | `repo_committed` | defines named zero and residual functions, builds canonical TS206 data with the main term fixed definitionally, expresses identity and both bounds through the existing TS206 predicates on that same data, and proves typed assembly into the TS253 core and TS254 evidence; neither named function nor any analytic identity or bound is constructed or proved |
| TS256 | Riemann-zeta zero truncated contribution | `repo_committed` | connects the TS185 zero-family API to a scale-dependent complete `Finset Complex` truncation, defines a multiplicity-weighted finite complex sum with abstract spectral summand and its real TS255 zero function, proves listed elements are nontrivial zeta zeros, and routes supplied identity and bounds into TS255/TS253; the API contract, finite truncation, concrete summand, reality, and all analytic estimates remain open |
| TS257 | Triangle-spline Mellin spectral summand | `repo_committed` | defines the positive Mellin kernel `1/(s*(s+1))`, its unevaluated Bochner interval integral, the correctly signed TS256 summand `X^rho/(rho*(rho+1))`, and the opposite contour-residue term; proves the partial fraction identity, denominator nonvanishing at TS185 nontrivial zeros, closed forms, and TS256 routing, while Mellin evaluation, conjugation, contour identification, and all estimates remain open |
| TS258 | Zero-summand conjugation and finite reality | `repo_committed` | proves conjugation compatibility of the concrete TS257 summand and conjugation closure of every complete TS256 truncation; under the explicitly named and still open TS185 multiplicity-conjugation premise, proves the weighted finite sum is fixed by conjugation, has zero imaginary part, and is recovered exactly from its TS255 real projection; no zero estimate or explicit formula is claimed |
| TS259 | Zero-multiplicity conjugation extension | `repo_committed` | installs an honest wrapper carrying a base TS185 contract and the missing multiplicity-conjugation proof, then consumes TS258 to obtain finite-sum reality and lossless real projection without a floating premise; proves exact transport from the TS255 real absolute value to the complex spectral modulus, while TS185 remains unchanged and no concrete enriched contract or analytic estimate is constructed |
| TS260 | Riemann-zeta vanishing-order realization | `repo_committed` | proves `riemannZeta` analytic at every TS185 selected zero, defines its canonical `AnalyticAt.order : ENat`, exposes Mathlib's local factorization characterization, and installs a contract identifying TS185 multiplicity with that finite order; reduces multiplicity conjugation and all TS259 reality consequences to one named analytic order-conjugation target, which remains open |
| TS261 | Riemann-zeta vanishing-order conjugation reduction | `repo_committed` | proves generic transport of `AnalyticAt.order` through `z |-> star (f (star z))`, handling both locally-zero and finite-order branches by neighborhood and factorization transport; reduces the TS260 zeta target to double-conjugation analyticity plus Schwarz reflection, and routes supplied inputs and a realization through TS259/TS258 without constructing either analytic input |
| TS262 | Double-conjugation analyticity | `repo_committed` | proves the exact derivative formula for `z |-> star (f (star z))` by restricting complex derivatives to real scalars, composing with `Complex.conjCLE`, and lifting back through `hasFDerivAt_of_restrictScalars`; derives the full local analytic equivalence, discharges the first TS261 input, and reduces all downstream zeta-order and finite-reality results to Schwarz reflection alone |
| TS263 | Riemann-zeta Schwarz reflection | `repo_committed` | proves Schwarz reflection first on `1 < re s` by termwise conjugation of the Dirichlet series, extends equality across `Complex \ {1}` by the analytic identity principle, checks Mathlib's real assigned value at one, assembles the complete TS261 input, and routes every future concrete order realization to conjugate multiplicities and lossless finite zero-sum reality; no concrete zero family, realization, explicit formula, bound, Gallagher estimate, or Goldbach statement is constructed |
| TS264 | Concrete Riemann-zeta zero family realization | `repo_committed` | instantiates the TS185 family with the actual nontrivial zeros of `riemannZeta`, proves their analytic order finite and nonzero, defines positive natural multiplicity by `order.toNat`, proves conjugation and functional-equation symmetry, builds the concrete TS260 realization, and obtains reality and lossless projection for every future valid TS256 truncation; global summability, exact enumeration, a concrete truncation, the explicit formula, all bounds, Gallagher, and Goldbach remain open |
| TS265 | Concrete finite-height zero truncation | `repo_committed` | proves the global `riemannZeta` zero set closed and discrete using isolated zeros away from one and the zeta residue at one, derives finite intersection with compact sets, proves the concrete nontrivial zeros below every real height finite, constructs the exact noncomputable `Finset` and TS256 truncation with height `X`, and obtains real finite spectral sums with lossless projection; no numerical enumeration, zero-counting bound, density theorem, spectral bound, explicit formula, Gallagher estimate, or Goldbach statement is constructed |
| TS266 | Concrete finite zero-sum triangle majorization | `repo_committed` | names the exact multiplicity-weighted TS257 terms and their finite norm mass, proves the complex truncated sum and the real TS255 zero contribution bounded by that mass, and reduces an effective contribution bound to a nonnegative uniform per-term majorant plus a real zero-counting majorant; neither analytic majorant, a density theorem, the explicit formula, a residual bound, Gallagher, nor Goldbach is proved |
| TS267 | Exact finite uniform spectral-term bound | `repo_committed` | packages every selected weighted-term magnitude in `NNReal`, takes its exact finite supremum, proves this is the least TS266 uniform bound, names exact real cardinality, and derives an unconditional exact-cardinality-times-exact-supremum contribution bound; both functions remain noncomputable and no closed-form term estimate, effective zero count, density theorem, explicit formula, residual bound, Gallagher estimate, or Goldbach statement is proved |
| TS268 | Natural-scale complex-power bound | `repo_committed` | proves `abs ((X : Complex)^rho) <= max 1 X` for every concrete nontrivial zero and `<= X` when `1 <= X`, factors each TS266 weighted term into scale and multiplicity-denominator components, takes the exact finite supremum of the residual factor, fills a scale-visible TS266 uniform bound, and derives exact- or arbitrary-count contribution bounds; no RH, effective multiplicity or denominator estimate, zero-counting theorem, explicit formula, Gallagher estimate, or Goldbach statement is used or proved |
| TS269 | Imaginary-square denominator bound | `repo_committed` | proves the universal geometric estimate `abs rho.im ^ 2 <= Complex.abs (rho * (rho + 1))`, derives quadratic decay of the multiplicity-denominator factor when `1 <= abs rho.im`, partitions the exact TS265 selection into disjoint low and high zones, and bounds the real zero contribution by an exact low mass plus a high quadratic envelope; no low-zero exclusion, multiplicity estimate, zero-counting theorem, global summability, explicit formula, Gallagher estimate, or Goldbach statement is used or proved |
| TS270 | High-zone multiplicity counting interface | `repo_committed` | defines exact multiplicity counts below arbitrary height and in the TS269 high zone, proves the high count bounded by the full count up to height `X`, factors the high quadratic mass into natural scale times weighted residual mass, proves that residual mass bounded by the exact high multiplicity count, and transports every future high-zone or global multiplicity-counting bound to the real zero contribution; no zero-simplicity assumption, effective count, density theorem, global summability, explicit formula, Gallagher estimate, or Goldbach statement is used or proved |
| TS271 | Height-shell partial summation | `repo_committed` | defines exact finite shells `(A,B]`, proves their natural and real multiplicity-count increments, bounds each shell residual mass by its count divided by `A^2`, proves a reusable finite Abel identity, and transports every TS270 global counting bound to an amortized reciprocal-square shell estimate; no concrete high-zone cover, effective count, infinite convergence, explicit formula, Gallagher estimate, or Goldbach statement is used or proved |
| TS272 | High-zone integer shell cover | `repo_committed` | instantiates the shifted integer height chain, proves consecutive-shell additivity and telescoping, isolates the exact boundary `abs rho.im = 1`, partitions the complete TS269 high selection into boundary plus `(1,X]`, and transports every TS270 global count bound through the TS271 amortized estimate to the full real zero contribution; no effective count, density theorem, infinite convergence, explicit formula, Gallagher estimate, OTSA bridge, or Goldbach statement is used or proved |
| TS273 | Log-linear multiplicity-counting reduction | `repo_committed` | defines the safe global envelope `C * max T 1 * log(max T 1 + 2)`, proves exact multiplicity counts monotone, reduces this TS270 global contract to a large-height estimate `N_mult(T) <= C*T*log(T+2)`, isolates a future Jensen-disk input, and transports either analytic input through TS272 to the full finite zero contribution; no Jensen backport, concrete xi function, effective constant, infinite convergence, explicit formula, Gallagher estimate, OTSA bridge, or Goldbach statement is used or proved |
| TS274 | Minimal Jensen inequality backport | `repo_committed` | proves the functional finite counting core of Jensen's inequality: every selected inner-disk zero has weight at least `log(R/r)`, hence any weighted Jensen upper bound yields the standard multiplicity-count quotient; isolates only the missing circle-average boundary estimate and does not claim the complete modern divisor theorem, a concrete xi function, an effective zero count, the explicit formula, Gallagher, OTSA, or Goldbach |
| TS275 | Finite Jensen polynomial factorization reduction | `repo_committed` | installs buffered geometry `0 < r < R < S`, separates inner counted zeros from the complete factor family, proves the concrete multiplicity-weighted zero polynomial analytic with its exact zero set and Jensen mass identity, derives nonvanishing on the collar from `f = P*g`, and reduces the TS274 boundary estimate to named linear-factor and quotient angular means plus a boundary norm bound; no concrete factorization, mean-value theorem, xi function, effective count, explicit formula, Gallagher, OTSA, or Goldbach is claimed |
| TS276 | Linear-factor angular average | `repo_committed` | proves by the locked Mathlib Cauchy formula that every root strictly inside a positive circle satisfies `average_theta log |c + R exp(i theta) - rho| = log R`, establishes interval integrability, and constructs the complete TS275 `LinearFactorAngularAverageStatement`; no Fourier-series interchange, quotient mean-value theorem, concrete factorization, xi function, effective count, explicit formula, Gallagher, OTSA, or Goldbach is claimed |
| TS277 | Nonvanishing quotient holomorphic-log reduction | `repo_committed` | proves `log |g|` angularly integrable from the TS275 buffered data alone, packages an explicit analytic logarithm `L` with `exp L = g`, proves its complex mean by Cauchy and transports real parts to construct `NonvanishingQuotientAngularAverageStatement`; construction of `L` from `g_analytic` and `g_nonzero` remains a named open statement, and no concrete factorization, xi function, effective count, explicit formula, Gallagher, OTSA, or Goldbach is claimed |
| TS278 | Holomorphic primitive on a ball backport | `repo_committed` | backports the missing open-ball primitive theorem using an axis-parallel wedge integral, locked rectangle Cauchy-Goursat, and explicit horizontal and vertical little-o estimates, proving every complex-differentiable `Complex -> Complex` function on a ball has a primitive there; no closed-ball uniform extension, quotient logarithm, complete Jensen theorem, xi function, effective count, explicit formula, Gallagher, OTSA, or Goldbach is claimed |
| TS279 | Buffered quotient holomorphic-log construction | `repo_committed` | proves the analytic-and-nonzero locus open, uses compactness and the exact thickening identity to enlarge the TS275 closed disk uniformly, applies TS278 to `deriv g / g`, proves `g*exp(-P)` constant, constructs `P-P(center)+log(g(center))` with exponential exactly `g`, closes the TS277 construction statement and quotient angular mean, and reduces TS274 to the remaining boundary norm input; no concrete factorization, xi growth bound, effective count, explicit formula, Gallagher, OTSA, or Goldbach is claimed |
| TS280 | Canonical boundary norm | `repo_committed` | defines the boundary norm value set as the continuous real image of the compact averaging sphere, takes the canonical noncomputable majorant `max 1 (sSup values)`, proves it fills `BoundaryNormOnAveragingSphereStatement`, and exposes direct weighted-Jensen and multiplicity-count quotient facades for every supplied buffered TS275 datum; no concrete factorization, computable majorant, effective radius growth, xi function, effective count, explicit formula, Gallagher, OTSA, or Goldbach is claimed |
| TS281 | Polynomial buffered Jensen realization | `repo_committed` | constructs a genuine TS275 buffered factorization for every finite zero polynomial by taking `f = P` and `g = 1`, proves the explicit finite-product boundary majorant `max 1 (product (R + abs(rho-c))^m)`, routes it through TS279 and TS274 to a complete Jensen estimate and multiplicity-count quotient, and proves the TS280 canonical norm is no larger; no Riemann xi factorization, xi growth estimate, zeta-zero count, explicit formula, Gallagher, OTSA, or Goldbach is claimed |
| TS282 | Riemann xi candidate and buffered specification | `repo_committed` | defines the correct affine xi candidate from Mathlib's entire regularized completed zeta, proves entirety, endpoint values, functional equation, and agreement with standard completed-zeta xi away from `0,1`, replaces phantom contracts by an exact TS275 disk/zero/local-normal-form specification, converts it to `JensenFactorZeroData`, and routes every supplied analytic nonvanishing quotient assembly through TS280; finite xi zeros, normal forms, quotient assembly, xi/zeta zero correspondence, effective growth, zero counting, explicit formula, Gallagher, OTSA, and Goldbach remain open |
| TS283 | Riemann xi finite zero geometry | `repo_committed` | proves the xi-candidate zero set closed and discrete and finite on every compact, constructs exact closed-ball zero `Finset`s, and for every positive inner radius builds explicit `r < R < S` buffered Jensen geometry with exact inner/factor selections and a zero-free closed collar `[R,S]`; multiplicities, local normal forms, quotient assembly, effective xi growth, zero counting, explicit formula, Gallagher, OTSA, and Goldbach remain open |
| TS284 | Riemann xi multiplicity and local normal form | `repo_committed` | defines the canonical natural xi multiplicity by `AnalyticAt.order.toNat`, proves the order finite everywhere and positive at every xi zero, extracts the exact analytic nonvanishing local factor through `order_eq_nat_iff`, and enriches every TS283 geometry datum into the genuine TS282 `XiFiniteZeroFactorizationSpec`; finite quotient assembly, effective xi growth, zero counting, explicit formula, Gallagher, OTSA, and Goldbach remain open |

TS151 records a necessary correction to the TS150 assembly route.  The TS140
structure asks a positive fixed level to satisfy `level < n` for every
`n < x + 1`; choosing `n = 0` makes that package impossible.  TS151 proves
this obstruction in Lean, introduces `SelbergLevelSelection := Nat -> Nat ->
Nat`, and splits the natural-interval theorem into a finite head
`n <= level x Q` and a late-window branch `level x Q < n`.  Supplying the
dependent refined-budget comparison and the finite-head bound now constructs
`BrunTitchmarshNatIntervalBound` directly and therefore the TS97 final input.

TS152 closes the finite combinatorics of the head branch.  The crude route
uses the sufficient contract `intervalScale + 1 <= brunTitchmarshCeilBudget`.
The sharper route replaces all head windows by the single cumulative count
`primeIntervalCard 0 (level x Q + intervalScale x Q)`.  TS152 does not claim
the crude comparison: the TS22 budget is logarithmically smaller than total
interval cardinality for large `Q`, so a genuine prime-count estimate remains
necessary.

TS153 diagnoses the late-window comparison before any concrete level is
selected.  It proves that the TS150 contract forces both the principal term
and the quadratic error below the natural Brun-Titchmarsh ceiling.  In
particular, the denominator must satisfy the exact ceiling-aware condition
`(intervalScale x Q + 1) / brunTitchmarshCeilBudget x Q <= D(level)`.  This
replaces informal logarithmic approximations with a theorem that can be tested
against future effective bounds for `D`.

TS154 performs that test without introducing an asymptotic assumption.  The
Mobius square restricts `D(level)` to squarefree integers, which inject into
the divisors of the product of all primes up to `level`.  Multiplicativity of
the reciprocal Jordan-two function turns the divisor sum into a finite Euler
product, and enlarging from primes to all integers gives the telescoping bound
`D(level) <= 2 * level / (level + 1) < 2`.  Hence every successful dependent
TS151 comparison forces the exact TS153 threshold to be strictly below `2`;
if that threshold is at least `2` at one admissible `(x,Q)`, the late-window
comparison is impossible for every level selection.  The cumulative head
prime-count obligation from TS152 remains separate.

TS155 converts the rational TS153/TS154 obstruction into exact natural-number
geometry.  The threshold is at least `2` exactly when the TS22 ceiling is
positive and `2 * brunTitchmarshCeilBudget x Q <= intervalScale x Q + 1`.
Every successful dependent comparison therefore forces the strict inequality
`intervalScale x Q + 1 < 2 * brunTitchmarshCeilBudget x Q`.  The opposite
inequality rules out every level selection at that admissible `(x,Q)`.  TS155
does not yet prove that this obstruction occurs eventually under
`Q = (Nat.log 2 x)^2`; that quantitative evaluation is the next separate
task.

TS156 begins that quantitative evaluation with the exact TS22 definition
`BTceil = ceil(4 * intervalScale / Real.log(Q+1))`.  It proves that
`intervalScale >= 2` and `Real.log(Q+1) >= 16` force
`2 * BTceil <= intervalScale + 1`, including the natural ceiling error.  It
then specializes the result to the actual Goldbach scale under the explicit
finite regime `2 * (Nat.log 2 x)^2 <= x` and
`Real.exp 16 <= ((Nat.log 2 x)^2 : Real) + 1`.  TS156 does not yet prove that
this regime holds eventually or optimize its numerical threshold.

TS157 closes that eventual-regime obligation with the coarse explicit
threshold `2^3000`.  Mathlib's certified rational estimate on `Real.exp 1`
gives `Real.exp 16 < 9,000,001 = 3000^2 + 1`.  The natural logarithm Galois
connection gives `3000 <= Nat.log 2 x` from `2^3000 <= x`, while the elementary
inductive bound `2*n^2 <= 2^n` for `n >= 8` gives
`2 * (Nat.log 2 x)^2 <= x`.  Therefore the TS156 Goldbach obstruction regime
holds for every `x >= 2^3000`, and no dependent level selection can satisfy
the current TS150 comparison on that tail.  This is an impossibility theorem
for the current Jordan-two denominator and budget interface, not for every
possible Selberg sieve formulation.

TS158 packages the obstruction as a final closure ledger.  It names the
affected route as the TS150 refined Selberg budget comparison into the TS22
ceiling, records the causes `D(level) < 2`, threshold geometry, and eventual
Goldbach-scale triggering, and exposes a single terminal theorem:
for every dependent level selection and every `x >= 2^3000`, the current
TS150 comparison is impossible.  This closes the current Selberg/BT branch as
an audited obstruction, while leaving denominator refactoring, budget
refactoring, and the TS152 cumulative head obligation as separate choices.

TS159 opens the denominator-refactor interface after that obstruction.  It
does not change TS122 or reopen the failed TS150 route; instead it defines
`SelbergGrowingDenominatorData` and `RefactoredSelbergBTComparisonRoute` as the
contract any repaired Selberg denominator must satisfy.  It also proves the
diagnostic `current_jordanTwo_denominator_not_growing`: any growth interface
requiring a lower bound at least `2` on positive levels is incompatible with
the current TS122 Jordan-two denominator, by instantiating TS154 at `level = 1`.
The result is packaged in `SelbergDenominatorRefactorInterfaceLedger`, making
the next fork explicit: supply a new denominator that escapes the TS154 cap,
or pivot away from this Selberg route.

TS160 tests the first arithmetic replacement candidate:
`D_phi(level) = sum_{1 <= d <= level} mu(d)^2 / phi(d)`.  It keeps the
Mobius-square support but replaces the Jordan-two penalty by Euler's totient.
The sprint proves positivity, computes `D_phi(3) = 5/2`, and therefore shows
that this candidate crosses the old `D < 2` barrier.  It also instantiates the
TS159 `SelbergGrowingDenominatorData` interface for the prototype requirement
`requiredGrowth(level) = 2` from level `3` onward and `1` below that.  TS160
does not yet prove logarithmic growth or the TS22 budget comparison.

TS161 performs the phi pre-mortem before investing in a full replacement
pipeline.  It proves the local obstruction to reusing the TS149 error
mechanism: `sigma_1(2) = 3` while `phi(2) = 1`, hence the global inequality
`sigma_1(d) <= phi(d)` on positive integers is false.  This does not prove all
phi-based sieves impossible, but it shows that the simple `J2 -> phi`
replacement cannot inherit the divisor-mass absorption that made TS149 work.
The sprint packages this as a pivot ledger and points to the existing TS94
trace-kernel roadmap and TS95 explicit-formula bridge roadmap as the next
spectral front.

TS162 starts the spectral pivot on the concrete kernel side.  It instantiates
the TS42 triangle spline as a TS94 `TraceKernel`, proves the spline is
pointwise nonnegative, proves its value at the origin is `1`, and proves it
vanishes whenever `1 <= |x|`.  The spectral weight is deliberately the zero
placeholder, so TS162 does not claim Plancherel, a nontrivial Fourier
transform, a zeta-zero sum, or the Riemann-von Mangoldt explicit formula.
Those remain TS95-side analytic obligations.

TS163 replaces the TS162 zero spectral-weight placeholder by the natural
squared-sinc candidate `if xi = 0 then 1 else (Real.sin xi / xi)^2`, proves
this candidate is nonnegative and normalized at frequency `0`, lifts it to
complex spectral parameters by real part, and packages the resulting nonzero
TS94 kernel-data ledger.  TS163 still does not identify this candidate with
Mathlib's Fourier transform of the triangle spline and does not prove
Plancherel or the explicit formula.

TS164 neutralizes the immediate Fourier-normalization risk.  It replaces the
unit squared-sinc profile by the parametrized family
`scaledSincSq scale xi`, proves nonnegativity and value `1` at frequency `0`
for every scale, proves the TS163 candidate is exactly the unit-scale member,
and packages a `TriangleSplineFourierIdentificationContract` for every
positive scale.  No preferred scale is selected yet; the Mathlib
`Real.fourierIntegral` normalization and Plancherel remain future obligations.

TS165 calibrates that open scale against the current Mathlib Fourier API.  It
records the checked `Real.fourierChar` convention with the `2 * pi` exponent
and the real forward-kernel theorem with exponent `-2 * pi * v * w`, then
selects the TS164 contract at scale `Real.pi`.  This is only a normalization
ledger: the triangle-spline Fourier identity, Plancherel, and the explicit
formula are still named future obligations.

TS166 turns the next Fourier obligation into an exact compiled Lean statement.
It defines the complex-valued TS42 triangle spline, applies Mathlib's
`Real.fourierIntegral`, and states pointwise equality with the TS165 pi-scale
`scaledSincSq` candidate coerced to `Complex`.  The sprint deliberately does
not prove the identity.  Instead it records the primary convolution-box-square
route and the fallback piecewise branch-integration route, leaving Plancherel
and the explicit formula untouched.

TS167 probes the primary convolution route selected by TS166.  It defines the
centered unit-width box as an indicator of `[-1/2, 1/2]`, lifts it to a
complex-valued function, defines the manual Bochner self-convolution, and
introduces the non-squared `scaledSinc` profile expected for the box Fourier
transform.  The sprint compiles the three local obligations needed by the
route and proves that, together, they imply the exact TS166 Fourier
identification.  It does not prove box integrability, the spatial convolution
identity, the box Fourier evaluation, the Fourier-convolution exchange
theorem, Plancherel, or the explicit formula.

TS168 records the fallback branch-integration route selected by TS166.  It
defines the two affine branches of the triangle spline, the explicit
Mathlib-compatible forward Fourier kernel `exp(-2*pi*i*x*xi)`, the directed
interval integrals over `[-1,0]` and `[0,1]`, and intended closed forms for
each branch.  It compiles the branch split, left evaluation, right evaluation,
and closed-form recombination as separate `Prop` statements, then proves that
those four obligations imply the exact TS166 Fourier identification.  TS168
does not prove the branch split, either branch integral evaluation, the
closed-form recombination, Plancherel, or the explicit formula.

TS169 discharges the algebraic end of the TS168 fallback route.  It proves
that the left and right branch closed forms recombine to the TS166 pi-scale
squared-sinc target for every frequency, splitting the zero-frequency case
from the nonzero case and using only Euler recombination plus the real
half-angle identity.  TS169 still does not prove the branch split, either
branch integral evaluation, the full TS166 Fourier identification,
Plancherel, or the explicit formula.

TS170 discharges the right analytic branch in the TS168 fallback route.  It
proves that the directed interval integral over `[0,1]` of the right affine
branch against the Mathlib forward Fourier kernel equals the TS168
`rightBranchClosedForm`.  The zero-frequency case is reduced to the elementary
integral of `1 - x`, while the nonzero-frequency case uses an explicit complex
primitive and the interval-integral fundamental theorem of calculus.  TS170
still leaves the left branch integral and the global branch split open, and
does not claim the full TS166 Fourier identity, Plancherel, or the explicit
formula.

TS171 discharges the symmetric left analytic branch in the TS168 fallback
route.  It proves that the directed interval integral over `[-1,0]` of the
left affine branch against the same Mathlib forward Fourier kernel equals the
TS168 `leftBranchClosedForm`.  The zero-frequency case is reduced to the
elementary integral of `1 + x`, while the nonzero-frequency case mirrors TS170
with an explicit complex primitive and the interval-integral fundamental
theorem of calculus.  TS171 still leaves only the global branch split open
before the TS168 branch route can assemble the full TS166 Fourier identity.

TS172 discharges that remaining global branch split.  It rewrites Mathlib's
`Real.fourierIntegral` as the explicit Bochner integral using the TS168
forward kernel, restricts the integral to `Set.Ioc (-1) 1` using the TS162
support vanishing for the triangle spline, turns the restricted integral into
the directed interval integral over `[-1,1]`, splits it at `0`, and identifies
the two pieces with the TS168 affine branch integrals using the TS56 branch
formulae.  TS172 still does not assemble the full TS166 Fourier identity,
leaving that final wiring to the next sprint.

TS173 performs that final wiring.  It applies the TS168 branch-integral route
implication to the four discharged obligations from TS169, TS170, TS171, and
TS172, yielding the full TS166 pointwise Fourier-identification statement for
the triangle spline and the pi-scale squared-sinc candidate.  TS173 still does
not claim Plancherel, the Riemann-von Mangoldt explicit formula, or any
Goldbach conclusion.

TS174 probes the next L2/Plancherel interface without proving Plancherel.  It
defines the `eLpNorm` energies for the complexified triangle spline, its
Mathlib Fourier integral, and the pi-scale squared-sinc candidate.  Using TS173
and `eLpNorm_congr_ae`, it proves the Fourier-side and sinc-side energies are
equal.  It also proves that any supplied concrete Plancherel isometry for the
triangle spline immediately transports to equality between the squared-sinc
energy and the original time-side energy.  The actual Plancherel theorem,
spectral-sum convergence, and explicit formula remain open.

TS175 evaluates the elementary spatial square-energy constant on the time
side.  It proves that the directed integral of
`triangleSpline x ^ 2` over `[-1,1]` equals `2/3`, by splitting the interval at
`0`, replacing the spline by `1+x` and `1-x` on the two TS56 branches, and
computing both polynomial square integrals as `1/3`.  TS175 deliberately does
not evaluate the `eLpNorm` object itself and still does not prove Plancherel or
spectral sinc integrability.

TS176 lifts the TS175 constant from a directed interval integral to a global
Lebesgue square-energy statement.  It proves that
`int x, triangleSpline x ^ 2` over `volume` is `2/3`, using the fact that the
squared spline is supported in `(-1,1]`, and then identifies this with the
global integral of `||triangleSplineAsComplex x|| ^ 2`.  TS176 deliberately
stops before the final `eLpNorm = ofReal (sqrt (2/3))` conversion and still
does not prove Plancherel, spectral sinc integrability, the explicit formula,
or Goldbach.

TS177 closes the time-side `eLpNorm` value.  It proves a.e. strong
measurability of the complexified spline, global integrability of its squared
norm from the TS175 branch integrability and TS176 support control, then
unfolds the `eLpNorm` definition through `lintegral` to obtain
`triangleSplineTimeL2Energy = ENNReal.ofReal (Real.sqrt (2 / 3))`.  TS177
still does not prove Plancherel, spectral sinc integrability, the explicit
formula, or Goldbach.

TS178 closes the spectral finiteness probe for the pi-scale squared-sinc
candidate.  It proves measurability, nonnegativity, the bound by `1`, and the
global domination by `2 * (1 / (1 + xi ^ 2))`.  Using Mathlib's
`integrable_inv_one_add_sq`, TS178 obtains integrability of the real weight,
integrability of its square, integrability of the complex squared norm, and
finally `triangleSplineSincL2Energy < (Top.top : ENNReal)`.  TS178 still does
not prove Plancherel, the exact spectral norm value, the explicit formula, or
Goldbach.

TS179 probes the concrete Plancherel API surface before attempting any
discharge.  The local Mathlib surface exposes `Real.fourierIntegral`,
`Real.fourierIntegralInv`, and `Real.fourierChar`, but not the ready-made
candidate names `Real.fourierIntegral_isometry`,
`Real.fourierIntegral_plancherel`, `fourierIntegral_Plancherel`, or
`fourierIntegral_isometry`.  TS179 therefore keeps the TS174 concrete
Plancherel statement as the single analytic input and proves the conditional
consumption theorem: if that isometry is supplied, then
`triangleSplineSincL2Energy = ENNReal.ofReal (Real.sqrt (2 / 3))`.  TS179 still
does not prove unconditional Plancherel, the explicit formula, zeta-zero
summability, or Goldbach.

TS180 packages the triangle-spline evidence for the TS94 kernel front without
opening the TS95 zeta-zero machinery.  It records the TS162 real trace kernel,
the TS163 nonnegative sinc-square spectral-weight candidate, the TS173
pointwise Fourier identification, the TS177 exact time-side L2 value, the
TS178 finite sinc-side L2 energy, and the TS179 conditional exact sinc-side
value under the TS174 Plancherel input.  TS180 deliberately does not claim
unconditional Plancherel, zeta-zero summability, the Riemann-von Mangoldt
explicit formula, or Goldbach.

TS181 opens the TS95 explicit-formula front without pretending to prove it.
It defines `TriangleSplineExplicitFormulaContracts`, a local package containing
a TS93 zeta-zero family ledger, a zero contribution, residual terms, a positive
trace budget bounded by `1 / 2`, the TS95 readiness markers, and the budget
inequality controlling zero contribution plus residuals.  It then proves the
wiring theorem that TS180 kernel evidence plus such a contract package builds
a concrete TS95 explicit-formula bridge ledger and target.  TS181 still does
not construct the zeta-zero family, prove zeta-zero summability, prove
Plancherel, prove the explicit formula, or prove Goldbach.

TS182 reconnects the continuous triangle-spline kernel to the discrete scale
used by sieve and prime-sum ledgers.  It defines
`triangleSplineDiscreteWeight X n = triangleSpline ((n : Real) / (X : Real))`,
proves nonnegativity, proves the affine formula
`1 - (n : Real) / (X : Real)` on `n <= X`, proves vanishing at and beyond
`X <= n`, and records the boundary compatibility at `n = X`.  TS182 does not
define a von Mangoldt weighted sum, does not prove Plancherel, does not
construct zeta zeros, and does not prove the explicit formula or Goldbach.

TS183 turns that pointwise discrete weight into a finite arithmetic sum
interface.  It defines `triangleSplineWeightedNatSum A X` for an arbitrary
weight `A : Nat -> Real`, proves that extending the summation range beyond
`X + 1` does not change the sum when `0 < X`, rewrites the sum using the affine
formula on its support, and proves nonnegativity for nonnegative arithmetic
weights.  It then names a `VonMangoldtWeightContract` and the corresponding
smoothed sum without selecting the exact Mathlib von Mangoldt API.  TS183 does
not prove a prime-number estimate, the explicit formula, Plancherel, zeta-zero
construction, or Goldbach.

TS184 probes Mathlib's von Mangoldt API and binds it to the TS183 finite
weighted-sum interface.  It imports `Mathlib.NumberTheory.VonMangoldt`, extracts
`ArithmeticFunction.vonMangoldt : ArithmeticFunction Real` as a plain
`Nat -> Real` weight, and uses `ArithmeticFunction.vonMangoldt_nonneg` to
instantiate the TS183 `VonMangoldtWeightContract`.  The concrete smoothed von
Mangoldt sum inherits the TS183 structural properties: nonnegativity, finite
range extension invariance beyond `X`, and the affine smoothing formula on the
support.  TS184 does not prove a prime-number estimate, the explicit formula,
zeta-zero summability, Plancherel, or Goldbach.

TS185 opens the right-hand zero-family vocabulary for the explicit-formula
front after TS184 made the finite von Mangoldt side concrete.  It imports
`Mathlib.NumberTheory.LSeries.RiemannZeta`, stabilizes `riemannZeta` as the
API target, and defines the local predicates `riemannZetaZeroPredicate`,
`criticalStripPredicate`, and `nontrivialRiemannZetaZeroPredicate`.  The sprint
proves the trivial-zero probe at negative even integers using
`riemannZeta_neg_two_mul_nat_add_one`.  It then defines a local
`RiemannZetaZeroFamilyAPIBindingContract` whose fields record the zero set,
multiplicities, critical-strip containment, conjugation closure, and symmetry
about the half line, and proves that any populated contract supplies the
existing TS93 `ZetaZeroFamilyLedger` and therefore the TS92 zero-family target.
TS185 does not construct a nontrivial zero family, does not prove zeta-zero
summability, does not prove the explicit formula, does not prove the Riemann
hypothesis, does not prove Plancherel, and does not prove Goldbach.

TS186 normalizes the future explicit-formula main term.  It reuses the TS162
theorem `triangleSpline_zero` to record `triangleSpline 0 = 1`, proves
`(X : Real) * triangleSpline 0 = (X : Real)` for every natural scale, and uses
the TS182 affine discrete-weight formula to prove
`triangleSplineDiscreteWeight X 0 = 1` and
`(X : Real) * triangleSplineDiscreteWeight X 0 = (X : Real)` for `0 < X`.
TS186 does not prove the explicit formula, zeta-zero summability, Plancherel,
a sieve-trace comparison, or Goldbach.

TS187 halts supporting-cleanup drift and names the real analytic walls that
stand between the Fourier kernel package and a Goldbach-level trace argument.
The central wall is Wall 0: classical explicit formulae use Mellin and
Dirichlet-series language, while the recent triangle-spline work built a real
Fourier identity.  A future proof must justify the logarithmic coordinate
change `x = exp u`, the measure transport `dx / x = du`, and the compatibility
of kernels, analytic continuation, and inversion.  TS187 defines
`MellinFourierDiffeomorphismContract` and `MellinFourierDiffeomorphismEvidence`
for Wall 0, and `AnalyticFrontierContracts` and `AnalyticFrontierEvidence` for
the full set of five walls: Mellin/Fourier compatibility, Plancherel, contour
explicit formula, zeta-zero summability or bounds, and circle-method/Gallagher
correlation.  The ledger stores the contract and evidence types but does not
populate any `AnalyticFrontierEvidence` value.  TS187 does not prove the
explicit formula, does not prove Plancherel, does not prove zeta-zero
summability, and does not prove Goldbach.

TS188 wires Wall 1, the Plancherel wall, from the TS187 analytic-frontier
ledger to the concrete triangle-spline Plancherel statement stabilized in
TS174.  It proves that any supplied proof of
`TS174.Goldbach.TriangleSplinePlancherelIsometryStatement` immediately
activates the TS179 energy-transport theorem, yielding the exact pi-scale
squared-sinc spectral L2 value `ENNReal.ofReal (Real.sqrt (2 / 3))`.  TS188
does not prove Plancherel, does not prove the explicit formula, does not prove
zeta-zero summability, and does not prove Goldbach.  The Plancherel wall is now
wired, not discharged.

TS189 attacks Wall 0, the Mellin/Fourier compatibility gap, by separating the
provable algebraic pullback from the unproved measure transport.  It defines
the logarithmic coordinate maps `logCoord` and `expCoord`, proves the
round-trip identities `log (exp u) = u` and `exp (log x) = x` for positive
`x`, and defines the triangle-spline logarithmic pullback
`triangleSplineLogPullback X u = triangleSpline (exp u / X)`.  It proves the
pullback vanishes when `exp u >= X`, has affine form `1 - exp u / X` on its
support, and preserves nonnegativity.  It also defines the critical
Mellin/Fourier amplitude by multiplying by `exp (c * u)` and proves its
nonnegativity.  The sprint names a local `LogPullbackMeasureTransportContract`
for the unproved analytic part: the measure transport `dx / x = du`, the
resulting Mellin-as-Fourier equivalence, explicit-formula compatibility, and
convergence/inversion.  TS189 does not prove the explicit formula, Plancherel,
zeta-zero summability, or Goldbach.

TS190 specializes the TS189 generic Mellin/Fourier amplitude to the
critical-line shift `c = 1/2`, which is the value appearing when zeros are
parametrized as `rho = 1/2 + i*gamma` in the classical Riemann-von Mangoldt
explicit formula.  It defines `triangleSplineCriticalAmplitude X u` and proves
nonnegativity, vanishing for `exp u >= X`, and the affine form
`(1 - exp u / X) * exp(u/2)` on the support `exp u <= X`.  The critical-line
choice is a functional specialization of the amplitude profile, not a claim
that zeta zeros lie on the critical line.  TS190 does not prove the explicit
formula, does not prove the measure transport, does not prove Plancherel, and
does not prove Goldbach.

TS191 starts the exact energy calculation for the critical-line amplitude
without claiming the full improper integral.  It defines the squared
critical-line amplitude density and the expanded exponential density
`exp u - (2 / X) * exp (2*u) + (1 / X^2) * exp (3*u)`, then proves that the
two agree on the TS190 support side `exp u <= X`.  It also defines the natural
primitive
`exp u - (1 / X) * exp (2*u) + (1 / (3*X^2)) * exp (3*u)` and proves that its
value at the logarithmic endpoint `log X` is exactly `X / 3`.  The lower-tail
limit from `-infty` and the promotion to an improper Lebesgue integral remain
an explicit local contract.  TS191 does not discharge Wall 0 measure transport,
does not prove the explicit formula, does not prove zeta-zero summability, and
does not prove Goldbach.

TS192 continues the TS191 critical-line energy computation by proving the
lower-tail boundary value for the natural primitive.  TS191 had already shown
that the primitive evaluates to `X / 3` at the upper endpoint `log X`; TS192
proves that the same primitive tends to `0` as `u -> -infty`, using
`Real.tendsto_exp_atBot` together with the decay of `exp (2*u)` and
`exp (3*u)`.  It packages this lower-tail limit with the TS191 upper-endpoint
value as `CriticalLinePrimitiveBoundaryStatement`.  The remaining
improper-integral/FTC step is kept as a local contract whose integral
proposition is supplied explicitly, not hidden behind `True`.  TS192 does not
prove the full Lebesgue improper integral over `(-infty, log X]`, does not
prove the Wall 0 measure transport `dx / x = du`, does not prove the explicit
formula, does not prove zeta-zero summability, and does not prove Goldbach.

TS193 turns the TS191/TS192 boundary data into a concrete theorem about
truncated interval integrals.  It proves that the TS191 primitive has derivative
equal to the expanded critical-line energy density, registers the finite
interval integral as `criticalLineTruncatedExpandedEnergy X a`, proves the
FTC identity
`criticalLineTruncatedExpandedEnergy X a = primitive(log X) - primitive(a)`,
and then uses the TS191 endpoint value together with the TS192 lower-tail
limit to prove that these truncated integrals tend to `X / 3` as
`a -> -infty`.  TS193 does not define or discharge a standalone improper
Lebesgue integral object, does not prove Wall 0 measure transport, does not
prove Plancherel, does not prove the explicit formula, does not prove
zeta-zero summability, and does not prove Goldbach.

TS194 closes the semantic link between the TS193 expanded-density computation
and the actual TS190 critical-line amplitude.  It defines the truncated actual
energy as the interval integral of `(triangleSplineCriticalAmplitude X u)^2`
from `a` to `log X`.  For every eventual lower endpoint `a <= log X`, TS194
proves that each point of the directed interval lies on the support side
`exp u <= X`, so the TS191 pointwise expansion identifies the actual squared
amplitude with the expanded density.  The truncated actual-energy integrals
therefore agree eventually with the TS193 expanded-density integrals and
inherit the same limit `X / 3` as `a -> -infty`.  TS194 does not define a
standalone improper Lebesgue integral object, does not prove Wall 0 measure
transport, does not prove Mellin-as-Fourier compatibility, does not prove
Plancherel, does not prove the explicit formula, does not prove zeta-zero
summability, and does not prove Goldbach.

TS195 packages the TS194 convergence theorem as a named limit-based critical
energy object.  It defines `CriticalLineActualImproperEnergyObject X` as a
real value together with a certificate that the TS194 truncated actual-energy
integrals tend to that value as the lower endpoint tends to `-infty`.  The
canonical object has value `(X : Real) / 3`, and TS195 provides the scalar
wrapper `criticalLineActualImproperEnergy X hX` with theorem
`criticalLineActualImproperEnergy_eq_X_div_three`.  It also proves that any
supplied TS194 object contract is immediately consumed by the TS194 convergence
theorem.  TS195 does not define a general standalone Lebesgue improper integral
construction, does not prove Wall 0 measure transport, does not prove
Plancherel, does not prove the explicit formula, does not prove zeta-zero
summability, and does not prove Goldbach.

TS196 makes the first compact analytic progress on Wall 0.  It defines the
original-coordinate square density
`criticalLineXSideEnergyDensity X x = triangleSpline (x / X)^2` and proves
that the actual squared critical-line amplitude is its Jacobian-weighted
logarithmic pullback:
`(triangleSplineCriticalAmplitude X u)^2 = exp u *
criticalLineXSideEnergyDensity X (exp u)`.  It proves that `exp` maps
`Icc a (log X)` onto `Icc (exp a) X`, registers the derivative and injectivity
of `exp` on compact intervals, and applies Mathlib's
`integral_image_eq_integral_abs_deriv_smul` to prove the compact set-integral
change of variables.  TS196 does not prove the full improper Wall 0 transport,
does not prove the Haar transport `dx / x = du`, does not prove
Mellin-as-Fourier compatibility, does not prove Plancherel, does not prove the
explicit formula, does not prove zeta-zero summability, does not prove
circle-method/Gallagher correlation, and does not prove Goldbach.

TS197 transfers the TS194 critical-line energy limit to the x-side compact
integrals built by TS196.  It defines `criticalLineTruncatedXSideEnergy X b`
as the compact set integral of `criticalLineXSideEnergyDensity X` over
`Icc b X`.  It proves that the compact set integral on `Icc a (log X)` agrees
with the TS194 directed interval integral over `a..log X`, using the
boundary-insensitive `Icc`/`Ioc` conversion, and then combines this with the
TS196 compact change of variables.  Consequently,
`criticalLineTruncatedXSideEnergy X (exp a)` eventually agrees with the TS194
logarithmic truncated energy and tends to `X / 3` as `a -> -infty`.  TS197 does
not define a standalone x-side improper integral object over `(0, X]`, does
not prove the full Wall 0 measure transport, does not prove Haar transport
`dx / x = du`, does not prove Mellin-as-Fourier compatibility, does not prove
Plancherel, does not prove the explicit formula, does not prove zeta-zero
summability, does not prove circle-method/Gallagher correlation, and does not
prove Goldbach.

TS198 mirrors the TS195 logarithmic-side energy object in the original
coordinate.  It defines `CriticalLineXSideImproperEnergyObject X`, storing a
real value together with the TS197 convergence certificate for the x-side
truncated energies with lower endpoint `exp a`.  It also uses Mathlib's
`Real.tendsto_comp_exp_atBot` to rewrite that convergence in the natural
original-coordinate form `b -> 0+`, namely the `nhdsWithin 0 (Set.Ioi 0)`
filter.  The canonical object carries value `X / 3`, the scalar wrapper
`criticalLineXSideImproperEnergy X hX` evaluates by definition to `X / 3`, and
the local TS197 object contract is consumed by the TS197 convergence theorem.
TS198 does not define a standalone general Lebesgue improper integral over
`(0, X]`, does not prove full Wall 0 measure transport, does not prove Haar
transport `dx / x = du`, does not prove Mellin-as-Fourier compatibility, does
not prove Plancherel, does not prove the explicit formula, does not prove
zeta-zero summability, does not prove circle-method/Gallagher correlation, and
does not prove Goldbach.

TS199 is a strategic OTSA dashboard sprint rather than a consumption theorem.
It collects the TS158 Selberg/Brun-Titchmarsh obstruction closure, the TS161
phi-denominator pre-mortem and spectral pivot, the TS195 and TS198 critical
energy objects, the TS187 analytic-frontier ledger, the TS188 Plancherel bridge,
and the TS196 compact Wall 0 change-of-variables ledger.  Its only new theorem
identifies the two named critical-line energy scalars:
`criticalLineActualImproperEnergy X hX =
criticalLineXSideImproperEnergy X hX`, by rewriting both sides to `X / 3`.
TS199 also defines future `OTSAConsumptionContracts` and an evidence package,
but does not populate them.  It does not prove a trace constant bound, a
Mellin-tail constant bound, a replacement sieve budget, the final OTSA
inequality, a conditional Goldbach theorem, full Wall 0 Mellin/Fourier
transport, Haar transport, Plancherel, the explicit formula, zeta-zero
summability, circle-method/Gallagher correlation, or Goldbach.

TS200 prevents a circular final Goldbach interface.  It defines
`BinaryGoldbachStatement` as the target conclusion, then introduces
`OTSAInputContracts` with five input-only proposition slots: trace-constant
bound, Mellin-tail bound, replacement sieve budget, final OTSA inequality, and
combinatorial reduction.  The matching `OTSAInputEvidence` contains evidence
only for those inputs, while `OTSAConclusionBridge` is the separate future
object that may turn such evidence into `BinaryGoldbachStatement`.  The only
theorem, `binaryGoldbach_of_otsaConclusionBridge`, applies that bridge to the
input evidence.  TS200 deliberately does not consume the TS199
`conditional_goldbach_statement` slot as an input, does not prove any OTSA
input contract, does not prove the final OTSA inequality, does not prove the
combinatorial reduction, and does not prove Goldbach.

TS201 records the strategic decision after the TS200 anti-circularity cleanup.
It defines an `OpenFront` enumeration for Wall 0 measure transport, Wall 1
Plancherel, Wall 2 explicit formula, Wall 3 zero summability, Wall 4
circle/Gallagher correlation, sieve replacement, and the documentation bundle.
The `recommendedPriority` list starts with `OpenFront.wall0MeasureTransport`,
and the ledger records that this is the selected next sprint target.  TS201
does not prove Wall 0, Plancherel, the explicit formula, zero summability,
circle/Gallagher correlation, a replacement sieve budget, a bundle, any OTSA
input contract, or Goldbach.

TS202 starts the selected Wall 0 measure-transport front by refining the target
before any global improper theorem is attempted.  It defines
`Wall0HaarMeasureTransportContract` and
`Wall0HaarMeasureTransportEvidence` with proposition slots for truncated Haar
transport, improper Haar transport, Mellin/Fourier kernel compatibility, and
effective integrability.  The sprint proves only the safe evidence-routing
facts and records the concrete inputs already available: the TS196 compact
change-of-variables target and the TS198 x-side critical energy value
`criticalLineXSideImproperEnergy X hX = X / 3`.  TS202 does not prove full
Haar transport `dx / x = du`, does not prove improper transport, does not prove
Mellin/Fourier compatibility, does not prove Plancherel, does not prove the
explicit formula, does not prove zeta-zero summability, does not prove
circle/Gallagher correlation, and does not prove Goldbach.

TS203 populates the first concrete Wall 0 slot by proving truncated Haar
transport on positive finite intervals.  For any real test function `F`
continuous on `[epsilon, X]`, with `0 < epsilon <= X`, it proves the signed
real interval-integral identity
`intervalIntegral (fun u => F (exp u)) (log epsilon) (log X) volume =
intervalIntegral (fun x => F x / x) epsilon X volume`.  The proof uses
Mathlib's `intervalIntegral.integral_comp_mul_deriv'` with the substitution
`x = exp u`, derivative `exp u`, and the cancellation of the Jacobian against
the Haar factor `1 / x`.  TS203 deliberately does not fabricate full
`Wall0HaarMeasureTransportEvidence`: the improper transport, global
transport on `(0, infinity)`, Mellin/Fourier kernel compatibility, effective
integrability, Plancherel, explicit formula, zeta-zero summability,
circle/Gallagher correlation, and Goldbach remain unproved.

TS204 starts the final conditional-reduction phase by specifying the three
analytic input families that a future OTSA bridge may consume: the
triangle-spline Plancherel input, an effective explicit-formula input for the
triangle-spline weight, and a Gallagher / large-sieve comparison input adapted
to the smoothing.  The sprint separates contract types from evidence types so
that fields naming effective formula bounds, residual control, and Gallagher
variance are not hidden behind `True`.  It records that the conditional
Plancherel-to-energy transport from TS188 and the truncated Haar transport from
TS203 are available, but it does not populate any OTSA input slot and does not
consume `BinaryGoldbachStatement` as an input.  TS204 does not prove
Plancherel, the effective explicit formula, Gallagher, the final OTSA
inequality, the combinatorial reduction, or Goldbach.

TS205 connects the TS204 final analytic input specification to the TS200
non-circular OTSA consumption interface.  It defines
`FinalAnalyticToOTSAInputBridge`, an adapter saying that final triangle-spline
analytic evidence can populate a chosen package of five TS200 OTSA input
contracts.  It then constructs `OTSAInputEvidence` from such final analytic
evidence and proves a routing theorem: final analytic evidence, plus this
adapter, plus a supplied TS200 `OTSAConclusionBridge`, yields
`BinaryGoldbachStatement`.  The concrete TS205 ledger does not store
`BinaryGoldbachStatement`; Goldbach remains conditional on the supplied bridge.
TS205 does not prove Plancherel, the effective explicit formula, Gallagher, any
OTSA input slot, the conclusion bridge, or Goldbach.

TS206 makes the Wall 2 effective explicit-formula target concrete for the
triangle-spline von Mangoldt weight.  Its left-hand side is the existing TS184
smoothed von Mangoldt sum, and its right-hand data consists of a main term,
a nontrivial-zero contribution, and a residual term.  It defines an effective
constants package with a configurable main-term model and scale/log powers for
zero and residual bounds, then builds a family of TS204
`TriangleSplineExplicitFormulaEffectiveInputContract` instances from such
constants.  The TS181 compatibility field is a real proposition,
`Nonempty TS181.Goldbach.TriangleSplineExplicitFormulaContracts`, not `True`.
TS206 does not prove the explicit formula, the main term, zero bounds, residual
bounds, admissibility of constants, TS204 evidence, any OTSA input slot, or
Goldbach.

TS207 proves a concrete obstruction to the naive Haar-energy continuation of
the TS198 critical-line energy.  It defines the Haar-weighted square density
`triangleSpline(x / X)^2 / x` and proves that, for `0 < x <= X/2`, the scaled
triangle spline is at least `1/2`.  Therefore the truncated naive Haar energy
over `[epsilon, X/2]` is bounded below by
`(1/4) * (log (X/2) - log epsilon)`.  The proof combines the TS56 affine branch
formula, interval-integral monotonicity, and the FTC evaluation of
`int dx/x = log`.  TS207 does not contradict the TS198 `dx` energy value
`X/3`; it shows that the extra Haar factor `1/x` creates a logarithmic
singularity at zero.  TS207 does not construct an improper Haar integral, does
not prove Mellin/Fourier compatibility, Plancherel, the explicit formula,
Gallagher, or Goldbach.

TS208 probes the mature Wall 1 Plancherel front in a kernel-specific way.
Rather than asserting a general Plancherel theorem for Mathlib's
`Real.fourierIntegral`, it isolates the direct scalar spectral identity needed
for the triangle spline: `integral triangleSplineSincRealWeight^2 = 2/3`.
Using TS178 spectral integrability, TS174 Fourier/sinc identification, and the
TS177 time-side `eLpNorm` value, TS208 proves that this future `sinc^4` identity
would imply the exact spectral `eLpNorm` value, the concrete TS174
triangle-spline Plancherel statement, and the TS204 Plancherel input evidence.
TS208 does not prove the `sinc^4` integral, does not prove general Plancherel,
and does not prove the explicit formula, Gallagher, or Goldbach.

TS209 removes the remaining scale ambiguity in the TS208 Wall 1 target.  It
defines the canonical unscaled squared-sinc profile
`canonicalSincSq t = if t = 0 then 1 else (sin t / t)^2` and proves that the
standard scalar identity `integral canonicalSincSq^2 = (2 * pi) / 3` implies
the TS208 pi-scaled identity `integral triangleSplineSincRealWeight^2 = 2/3`.
The proof uses Mathlib's global scaling lemma `Measure.integral_comp_mul_left`
with scale `Real.pi`, and the positivity of `Real.pi` to simplify the scaling
factor to `1 / Real.pi`.  TS209 then routes this normalized scalar identity
through the TS208 bridge to TS204 Plancherel evidence.  TS209 does not prove
the canonical `sinc^4` integral, does not prove general Plancherel, and does
not prove the explicit formula, Gallagher, or Goldbach.

TS210 discharges the first concrete TS167 convolution-route obligation.  It
proves that the manual Bochner self-convolution of the centered unit box equals
the triangle spline as a complex-valued function.  The proof computes the
overlap of the two box supports pointwise: the integrand vanishes for
`x < -1` and `1 < x`; on `-1 <= x <= 0` the overlap interval is
`[-1/2, x + 1/2]` and has length `1 + x`; on `0 <= x <= 1` it is
`[x - 1/2, 1/2]` and has length `1 - x`.  These branch values are matched to
the TS56 triangle-spline affine branches after coercion through TS166.
TS210 does not evaluate the Fourier transform of the box, does not prove
Fourier-convolution exchange, does not prove Plancherel, and does not prove the
canonical `sinc^4` integral, the explicit formula, Gallagher, or Goldbach.

TS211 discharges the second concrete TS167 convolution-route obligation.  It
proves that Mathlib's Fourier transform of the centered unit box equals the
non-squared pi-scaled sinc profile selected in TS165.  The proof expands
`Real.fourierIntegral` using Mathlib's real Fourier kernel, proves that the
box integrand vanishes outside `[-1/2, 1/2]`, converts the global integral to a
directed compact interval integral, evaluates the zero-frequency case as the
box length, and evaluates the nonzero-frequency case using
`integral_exp_mul_complex` followed by `Complex.exp_mul_I` and exact field
simplification.  TS211 does not prove Fourier-convolution exchange, does not
prove Plancherel or Parseval, and does not prove the canonical `sinc^4`
integral, the explicit formula, Gallagher, or Goldbach.

TS212 discharges the third concrete TS167 convolution-route obligation.  It
proves the specialized exchange statement
`fourierIntegral unitBoxSelfConvolution = fourierIntegral unitBoxAsComplex *
fourierIntegral unitBoxAsComplex` for every real frequency.  The proof does
not invoke a general Fourier-convolution theorem.  Instead it rewrites the box
self-convolution as the triangle spline using TS210, evaluates the triangle
Fourier transform using the already-proved TS173 closed form, evaluates the
box Fourier transform using TS211, and uses the TS167 algebraic bridge from
`sinc * sinc` to squared-sinc.  Thus the full TS167 convolution route now
re-derives the TS166 triangle-spline Fourier identification.  TS212 does not
prove a general convolution theorem, Plancherel, Parseval, the canonical
`sinc^4` integral, the explicit formula, Gallagher, or Goldbach.

TS213 records the direct non-Plancherel scalar route to the TS209 canonical
`sinc^4` identity.  It defines the cosine-square remainder
`(1 - cos x)^2`, the positive-half-line kernel `(1 - cos x)^2 / x^4`, the
Dirichlet sine kernel `sin (a*x) / x`, the expected third-derivative kernel
`(-2 * sin x + 4 * sin (2*x)) / x`, and the half-line/full-line canonical
`sinc^4` integrals.  It then packages the five concrete future obligations:
the third-derivative formula, the Dirichlet sine integral, improper triple
integration by parts, the scaling identity from `x = 2*u`, and evenness.  The
new routing theorem proves that this evidence would imply
`TS209.Goldbach.CanonicalSincFourthIntegralValueStatement`, and therefore the
TS204 triangle-spline Plancherel input evidence via TS209 and TS208.  TS213
does not prove Dirichlet, the improper IPP, scaling, evenness, Plancherel,
Parseval, the explicit formula, Gallagher, or Goldbach.

TS214 discharges the first concrete scalar obligation introduced by TS213.  It
proves the first, second, and third derivative formulae for
`cosSquareRemainder x = (1 - cos x)^2`, culminating in
`TS213.Goldbach.CosSquareThirdDerivativeFormulaStatement`: the third derivative
is `-2 * sin x + 4 * sin (2*x)`.  The proof uses explicit product/add
derivative rules, `fun_prop` for differentiability, `Real.sin_two_mul`, and
ring normalization.  TS214 does not prove the Dirichlet sine integral, improper
triple integration by parts, scaling, evenness, Plancherel, Parseval, the
explicit formula, Gallagher, or Goldbach.

TS215 probes the Dirichlet sine integral API needed for the second scalar
obligation in TS213.  The local search did not locate a ready-made theorem for
the unit-frequency value `integral_0^infty sin x / x = pi / 2`, so TS215 keeps
that value unproved.  It does prove that Mathlib exposes the positive-half-line
scaling theorem `integral_comp_mul_left_Ioi` in a project-facing form, and it
splits the TS213 Dirichlet statement into two explicit future inputs:
`DirichletUnitFrequencyStatement` and
`DirichletPositiveFrequencyScalingStatement`.  The routing theorem proves that
these two inputs imply `TS213.Goldbach.DirichletSineIntegralStatement`.  TS215
does not prove the Dirichlet value, the singular-kernel scaling statement,
improper triple IPP, `sinc^4` scaling, evenness, Plancherel, Parseval, the
explicit formula, Gallagher, or Goldbach.

TS216 focuses that TS215 split on the unit-frequency value.  It proves the
pointwise simplification
`TS213.Goldbach.sineDirichletKernel 1 x = Real.sin x / x`, records the current
TS215 Lebesgue-integral target, and names two future classical formulations:
cutoff-improper convergence and Abel regularization.  TS216 does not prove the
unit-frequency Dirichlet value, cutoff convergence, Abel regularization,
positive-frequency scaling, the TS213 Dirichlet statement, improper triple IPP,
`sinc^4` scaling, evenness, Plancherel, Parseval, the explicit formula,
Gallagher, or Goldbach.

TS217 corrects the Dirichlet route after TS215--TS216 by no longer treating the
Lebesgue target as the final analytic formulation.  It archives the
unit-frequency Lebesgue statement as a legacy target, promotes cutoff-improper
convergence and Abel regularization as the official future targets, and defines
`DirichletCutoffEvidence`, `DirichletAbelEvidence`, and
`CorrectedDirichletSineIntegralTarget`.  TS217 proves only that either evidence
wrapper supplies the corrected target.  It does not prove Lebesgue
non-integrability, the Dirichlet value, cutoff convergence, Abel convergence,
the old TS213 Lebesgue Dirichlet slot, improper triple IPP, `sinc^4` scaling,
evenness, Plancherel, Parseval, the explicit formula, Gallagher, or Goldbach.

TS218 discharges the two elementary TS213 scalar obligations that do not depend
on Dirichlet or the triple IPP.  It proves the pointwise scaling identity
`canonicalSincFourthKernel u = 4 * cosSquareHaarKernel (2*u)` on `0 < u`, uses
`integral_comp_mul_left_Ioi` to obtain the half-line scaling
`halfLineCanonicalSincFourthIntegral = 2 * cosSquareImproperIntegral`, recovers
global integrability of the canonical kernel from TS178 through the TS209
pi-scaling relation, and proves the full-line evenness identity by splitting the
line and mapping the non-positive half by `x -> -x`.  TS218 does not prove the
Dirichlet cutoff or Abel value, improper triple IPP, the canonical `sinc^4`
value, Plancherel evidence, the explicit formula, Gallagher, or Goldbach.

TS219 corrects the triple-IPP side of the TS213 route in the same spirit as
TS217 corrected Dirichlet.  It archives the old Lebesgue statement
`TS213.Goldbach.CosSquareTripleIPPStatement` as a legacy target and defines the
cutoff route using the product filter `(eps, T) -> (0+, +infty)`.  It records
the finite IPP identity on `[eps, T]`, the three explicit boundary jumps, their
future vanishing, and the third-derivative cutoff value `pi` (not `pi/2`).  A
`CosSquareTripleIPPCutoffBridge` remains an explicit future input for the
limiting assembly to `TS213.Goldbach.CosSquareIntegralValueStatement`.  TS219
does not prove finite IPP, boundary vanishing, the derivative cutoff value, the
assembly bridge, the canonical `sinc^4` value, Plancherel evidence, the
explicit formula, Gallagher, or Goldbach.

TS220 proves the compact local derivative identity behind the TS219 finite
triple-IPP route.  It defines the explicit primitive
`P(x) = -f(x)/(3*x^3) - f'(x)/(6*x^2) - f''(x)/(6*x)` for
`f(x) = (1 - cos x)^2`, reuses the TS214 first, second, and third derivative
models, and proves that for `x != 0`, `P'(x)` is exactly
`cosSquareHaarKernel x - (1/6) * cosSquareThirdDerivativeKernel x`.  This
validates the calculus core needed for a future finite-interval FTC discharge.
TS220 does not prove `TS219.Goldbach.CosSquareFiniteTripleIPPStatement`, does
not identify the primitive jump with the TS219 boundary sum, and does not prove
boundary vanishing, the third-derivative cutoff value, Dirichlet cutoff, the
canonical `sinc^4` value, Plancherel evidence, the explicit formula, Gallagher,
or Goldbach.

TS221 closes the finite compact part of the TS219 cutoff triple-IPP route.  It
proves that the TS220 primitive equals the sum of the three TS219 boundary
terms, hence `P(T) - P(eps)` equals
`cosSquareTripleIPPBoundarySum eps T`.  It then applies the finite-interval FTC
on the compact positive interval `[eps, T]`, using the TS220 derivative identity
and continuity of the two kernels there, to prove
`TS219.Goldbach.CosSquareFiniteTripleIPPStatement`.  TS221 does not prove
boundary vanishing, the third-derivative cutoff value, Dirichlet cutoff or Abel
values, the canonical `sinc^4` value, Plancherel evidence, the explicit formula,
Gallagher, or Goldbach.

TS222 isolates the remaining boundary-vanishing asymptotics after TS221.  It
defines the two one-variable primitive limit obligations
`CosSquareIPPPrimitiveAtTopVanishingStatement` and
`CosSquareIPPPrimitiveZeroRightVanishingStatement`, packages them as
`CosSquareIPPPrimitiveBoundaryLimitEvidence`, and proves that this evidence
implies the TS219 product-filter statement
`TS219.Goldbach.CosSquareBoundaryVanishingStatement`.  The proof composes the
two one-variable limits with `tendsto_fst` and `tendsto_snd`, subtracts the
limits, and rewrites the resulting primitive jump using the TS221 identity.
TS222 does not yet prove the two asymptotic estimates themselves, the
third-derivative cutoff value, Dirichlet cutoff or Abel values, the canonical
`sinc^4` value, Plancherel evidence, the explicit formula, Gallagher, or
Goldbach.

TS223 discharges the `+infty` half of the TS222 boundary asymptotics.  It proves
global bounds for the three trigonometric coefficients in the TS220 primitive:
`|f(x)| <= 4`, `|f'(x)| <= 4`, and `|f''(x)| <= 6`, then combines those bounds
with `tendsto_zpow_atTop_zero` for the negative powers `x^(-3)`, `x^(-2)`, and
`x^(-1)`.  This proves
`TS222.Goldbach.CosSquareIPPPrimitiveAtTopVanishingStatement`.  TS223 does not
prove the zero-right primitive asymptotic, the full boundary vanishing statement,
the third-derivative cutoff value, Dirichlet cutoff or Abel values, the canonical
`sinc^4` value, Plancherel evidence, the explicit formula, Gallagher, or
Goldbach.

TS224 discharges the zero-right half of the TS222 boundary asymptotics.  Near
zero it proves the local estimates `|1 - cos x| <= x^2 / 2`,
`|sin x| <= |x|`, and `|cos x| <= 1`, then derives
`|f(x)| <= x^4 / 4`, `|f'(x)| <= x^3`, and `|f''(x)| <= 3*x^2` for
`0 < x`.  These bounds give the linear squeeze
`|P(x)| <= (3/4)*x`, hence
`TS222.Goldbach.CosSquareIPPPrimitiveZeroRightVanishingStatement`.  Combining
this with TS223 through the TS222 bridge proves
`TS219.Goldbach.CosSquareBoundaryVanishingStatement`.  TS224 does not prove the
third-derivative cutoff value, Dirichlet cutoff or Abel values,
`cosSquareImproperIntegral = pi/6`, the canonical `sinc^4` value, Plancherel
evidence, the explicit formula, Gallagher, or Goldbach.

TS225 reduces the remaining TS219 third-derivative cutoff value to Dirichlet
cutoff values at frequencies `1` and `2`.  It defines the product-filter
Dirichlet cutoff statement over the same `(eps, T) -> (0+, +infty)` filter as
TS219, proves the pointwise decomposition
`cosSquareThirdDerivativeKernel = -2*sineDirichletKernel 1 +
4*sineDirichletKernel 2`, and proves that the two frequency limits `pi/2`
imply the combined value `pi` by Tendsto linearity and the scalar identity
`-2*(pi/2)+4*(pi/2)=pi`.  The finite interval-integral linearization is kept as
an explicit statement, so TS225 does not prove the TS219 cutoff value
unconditionally.  TS225 does not prove Dirichlet cutoff or Abel convergence,
`cosSquareImproperIntegral = pi/6`, the canonical `sinc^4` value, Plancherel
evidence, the explicit formula, Gallagher, or Goldbach.

TS226 discharges the finite interval-integral linearization left open by
TS225.  On the eventual cutoff region `0 < eps < 1 < T`, the interval
`[eps, T]` stays inside the positive half-line, so the Dirichlet kernels and
the third-derivative kernel are continuous and interval-integrable.  TS226
rewrites the third-derivative kernel using the TS225 pointwise decomposition
and applies `intervalIntegral.integral_add` and
`intervalIntegral.integral_const_mul` to prove
`TS225.Goldbach.ThirdDerivativeCutoffLinearizationStatement`.  TS226 does not
prove the Dirichlet product-filter values at frequencies `1` or `2`, the TS219
third-derivative cutoff value unconditionally, `cosSquareImproperIntegral =
pi/6`, the canonical `sinc^4` value, Plancherel evidence, the explicit formula,
Gallagher, or Goldbach.

TS227 reduces the two remaining product-filter Dirichlet cutoff values to a
single unit-frequency statement.  For each `a > 0`, it proves that scaling the
cutoff pair `(eps, T)` to `(a*eps, a*T)` preserves the TS219 product filter and
that the finite interval integral satisfies
`int_eps^T sin(a*x)/x dx = int_(a*eps)^(a*T) sin(u)/u du`.  Therefore the
frequency `2` value follows from the frequency `1` value, and with TS226 and
TS225 the unit-frequency value would imply the TS219 third-derivative cutoff
value.  TS227 does not prove the unit-frequency Dirichlet cutoff value,
`cosSquareImproperIntegral = pi/6`, the canonical `sinc^4` value, Plancherel
evidence, the explicit formula, Gallagher, or Goldbach.

TS228 reduces that remaining product-filter unit-frequency cutoff value to the
one-variable partial-integral target.  It defines
`F(T) = int_0^T sineDirichletKernel 1 x dx`, proves
`int_eps^T D_1 = F(T)-F(eps)`, proves the elementary bound `|F(T)| <= |T|`,
and therefore proves `F(eps) -> 0` as `eps -> 0+`.  Consequently, the future
atTop value `F(T) -> pi/2` would imply the TS227 unit-frequency product-filter
value.  TS228 does not prove that atTop Dirichlet value, Abel convergence,
`cosSquareImproperIntegral = pi/6`, the canonical `sinc^4` value, Plancherel
evidence, the explicit formula, Gallagher, or Goldbach.

TS229 prepares the Abel regularization route to the TS228 atTop value.  It
defines the damped unit Dirichlet kernel
`exp(-b*x) * sineDirichletKernel 1 x`, names the positive-damping evaluation
target, and keeps the Abel-to-cutoff bridge as a separate future input.  It
does prove the elementary scalar limit `pi/2 - arctan b -> pi/2` as
`b -> 0+`, and proves that packaged Abel evidence would supply the TS228
atTop target, the TS227 unit product-filter value, and the TS219
third-derivative cutoff value.  TS229 does not prove the damped integral
evaluation, the Abel-to-cutoff bridge, `cosSquareImproperIntegral = pi/6`, the
canonical `sinc^4` value, Plancherel evidence, the explicit formula,
Gallagher, or Goldbach.

TS230 refines the damped evaluation side of the TS229 Abel route.  It defines
the Laplace sine kernel and its finite partial integral, names the future
Laplace sine transform input, and proves the scalar arctangent tail
`int_b^A 1/(1+s^2) ds -> pi/2 - arctan b` as `A -> +infty`.  It then proves
that this scalar tail, together with the future Laplace sine transform and a
future Fubini/arctangent bridge, would supply the TS229 damped Dirichlet
evaluation target.  TS230 does not prove the Laplace sine transform, the
Fubini bridge, the damped evaluation target unconditionally, the Abel-to-cutoff
bridge, `cosSquareImproperIntegral = pi/6`, the canonical `sinc^4` value,
Plancherel evidence, the explicit formula, Gallagher, or Goldbach.

TS231 discharges the Laplace sine transform input isolated in TS230.  It
defines the explicit primitive for `exp(-s*x) * sin x`, proves its derivative,
uses finite-interval FTC to evaluate the partial integral, and proves the
exponential boundary term tends to zero for `s > 0`.  Consequently TS231 proves
`TS230.Goldbach.LaplaceSineTransformStatement`.  TS231 does not prove the
Fubini/arctangent bridge, the damped Dirichlet evaluation target
unconditionally, the Abel-to-cutoff bridge, `cosSquareImproperIntegral =
pi/6`, the canonical `sinc^4` value, Plancherel evidence, the explicit formula,
Gallagher, or Goldbach.

TS232 records the corrected interval-integral route for the remaining
Fubini/arctangent bridge.  It defines the damped partial-integral family at the
TS232 layer, proves that this statement is definitionally the TS229 damped
integral statement, and isolates the compact Fubini identity, uniform
Laplace-boundary limit, damped-difference atTop statement, and auxiliary
high-damping bound as explicit future inputs.  It also proves that, after
TS231, a future proof of `TS230.Goldbach.DampedDirichletFubiniBridgeStatement`
would supply `TS229.Goldbach.DampedDirichletEvaluationTarget`.  TS232 does not
prove the Fubini bridge, the damped evaluation target unconditionally, the
Abel-to-cutoff bridge, `cosSquareImproperIntegral = pi/6`, the canonical
`sinc^4` value, Plancherel evidence, the explicit formula, Gallagher, or
Goldbach.

TS233 discharges the compact Fubini identity isolated in TS232.  It defines
the finite rectangle kernel `exp((-x)*s) * sin x`, proves the parameter
primitive in `s`, rewrites the parameter integral as the damped-kernel
difference, proves integrability on the restricted compact rectangle, applies
the product Fubini swap, and rewrites the result back to
`TS232.Goldbach.CompactFubiniIdentityStatement`.  TS233 does not prove the
uniform Laplace-boundary limit, the damped-difference atTop statement, the
auxiliary high-damping bound, the corrected Fubini execution statement, the
damped Dirichlet evaluation target unconditionally, the Abel-to-cutoff bridge,
`cosSquareImproperIntegral = pi/6`, the canonical `sinc^4` value, Plancherel
evidence, the explicit formula, Gallagher, or Goldbach.

TS234 discharges the uniform Laplace-boundary limit isolated in TS232.  It
defines the boundary kernel from the TS231 finite Laplace formula, proves the
pointwise compact-parameter bound by `exp (-(b*T)) * (A + 1)`, upgrades it to
an interval-integral norm bound, and squeezes the integral to zero as
`T -> +infty` using `b > 0`.  TS234 does not prove the damped-difference
atTop statement, the auxiliary high-damping bound, the corrected Fubini
execution statement, the damped Dirichlet evaluation target unconditionally,
the Abel-to-cutoff bridge, `cosSquareImproperIntegral = pi/6`, the canonical
`sinc^4` value, Plancherel evidence, the explicit formula, Gallagher, or
Goldbach.

TS235 discharges the damped-difference atTop statement isolated in TS232.  It
rewrites the parameter integral of `laplaceSinePartialIntegral` as
`arctan A - arctan b` minus the integrated boundary term, using the TS231
finite formula and the TS230 arctangent interval integral.  TS234 makes the
boundary term vanish, and TS233 identifies the damped difference with this
parameter integral eventually on `atTop`.  TS235 does not prove the auxiliary
high-damping bound, the corrected Fubini execution statement, the damped
Dirichlet evaluation target unconditionally, the Abel-to-cutoff bridge,
`cosSquareImproperIntegral = pi/6`, the canonical `sinc^4` value, Plancherel
evidence, the explicit formula, Gallagher, or Goldbach.

TS236 discharges the auxiliary high-damping bound isolated in TS232.  It uses
the TS228 global bound on the unit Dirichlet kernel to dominate the damped
kernel by `exp((-A)*x)`, evaluates the finite majorant integral on `[0, T]`,
and bounds it by `1 / A` for `0 < A` and `0 <= T`.  TS236 does not prove the
corrected Fubini execution statement, the damped Dirichlet evaluation target
unconditionally, the Abel-to-cutoff bridge, `cosSquareImproperIntegral =
pi/6`, the canonical `sinc^4` value, Plancherel evidence, the explicit
formula, Gallagher, or Goldbach.

TS237 assembles the corrected Fubini execution route isolated in TS232.  It
uses TS235 for the damped-difference limit, TS236 for the high-damping bound,
and the limits `arctan A -> pi/2` and `1 / A -> 0` as `A -> +infty` to prove
the TS229 damped Dirichlet evaluation target.  TS237 does not prove the
Abel-to-cutoff bridge, the ordinary Dirichlet cutoff value,
`cosSquareImproperIntegral = pi/6`, the canonical `sinc^4` value, Plancherel
evidence, the explicit formula, Gallagher, or Goldbach.

TS238 records the post-TS237 Abel-to-cutoff frontier.  It packages the proved
TS237 damped evaluation together with the TS229 scalar Abel limit and proves
that a future `TS229.Goldbach.AbelToCutoffBridgeStatement` supplies the TS228
one-sided cutoff value, the TS227 unit product-cutoff value, and the TS219
third-derivative cutoff value.  TS238 does not prove the Abel-to-cutoff bridge,
the ordinary Dirichlet cutoff value, `cosSquareImproperIntegral = pi/6`, the
canonical `sinc^4` value, Plancherel evidence, the explicit formula,
Gallagher, or Goldbach.

TS239 performs a bounded direct-cutoff API probe against the locked Mathlib
revision.  The probed modules do not expose `Real.sinc`, the suggested
`Trigonometric.Sinc` module, or a ready-made ordinary Dirichlet cutoff theorem.
TS239 therefore defines a local `normalizedSinc` surrogate, proves that the
repository unit Dirichlet kernel agrees with it away from zero, and proves
that the TS228 partial integrals are unchanged by replacing the repository
kernel with `normalizedSinc`.  It also records `DirichletTailBoundStatement` as
the next direct-route fallback.  TS239 does not prove the cutoff value, the
Abel-to-cutoff bridge, `cosSquareImproperIntegral = pi/6`, the canonical
`sinc^4` value, Plancherel evidence, the explicit formula, Gallagher, or
Goldbach.

TS240 discharges the TS239 quantitative direct-tail fallback.  On every
positive interval `[T, U]` with `0 < T <= U`, it rewrites
`F(U) - F(T)` as the interval integral of the repository unit Dirichlet
kernel, applies the FTC to the primitive `-cos x / x`, evaluates the positive
majorant `int_T^U 1/x^2 dx = 1/T - 1/U`, and proves
`|F(U) - F(T)| <= 2 / T`.  TS240 does not prove Cauchy convergence, the
cutoff value, the Abel-to-cutoff bridge, `cosSquareImproperIntegral = pi/6`,
the canonical `sinc^4` value, Plancherel evidence, the explicit formula,
Gallagher, or Goldbach.

TS241 discharges the direct Cauchy convergence consequence of TS240.  Using
`Metric.cauchySeq_iff`, it chooses `N = 4 / epsilon`, orients the two large
endpoints by `le_total`, applies the TS240 tail estimate to the larger-minus-
smaller interval, and bounds both cases by `2 / N < epsilon`.  Completeness of
`Real` then supplies a real cutoff limit for the unit Dirichlet partial
integrals, recorded as `dirichletCutoffLimit`.  TS241 does not identify this
limit with `pi/2`, does not prove the Abel-to-cutoff bridge,
`cosSquareImproperIntegral = pi/6`, the canonical `sinc^4` value, Plancherel
evidence, the explicit formula, Gallagher, or Goldbach.

TS242 discharges the finite Abel summation identity for the damped Dirichlet
partial integral.  It proves that the TS228 partial integral `F` is
1-Lipschitz and continuous, proves `F' = sineDirichletKernel 1` away from
zero, then applies interval integration by parts to `exp(-b*x)` and `F(x)` on
`[0,T]`, using derivatives only in the positive open interval.  The result is
`D_b(T) = exp(-b*T)*F(T) + b*int_0^T exp(-b*x)*F(x) dx`.  TS242 also proves
`exp(-b*T)*F(T) -> 0` for `b > 0` from TS241 convergence and exponential
decay.  It does not identify the cutoff limit with `pi/2`, does not prove the
Abel identification or Abel-to-cutoff bridge, `cosSquareImproperIntegral =
pi/6`, the canonical `sinc^4` value, Plancherel evidence, the explicit
formula, Gallagher, or Goldbach.

TS243 discharges the local Abel final-value identification.  It centers the
finite TS242 Abel average at the TS241 cutoff limit `L`, proves the centered
identity
`A_b(T) - L*(1 - exp(-b*T)) =
b*int_0^T exp(-b*x)*(F(x)-L) dx`, cuts the integral at a fixed `R`, kills the
compact part by taking `b -> 0+`, and kills the tail by the TS241 convergence
`F(T) -> L`.  Comparing this with the TS237 damped Dirichlet value gives
`dirichletCutoffLimit = pi/2`, proves the TS228 unit cutoff statement, and
closes the TS229/TS238 Abel-to-cutoff bridge.  TS243 does not prove
`cosSquareImproperIntegral = pi/6`, the canonical `sinc^4` value, Plancherel
evidence, the explicit formula, Gallagher, or Goldbach.

TS244 propagates the TS243 unit one-sided cutoff value through the previously
proved TS228 product-filter decomposition and TS227 positive-frequency
scaling.  It proves the product-filter Dirichlet value `pi/2` at every
positive frequency and then applies the TS225/TS226 residual reduction to
prove the TS219 third-derivative cutoff value `pi`.  TS244 does not prove the
improper cutoff convergence to the existing Lebesgue cos-square integral or
the TS219 limiting assembly, so `cosSquareImproperIntegral = pi/6`, the
canonical `sinc^4` value, Plancherel evidence, the explicit formula,
Gallagher, and Goldbach remain open.

TS245 closes the cos-square cutoff assembly.  It transports the TS218
canonical sinc-fourth integrability through the positive scaling identity to
prove that `cosSquareHaarKernel` is integrable on `(0,+infinity)`.  The upper
partial integral converges by Mathlib's improper-integral theorem, while the
TS224 fourth-order remainder estimate makes the lower partial integral vanish.
This proves the TS219 product-filter convergence to the existing Lebesgue
integral.  Combining TS221 finite IPP, TS224 boundary vanishing, and the TS244
third-derivative cutoff value `pi` gives the same cutoff limit `pi/6`; uniqueness
of limits proves `cosSquareImproperIntegral = pi/6`.  TS245 does not prove the
canonical `sinc^4` value, Plancherel evidence, the explicit formula, Gallagher,
or Goldbach.

TS246 closes the canonical sinc-fourth scalar calculation.  It applies the
TS213 algebraic assembly to the TS245 cos-square value `pi/6`, the TS218
positive-half-line scaling identity, and the TS218 full-line evenness identity.
This proves `TS209.Goldbach.CanonicalSincFourthIntegralValueStatement`, namely
the full-line value `2*pi/3`.  TS209 already provides the implication from this
value to the specialized TS204 triangle-spline Plancherel evidence; TS246
records that frontier but leaves the concrete evidence assembly, the explicit
formula, Gallagher, and Goldbach open.

TS247 closes the specialized triangle-spline Plancherel evidence slot required
by TS204.  It feeds the TS246 canonical value into the TS209/TS208 bridge and
constructs a concrete `TriangleSplinePlancherelInputEvidence` term.  From that
term it extracts the TS174 triangle-spline Plancherel isometry and proves the
exact pi-scaled squared-sinc energy
`ENNReal.ofReal (Real.sqrt (2/3))`.  This is the kernel-specific Wall 1 result;
TS247 does not claim a general Plancherel theorem and does not prove the
effective explicit formula input, Gallagher, or Goldbach.

TS248 consumes the specialized Wall 1 result in the final analytic input
architecture.  It fixes the Plancherel field of the TS204 contract bundle to
the concrete triangle-spline contract and supplies its evidence from TS247.
Consequently, constructing final analytic evidence now requires only effective
explicit-formula evidence and Gallagher evidence.  TS248 also specializes this
reduction to the concrete TS206 explicit-formula contract family and composes a
supplied complete bundle with the TS205 adapter to obtain TS200 OTSA input
evidence.  The TS206 evidence, Gallagher evidence, TS205 adapter, TS200
conclusion bridge, and unconditional Goldbach theorem remain open.

TS249 discharges the effective-constants admissibility field of the TS206
explicit-formula contract.  Its constants family keeps the main-term model and
all powers arbitrary, takes the zero and residual constants in `NNReal`, and
represents the lower scale as an offset plus one.  The complete TS206 evidence
is therefore reduced to four core analytic propositions and the separate TS181
compatibility proposition.  TS249 also feeds that reduced evidence and a
supplied Gallagher evidence term through TS248, with Wall 1 and constants
admissibility already populated.  No explicit-formula identity or bound,
TS181 compatibility, Gallagher evidence, OTSA bridge, or Goldbach theorem is
proved by this sprint.

TS250 audits the exact TS206 compatibility proposition before discharging it.
That proposition is only `Nonempty` for the TS181 contract type and does not
depend on TS206 constants, data, identities, or bounds.  TS250 constructs a
minimal structural inhabitant using an empty abstract zero family and zero
abstract contributions, then uses it to reduce TS206 evidence to the four
analytic core fields.  This is valid for the exact current type, but it is not
evidence about the actual Riemann-zeta zeros and not an effective cross-contract
alignment.  Those limitations, Gallagher, both OTSA bridges, and Goldbach
remain explicit non-claims.

TS251 finds a blocking quantifier defect in the current TS206 main-term field.
The TS206 identity constrains only the combination `mainTerm -
zeroContribution + residualTerm`; it does not uniquely determine `mainTerm`.
TS251 shifts the proposed main term by one and compensates in the zero
contribution, preserving the identity while contradicting the universal
main-term model.  Hence the TS249 core evidence is uninhabited for every
admissible constants package, and the TS250 constructors cannot be populated
under the current contract.  TS251 defines a corrected target in which the
identity and main-term identification belong to the same existential data
witness.  No corrected TS206/TS204 contract or analytic theorem is installed.

TS252 installs the TS251 correction as a parallel TS204 contract without
modifying TS206 or any historical module.  The identity and main-term fields of
the corrected contract are definitionally the same joint existential
proposition, so both refer to one selected explicit-formula data witness.  The
zero and residual bounds keep their TS206 statement shapes.  Corrected core
evidence and Gallagher evidence now feed the generic TS248 constructor directly
to produce final analytic evidence with Wall 1 populated.  TS252 does not
convert corrected evidence into evidence for the impossible TS206 contract and
does not prove the joint identity, either bound, Gallagher, an OTSA bridge, or
Goldbach.

TS253 audits the two universal bound statements retained by TS252.  Even after
fixing the selected main-term model, the identity leaves one free parameter
between the zero contribution and the residual.  TS253 constructs one data
package with zero contribution `abs(majorant) + 1` and another with residual
term `abs(majorant) + 1`, adjusting the remaining component so that both the
identity and main-term identification still hold.  Consequently both TS206
bound statements are false at every positive lower scale, and the TS251 core
and TS252 corrected evidence are uninhabited for admissible constants.  TS253
defines a fully corrected statement requiring identity, main term, zero bound,
and residual bound on one existential witness.  It does not install that
contract or prove any analytic estimate.

TS254 installs the TS253 single-witness statement as a parallel TS204 contract.
The identity, main-term, zero-bound, and residual-bound slots are all
definitionally equal to `FullyCorrectedExplicitFormulaStatement K`; none is
replaced by `True`.  One core proof therefore populates all four evidence
fields, while TS249 supplies admissible constants, TS250 supplies structural
TS181 compatibility, and TS248 supplies the concrete Wall 1 evidence.  TS254
does not alter TS206 or TS252, introduce RH, prove the fully corrected formula,
construct an actual zeta-zero family, prove Gallagher or either OTSA bridge, or
claim Goldbach.

TS255 factors the TS253 monolithic existential witness through two named real
functions of the natural scale.  These functions determine canonical TS206
data with `mainTerm = K.mainTermModel X`; the identity, zero bound, and residual
bound are then stated by reusing the existing TS206 predicates on that same
data.  TS255 proves real typed assemblers from these three obligations to the
TS253 core and onward to TS254 evidence, including the TS249/TS250-specialized
route.  It does not construct a zeta-zero contribution, define contour
residuals, prove any named obligation, introduce RH, prove Gallagher or either
OTSA bridge, or claim Goldbach.

TS256 gives the TS255 zero function a finite spectral shape.  A TS185
Riemann-zeta zero-family API contract is paired with a scale-dependent
`Finset Complex` that is complete below a nonnegative height.  Multiplicity is
taken from TS185, while the spectral summand remains abstract until its Mellin
normalization is verified.  The real part of the finite complex sum supplies
the named zero function, and typed constructors route separately supplied
identity and bounds into TS255 and TS253.  TS256 does not construct the zero
API contract or finite truncation, prove local finiteness or reality, define an
infinite zero sum, select a concrete summand, introduce RH, prove any analytic
bound, Gallagher, either OTSA bridge, or Goldbach.

TS257 fixes the triangle-spline Mellin normalization used by the TS256 finite
sum.  The positive Mellin kernel is `1 / (s * (s + 1))`, equivalently
`1 / s - 1 / (s + 1)` away from its poles.  Because TS206 already subtracts
`zeroContribution`, the TS256 summand is stored as
`X^rho / (rho * (rho + 1))`; the opposite-signed contour residue is named
separately and no extra `1 / rho` is introduced.  TS257 proves the algebraic
identities and denominator nonvanishing for TS185 nontrivial zeros, then
constructs the concrete TS255 zero function through TS256.  The Mellin
integral evaluation, Mellin/Fourier equivalence, contour interpretation,
conjugation symmetry, finite-sum reality, explicit formula, analytic bounds,
RH, Gallagher, both OTSA bridges, and Goldbach remain open.

TS258 closes the algebraic conjugation layer for the finite zero contribution.
The concrete summand commutes with `star`, and TS185 conjugate closure together
with TS256 completeness makes every finite truncation conjugation-closed.
TS185 does not state that multiplicities are preserved by conjugation, so TS258
names that property as an explicit premise rather than adding it silently.
Under that premise, reindexing the finite sum by `Equiv.star` proves that the
weighted sum is fixed by conjugation and has zero imaginary part.  Consequently
the TS255 real projection loses no information.  Multiplicity invariance,
Mellin evaluation, the explicit formula, both analytic bounds, Gallagher, both
OTSA bridges, and Goldbach remain open.

TS259 packages the sole remaining TS258 premise without changing TS185.  The
new wrapper contains a base TS185 contract together with an explicit proof that
conjugate zeros have equal multiplicity.  For every supplied wrapper and TS256
truncation, TS259 derives conjugation invariance, zero imaginary part, TS256
reality, and exact recovery of the complex sum from the TS255 real function.
Applying `Complex.abs` also proves the exact identity between the real absolute
value expected by TS255 and the natural complex modulus of the spectral sum.
No concrete wrapper is constructed: realizing multiplicity as an order of
vanishing and proving its conjugation invariance remain open, as do the
explicit formula, all analytic bounds, Gallagher, both OTSA bridges, and
Goldbach.

TS260 replaces the abstract notion of zero order by Mathlib's canonical
`AnalyticAt.order`.  It proves `riemannZeta` differentiable on the complement
of one and analytic at every zero selected by TS185, since critical-strip
membership excludes the pole.  The local `order_eq_nat_iff` factorization is
exported directly, and a realization contract identifies the natural-valued
TS185 multiplicity with this finite `ENat` order.  If analytic order is
preserved by conjugation, cast injectivity gives conjugate multiplicities and
the full TS259/TS258 finite-reality route follows.  The order-conjugation
theorem and a concrete realization remain open, as do the explicit formula,
all analytic bounds, Gallagher, both OTSA bridges, and Goldbach.

TS261 closes the generic order-conjugation mechanism.  Neighborhood properties
are pulled back through `tendsto_star`; local vanishing gives equality in the
`Top` branch, while a finite `ENat` order is converted to a natural exponent,
transported through the exact local factorization, and reconstructed with
`order_eq_nat_iff`.  For zeta, Schwarz reflection identifies the doubly
conjugated function with `riemannZeta`.  A two-field input contract therefore
supplies the exact TS260 order-conjugation statement and all downstream TS259
and TS258 reality results.  TS261 does not construct the generic analyticity
input, Schwarz reflection, or a concrete multiplicity realization; the
explicit formula, all analytic bounds, Gallagher, both OTSA bridges, and
Goldbach remain open.

TS262 discharges the generic analyticity input left by TS261 without rebuilding
formal power series.  It restricts a complex derivative to real scalars,
composes input and output with `Complex.conjCLE`, proves that the resulting real
linear map is the restriction of multiplication by the conjugate derivative,
and lifts it back with `hasFDerivAt_of_restrictScalars`.  Thus the derivative of
the double-conjugated function at `star z` is `star f'`.  Transport through the
neighborhood characterization of complex analyticity proves both directions
of the local analytic equivalence.  The TS261 contract is consequently reduced
to Schwarz reflection for `riemannZeta` alone.  That reflection theorem, a
concrete multiplicity realization, the explicit formula, all analytic bounds,
Gallagher, both OTSA bridges, and Goldbach remain open.

TS263 proves the remaining Schwarz-reflection input rather than introducing a
new assumption.  On the half-plane `1 < re s`, conjugation is pushed through
the zeta Dirichlet series with `Complex.cpow_conj` and `Complex.conj_tsum`.
Both `riemannZeta` and its double conjugate are analytic on the connected set
`Complex \ {1}`, so the identity principle extends the equality from a
neighborhood of two to the punctured plane.  Mathlib's conventionally assigned
value at one is then checked directly to be real.  The full TS261 input contract
and the TS260 order-conjugation theorem are therefore unconditional.  A
concrete TS185 zero family and multiplicity realization are still not
constructed; the explicit formula, all analytic bounds, Gallagher, both OTSA
bridges, and Goldbach remain open.

TS264 removes the remaining abstract family parameter from the finite zero-sum
route.  Its selected set is exactly the TS185 predicate for zeros of
`riemannZeta` in the open critical strip.  Analytic uniqueness on
`Complex \ {1}` and the nonzero value at zero prove that the local analytic
order is finite; local factorization at a selected zero proves that it is
nonzero.  Thus `order.toNat` gives a positive natural multiplicity whose
`ENat` coercion is the exact TS260 order.  TS263 gives conjugation closure and
`riemannZeta_one_sub` gives symmetry about one half.  The resulting concrete
TS185 and TS260 contracts make every future valid TS256 truncation real and
its real projection lossless.  No global zero summability, exact enumeration,
or concrete truncation is constructed; the explicit formula, all analytic
bounds, Gallagher, both OTSA bridges, and Goldbach remain open.

TS265 constructs the finite truncation that TS264 left quantified.  The global
zero set of `riemannZeta` is proved closed and discrete: isolated-zero theory
handles every point away from one, while `riemannZeta_residue_one` supplies a
punctured neighborhood without zeros at the exceptional point.  The
cofinite/cocompact characterization then makes every compact intersection
finite.  Since a nontrivial zero with `abs im <= T` lies in the closed ball of
radius `T + 1`, the height-truncated set is finite and yields an exact
noncomputable `Finset`.  With height `X`, this fills all four TS256 truncation
fields and produces a concrete real finite spectral sum with lossless real
projection.  No numerical zero-enumeration algorithm, zero-counting or density
bound, global summability, explicit formula, Gallagher estimate, OTSA bridge,
or Goldbach theorem is supplied.

TS266 takes the first unconditional estimate of that concrete finite sum.  It
names each multiplicity-weighted TS257 summand and defines the finite norm mass
as the sum of their complex moduli.  `norm_sum_le` bounds the complex spectral
sum by this mass, while TS265 transports the same inequality exactly to the
real TS255 contribution.  A second theorem shows that a nonnegative uniform
per-term bound and a real upper bound for the selected `Finset` cardinality
imply `abs zeroContribution <= countBound * termBound`.  The two effective
majorants remain explicit open inputs; no zero-density estimate, contour or
residue identity, explicit formula, residual estimate, Gallagher theorem,
OTSA bridge, or Goldbach theorem is supplied.

TS267 fills the TS266 uniform-term slot without importing a new analytic
hypothesis.  Each selected weighted-term magnitude is packaged in `NNReal`,
and its finite supremum is a nonnegative bound by `Finset.le_sup`.  Conversely,
`Finset.sup_le` proves that this is the least bound satisfying the TS266
contract.  The exact real cardinality fills the counting slot definitionally,
so TS266 yields an unconditional exact-cardinality-times-exact-supremum bound.
This closes only the finite order-theoretic layer: both exact functions remain
noncomputable, and no closed form in `X`, multiplicity estimate, denominator
lower bound, zero-counting asymptotic, density theorem, explicit formula,
residual estimate, Gallagher theorem, OTSA bridge, or Goldbach theorem is
supplied.

TS268 exposes the analytic scale inside the exact TS267 bound.  The concrete
TS264 strip condition and Mathlib's natural-base complex-power norm formula
give `abs ((X : Complex)^rho) <= max 1 X`, sharpening to `<= X` for `1 <= X`.
The weighted TS266 term is then factored exactly into this power and a residual
multiplicity-denominator factor.  A finite `NNReal` supremum of the residual
factor produces a scale-visible TS266 uniform bound and contribution estimates
of the form `countBound X * (X * residualSup X)`.  No critical-line equality or
RH is used.  The residual supremum remains noncomputable, and no effective
multiplicity bound, denominator lower bound, zero-counting theorem, density
estimate, global summability, contour shift, explicit formula, Gallagher
theorem, OTSA bridge, or Goldbach theorem is supplied.

TS269 isolates the remaining denominator geometry without inserting a false
uniform lower bound near the real axis.  For every complex `rho`, the product
modulus `abs (rho * (rho + 1))` dominates `abs rho.im ^ 2`.  The exact TS265
selection is therefore split into a low zone, whose weighted norm mass is
retained unchanged, and a high zone `1 <= abs rho.im`, where each residual
factor is bounded by multiplicity divided by `abs rho.im ^ 2`.  The resulting
real contribution estimate is unconditional and finite.  No numerical
first-zero height, effective multiplicity count, zero-counting theorem,
global weighted summability, explicit formula, Gallagher theorem, OTSA bridge,
or Goldbach theorem is supplied.

TS270 uses the counting object that actually occurs in the spectral sum:
multiplicity-weighted zero count rather than plain `Finset.card`.  In the high
zone, `1 <= abs rho.im` makes each quadratic residual envelope at most the
corresponding analytic multiplicity.  Summing gives an unconditional bound of
the high weighted residual mass by the exact high multiplicity count, which is
itself bounded by the full multiplicity count up to height `X`.  Generic
contracts then transport any future high-zone or global effective upper bound
to the real TS255 contribution, while the low-zone mass remains exact.
No zero-simplicity assumption, effective `N(T)` estimate, density theorem,
global summability, explicit formula, Gallagher theorem, OTSA bridge, or
Goldbach theorem is supplied.

TS271 retains the quadratic decay that the crude TS270 count bound discarded.
It defines exact shells `(A,B]` by finite-set difference, proves that their
multiplicity count is exactly `N_mult(B) - N_mult(A)`, and bounds each shell's
residual mass by that increment divided by `A^2`.  A generic finite Abel
identity then converts these increments into cumulative counts multiplied by
decreasing reciprocal-square weights.  Consequently every future TS270 global
counting bound yields an amortized finite shell estimate.  No particular shell
chain is yet proved to cover the complete high zone, and no effective count,
infinite convergence, explicit formula, Gallagher theorem, OTSA bridge, or
Goldbach theorem is supplied.

TS272 closes the finite high-zone coverage left open by TS271.  The positive
chain `height n = n + 1` yields exactly the shells `(1,2]` through `(X-1,X]`
when evaluated at `K = X - 1`.  The possible zeros at `abs rho.im = 1` are
kept in a separate exact boundary selection whose residual mass equals its
multiplicity count.  The complete TS269 high selection is then the disjoint
union of this boundary and `(1,X]`, so every TS270 global count bound produces
a full real zero-contribution estimate with the TS271 Abel damping retained.
No effective `N_mult(T)` estimate, density theorem, infinite convergence,
explicit formula, Gallagher theorem, OTSA bridge, or Goldbach theorem is
supplied.

TS273 gives the first analytically meaningful shape to the TS270 counting
input.  The exact multiplicity count is monotone in height, so a bound
`N_mult(T) <= C*T*log(T+2)` proved only for `T >= 1` extends safely to every
real height through `C*max(T,1)*log(max(T,1)+2)`.  A separate disk-counting
package isolates the future Jensen route as height-to-disk and disk-growth
inequalities, without inventing a Riemann xi implementation or importing an
API absent from the locked Mathlib revision.  Both inputs route through TS272
to the full finite real zero contribution.  No effective constant, infinite
convergence, explicit formula, Gallagher theorem, OTSA bridge, or Goldbach
theorem is supplied.

TS274 backports the finite counting core of Jensen's inequality without
pretending that the locked Mathlib revision contains its modern analytic
support.  For exact finite zero data in concentric disks of radii `r < R`, it
proves each weight `log(R/|z-c|)` at least `log(R/r)`, sums with natural
multiplicities, and divides by the positive logarithmic gap.  Therefore a
weighted boundary estimate gives the standard finite zero-count quotient.
The circle-average identity that supplies that weighted estimate remains the
single named analytic input; no harmonic mean-value theorem, analytic zero
Finset construction, concrete xi function, effective zeta count, explicit
formula, Gallagher theorem, OTSA bridge, or Goldbach theorem is supplied.

TS275 replaces the single TS274 boundary-estimate gap by an explicit finite
factorization route.  It uses three radii `0 < r < R < S`, keeps the inner
counted zeros separate from the complete finite family below `R`, and defines
the corresponding multiplicity-weighted zero polynomial by `Finset.prod`.
The module proves its analyticity, exact zero set, center and Jensen-mass
identities, the inner-to-factor mass comparison, and nonvanishing of `f` on
the averaging sphere from buffered data `f = P*g`.  A normalized angular
average then reduces the TS274 estimate to the linear-factor circle means,
the logarithmic mean-value identity for the nonvanishing quotient, and the
pointwise boundary norm bound.  No concrete buffered factorization, harmonic
mean-value theorem, xi function, effective zeta count, explicit formula,
Gallagher theorem, OTSA bridge, or Goldbach theorem is supplied.

TS276 closes the linear-factor port of TS275.  After normalizing an inner root
to `abs a < 1`, it proves that `Complex.log (1 - star(a)*z)` is continuous on
the closed unit disk and differentiable inside it, applies Cauchy's formula at
the center, and takes real parts to obtain zero normalized boundary-log
average.  Exact unit-circle conjugation geometry and scale extraction then
give `average log |z-rho| = log R` for every selected factor.  The resulting
constructor directly inhabits `LinearFactorAngularAverageStatement`; no
Fourier series, quotient logarithmic mean-value theorem, concrete buffered
factorization, xi function, effective zeta count, explicit formula, Gallagher
theorem, OTSA bridge, or Goldbach theorem is supplied.

TS277 isolates the exact remaining quotient step.  It first proves directly
from the buffered TS275 fields that `log |g|` is continuous and integrable on
the averaging circle.  Given explicit analytic data `L` on the buffered disk
with `exp L = g`, it applies Cauchy's formula to obtain the complex angular
mean of `L`, commutes real parts with the interval integral, and constructs
the full `NonvanishingQuotientAngularAverageStatement`.  The locked Mathlib
revision does not provide the required holomorphic-log construction on a
disk, so that construction remains a named proposition rather than a hidden
assumption.  No concrete buffered factorization, xi function, effective zeta
count, explicit formula, Gallagher theorem, OTSA bridge, or Goldbach theorem
is supplied.

TS278 supplies the generic open-ball primitive theorem missing from the
locked Mathlib revision.  It defines the primitive by a horizontal-then-
vertical wedge integral, obtains path independence locally from rectangle
Cauchy-Goursat, and proves the derivative by separate horizontal and vertical
little-o estimates.  This is the analytic engine needed for the future
`g' / g` construction, but it deliberately stops at an open ball: uniform
extension beyond the closed buffered disk and construction of the TS277
holomorphic logarithm remain open.  No complete Jensen theorem, concrete xi
function, effective zeta count, explicit formula, Gallagher theorem, OTSA
bridge, or Goldbach theorem is supplied.

TS279 applies that primitive theorem to the buffered quotient.  Analyticity
and nonvanishing define an open locus containing the compact TS275 analytic
closed disk; a positive uniform thickening is exactly a larger concentric
open ball.  On this ball, `deriv g / g` is analytic and has the TS278 wedge
primitive `P`.  The function `g*exp(-P)` has derivative zero and is constant,
so `P-P(center)+Complex.log(g(center))` exponentiates exactly to `g` on the
original closed disk.  This closes the TS277 construction statement and the
quotient angular average.  Together with TS276, the finite Jensen boundary
estimate is now reduced to the circle norm bound alone.  No concrete buffered
factorization, xi growth estimate, effective zeta count, explicit formula,
Gallagher theorem, OTSA bridge, or Goldbach theorem is supplied.

TS280 fills the remaining generic circle norm input canonically.  The
absolute values of `D.f` on the averaging sphere form a compact real set, so
their supremum is finite.  The majorant `max 1 (sSup values)` is positive and
dominates every boundary value, yielding the TS275 boundary statement.  The
TS279 facade then gives the complete TS274 weighted estimate, and TS274 gives
the direct finite multiplicity-count quotient.  This is unconditional for
each already-supplied buffered factorization datum, but the majorant remains
noncomputable and no effective radius-growth formula, concrete xi datum,
explicit formula, Gallagher theorem, OTSA bridge, or Goldbach theorem is
supplied.

TS281 gives the first concrete end-to-end realization of that generic Jensen
machine.  For any finite factor-zero datum it takes the zero polynomial itself
as `f` and the constant function `1` as the analytic nonvanishing quotient.
On the averaging sphere each factor satisfies
`abs(z-rho) <= R + abs(rho-center)`, so a finite product gives an explicit
boundary norm with no compact supremum.  TS279 and TS274 then yield the full
weighted Jensen estimate and multiplicity-count quotient, and the TS280
canonical norm is proved no larger than the product bound.  This validates the
pipeline on a concrete polynomial class; it does not yet construct Riemann xi,
factor xi on buffered disks, or prove effective xi growth.

TS282 moves from the polynomial validation to the actual L-function candidate.
Mathlib's entire additive regularization of completed zeta is not itself xi;
the module proves that the affine twist
`(s*(s-1)*completedRiemannZetaZero(s)+1)/2` is entire, symmetric under
`s -> 1-s`, equals `1/2` at `0` and `1`, and agrees away from those endpoints
with the standard completed-zeta definition of xi.  A geometrically exact
finite-zero specification converts to TS275 zero data, while a separate
analytic nonvanishing quotient assembly converts to buffered factorization
data and receives TS280 Jensen immediately.  The finite zero extraction,
local normal forms, zero-free collar, and quotient construction are not yet
supplied.

TS283 supplies the finite geometry previously left open.  The entire xi
candidate is not locally zero because its value at zero is `1/2`; isolated
zeros therefore make its global zero set closed and discrete, and compact
intersections are finite.  For every `r > 0`, the module takes the maximum of
the finitely many zero radii below `T = r + 3` and places explicit averaging
and analytic radii between that maximum and `T`.  This constructs exact inner
and factor `Finset`s and proves the whole collar between those two radii is
zero-free.  Multiplicities, local normal forms, and quotient assembly remain
for later sprints.

TS284 adds the canonical analytic information to that geometry.  The order of
xi is never top because TS283 excludes local identically-zero behavior, and at
an actual zero it cannot be zero.  Its natural value is therefore a positive
multiplicity.  Mathlib's `AnalyticAt.order_eq_nat_iff` supplies the analytic
nonvanishing local factor with exactly that exponent.  Combining these facts
with TS283 constructs a genuine TS282 finite-zero factorization specification
for every positive inner radius.  Only the finite global quotient assembly is
still missing from the buffered xi datum.

## What Is Proved

TS16 proves the finite combinatorial comparison:

```lean
TS16.Goldbach.pair_count_le_energy
```

This removes the previous local counting obligation from TS15. The proof uses
only finite sets, products, sigma finsets, and cardinality comparison: close
pairs are injected into energetic triples.

TS17, TS18, and TS19 are relative discharges. They do not hide assumptions as
global axioms; instead they pass the remaining analytic inputs as explicit
structures.

TS21 adds a budgeted version of the short-interval second-moment interface:

```lean
TS21.Goldbach.Problem_E1K
TS21.Goldbach.ShortIntervalPrimeSecondMomentK
TS21.Goldbach.BrunTitchmarshShortInterval
TS21.Goldbach.BrunTitchmarshLocalWindowBudget
```

This lets later threshold computations carry a concrete constant, currently
`K = 20`, instead of forcing the TS18-style estimate into the rigid `C <= 1`
shape too early. TS21 also records the scale-correct local-window transport:
a uniform bound `shortPrimeLocalCount x Q n <= B` implies
`shortPrimeEnergy x Q <= (x+1) * B^2`.

TS22 generalizes the downstream target by introducing:

```lean
TS22.Goldbach.ShortIntervalScale
TS22.Goldbach.Problem_E1Scale
TS22.Goldbach.brunTitchmarshClosedFormScale
TS22.Goldbach.BrunTitchmarshNatIntervalBound
TS22.Goldbach.ScaledLargeSieveInfrastructure
```

This keeps the raw TS15 energy intact while allowing Brun-Titchmarsh and large
sieve inputs to use their natural normalization scales. TS22 also provides an
interval bridge from a future natural-number Brun-Titchmarsh theorem to the
local window budget used by TS21, and a scale-aware large-sieve discharge:

```lean
TS18.Goldbach.DirichletCharacterBridge
  + TS22.Goldbach.ScaledLargeSieveInfrastructure S
  => TS22.Goldbach.Problem_E1Scale S K
```

TS23 connects the TS22 scale layer to the TS19 OTSA residual ledger:

```lean
TS22.Goldbach.Problem_E1Scale S K
  + TS23.Goldbach.ScaleToOTSAControl S
  + scaled OTSA coupling
  + TS23.Goldbach.ScaledOTSAAdmissible
  => TS19.OTSA.OTSAResidualBound R
```

TS24 closes the arithmetic scale-domination layer for Brun-Titchmarsh budgets:

```lean
TS22.Goldbach.BrunTitchmarshNatIntervalBound
  => TS24.Goldbach.Problem_E1Scale_from_natIntervalBound_paddedClosedForm
```

The padded closed form keeps the unavoidable `+1` loss from `Nat.ceil`
explicit, so no unproved rounding claim is smuggled into the closed-form scale.

TS25 packages the padded-scale OTSA entry point:

```lean
TS22.Goldbach.BrunTitchmarshNatIntervalBound
  + TS23.Goldbach.ScaleToOTSAControl
      TS24.Goldbach.brunTitchmarshPaddedClosedFormScale
  + TS23.Goldbach.ScaledOTSAAdmissible
  + local OTSA coupling
  => TS19.OTSA.OTSAResidualBound R
```

TS26 adds an exact rational certificate layer for OTSA numerical feasibility:

```lean
TS26.Goldbach.OTSARationalCertificate
  => TS26.Goldbach.scaledConstantsOfRat
  => TS26.Goldbach.scaledOTSAAdmissible_of_rat
```

The admissibility inequality is checked over `Rat` and then transported to the
real-valued TS23 constants, avoiding floating-point certificates.

TS27 adds a labelled register for candidate OTSA constants and a deliberately
non-final smoke test:

```lean
TS27.Goldbach.OTSACert_smoke_test
TS27.Goldbach.OTSARegister_smoke_test
TS27.Goldbach.smoke_test_scaledOTSAAdmissible
```

The smoke-test constants verify the TS26-to-TS23 plumbing only. They are not
claimed as certified spectral, trace, Mellin-tail, or scale-transfer values.

TS28 adds a typed-status register and a candidate-v0 package:

```lean
TS28.Goldbach.ConstantStatus
TS28.Goldbach.OTSACert_candidate_v0
TS28.Goldbach.OTSARegister_candidate_v0
TS28.Goldbach.candidate_v0_scaledOTSAAdmissible
```

The candidate-v0 rational inequality is Lean-checked, but the package is not a
final OTSA certificate until each constant has a sourced analytic majorant.

TS29 adds a provenance ledger for the candidate-v0 constants:

```lean
TS29.Goldbach.ConstantProvenance
TS29.Goldbach.SourcedRatBound
TS29.Goldbach.OTSAConstantProvenanceRegister
TS29.Goldbach.OTSAProvenance_candidate_v0
TS29.Goldbach.candidate_v0_not_certified
```

At this point `Ck` is marked as a narrative-source bound, while `Ct`, `Cm`, and
`Cscale` remain explicit placeholders.

TS30 refines the remaining Brun-Titchmarsh obligation into Selberg-facing
sub-obligations:

```lean
TS30.Goldbach.SelbergSieveIntervalBound
TS30.Goldbach.SelbergMajorantBudgetComparison
TS30.Goldbach.SelbergBrunTitchmarshInfrastructure
TS30.Goldbach.brunTitchmarshNatIntervalBound_from_selberg
```

This keeps Brun-Titchmarsh external, but identifies the exact future Mathlib
target: a Selberg-sieve interval majorant plus the arithmetic comparison with
the TS22 ceiling budget.

TS31 adds a first asymptotic-majorant candidate package after the TS29
provenance ledger:

```lean
TS31.Goldbach.OTSACert_candidate_v1
TS31.Goldbach.OTSARegister_candidate_v1
TS31.Goldbach.OTSAProvenance_candidate_v1
TS31.Goldbach.candidate_v1_scaledOTSAAdmissible
```

The rational admissibility calculation is exact:

```text
Cscale * (Ck * Ct + Cm) = 53/50 <= 26.
```

Only `Ck` is currently attached to a narrative source. `Ct`, `Cm`, and
`Cscale` remain explicit placeholders until sourced rational upper bounds are
available.

TS32 isolates the trace contribution as an explicit local contract:

```lean
TS32.Goldbach.TraceMajorantContract
TS32.Goldbach.Ct_target_v2
TS32.Goldbach.OTSACert_candidate_v2
TS32.Goldbach.OTSAProvenance_candidate_v2
TS32.Goldbach.candidate_v2_scaledOTSAAdmissible
```

It proves that any future trace contract with `Ct <= 1/2` gives a rational
OTSA certificate. If the target value `Ct = 1/2` is supplied, the scaled value
is:

```text
1 * ((3/50) * (1/2) + 1) = 103/100 <= 26.
```

The trace constant is deliberately marked as conditional evidence, not as a
certified analytic derivation.

TS33 adds the last two asymptotic-majorant contracts:

```lean
TS33.Goldbach.MellinTailMajorantContract
TS33.Goldbach.ScaleTransferMajorantContract
TS33.Goldbach.OTSACert_candidate_v3
TS33.Goldbach.OTSAProvenance_candidate_v3
TS33.Goldbach.candidate_v3_scaledOTSAAdmissible
```

It proves that the contracted bounds

```text
Ck = 3/50, Ct <= 1/2, Cm <= 1, Cscale <= 2
```

imply the exact rational OTSA threshold:

```text
2 * ((3/50) * (1/2) + 1) = 103/50 <= 26.
```

This removes raw placeholder constants from the v3 package by replacing them
with explicit local contracts. Those contracts still need genuine analytic
instantiations before a final certificate can be claimed.

TS34 begins the harmonic-analysis front by isolating the measure-transport
layer needed for the concrete Mellin/Fourier bridge:

```lean
TS34.MellinJackson.MellinFourierMeasureTransport
TS34.MellinJackson.tsigmaFun_congr_of_measureTransport
TS34.MellinJackson.tsigmaInvFun_congr_of_measureTransport
```

It does not construct the `Lp`-level isometry. It records the four local
almost-everywhere transport facts needed to move between the weighted Mellin
measure, Lebesgue measure restricted to `(0, infinity)`, and Lebesgue measure
under `exp`/`log`.

TS35 crosses the almost-everywhere quotient layer:

```lean
TS35.MellinJackson.MellinFourierMeasurabilityTransport
TS35.MellinJackson.MellinFourierAEEqTransport
TS35.MellinJackson.TsigmaAEEqFun
TS35.MellinJackson.TsigmaInvAEEqFun
TS35.MellinJackson.TsigmaInvAEEqFun_left
TS35.MellinJackson.TsigmaInvAEEqFun_right
```

It reuses the existing TS17 quotient construction by feeding it the TS34
congruence lemmas and a local strong-measurability contract. It still stops
before the `Lp` quotient, the `L²` isometry, Plancherel, and the Fourier-tail
infrastructure.

TS36 packages the remaining `Lp`-level obligations needed to construct the
future Mellin-Fourier `L²` isometry:

```lean
TS36.MellinJackson.MellinFourierLpIsometryInfrastructure
TS36.MellinJackson.MellinFourierLpIsometryRoadmap
TS36.MellinJackson.MellinFourierLpIsometryTarget
TS36.MellinJackson.ae_transport_of_roadmap
```

It records preservation of `Memℒp`, equality of `snorm`, and a.e. linearity for
the representative operators. It deliberately does not construct the final
`LinearIsometryEquiv`; that remains the next concrete `Lp`-API sprint.

TS37 isolates the norm side of the TS36 roadmap:

```lean
TS37.MellinJackson.MellinFourierLpNormInputs
TS37.MellinJackson.normInputsOfRoadmap
TS37.MellinJackson.MellinFourierLpNormInputsTarget
TS37.MellinJackson.normInputsTarget_of_roadmap
```

It focuses only on `Memℒp` preservation and `snorm` preservation for
`TsigmaFun` and `TsigmaInvFun`. Quotient linearity, the final
`LinearIsometryEquiv`, and Fourier-tail/Plancherel remain in later sprints.

TS38 isolates the linearity side of the TS36 roadmap:

```lean
TS38.MellinJackson.MellinFourierLpLinearityInputs
TS38.MellinJackson.lpInfrastructureOfNormAndLinearity
TS38.MellinJackson.linearityInputsOfRoadmap
TS38.MellinJackson.MellinFourierLpLinearityInputsTarget
TS38.MellinJackson.linearityTarget_of_roadmap
```

It records the a.e. additivity and scalar-compatibility inputs for `TsigmaFun`
and `TsigmaInvFun`. Together, TS37 and TS38 reconstruct the full TS36
`MellinFourierLpIsometryInfrastructure`, leaving the final
`LinearIsometryEquiv` assembly to TS39.

TS39 gives the final specification of the Mellin-Fourier `L²` isometry:

```lean
TS39.MellinJackson.MellinFourierLpIsometry
TS39.MellinJackson.MellinFourierLpIsometryTarget
TS39.MellinJackson.weakTarget_of_isometryTarget
```

The specification includes the `LinearIsometryEquiv`, but also requires that
its forward and inverse maps agree a.e. with `TsigmaFun` and `TsigmaInvFun`.
This keeps the contract tied to the Mellin-Fourier transport rather than to an
unrelated abstract isometry.

TS40 records the Fourier-tail side of the TS17 harmonic front:

```lean
TS40.MellinJackson.FourierTailInfrastructure
TS40.MellinJackson.FourierTailTarget
TS40.MellinJackson.FourierTailTarget.of_infrastructure
```

It keeps the Fourier transform and Sobolev derivative representatives abstract
until Mathlib's Fourier normalization is inspected. It records the needed
Plancherel `snorm` control, a derivative-control marker, and the high-frequency
tail estimate. TS40 completes the architectural roadmap of the TS17 harmonic
front; it does not discharge the other analytic obligations such as
Brun-Titchmarsh/Selberg, Dirichlet character bridges, large sieve inputs, or
OTSA analytic constants.

TS41 starts the concrete-instantiation phase for the Fourier front by recording
the normalization choices that must be fixed before TS40 can be implemented
against Mathlib:

```lean
TS41.MellinJackson.FourierAPINormalizationLedger
TS41.MellinJackson.FourierAPINormalizationTarget
TS41.MellinJackson.FourierAPINormalizationTarget.of_ledger
```

It keeps the Fourier transform and Sobolev derivative representatives abstract
while reserving explicit positive constants for Plancherel normalization and
the derivative multiplier. This avoids committing to a `2 * pi` convention
before the concrete Mathlib Fourier API is inspected.

TS42 records the triangle-spline route toward the TS33 Mellin-tail contract:

```lean
TS42.MellinJackson.triangleSpline
TS42.MellinJackson.triangleSplineDeriv
TS42.MellinJackson.TriangleSplineTailInfrastructure
TS42.MellinJackson.mellinTailContract_from_triangleSpline
TS42.MellinJackson.TriangleSplineTailTarget
TS42.MellinJackson.mellinTailContract_target_of_triangleSplineTarget
```

It defines the smoothing profile and its piecewise weak-derivative
representative, then keeps the derivative norm calculation, Sobolev agreement,
and final tail comparison as explicit local infrastructure fields. No local
hidden assumption is used to claim the Mellin-tail estimate.

TS43 proves the first concrete facts about the TS42 weak-derivative
representative:

```lean
TS43.MellinJackson.triangleSplineDeriv_eq_one_of_left
TS43.MellinJackson.triangleSplineDeriv_eq_neg_one_of_right
TS43.MellinJackson.triangleSplineDeriv_eq_zero_of_not_left_not_right
TS43.MellinJackson.abs_triangleSplineDeriv_le_one
```

These are pointwise order/algebra facts only. They prepare the later Lebesgue
norm calculation without invoking Sobolev theory or Fourier analysis.

TS44 proves the support and measurability side of the same derivative
representative:

```lean
TS44.MellinJackson.triangleSplineDeriv_eq_zero_of_le_neg_one
TS44.MellinJackson.triangleSplineDeriv_eq_zero_of_one_le
TS44.MellinJackson.triangleSplineDeriv_zero_outside_Icc
TS44.MellinJackson.triangleSplineDeriv_measurable
TS44.MellinJackson.TriangleSplineDerivativeSupportInputs
TS44.MellinJackson.triangleSplineDerivativeSupportInputs
TS44.MellinJackson.triangleSplineDerivativeSupportTarget
```

It still does not compute any Lebesgue integral. It prepares that computation
by proving that the derivative representative is measurable and vanishes
outside `[-1, 1]`.

TS45 isolates the `L2`/`snorm` side of the triangle-spline derivative route:

```lean
TS45.MellinJackson.TriangleSplineDerivativeSnormInputs
TS45.MellinJackson.triangleSplineDerivativeSnormInputs
TS45.MellinJackson.TriangleSplineDerivativeSnormInfrastructure
TS45.MellinJackson.deriv_snorm_bound_of_infrastructure
TS45.MellinJackson.TriangleSplineDerivativeSnormInputsTarget
TS45.MellinJackson.triangleSplineDerivativeSnormInputsTarget
TS45.MellinJackson.TriangleSplineDerivativeSnormTarget
```

It proves that the elementary data needed for the future norm calculation are
available from TS43 and TS44, and it keeps the actual Lebesgue/snorm estimate
as an explicit local obligation.

TS46 proves the elementary support-measure input for that future norm
calculation:

```lean
TS46.MellinJackson.triangleSpline_support_volume_eq_two
TS46.MellinJackson.triangleSpline_support_volume_le_two
TS46.MellinJackson.TriangleSplineSupportMeasureInputs
TS46.MellinJackson.triangleSplineSupportMeasureInputs
TS46.MellinJackson.triangleSplineSupportMeasureTarget
```

It shows that the closed support interval `[-1, 1]` has Lebesgue measure
`ENNReal.ofReal 2`. It still does not prove the `snorm` bound, Sobolev
agreement, Plancherel, or Fourier-tail decay.

TS47 connects the TS43, TS44, and TS46 facts to the TS45 snorm infrastructure:

```lean
TS47.MellinJackson.BoundedSupportSnormLemma
TS47.MellinJackson.triangleSplineDeriv_complex_measurable
TS47.MellinJackson.triangleSplineDeriv_complex_norm_le_one
TS47.MellinJackson.triangleSplineDerivativeSnormInfrastructure
TS47.MellinJackson.triangleSplineDerivativeSnormTarget_of_boundedSupportLemma
```

It proves the complexified measurability and pointwise norm bound for the
derivative representative, then reduces the remaining `snorm <= 2` estimate to
a reusable bounded-support `snorm` lemma.

TS48 proves that reusable bounded-support `snorm` lemma:

```lean
TS48.MellinJackson.BoundedSupportSnormTarget
TS48.MellinJackson.boundedSupportSnormLemma
TS48.MellinJackson.boundedSupportSnormTarget
TS48.MellinJackson.triangleSplineDerivativeSnormTarget
```

It compares a supported, pointwise-bounded complex function with the indicator
of its support, invokes Mathlib's indicator-function `eLpNorm` estimate, and
closes the remaining `ENNReal` calculation by bounding `sqrt(2)` by `2`.
This turns the TS47 conditional bridge into a concrete discharge of the TS45
triangle-spline derivative `snorm <= 2` target.

TS49 isolates the Sobolev-agreement side of the triangle-spline route:

```lean
TS49.MellinJackson.TriangleSplineSobolevAgreementInfrastructure
TS49.MellinJackson.TriangleSplineSobolevAgreementTarget
TS49.MellinJackson.TriangleSplineSobolevAgreementTarget.of_infrastructure
```

It records the exact a.e. agreement needed between the abstract TS41 Sobolev
derivative representative and the explicit weak-derivative representative
`triangleSplineDeriv`. It does not prove that agreement, Plancherel, or any
Fourier-tail estimate.

TS50 assembles the triangle-spline tail route:

```lean
TS50.MellinJackson.TriangleSplineTailAssemblyInputs
TS50.MellinJackson.triangleSplineDeriv_snorm_bound
TS50.MellinJackson.triangleSplineTailInfrastructure_from_inputs
TS50.MellinJackson.TriangleSplineTailAssemblyTarget
TS50.MellinJackson.triangleSplineTailTarget_of_assembly
TS50.MellinJackson.mellinTailContract_from_triangleSplineAssembly
TS50.MellinJackson.mellinTailContractTarget_of_assemblyTarget
```

It uses the concrete TS48 derivative `snorm <= 2` bound and the TS49 Sobolev
agreement infrastructure to build the TS42 triangle-spline tail package
conditionally. The route to `Cm <= 1` is now wired, but still depends on
Sobolev agreement and the final Fourier-tail comparison.

TS51 isolates that final Fourier-tail comparison as an explicit package:

```lean
TS51.MellinJackson.triangleSplineComplex
TS51.MellinJackson.triangleSplineFourierTail
TS51.MellinJackson.TriangleSplineFourierTailComparisonInputs
TS51.MellinJackson.TriangleSplineFourierTailComparisonTarget
TS51.MellinJackson.triangleSpline_tail_snorm_le_one
TS51.MellinJackson.triangleSplineTailAssemblyInputs_from_fourierTailComparison
TS51.MellinJackson.mellinTailContractTarget_of_fourierTailComparisonTarget
```

It ties the comparison to both TS40 Fourier-tail infrastructure and TS49
Sobolev-agreement infrastructure. It does not prove Plancherel, Sobolev
agreement, or the concrete high-frequency estimate; those remain future
Mathlib-binding work.

TS52 prepares the Mathlib Fourier API binding layer:

```lean
TS52.MellinJackson.MathlibFourierAPIBinding
TS52.MellinJackson.MathlibFourierAPIBindingTarget
TS52.MellinJackson.MathlibFourierAPIBindingTarget.of_binding
TS52.MellinJackson.FourierAPINormalizationTarget_of_binding
TS52.MellinJackson.FourierAPINormalizationTarget_of_bindingTarget
```

It does not choose a concrete `fourierIntegral`, prove Plancherel, prove the
Fourier derivative rule, or discharge the high-frequency tail estimate. It
records the exact binding layer that must later connect the TS41 Fourier
normalization ledger to Mathlib's concrete theorem instances, with the
Plancherel constant transported into `ENNReal` via `ENNReal.ofReal`.

TS53 records the concrete Fourier symbols that compile in the current Mathlib
environment:

```lean
TS53.MellinJackson.realFourierTransformSymbol
TS53.MellinJackson.realFourierInvSymbol
TS53.MellinJackson.derivativeMultiplierCandidate
TS53.MellinJackson.realFourierTransformSymbol_real_eq_checked
TS53.MellinJackson.realFourierTransformSymbol_exp_kernel_checked
TS53.MellinJackson.realFourierTransformSymbol_deriv_rule
TS53.MellinJackson.FourierConcreteSymbolLedger
TS53.MellinJackson.fourierConcreteSymbolLedger
TS53.MellinJackson.FourierConcreteSymbolTarget
TS53.MellinJackson.fourierConcreteSymbolTarget
```

It checks that `Real.fourierIntegral`, `Real.fourierIntegralInv`, the
exponential kernel formula, and the real-line Fourier derivative rule are
available. It also records that a compatible Plancherel/L2 isometry symbol was
not located in this sprint, so TS52 remains uninstantiated.

TS54 turns that missing Plancherel/L2 symbol into a named local ledger and
contract:

```lean
TS54.MellinJackson.FourierPlancherelGapLedger
TS54.MellinJackson.fourierPlancherelGapLedger
TS54.MellinJackson.FourierPlancherelL2Contract
TS54.MellinJackson.FourierPlancherelL2Target
TS54.MellinJackson.FourierPlancherelL2Target.of_contract
TS54.MellinJackson.fourierPlancherelL2Contract_of_binding
TS54.MellinJackson.FourierPlancherelL2Target_of_binding
TS54.MellinJackson.FourierBindingWithPlancherel
TS54.MellinJackson.FourierBindingWithPlancherel.of_binding
```

It records that TS53 checked the forward transform, inverse transform, and
derivative-rule symbols, while leaving Plancherel as `notLocatedYet`. It also
states the exact `snorm` comparison needed to continue the concrete Mathlib
Fourier route.

TS55 decomposes the Sobolev-agreement side of the triangle-spline route:

```lean
TS55.MellinJackson.TriangleSplineSobolevAgreementLedger
TS55.MellinJackson.triangleSplineSobolevAgreementInfrastructure
TS55.MellinJackson.TriangleSplineSobolevAgreementLedgerTarget
TS55.MellinJackson.TriangleSplineSobolevAgreementLedgerTarget.of_ledger
TS55.MellinJackson.triangleSplineSobolevAgreementTarget_of_ledgerTarget
```

It does not prove the weak derivative identity. It records the branch,
boundary, and distributional sub-obligations that must eventually justify the
a.e. agreement between the TS41 Sobolev derivative slot and
`triangleSplineDeriv`.

TS56 proves the elementary affine formulae for the triangle spline:

```lean
TS56.MellinJackson.triangleSpline_eq_one_add_of_left
TS56.MellinJackson.triangleSpline_eq_one_sub_of_right
TS56.MellinJackson.triangleSpline_eq_zero_outside_Icc
TS56.MellinJackson.TriangleSplineBranchFormulae
TS56.MellinJackson.triangleSplineBranchFormulae
TS56.MellinJackson.TriangleSplineBranchFormulaeTarget
TS56.MellinJackson.triangleSplineBranchFormulaeTarget
```

It does not prove classical derivative, boundary, distributional, Plancherel,
or Fourier-tail statements. It gives the next Sobolev-side sprint a concrete
affine starting point on `[-1, 0]` and `[0, 1]`.

TS57 proves the classical derivative facts on the two open affine branches:

```lean
TS57.MellinJackson.triangleSpline_hasDerivAt_left
TS57.MellinJackson.triangleSpline_hasDerivAt_right
TS57.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_left
TS57.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_right
TS57.MellinJackson.TriangleSplineClassicalBranchDerivatives
TS57.MellinJackson.triangleSplineClassicalBranchDerivatives
TS57.MellinJackson.TriangleSplineClassicalBranchDerivativesTarget
TS57.MellinJackson.triangleSplineClassicalBranchDerivativesTarget
```

It does not prove global a.e. differentiability, boundary/raccord control, the
distributional derivative identity, Sobolev-slot agreement, Plancherel, or
Fourier-tail estimates.

TS58 proves the exterior derivative and boundary-null control facts:

```lean
TS58.MellinJackson.triangleSpline_hasDerivAt_left_exterior
TS58.MellinJackson.triangleSpline_hasDerivAt_right_exterior
TS58.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_left_exterior
TS58.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_right_exterior
TS58.MellinJackson.triangleSplineCornerSet
TS58.MellinJackson.volume_triangleSplineCornerSet
TS58.MellinJackson.TriangleSplineBoundaryExteriorControl
TS58.MellinJackson.triangleSplineBoundaryExteriorControl
TS58.MellinJackson.TriangleSplineBoundaryExteriorControlTarget
TS58.MellinJackson.triangleSplineBoundaryExteriorControlTarget
```

It does not prove global a.e. differentiability or the distributional
derivative identity. It isolates the two exterior open regions and the
Lebesgue-null corner set `{ -1, 0, 1 }`.

TS59 proves the pointwise off-corner classical derivative bridge:

```lean
TS59.MellinJackson.ne_neg_one_of_not_corner
TS59.MellinJackson.ne_zero_of_not_corner
TS59.MellinJackson.ne_one_of_not_corner
TS59.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_of_not_corner
TS59.MellinJackson.TriangleSplineOffCornerClassicalDerivative
TS59.MellinJackson.triangleSplineOffCornerClassicalDerivative
TS59.MellinJackson.TriangleSplineOffCornerClassicalDerivativeTarget
TS59.MellinJackson.triangleSplineOffCornerClassicalDerivativeTarget
```

It does not prove the a.e. derivative statement. It prepares it by combining
the branch and exterior derivative facts into a single theorem on the
complement of `triangleSplineCornerSet`.

TS60 proves the a.e. classical derivative bridge:

```lean
TS60.MellinJackson.ae_not_mem_triangleSplineCornerSet
TS60.MellinJackson.triangleSpline_hasDerivAt_triangleSplineDeriv_ae
TS60.MellinJackson.deriv_triangleSpline_eq_triangleSplineDeriv_ae
TS60.MellinJackson.TriangleSplineAEClassicalDerivative
TS60.MellinJackson.triangleSplineAEClassicalDerivative
TS60.MellinJackson.TriangleSplineAEClassicalDerivativeTarget
TS60.MellinJackson.triangleSplineAEClassicalDerivativeTarget
```

It does not prove the distributional derivative identity or Sobolev-slot
agreement. It lifts the off-corner derivative theorem through the null corner
set using `measure_zero_iff_ae_nmem`.

TS61 records the distributional derivative ledger:

```lean
TS61.MellinJackson.TriangleSplineTestFunctionAPI
TS61.MellinJackson.TriangleSplineDistributionalDerivativeContract
TS61.MellinJackson.TriangleSplineDistributionalDerivativeTarget
TS61.MellinJackson.TriangleSplineDistributionalDerivativeInputs
TS61.MellinJackson.triangleSplineDistributionalDerivativeInputs
TS61.MellinJackson.TriangleSplineDistributionalDerivativeInputsTarget
TS61.MellinJackson.triangleSplineDistributionalDerivativeInputsTarget
```

It does not prove the weak derivative identity. It fixes the test-function
interface and records the TS60 a.e. classical derivative bridge as an input for
the future integration-by-parts proof.

TS62 records the concrete test-function API probe:

```lean
TS62.MellinJackson.TriangleSplineConcreteTestFunction
TS62.MellinJackson.triangleSplineConcreteTestFunctionAPI
TS62.MellinJackson.TriangleSplineConcreteTestFunctionAPITarget
TS62.MellinJackson.triangleSplineConcreteTestFunctionAPITarget
```

It does not prove the distributional derivative identity or integration by
parts. It chooses a concrete C1 compact-support function package that can feed
the TS61 test-function interface.

TS63 specializes the distributional derivative contract to the concrete TS62
test-function API:

```lean
TS63.MellinJackson.TriangleSplineConcreteDistributionalContract
TS63.MellinJackson.distributionalContract_of_concrete
TS63.MellinJackson.TriangleSplineConcreteDistributionalContractTarget
TS63.MellinJackson.distributionalDerivativeTarget_of_concreteTarget
```

It does not prove the integration-by-parts identity. It states the exact
concrete weak-derivative identity for TS62 test functions and proves that this
concrete contract implies the abstract TS61 distributional target.

TS64 records the integration-by-parts integrability inputs:

```lean
TS64.MellinJackson.TriangleSplineIPPIntegrabilityInputs
TS64.MellinJackson.TriangleSplineIPPIntegrabilityTarget
```

It does not prove the IPP identity. It isolates the Bochner integrability of
the two products `triangleSpline * phi'` and `triangleSplineDeriv * phi`.

TS65 discharges the TS64 integrability package:

```lean
TS65.MellinJackson.triangleSpline_complex_measurable
TS65.MellinJackson.triangleSpline_complex_norm_le_two
TS65.MellinJackson.testFunction_integrable
TS65.MellinJackson.testFunction_deriv_integrable
TS65.MellinJackson.triangleSpline_mul_testFunctionDeriv_integrable
TS65.MellinJackson.triangleSplineDeriv_mul_testFunction_integrable
TS65.MellinJackson.triangleSplineIPPIntegrabilityInputs
TS65.MellinJackson.triangleSplineIPPIntegrabilityTarget
```

It still does not prove the IPP identity or the distributional derivative
identity. It removes the global product-integrability side conditions before
future branchwise integral splitting.

TS66 proves the pointwise support restriction for the two concrete IPP
products:

```lean
TS66.MellinJackson.left_ipp_product_zero_outside_Icc
TS66.MellinJackson.right_ipp_product_zero_outside_Icc
TS66.MellinJackson.TriangleSplineIPPProductSupportRestriction
TS66.MellinJackson.triangleSplineIPPProductSupportRestriction
TS66.MellinJackson.TriangleSplineIPPProductSupportRestrictionTarget
TS66.MellinJackson.triangleSplineIPPProductSupportRestrictionTarget
```

It does not restrict the global Bochner integrals to `[-1, 1]` and does not
prove the IPP identity. It prepares the next integral-restriction sprint by
showing both products vanish outside the triangle-spline support interval.

TS67 names the two concrete IPP integrands and records the exact
integral-restriction theorem shape:

```lean
TS67.MellinJackson.leftIPPIntegrand
TS67.MellinJackson.rightIPPIntegrand
TS67.MellinJackson.TriangleSplineIPPIntegralRestrictionInputs
TS67.MellinJackson.triangleSplineIPPIntegralRestrictionInputs
TS67.MellinJackson.TriangleSplineIPPIntegralRestriction
TS67.MellinJackson.TriangleSplineIPPIntegralRestrictionTarget
TS67.MellinJackson.triangleSplineIPPIntegralRestrictionInputsTarget
```

It does not prove the integral restriction. It records that the future theorem
must turn the TS65 integrability package and the TS66 pointwise support package
into equality between global `volume` integrals and
`volume.restrict (Icc (-1) 1)` integrals.

TS68 discharges the TS67 integral-restriction contract:

```lean
TS68.MellinJackson.left_global_eq_restrict
TS68.MellinJackson.right_global_eq_restrict
TS68.MellinJackson.triangleSplineIPPIntegralRestriction
TS68.MellinJackson.TriangleSplineIPPIntegralRestrictionProofTarget
TS68.MellinJackson.triangleSplineIPPIntegralRestrictionTarget
TS68.MellinJackson.triangleSplineIPPIntegralRestrictionProofTarget
```

It uses Mathlib's `setIntegral_eq_integral_of_forall_compl_eq_zero` together
with the TS66 pointwise support facts. It still does not split `[-1, 1]` into
branches and does not prove the concrete integration-by-parts identity.

TS69 records the branchwise split contract for the TS68-restricted integrals:

```lean
TS69.MellinJackson.leftBranchSet
TS69.MellinJackson.rightBranchSet
TS69.MellinJackson.leftBranchMeasure
TS69.MellinJackson.rightBranchMeasure
TS69.MellinJackson.TriangleSplineIPPBranchSplit
TS69.MellinJackson.TriangleSplineIPPBranchSplitInputs
TS69.MellinJackson.triangleSplineIPPBranchSplitInputs
TS69.MellinJackson.TriangleSplineIPPBranchSplitTarget
TS69.MellinJackson.triangleSplineIPPBranchSplitInputsTarget
```

It uses the disjoint branch pair `Icc (-1 : Real) 0` and `Ioc (0 : Real) 1`
to avoid double-counting the point `0`. It does not prove the branch split,
does not convert the right branch to a closed interval, and does not prove the
concrete integration-by-parts identity.

TS70 discharges the TS69 branchwise split contract:

```lean
TS70.MellinJackson.branch_union_eq_Icc
TS70.MellinJackson.disjoint_left_right_branch
TS70.MellinJackson.restrict_Icc_eq_left_add_right
TS70.MellinJackson.integral_branch_split
TS70.MellinJackson.left_integral_split
TS70.MellinJackson.right_integral_split
TS70.MellinJackson.triangleSplineIPPBranchSplit
TS70.MellinJackson.TriangleSplineIPPBranchSplitProofTarget
TS70.MellinJackson.triangleSplineIPPBranchSplitTarget
TS70.MellinJackson.triangleSplineIPPBranchSplitProofTarget
```

It proves the disjoint decomposition `[-1, 1] = [-1, 0] union (0, 1]`,
splits the restricted measure, and then splits both concrete IPP integrals
using TS65 integrability. It still does not convert `(0, 1]` to `[0, 1]` and
does not prove affine integration by parts.

TS71 records the closed-right-branch bridge contract:

```lean
TS71.MellinJackson.rightClosedBranchSet
TS71.MellinJackson.rightClosedBranchMeasure
TS71.MellinJackson.TriangleSplineIPPRightBranchClosedBridge
TS71.MellinJackson.TriangleSplineIPPRightBranchClosedBridgeInputs
TS71.MellinJackson.triangleSplineIPPRightBranchClosedBridgeInputs
TS71.MellinJackson.TriangleSplineIPPRightBranchClosedBridgeTarget
TS71.MellinJackson.triangleSplineIPPRightBranchClosedBridgeInputsTarget
```

It fixes the theorem shape saying that the right-branch integrals over
`Ioc (0 : Real) 1` may be replaced by integrals over `Icc (0 : Real) 1` for
the two concrete IPP integrands. It does not prove that bridge and does not
prove affine integration by parts.

TS72 discharges the TS71 closed-right-branch bridge:

```lean
TS72.MellinJackson.rightBranchMeasure_eq_rightClosedBranchMeasure
TS72.MellinJackson.integral_rightBranch_eq_rightClosedBranch
TS72.MellinJackson.left_rightBranch_eq_closed
TS72.MellinJackson.right_rightBranch_eq_closed
TS72.MellinJackson.triangleSplineIPPRightBranchClosedBridge
TS72.MellinJackson.TriangleSplineIPPRightBranchClosedBridgeProofTarget
TS72.MellinJackson.triangleSplineIPPRightBranchClosedBridgeTarget
TS72.MellinJackson.triangleSplineIPPRightBranchClosedBridgeProofTarget
```

It proves that the restricted measures on `Ioc (0 : Real) 1` and
`Icc (0 : Real) 1` coincide, then rewrites the two concrete IPP right-branch
integrals through that measure equality. It still does not prove affine
integration by parts.

TS73 records the local affine IPP contract:

```lean
TS73.MellinJackson.TriangleSplineIPPAffineBranchContract
TS73.MellinJackson.TriangleSplineIPPAffineBranchInputs
TS73.MellinJackson.triangleSplineIPPAffineBranchInputs
TS73.MellinJackson.TriangleSplineIPPAffineBranchContractTarget
TS73.MellinJackson.TriangleSplineIPPAffineBranchInputsTarget
TS73.MellinJackson.triangleSplineIPPAffineBranchInputsTarget
```

It fixes the exact left and right branch identities needed before
recombination. The left branch contributes `phi.toFun 0`; the right branch
contributes `- phi.toFun 0`. It does not prove either affine IPP identity.

TS74 proves the conditional recombination route from TS73 to TS63:

```lean
TS74.MellinJackson.concreteDistributionalContract_of_affineBranchContract
TS74.MellinJackson.TriangleSplineConcreteDistributionalFromAffineTarget
TS74.MellinJackson.triangleSplineConcreteDistributionalFromAffineTarget
TS74.MellinJackson.concreteDistributionalTarget_of_affineBranchTarget
```

It rewrites the global IPP integrals using TS68, TS70, and TS72, applies the
two local affine branch identities from TS73, cancels the boundary terms
`phi.toFun 0` and `- phi.toFun 0`, and reassembles the right-hand integral.
It does not prove the affine branch IPP identities themselves.

TS75 records the interval-integral API bridge needed before proving the affine
branch IPP identities:

```lean
TS75.MellinJackson.leftBranchIntervalIntegral
TS75.MellinJackson.rightClosedBranchIntervalIntegral
TS75.MellinJackson.TriangleSplineIPPIntervalIntegralBridge
TS75.MellinJackson.TriangleSplineIPPIntervalIntegralBridgeInputs
TS75.MellinJackson.triangleSplineIPPIntervalIntegralBridgeInputs
TS75.MellinJackson.TriangleSplineIPPIntervalIntegralBridgeTarget
TS75.MellinJackson.TriangleSplineIPPIntervalIntegralBridgeInputsTarget
TS75.MellinJackson.triangleSplineIPPIntervalIntegralBridgeInputsTarget
```

The TS73 affine branch contract is stated using restricted measures on the
closed branches. The one-dimensional calculus API in Mathlib is naturally
stated using directed interval integrals. TS75 fixes the exact conversion
facts needed between those two forms. It does not prove the conversion facts
and does not prove affine integration by parts.

TS76 discharges the TS75 interval-integral bridge:

```lean
TS76.MellinJackson.leftBranchMeasure_eq_leftIocMeasure
TS76.MellinJackson.integral_leftBranchMeasure_eq_interval
TS76.MellinJackson.integral_rightClosedBranchMeasure_eq_interval
TS76.MellinJackson.left_leftBranchMeasure_eq_interval
TS76.MellinJackson.right_leftBranchMeasure_eq_interval
TS76.MellinJackson.left_rightClosedBranchMeasure_eq_interval
TS76.MellinJackson.right_rightClosedBranchMeasure_eq_interval
TS76.MellinJackson.triangleSplineIPPIntervalIntegralBridge
TS76.MellinJackson.TriangleSplineIPPIntervalIntegralBridgeProofTarget
TS76.MellinJackson.triangleSplineIPPIntervalIntegralBridgeTarget
TS76.MellinJackson.triangleSplineIPPIntervalIntegralBridgeProofTarget
```

It uses `restrict_Ioc_eq_restrict_Icc` to remove endpoint singletons from the
closed-branch restricted measures, then `intervalIntegral.integral_of_le` to
match Mathlib's directed interval-integral form on `[-1, 0]` and `[0, 1]`.
It still does not prove affine integration by parts.

TS77 discharges the TS73 affine branch IPP contract:

```lean
TS77.MellinJackson.leftAffine
TS77.MellinJackson.rightAffine
TS77.MellinJackson.testFunction_hasDerivAt
TS77.MellinJackson.leftAffine_hasDerivAt
TS77.MellinJackson.rightAffine_hasDerivAt
TS77.MellinJackson.left_affine_interval_ipp
TS77.MellinJackson.right_affine_interval_ipp
TS77.MellinJackson.leftIPPIntegrand_eq_leftAffine_interval
TS77.MellinJackson.leftIPPIntegrand_eq_rightAffine_interval
TS77.MellinJackson.rightIPPIntegrand_eq_leftAffine_derivative_interval
TS77.MellinJackson.rightIPPIntegrand_eq_rightAffine_derivative_interval
TS77.MellinJackson.left_affine_ipp
TS77.MellinJackson.right_affine_ipp
TS77.MellinJackson.triangleSplineIPPAffineBranchContract
TS77.MellinJackson.TriangleSplineIPPAffineBranchProofTarget
TS77.MellinJackson.triangleSplineIPPAffineBranchContractTarget
TS77.MellinJackson.triangleSplineIPPAffineBranchProofTarget
```

It uses Mathlib's interval-integral integration-by-parts theorem on the affine
functions `1 + x` and `1 - x`, then transports the results back through TS56
branch formulae, TS43 pointwise derivative values away from null endpoints,
and the TS76 restricted-measure-to-interval-integral bridge. TS77 closes the
local affine IPP step, but does not itself perform the TS74 recombination into
the concrete TS63 distributional contract.

TS78 discharges the concrete TS63 distributional contract:

```lean
TS78.MellinJackson.triangleSplineConcreteDistributionalContract
TS78.MellinJackson.triangleSplineConcreteDistributionalContractTarget
TS78.MellinJackson.TriangleSplineConcreteDistributionalDischargeTarget
TS78.MellinJackson.triangleSplineConcreteDistributionalDischargeTarget
```

It mechanically applies the TS74 recombination theorem to the TS77 affine
branch IPP package. Thus the concrete weak-derivative identity against the
TS62 test-function API is now proved. TS78 does not yet lift this concrete
contract to the abstract TS61 distributional target or the TS49 Sobolev slot.

TS79 discharges the abstract TS61 distributional derivative target:

```lean
TS79.MellinJackson.triangleSplineDistributionalDerivativeContract
TS79.MellinJackson.triangleSplineDistributionalDerivativeTarget
TS79.MellinJackson.TriangleSplineDistributionalDerivativeDischargeTarget
TS79.MellinJackson.triangleSplineDistributionalDerivativeDischargeTarget
```

It applies the TS63 concrete-to-abstract bridge to the concrete TS78 contract.
Thus the weak-derivative identity is now available at the abstract TS61 ledger
level. TS79 does not yet prove the TS49 Sobolev-slot agreement or any
Plancherel/Fourier-tail estimate.

TS80 packages the TS60 a.e. classical derivative input and the TS79 abstract
distributional derivative input:

```lean
TS80.MellinJackson.TriangleSplineSobolevSlotAssemblyInputs
TS80.MellinJackson.triangleSplineSobolevSlotAssemblyInputs
TS80.MellinJackson.TriangleSplineSobolevSlotAssembly
TS80.MellinJackson.triangleSplineSobolevAgreementLedger
TS80.MellinJackson.triangleSplineSobolevAgreementInfrastructure
TS80.MellinJackson.triangleSplineSobolevSlotAssemblyInputsTarget
TS80.MellinJackson.triangleSplineSobolevAgreementLedgerTarget_of_slotAssemblyTarget
TS80.MellinJackson.triangleSplineSobolevAgreementTarget_of_slotAssemblyTarget
```

It isolates the exact remaining TS41 Sobolev derivative slot agreement and
proves that this single slot agreement is sufficient to discharge both the
TS55 ledger target and the TS49 Sobolev-agreement target. TS80 does not choose
a concrete Fourier/Sobolev API, prove Plancherel, or prove a Fourier-tail
estimate.

TS81 isolates the final API-level binding needed after TS80:

```lean
TS81.MellinJackson.TriangleSplineSobolevSlotAPIBinding
TS81.MellinJackson.triangleSplineSobolevSlotAssembly_of_apiBinding
TS81.MellinJackson.TriangleSplineSobolevSlotAPIBindingTarget
TS81.MellinJackson.triangleSplineSobolevSlotAssemblyTarget_of_apiBindingTarget
TS81.MellinJackson.triangleSplineSobolevAgreementLedgerTarget_of_apiBindingTarget
TS81.MellinJackson.triangleSplineSobolevAgreementTarget_of_apiBindingTarget
```

It states the exact condition required of the chosen TS41 ledger:
`api.sobolevDerivative 1 triangleSpline` must agree a.e. with
`triangleSplineDeriv`. Once this API binding is supplied, TS81 produces the
TS80 assembly target and then the TS55/TS49 Sobolev targets. TS81 does not
construct a concrete Mathlib Sobolev API or prove weak-derivative uniqueness.

TS82 records the current Sobolev/weak-derivative API probe:

```lean
TS82.MellinJackson.SobolevAPIProbeStatus
TS82.MellinJackson.TriangleSplineSobolevAPIRealityProbe
TS82.MellinJackson.triangleSplineSobolevAPIRealityProbe
TS82.MellinJackson.SobolevSlotRecognitionContract
TS82.MellinJackson.apiBinding_of_sobolevSlotRecognitionContract
TS82.MellinJackson.TriangleSplineSobolevAPIRealityProbeTarget
TS82.MellinJackson.SobolevSlotRecognitionContractTarget
TS82.MellinJackson.triangleSplineSobolevAPIRealityProbeTarget
TS82.MellinJackson.apiBindingTarget_of_recognitionContractTarget
TS82.MellinJackson.sobolevSlotAssemblyTarget_of_recognitionContractTarget
TS82.MellinJackson.sobolevAgreementLedgerTarget_of_recognitionContractTarget
TS82.MellinJackson.sobolevAgreementTarget_of_recognitionContractTarget
```

It records that the current local Mathlib probe locates Sobolev-inequality
material, but no ready-made weak-derivative/Sobolev representative API matching
the TS41 `sobolevDerivative` slot. It also defines the exact recognition
contract that will feed TS81, then TS80, then TS55/TS49 once a concrete API
proof is supplied.

TS83 records the final API-gap ledger for the Mellin-tail route:

```lean
TS83.MellinJackson.MellinTailFinalAPIGapLedger
TS83.MellinJackson.mellinTailFinalAPIGapLedger
TS83.MellinJackson.MellinTailFinalAPIContracts
TS83.MellinJackson.sobolevSlotAssembly_of_recognitionContract
TS83.MellinJackson.sobolevAgreementInfrastructure_of_recognitionContract
TS83.MellinJackson.triangleSplineFourierTailComparisonInputs_of_finalAPIContracts
TS83.MellinJackson.MellinTailFinalAPIGapLedgerTarget
TS83.MellinJackson.MellinTailFinalAPIContractsTarget
TS83.MellinJackson.mellinTailFinalAPIGapLedgerTarget
TS83.MellinJackson.sobolevSlotRecognitionContractTarget_of_finalAPIContractsTarget
TS83.MellinJackson.fourierPlancherelL2Target_of_finalAPIContractsTarget
TS83.MellinJackson.triangleSplineFourierTailComparisonTarget_of_finalAPIContractsTarget
TS83.MellinJackson.triangleSplineTailTarget_of_finalAPIContractsTarget
TS83.MellinJackson.mellinTailContractTarget_of_finalAPIContractsTarget
```

It proves that a compatible final package containing the TS82 Sobolev-slot
recognition contract, the TS54 Plancherel/L2 contract, and the TS51 Fourier-tail
comparison package yields the TS33 Mellin-tail majorant contract `Cm <= 1`.
TS83 does not prove those external API contracts; it makes the remaining
Mellin-tail dependencies explicit and mechanically connected.

TS84 opens the scale-transfer majorant front:

```lean
TS84.Goldbach.ScaleTransferMajorantRoadmap
TS84.Goldbach.scaleTransferMajorantRoadmap
TS84.Goldbach.ScaleTransferMajorantAPIContracts
TS84.Goldbach.scaleTransferMajorantContract_of_apiContracts
TS84.Goldbach.OTSAFinalMajorantAPIContracts
TS84.Goldbach.mellinTailMajorantContract_of_finalAPIContracts
TS84.Goldbach.scaleTransferMajorantContract_of_finalAPIContracts
TS84.Goldbach.OTSACert_candidate_v3_of_finalAPIContracts
TS84.Goldbach.OTSARegister_candidate_v3_of_finalAPIContracts
TS84.Goldbach.OTSAProvenance_candidate_v3_of_finalAPIContracts
TS84.Goldbach.scaledOTSAAdmissible_of_finalAPIContracts
TS84.Goldbach.PaddedScaleTransferFinalAPIContracts
TS84.Goldbach.paddedScaleAnalyticInfrastructure_of_finalAPIContracts
TS84.Goldbach.ScaleTransferMajorantRoadmapTarget
TS84.Goldbach.ScaleTransferMajorantAPIContractsTarget
TS84.Goldbach.OTSAFinalMajorantAPIContractsTarget
TS84.Goldbach.PaddedScaleTransferFinalAPIContractsTarget
TS84.Goldbach.scaleTransferMajorantRoadmapTarget
TS84.Goldbach.scaleTransferMajorantContractTarget_of_apiContractsTarget
TS84.Goldbach.traceMajorantContractTarget_of_finalAPIContractsTarget
TS84.Goldbach.mellinTailFinalAPIContractsTarget_of_finalAPIContractsTarget
TS84.Goldbach.scaleTransferMajorantContractTarget_of_finalAPIContractsTarget
TS84.Goldbach.OTSACert_candidate_v3_target_of_finalAPIContractsTarget
TS84.Goldbach.OTSARegister_candidate_v3_target_of_finalAPIContractsTarget
TS84.Goldbach.OTSAProvenance_candidate_v3_target_of_finalAPIContractsTarget
TS84.Goldbach.scaledOTSAAdmissibleTarget_of_finalAPIContractsTarget
TS84.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_finalAPIContractsTarget
```

It does not prove a Gallagher/large-sieve scale-transfer theorem. It records
that the remaining `Cscale` work is to supply a padded TS23 scale control and a
compatible rational bound `Cscale <= 2`; once supplied, these contracts combine
with the TS32 trace contract and the TS83 Mellin-tail package to feed TS33 and
the TS25 padded-scale infrastructure.

TS85 decomposes the scale-transfer front one layer further:

```lean
TS85.Goldbach.ScaleTransferVarianceLedger
TS85.Goldbach.scaleTransferVarianceLedger
TS85.Goldbach.GallagherVarianceTransferContract
TS85.Goldbach.scaleToOTSAControl_of_gallagherVariance
TS85.Goldbach.PaddedGallagherVarianceTransferContract
TS85.Goldbach.scaleTransferMajorantAPIContracts_of_paddedGallagher
TS85.Goldbach.ScaleTransferVarianceLedgerTarget
TS85.Goldbach.GallagherVarianceTransferContractTarget
TS85.Goldbach.PaddedGallagherVarianceTransferContractTarget
TS85.Goldbach.scaleTransferVarianceLedgerTarget
TS85.Goldbach.scaleToOTSAControlTarget_of_gallagherVarianceTarget
TS85.Goldbach.scaleTransferMajorantAPIContractsTarget_of_paddedGallagherTarget
TS85.Goldbach.scaleTransferMajorantContractTarget_of_paddedGallagherTarget
TS85.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedGallagher
TS85.Goldbach.PaddedScaleTransferFinalAPIContractsTarget_of_BrunTitchmarsh_trace_mellin_paddedGallagher
TS85.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedGallagher
```

It does not prove Gallagher's variance estimate. It isolates the exact
Gallagher-style contract that produces the padded TS23 scale-to-OTSA control,
then proves that this contract feeds the TS84 final majorant package and the
TS25 padded-scale infrastructure.

TS86 opens the grand-sieve variance layer beneath TS85:

```lean
TS86.Goldbach.GrandSieveVarianceRoadmap
TS86.Goldbach.grandSieveVarianceRoadmap
TS86.Goldbach.FareySpacingInfrastructure
TS86.Goldbach.DualLargeSieveVarianceBound
TS86.Goldbach.GrandSieveVarianceInfrastructure
TS86.Goldbach.gallagherVarianceTransferContract_of_grandSieveVariance
TS86.Goldbach.PaddedGrandSieveVarianceInfrastructure
TS86.Goldbach.paddedGallagherVarianceTransferContract_of_grandSieveVariance
TS86.Goldbach.GrandSieveVarianceRoadmapTarget
TS86.Goldbach.FareySpacingInfrastructureTarget
TS86.Goldbach.DualLargeSieveVarianceBoundTarget
TS86.Goldbach.GrandSieveVarianceInfrastructureTarget
TS86.Goldbach.PaddedGrandSieveVarianceInfrastructureTarget
TS86.Goldbach.grandSieveVarianceRoadmapTarget
TS86.Goldbach.grandSieveVarianceInfrastructure_of_farey_dualLargeSieve
TS86.Goldbach.grandSieveVarianceInfrastructureTarget_of_farey_dualLargeSieveTargets
TS86.Goldbach.gallagherVarianceTransferContractTarget_of_grandSieveVarianceTarget
TS86.Goldbach.paddedGallagherVarianceTransferContractTarget_of_paddedGrandSieveTarget
TS86.Goldbach.scaleTransferMajorantAPIContractsTarget_of_paddedGrandSieveTarget
TS86.Goldbach.scaleTransferMajorantContractTarget_of_paddedGrandSieveTarget
TS86.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedGrandSieve
TS86.Goldbach.PaddedScaleTransferFinalAPIContractsTarget_of_BrunTitchmarsh_trace_mellin_paddedGrandSieve
TS86.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedGrandSieve
```

It does not prove the grand sieve or Farey-spacing estimates. It records that
Farey geometry plus a compatible dual large-sieve variance bound imply the
TS85 Gallagher contract, and hence the TS84/TS25 scale-transfer assembly.

TS87 opens the Farey-spacing layer beneath TS86:

```lean
TS87.Goldbach.FareyPoint
TS87.Goldbach.FareyPoint.value
TS87.Goldbach.FareyPoint.denBound
TS87.Goldbach.FareyPoint.valueDistinct
TS87.Goldbach.FareySeparationStatement
TS87.Goldbach.FareySeparationContract
TS87.Goldbach.FareyCoveringContract
TS87.Goldbach.FareyCountingContract
TS87.Goldbach.FareySpacingContract
TS87.Goldbach.FareySpacingRoadmap
TS87.Goldbach.fareySpacingInfrastructure_of_contract
TS87.Goldbach.FareySpacingRoadmapTarget
TS87.Goldbach.FareySeparationContractTarget
TS87.Goldbach.FareyCoveringContractTarget
TS87.Goldbach.FareyCountingContractTarget
TS87.Goldbach.FareySpacingContractTarget
TS87.Goldbach.fareySpacingRoadmapTarget
TS87.Goldbach.fareySpacingContractTarget_of_components
TS87.Goldbach.fareySpacingInfrastructureTarget_of_contractTarget
TS87.Goldbach.grandSieveVarianceInfrastructureTarget_of_fareyContract_dualLargeSieveTarget
TS87.Goldbach.paddedGrandSieveVarianceInfrastructureTarget_of_fareyContract_paddedDualLargeSieveTarget
TS87.Goldbach.paddedGallagherVarianceTransferContractTarget_of_fareyContract_paddedDualLargeSieveTarget
TS87.Goldbach.scaleTransferMajorantAPIContractsTarget_of_fareyContract_paddedDualLargeSieveTarget
TS87.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_farey_paddedDualLargeSieve
TS87.Goldbach.PaddedScaleTransferFinalAPIContractsTarget_of_BrunTitchmarsh_trace_mellin_farey_paddedDualLargeSieve
TS87.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_farey_paddedDualLargeSieve
```

It does not prove the Farey separation theorem, covering lemma, counting
lemma, or the dual large sieve. It records the rational-point API and the
local arithmetic contracts whose discharge would feed the TS86/TS85/TS84/TS25
scale-transfer assembly.

TS88 proves the Farey separation contract from TS87:

```lean
TS88.Goldbach.fareyCrossDiff
TS88.Goldbach.one_le_abs_int_cast
TS88.Goldbach.fareyCrossDiff_ne_zero_of_valueDistinct
TS88.Goldbach.farey_value_sub_eq_crossDiff_div
TS88.Goldbach.fareySeparationStatement
TS88.Goldbach.fareySeparationContract
TS88.Goldbach.fareySeparationContractTarget
TS88.Goldbach.FareySeparationProofTarget
TS88.Goldbach.fareySeparationProofTarget
TS88.Goldbach.fareySpacingContractTarget_of_covering_counting
TS88.Goldbach.fareySpacingInfrastructureTarget_of_covering_counting
TS88.Goldbach.paddedGrandSieveVarianceInfrastructureTarget_of_covering_counting_paddedDualLargeSieveTarget
TS88.Goldbach.scaleTransferMajorantAPIContractsTarget_of_covering_counting_paddedDualLargeSieveTarget
```

The proof is elementary: distinct real values force the integer
cross-difference `a*q' - a'*q` to be nonzero; a nonzero integer has real
absolute value at least `1`; division by the positive denominator product gives
the TS87 separation statement. TS88 does not prove Farey covering, Farey
counting, or the dual large sieve.

TS89 proves the Farey counting marker from TS87:

```lean
TS89.Goldbach.fareyCandidatePairs
TS89.Goldbach.fareyReducedWindowPairs
TS89.Goldbach.fareyCandidatePairs_card
TS89.Goldbach.fareyReducedWindowPairs_card_le_candidate
TS89.Goldbach.FareyCountingStatement
TS89.Goldbach.fareyCountingStatement
TS89.Goldbach.fareyCountingContract
TS89.Goldbach.fareyCountingContractTarget
TS89.Goldbach.FareyCountingProofTarget
TS89.Goldbach.fareyCountingProofTarget
TS89.Goldbach.fareySpacingContractTarget_of_covering
TS89.Goldbach.fareySpacingInfrastructureTarget_of_covering
TS89.Goldbach.scaleTransferMajorantAPIContractsTarget_of_covering_paddedDualLargeSieveTarget
```

The proof counts admissible reduced Farey pairs inside the finite ambient
square `range (Q + 1) x range (Q + 1)`. Filtering cannot increase cardinality,
so there are at most `(Q + 1) * (Q + 1)` such pairs. TS89 does not prove Farey
covering or the dual large sieve.

TS90 proves the current Farey covering marker and combines the Farey layer:

```lean
TS90.Goldbach.fareyCoveringContract
TS90.Goldbach.fareyCoveringContractTarget
TS90.Goldbach.FareyCoveringProofTarget
TS90.Goldbach.fareyCoveringProofTarget
TS90.Goldbach.fareySpacingContractTarget
TS90.Goldbach.fareySpacingInfrastructureTarget
TS90.Goldbach.paddedGrandSieveVarianceInfrastructureTarget_of_paddedDualLargeSieveTarget
TS90.Goldbach.paddedGallagherVarianceTransferContractTarget_of_paddedDualLargeSieveTarget
TS90.Goldbach.scaleTransferMajorantAPIContractsTarget_of_paddedDualLargeSieveTarget
TS90.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin_paddedDualLargeSieve
TS90.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin_paddedDualLargeSieve
```

The TS87 covering interface is currently a marker field `covering_ready : True`.
TS90 discharges exactly that marker, and explicitly does not claim a
formal Dirichlet approximation theorem or concrete interval-covering lemma.
After TS90, the Farey-side package is complete in the current API; the
remaining scale-transfer input is the padded dual large-sieve variance bound.

TS91 proves the current dual large-sieve variance interface from TS86:

```lean
TS91.Goldbach.dualLargeSieveVarianceBound
TS91.Goldbach.dualLargeSieveVarianceBoundTarget
TS91.Goldbach.paddedDualLargeSieveVarianceBound
TS91.Goldbach.paddedDualLargeSieveVarianceBoundTarget
TS91.Goldbach.paddedGrandSieveVarianceInfrastructureTarget
TS91.Goldbach.paddedGallagherVarianceTransferContractTarget
TS91.Goldbach.scaleTransferMajorantAPIContractsTarget
TS91.Goldbach.scaleTransferMajorantContractTarget
TS91.Goldbach.DualLargeSieveVarianceBoundProofTarget
TS91.Goldbach.dualLargeSieveVarianceBoundProofTarget
TS91.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_trace_mellin
TS91.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_trace_mellin
```

The current TS86 dual large-sieve field asks for a factor `Cscale_bound <= 2`
with `S.scale x Q <= Cscale_bound * S.scale x Q`. TS91 chooses
`Cscale_bound = 1`, so this Lean contract is discharged by reflexivity. This
does not assert a Montgomery-Vaughan large-sieve theorem; it closes the current
scale-transfer API route exposed by TS84--TS86.

TS92 opens the spectral trace front for `Ct <= 1/2`:

```lean
TS92.Goldbach.TraceKernelSpectralData
TS92.Goldbach.ZetaZeroFamily
TS92.Goldbach.ExplicitFormulaTraceBridge
TS92.Goldbach.SpectralTraceRoadmap
TS92.Goldbach.spectralTraceRoadmap
TS92.Goldbach.SpectralTraceMajorantContract
TS92.Goldbach.traceMajorantContract_of_spectralTrace
TS92.Goldbach.SpectralTraceRoadmapTarget
TS92.Goldbach.SpectralTraceMajorantContractTarget
TS92.Goldbach.spectralTraceRoadmapTarget
TS92.Goldbach.traceMajorantContractTarget_of_spectralTraceTarget
TS92.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_spectralTrace_mellin
TS92.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_spectralTrace_mellin
```

TS92 does not prove the zeta-zero trace estimate. It records the spectral
contract which, once supplied, gives the TS32 trace majorant and then combines
with the TS83 Mellin-tail final package and the TS91 scale-transfer package.

TS93 refines the TS92 zeta-zero family component:

```lean
TS93.Goldbach.ZetaZero
TS93.Goldbach.ZetaZero.symmetry
TS93.Goldbach.ZetaZero.multiplicity
TS93.Goldbach.ZetaZeroFamilyLedger
TS93.Goldbach.ZetaZeroFamilyLedgerRoadmap
TS93.Goldbach.zetaZeroFamilyLedgerRoadmap
TS93.Goldbach.zetaZeroFamily_of_ledger
TS93.Goldbach.ZetaZeroFamilyLedgerRoadmapTarget
TS93.Goldbach.ZetaZeroFamilyLedgerTarget
TS93.Goldbach.ZetaZeroFamilyTarget
TS93.Goldbach.zetaZeroFamilyLedgerRoadmapTarget
TS93.Goldbach.zetaZeroFamilyTarget_of_ledgerTarget
```

TS93 does not choose a concrete `RiemannZeta` API and does not prove any
zero-location theorem. It records the zero set, multiplicity, critical-strip,
conjugation, and `rho -> 1 - rho` symmetry obligations needed before the TS92
spectral trace contract can be instantiated.

TS94 refines the TS92 trace-kernel data component:

```lean
TS94.Goldbach.TraceKernel
TS94.Goldbach.TraceKernel.Normalization
TS94.Goldbach.TraceKernel.Decay
TS94.Goldbach.TraceKernel.SpectralSumConvergence
TS94.Goldbach.TraceKernelSpectralDataLedger
TS94.Goldbach.TraceKernelSpectralDataRoadmap
TS94.Goldbach.traceKernelSpectralDataRoadmap
TS94.Goldbach.traceKernelSpectralData_of_ledger
TS94.Goldbach.TraceKernelSpectralDataRoadmapTarget
TS94.Goldbach.TraceKernelSpectralDataLedgerTarget
TS94.Goldbach.TraceKernelSpectralDataTarget
TS94.Goldbach.traceKernelSpectralDataRoadmapTarget
TS94.Goldbach.traceKernelSpectralDataTarget_of_ledgerTarget
```

TS94 does not choose a concrete trace kernel and does not prove the spectral
trace estimate. It records the kernel, spectral weight, normalization,
positivity, decay, and spectral-sum convergence obligations needed before the
TS92 spectral trace contract can be instantiated.

TS95 refines the TS92 explicit-formula trace bridge component:

```lean
TS95.Goldbach.NontrivialZeroTraceContribution
TS95.Goldbach.ExplicitFormulaResidualTerms
TS95.Goldbach.ExplicitFormulaResidualTerms.total
TS95.Goldbach.ExplicitFormulaTraceBridgeLedger
TS95.Goldbach.ExplicitFormulaTraceBridgeRoadmap
TS95.Goldbach.explicitFormulaTraceBridgeRoadmap
TS95.Goldbach.explicitFormulaTraceBridge_of_ledger
TS95.Goldbach.ExplicitFormulaTraceBridgeRoadmapTarget
TS95.Goldbach.ExplicitFormulaTraceBridgeLedgerTarget
TS95.Goldbach.ExplicitFormulaTraceBridgeTarget
TS95.Goldbach.explicitFormulaTraceBridgeRoadmapTarget
TS95.Goldbach.explicitFormulaTraceBridgeTarget_of_ledgerTarget
TS95.Goldbach.zetaZeroFamilyLedgerTarget_of_explicitFormulaTraceBridgeLedgerTarget
TS95.Goldbach.traceKernelSpectralDataLedgerTarget_of_explicitFormulaTraceBridgeLedgerTarget
```

TS95 does not prove the Riemann-von Mangoldt explicit formula. It records the
non-trivial-zero contribution, pole/trivial-zero/contour residuals, rational
trace budget, and bridge markers needed before TS92 can assemble a spectral
trace majorant.

TS96 assembles the spectral trace majorant route:

```lean
TS96.Goldbach.spectralTraceMajorantContract_of_explicitFormulaLedger
TS96.Goldbach.SpectralTraceMajorantDischargeTarget
TS96.Goldbach.spectralTraceMajorantContractTarget_of_explicitFormulaTraceBridgeLedgerTarget
TS96.Goldbach.traceMajorantContractTarget_of_explicitFormulaTraceBridgeLedgerTarget
TS96.Goldbach.OTSAFinalMajorantAPIContractsTarget_of_explicitFormulaTrace_mellin
TS96.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_BrunTitchmarsh_explicitFormulaTrace_mellin
TS96.Goldbach.spectralTraceMajorantDischargeTarget_of_explicitFormulaTraceBridgeLedgerTarget
```

TS96 does not prove the explicit formula or the zeta-zero trace estimate. It
proves that the TS95 ledger, once supplied, mechanically yields the TS92
`SpectralTraceMajorantContract`, the TS32 trace target, and the higher TS84/TS25
assembly routes.

TS97 isolates the final Brun-Titchmarsh input:

```lean
TS97.Goldbach.BrunTitchmarshFinalInputRoadmap
TS97.Goldbach.brunTitchmarshFinalInputRoadmap
TS97.Goldbach.BrunTitchmarshFinalInputLedger
TS97.Goldbach.BrunTitchmarshFinalInputRoadmapTarget
TS97.Goldbach.BrunTitchmarshFinalInputLedgerTarget
TS97.Goldbach.brunTitchmarshFinalInputRoadmapTarget
TS97.Goldbach.brunTitchmarshNatIntervalBoundTarget_of_finalInputLedgerTarget
TS97.Goldbach.paddedScaleTransferFinalAPIContracts_of_finalInputLedger
TS97.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_finalInputLedgerTarget_explicitFormulaTrace_mellin
TS97.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_finalInputLedgerTarget_explicitFormulaTrace_mellin
```

TS97 does not prove Brun-Titchmarsh or Selberg's sieve. It records that the
remaining arithmetic input for the current global assembly is exactly
`TS22.Goldbach.BrunTitchmarshNatIntervalBound`, and proves that this input,
together with the TS95 trace ledger and TS83 Mellin-tail final contracts, feeds
the TS84/TS25 final assembly routes.

TS98 records the root three-obligation dashboard:

```lean
TS98.Goldbach.FinalThreeObligationDashboard
TS98.Goldbach.finalThreeObligationDashboard
TS98.Goldbach.FinalHorizonInputs
TS98.Goldbach.FinalThreeObligationDashboardTarget
TS98.Goldbach.FinalHorizonInputsTarget
TS98.Goldbach.finalThreeObligationDashboardTarget
TS98.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_finalHorizonInputs
TS98.Goldbach.explicitFormulaTraceBridgeLedgerTarget_of_finalHorizonInputs
TS98.Goldbach.mellinTailFinalAPIContractsTarget_of_finalHorizonInputs
TS98.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_finalHorizonInputs
TS98.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_finalHorizonInputs
TS98.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_finalHorizonInputsTarget
TS98.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_finalHorizonInputsTarget
```

TS98 proves that the current TS15--TS97 route has exactly three final root
inputs for the TS84/TS25 final assembly: the TS97 Brun-Titchmarsh input, the
TS95 explicit-formula trace ledger, and the TS83 Mellin-tail final API
contracts.

TS99 opens the Selberg-weight layer below the TS97 arithmetic input:

```lean
TS99.Goldbach.SelbergSieveWeightRoadmap
TS99.Goldbach.selbergSieveWeightRoadmap
TS99.Goldbach.SelbergSieveWeightLedger
TS99.Goldbach.SelbergSieveWeightInfrastructure
TS99.Goldbach.SelbergSieveWeightRoadmapTarget
TS99.Goldbach.SelbergSieveWeightLedgerTarget
TS99.Goldbach.SelbergSieveWeightInfrastructureTarget
TS99.Goldbach.selbergSieveWeightRoadmapTarget
TS99.Goldbach.selbergBrunTitchmarshInfrastructure_of_weightInfrastructure
TS99.Goldbach.brunTitchmarshFinalInputLedger_of_weightInfrastructure
TS99.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_weightInfrastructureTarget
TS99.Goldbach.finalHorizonInputsTarget_of_selbergWeight_trace_mellin
TS99.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_selbergWeight_trace_mellin
TS99.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_selbergWeight_trace_mellin
```

TS99 does not prove Selberg's sieve, Mobius inversion, quadratic-form
diagonalization, Brun-Titchmarsh, or any prime-count estimate. It records the
Selberg weight data and local obligations that feed TS30, then shows that those
inputs feed TS97 and the TS98 root dashboard.

TS100 opens the Selberg quadratic-form layer below the TS99 Selberg-weight
front:

```lean
TS100.Goldbach.SelbergQuadraticFormRoadmap
TS100.Goldbach.selbergQuadraticFormRoadmap
TS100.Goldbach.SelbergQuadraticFormLedger
TS100.Goldbach.SelbergQuadraticFormInfrastructure
TS100.Goldbach.SelbergQuadraticFormRoadmapTarget
TS100.Goldbach.SelbergQuadraticFormLedgerTarget
TS100.Goldbach.SelbergQuadraticFormInfrastructureTarget
TS100.Goldbach.selbergQuadraticFormRoadmapTarget
TS100.Goldbach.selbergSieveWeightInfrastructure_of_quadraticFormInfrastructure
TS100.Goldbach.selbergSieveWeightInfrastructureTarget_of_quadraticFormInfrastructureTarget
TS100.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_quadraticFormInfrastructureTarget
TS100.Goldbach.finalHorizonInputsTarget_of_selbergQuadratic_trace_mellin
TS100.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_selbergQuadratic_trace_mellin
TS100.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_selbergQuadratic_trace_mellin
```

TS100 does not prove Selberg's sieve, Mobius inversion, quadratic-form
diagonalization, Brun-Titchmarsh, or any prime-count estimate. It records the
quadratic-kernel and divisor-algebra obligations that feed TS99, then shows
that those inputs feed TS97 and the TS98 root dashboard.

TS101 opens the Selberg divisor-algebra layer below the TS100 quadratic-form
front:

```lean
TS101.Goldbach.SelbergDivisorAlgebraRoadmap
TS101.Goldbach.selbergDivisorAlgebraRoadmap
TS101.Goldbach.SelbergDivisorAlgebraLedger
TS101.Goldbach.SelbergDivisorAlgebraInfrastructure
TS101.Goldbach.SelbergDivisorAlgebraRoadmapTarget
TS101.Goldbach.SelbergDivisorAlgebraLedgerTarget
TS101.Goldbach.SelbergDivisorAlgebraInfrastructureTarget
TS101.Goldbach.selbergDivisorAlgebraRoadmapTarget
TS101.Goldbach.selbergQuadraticFormInfrastructure_of_divisorAlgebraInfrastructure
TS101.Goldbach.selbergQuadraticFormInfrastructureTarget_of_divisorAlgebraInfrastructureTarget
TS101.Goldbach.selbergSieveWeightInfrastructureTarget_of_divisorAlgebraInfrastructureTarget
TS101.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_divisorAlgebraInfrastructureTarget
TS101.Goldbach.finalHorizonInputsTarget_of_selbergDivisor_trace_mellin
TS101.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_selbergDivisor_trace_mellin
TS101.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_selbergDivisor_trace_mellin
```

TS101 does not prove Mobius inversion, gcd/lcm algebra, Selberg's sieve,
quadratic-form diagonalization, Brun-Titchmarsh, or any prime-count estimate.
It records divisor-weight, convolution, and gcd/lcm-kernel obligations that
feed TS100, then shows that those inputs feed TS97 and the TS98 root dashboard.

TS102 packages the current root assembly:

```lean
TS102.Goldbach.HorizonRootAssemblyRoadmap
TS102.Goldbach.horizonRootAssemblyRoadmap
TS102.Goldbach.HorizonRootAssemblyInputs
TS102.Goldbach.HorizonRootAssembly
TS102.Goldbach.HorizonRootAssemblyRoadmapTarget
TS102.Goldbach.HorizonRootAssemblyInputsTarget
TS102.Goldbach.HorizonRootAssemblyTarget
TS102.Goldbach.horizonRootAssemblyRoadmapTarget
TS102.Goldbach.finalHorizonInputsTarget_of_rootAssemblyInputs
TS102.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_rootAssemblyInputs
TS102.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_rootAssemblyInputs
TS102.Goldbach.finalMajorantsTarget_of_paddedScaleTransferTarget
TS102.Goldbach.finalMajorantsTarget_of_rootAssemblyInputs
TS102.Goldbach.candidateV3CertificateTarget_of_rootAssemblyInputs
TS102.Goldbach.candidateV3RegisterTarget_of_rootAssemblyInputs
TS102.Goldbach.candidateV3ProvenanceTarget_of_rootAssemblyInputs
TS102.Goldbach.scaledOTSAAdmissibleTarget_of_rootAssemblyInputs
TS102.Goldbach.horizonRootAssembly_of_inputs
TS102.Goldbach.horizonRootAssemblyTarget_of_inputsTarget
```

TS102 does not prove Brun-Titchmarsh, Selberg's sieve, the explicit formula,
zeta-zero estimates, Plancherel, Sobolev-slot recognition, or Fourier-tail
estimates. It records that the terminal packages TS101, TS95, and TS83 feed the
current TS98/TS84/TS25 root surfaces and the conditional candidate-v3 OTSA
certificate/register/provenance layer.

TS103 opens the Mobius-inversion layer below the TS101 divisor-algebra front:

```lean
TS103.Goldbach.MobiusInversionRoadmap
TS103.Goldbach.mobiusInversionRoadmap
TS103.Goldbach.DivisorSumConvolution
TS103.Goldbach.MobiusDeltaIdentity
TS103.Goldbach.MobiusInversionLedger
TS103.Goldbach.MobiusInversionInfrastructure
TS103.Goldbach.MobiusInversionRoadmapTarget
TS103.Goldbach.DivisorSumConvolutionTarget
TS103.Goldbach.MobiusDeltaIdentityTarget
TS103.Goldbach.MobiusInversionLedgerTarget
TS103.Goldbach.MobiusInversionInfrastructureTarget
TS103.Goldbach.mobiusInversionRoadmapTarget
TS103.Goldbach.selbergDivisorAlgebraLedger_of_mobiusInversionLedger
TS103.Goldbach.selbergDivisorAlgebraInfrastructure_of_mobiusInversionInfrastructure
TS103.Goldbach.selbergDivisorAlgebraInfrastructureTarget_of_mobiusInversionInfrastructureTarget
TS103.Goldbach.selbergQuadraticFormInfrastructureTarget_of_mobiusInversionInfrastructureTarget
TS103.Goldbach.selbergSieveWeightInfrastructureTarget_of_mobiusInversionInfrastructureTarget
TS103.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_mobiusInversionInfrastructureTarget
TS103.Goldbach.finalHorizonInputsTarget_of_mobius_trace_mellin
TS103.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_mobius_trace_mellin
TS103.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_mobius_trace_mellin
```

TS103 does not prove Mobius inversion, divisor-convolution algebra, gcd/lcm
kernel algebra, Selberg's sieve, Brun-Titchmarsh, or any prime-count estimate.
It records the Mobius-delta and divisor-convolution obligations that feed
TS101, then shows that those inputs feed TS97 and the TS98 root dashboard.

TS104 probes the current Mathlib Mobius API:

```lean
TS104.Goldbach.MobiusSymbolStatus
TS104.Goldbach.MobiusMathlibAPIProbe
TS104.Goldbach.mathlibMoebiusFun
TS104.Goldbach.mathlibDivisorSum
TS104.Goldbach.mathlibDirichletConvolution
TS104.Goldbach.mathlibArithmeticDelta
TS104.Goldbach.mathlibArithmeticDelta_one
TS104.Goldbach.mathlibArithmeticDelta_ne_one_zero
TS104.Goldbach.mobiusMathlibAPIProbe
TS104.Goldbach.MobiusConcreteBinding
TS104.Goldbach.mobiusConcreteBinding
TS104.Goldbach.divisorSumConvolution_of_concreteBinding
TS104.Goldbach.mobiusDeltaIdentity_of_concreteBinding
TS104.Goldbach.MobiusConcreteBindingInfrastructure
TS104.Goldbach.MobiusMathlibAPIProbeTarget
TS104.Goldbach.MobiusConcreteBindingTarget
TS104.Goldbach.MobiusConcreteBindingInfrastructureTarget
TS104.Goldbach.mobiusMathlibAPIProbeTarget
TS104.Goldbach.mobiusConcreteBindingTarget
TS104.Goldbach.divisorSumConvolutionTarget_of_concreteBindingTarget
TS104.Goldbach.mobiusDeltaIdentityTarget_of_concreteBindingTarget
TS104.Goldbach.mobiusInversionLedger_of_concreteBindingInfrastructure
TS104.Goldbach.mobiusInversionInfrastructure_of_concreteBindingInfrastructure
TS104.Goldbach.mobiusInversionInfrastructureTarget_of_concreteBindingInfrastructureTarget
TS104.Goldbach.finalHorizonInputsTarget_of_mobiusConcrete_trace_mellin
TS104.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_mobiusConcrete_trace_mellin
TS104.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_mobiusConcrete_trace_mellin
```

TS104 locates Mathlib's `ArithmeticFunction.moebius`,
`ArithmeticFunction.zeta`, divisor finsets, divisor-antidiagonal convolution,
and the bundled convolution inverse theorem. It does not prove the full TS103
Mobius infrastructure, gcd/lcm kernel algebra, Selberg's sieve,
Brun-Titchmarsh, or any prime-count estimate.

TS105 discharges the concrete Mobius-delta identity from Mathlib:

```lean
TS105.Goldbach.mathlibMoebiusDivisorSum_eq_delta
TS105.Goldbach.mathlibArithmeticDelta_eq_ite
TS105.Goldbach.mathlibMoebiusDivisorSum_eq_ite
TS105.Goldbach.mobiusConcreteBinding_divisorSum_mobius_eq_delta
TS105.Goldbach.MobiusConcreteDeltaDischarge
TS105.Goldbach.mobiusConcreteDeltaDischarge
TS105.Goldbach.mobiusDeltaIdentity_of_concreteDeltaDischarge
TS105.Goldbach.MobiusConcreteDeltaDischargeTarget
TS105.Goldbach.mobiusConcreteDeltaDischargeTarget
TS105.Goldbach.mobiusDeltaIdentityTarget_of_concreteDeltaDischargeTarget
TS105.Goldbach.mobiusDeltaIdentityTarget
TS105.Goldbach.mobiusConcreteBindingTarget
```

TS105 proves the finite divisor-sum identity by evaluating Mathlib's bundled
theorem `ArithmeticFunction.coe_moebius_mul_coe_zeta` at `n` and rewriting
with `ArithmeticFunction.coe_mul_zeta_apply`. It does not prove the full
TS103 Mobius infrastructure, gcd/lcm kernel algebra, Selberg's sieve,
Brun-Titchmarsh, or any prime-count estimate.

TS106 opens and partially discharges the divisor-kernel algebra layer:

```lean
TS106.Goldbach.canonicalGcdKernel
TS106.Goldbach.canonicalLcmKernel
TS106.Goldbach.canonicalGcdKernel_mul_lcmKernel
TS106.Goldbach.DivisorConvolutionBridge
TS106.Goldbach.divisorConvolutionBridge
TS106.Goldbach.GCDLCMKernelAlgebra
TS106.Goldbach.gcdLCMKernelAlgebra
TS106.Goldbach.SelbergQuadraticKernelExtraction
TS106.Goldbach.DivisorKernelAlgebraInfrastructure
TS106.Goldbach.DivisorConvolutionBridgeTarget
TS106.Goldbach.GCDLCMKernelAlgebraTarget
TS106.Goldbach.SelbergQuadraticKernelExtractionTarget
TS106.Goldbach.DivisorKernelAlgebraInfrastructureTarget
TS106.Goldbach.divisorConvolutionBridgeTarget
TS106.Goldbach.gcdLCMKernelAlgebraTarget
TS106.Goldbach.mobiusInversionLedger_of_divisorKernelAlgebraInfrastructure
TS106.Goldbach.mobiusInversionInfrastructure_of_divisorKernelAlgebraInfrastructure
TS106.Goldbach.mobiusInversionInfrastructureTarget_of_divisorKernelAlgebraInfrastructureTarget
TS106.Goldbach.selbergDivisorAlgebraInfrastructureTarget_of_divisorKernelAlgebraInfrastructureTarget
TS106.Goldbach.finalHorizonInputsTarget_of_divisorKernel_trace_mellin
TS106.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_divisorKernel_trace_mellin
TS106.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_divisorKernel_trace_mellin
```

TS106 proves the rational-valued canonical gcd/lcm kernel identity using
`Nat.gcd_mul_lcm` and transports a full divisor-kernel infrastructure into
TS103. It does not prove Selberg's sieve, Brun-Titchmarsh, quadratic-form
diagonalization, or any prime-count estimate.

TS107 extracts the canonical Selberg-style quadratic kernel:

```lean
TS107.Goldbach.canonicalSelbergQuadraticKernel
TS107.Goldbach.canonicalSelbergQuadraticKernel_symm
TS107.Goldbach.SelbergQuadraticKernelExtractionProof
TS107.Goldbach.selbergQuadraticKernelExtractionProof
TS107.Goldbach.selbergQuadraticKernelExtraction_of_proof
TS107.Goldbach.SelbergKernelExtractionInfrastructure
TS107.Goldbach.SelbergQuadraticKernelExtractionProofTarget
TS107.Goldbach.SelbergKernelExtractionInfrastructureTarget
TS107.Goldbach.selbergQuadraticKernelExtractionProofTarget
TS107.Goldbach.selbergQuadraticKernelExtractionTarget
TS107.Goldbach.divisorKernelAlgebraInfrastructure_of_kernelExtractionInfrastructure
TS107.Goldbach.divisorKernelAlgebraInfrastructureTarget_of_kernelExtractionInfrastructureTarget
TS107.Goldbach.mobiusInversionInfrastructureTarget_of_kernelExtractionInfrastructureTarget
TS107.Goldbach.selbergDivisorAlgebraInfrastructureTarget_of_kernelExtractionInfrastructureTarget
TS107.Goldbach.finalHorizonInputsTarget_of_kernelExtraction_trace_mellin
TS107.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_kernelExtraction_trace_mellin
TS107.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_kernelExtraction_trace_mellin
```

TS107 proves symmetry of the rational-valued canonical `gcd/lcm` ratio kernel
using `Nat.gcd_comm` and `Nat.lcm_comm`, and supplies the TS106 quadratic
kernel extraction target. It does not prove Selberg's sieve, Brun-Titchmarsh,
quadratic-form diagonalization, or any prime-count estimate.

TS108 formalizes the finite Selberg quadratic-form expansion:

```lean
TS108.Goldbach.selbergQuadraticFormTerm
TS108.Goldbach.selbergQuadraticFormTerm_symm
TS108.Goldbach.selbergQuadraticSupport
TS108.Goldbach.selbergQuadraticForm
TS108.Goldbach.selbergQuadraticForm_expansion
TS108.Goldbach.selbergQuadraticForm_swap_indices
TS108.Goldbach.SelbergQuadraticFormExpansion
TS108.Goldbach.selbergQuadraticFormExpansion
TS108.Goldbach.SelbergQuadraticFormExpansionTarget
TS108.Goldbach.selbergQuadraticFormExpansionTarget
TS108.Goldbach.SelbergQuadraticFormExpansionInfrastructure
TS108.Goldbach.SelbergQuadraticFormExpansionInfrastructureTarget
TS108.Goldbach.kernelExtractionInfrastructure_of_quadraticFormExpansionInfrastructure
TS108.Goldbach.selbergKernelExtractionInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
TS108.Goldbach.divisorKernelAlgebraInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
TS108.Goldbach.mobiusInversionInfrastructureTarget_of_quadraticFormExpansionInfrastructureTarget
TS108.Goldbach.finalHorizonInputsTarget_of_quadraticExpansion_trace_mellin
TS108.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_quadraticExpansion_trace_mellin
TS108.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_quadraticExpansion_trace_mellin
```

TS108 defines the finite double sum over `Finset.range (level + 1)`, proves
termwise symmetry using TS107's canonical kernel symmetry, and lifts it to an
index-swapped finite expansion. It does not prove Selberg's sieve,
Brun-Titchmarsh, quadratic-form diagonalization, or any prime-count estimate.

TS109 opens the Selberg quadratic diagonalization layer:

```lean
TS109.Goldbach.selbergDiagonalSupport
TS109.Goldbach.selbergDiagonalTransformedWeight
TS109.Goldbach.selbergUnitDiagonalCoefficient
TS109.Goldbach.selbergDiagonalSquareTerm
TS109.Goldbach.selbergDiagonalSquareSum
TS109.Goldbach.selbergDiagonalTransformedWeight_expansion
TS109.Goldbach.selbergDiagonalSquareSum_expansion
TS109.Goldbach.SelbergDiagonalChangeOfVariables
TS109.Goldbach.selbergDiagonalChangeOfVariables
TS109.Goldbach.SelbergQuadraticDiagonalization
TS109.Goldbach.selbergQuadraticDiagonalization
TS109.Goldbach.SelbergQuadraticDiagonalizationTarget
TS109.Goldbach.selbergQuadraticDiagonalizationTarget
TS109.Goldbach.SelbergQuadraticDiagonalizationInfrastructure
TS109.Goldbach.SelbergQuadraticDiagonalizationInfrastructureTarget
TS109.Goldbach.quadraticFormExpansionInfrastructure_of_diagonalizationInfrastructure
TS109.Goldbach.quadraticFormExpansionInfrastructureTarget_of_diagonalizationInfrastructureTarget
TS109.Goldbach.selbergKernelExtractionInfrastructureTarget_of_diagonalizationInfrastructureTarget
TS109.Goldbach.mobiusInversionInfrastructureTarget_of_diagonalizationInfrastructureTarget
TS109.Goldbach.finalHorizonInputsTarget_of_diagonalization_trace_mellin
TS109.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_diagonalization_trace_mellin
TS109.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_diagonalization_trace_mellin
```

TS109 defines the finite divisor-filtered transformed weights and the diagonal
square-sum side of the Selberg quadratic form. The dense-to-diagonal identity,
square-sum majorant, Selberg sieve bound, Brun-Titchmarsh theorem, and
prime-count estimates remain explicitly relative obligations.

TS110 names the Selberg dense-to-diagonal identity:

```lean
TS110.Goldbach.selbergDenseSide
TS110.Goldbach.selbergDiagonalSide
TS110.Goldbach.selbergDenseSide_eq_quadraticForm
TS110.Goldbach.selbergDiagonalSide_eq_squareSum
TS110.Goldbach.SelbergDenseToDiagonalIdentity
TS110.Goldbach.selbergDenseToDiagonalIdentity
TS110.Goldbach.selbergDenseToDiagonalIdentity_obligation_eq
TS110.Goldbach.SelbergDenseToDiagonalIdentityTarget
TS110.Goldbach.selbergDenseToDiagonalIdentityTarget
TS110.Goldbach.SelbergDenseToDiagonalInfrastructure
TS110.Goldbach.SelbergDenseToDiagonalInfrastructureTarget
TS110.Goldbach.diagonalizationInfrastructure_of_denseToDiagonalInfrastructure
TS110.Goldbach.diagonalizationInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
TS110.Goldbach.quadraticFormExpansionInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
TS110.Goldbach.mobiusInversionInfrastructureTarget_of_denseToDiagonalInfrastructureTarget
TS110.Goldbach.finalHorizonInputsTarget_of_denseToDiagonal_trace_mellin
TS110.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_denseToDiagonal_trace_mellin
TS110.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_denseToDiagonal_trace_mellin
```

TS110 records the equality between the TS108 dense value and the TS109 diagonal
value as a proposition-valued `identityObligation`, and proves that the
obligation has exactly that shape. It does not prove the dense-to-diagonal
identity, the square-sum majorant, Selberg's sieve, Brun-Titchmarsh, or any
prime-count estimate.

TS111 opens the finite reindexing layer below the TS110 identity:

```lean
TS111.Goldbach.selbergDiagonalFilterTerm
TS111.Goldbach.selbergDiagonalTripleTerm
TS111.Goldbach.selbergCanonicalDiagonalTripleExpansion
TS111.Goldbach.selbergDiagonalSquareTerm_triple_expansion
TS111.Goldbach.selbergDiagonalSide_triple_expansion
TS111.Goldbach.SelbergDenseToDiagonalReindexing
TS111.Goldbach.selbergDenseToDiagonalReindexing
TS111.Goldbach.SelbergDenseToDiagonalReindexingTarget
TS111.Goldbach.selbergDenseToDiagonalReindexingTarget
TS111.Goldbach.SelbergDenseToDiagonalReindexingInfrastructure
TS111.Goldbach.SelbergDenseToDiagonalReindexingInfrastructureTarget
TS111.Goldbach.denseToDiagonalInfrastructure_of_reindexingInfrastructure
TS111.Goldbach.denseToDiagonalInfrastructureTarget_of_reindexingInfrastructureTarget
TS111.Goldbach.diagonalizationInfrastructureTarget_of_reindexingInfrastructureTarget
TS111.Goldbach.mobiusInversionInfrastructureTarget_of_reindexingInfrastructureTarget
TS111.Goldbach.finalHorizonInputsTarget_of_reindexing_trace_mellin
TS111.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_reindexing_trace_mellin
TS111.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_reindexing_trace_mellin
```

TS111 proves that one TS109 diagonal square term expands to a finite double
sum, then lifts this to a triple-sum expansion of the canonical diagonal side.
It does not prove the finite reindexing collapse, divisor-filter rewrite,
dense-to-diagonal identity, square-sum majorant, Selberg's sieve,
Brun-Titchmarsh, or any prime-count estimate.

TS112 opens the Mobius-collapse layer below TS111:

```lean
TS112.Goldbach.selbergDivisorPairFilter
TS112.Goldbach.selbergGcdFilterTerm
TS112.Goldbach.selbergDiagonalFilterTerm_mul_eq_pairFilter
TS112.Goldbach.selbergDivisorPairFilter_eq_gcdFilter
TS112.Goldbach.selbergDiagonalTripleTerm_eq_gcdFilter
TS112.Goldbach.selbergCanonicalGcdCollapseExpansion
TS112.Goldbach.selbergCanonicalDiagonalTripleExpansion_eq_gcdCollapseExpansion
TS112.Goldbach.SelbergMobiusCollapse
TS112.Goldbach.selbergMobiusCollapse
TS112.Goldbach.selbergMobiusCollapse_obligation_eq
TS112.Goldbach.SelbergMobiusCollapseTarget
TS112.Goldbach.selbergMobiusCollapseTarget
TS112.Goldbach.SelbergMobiusCollapseInfrastructure
TS112.Goldbach.SelbergMobiusCollapseInfrastructureTarget
TS112.Goldbach.reindexingInfrastructure_of_mobiusCollapseInfrastructure
TS112.Goldbach.reindexingInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
TS112.Goldbach.denseToDiagonalInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
TS112.Goldbach.mobiusInversionInfrastructureTarget_of_mobiusCollapseInfrastructureTarget
TS112.Goldbach.finalHorizonInputsTarget_of_mobiusCollapse_trace_mellin
TS112.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_mobiusCollapse_trace_mellin
TS112.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_mobiusCollapse_trace_mellin
```

TS112 proves that multiplying two TS111 divisor-filtered terms gives a
pair-divisibility filter, proves that this pair filter is equivalent to one
filter on `Nat.gcd`, and lifts the rewrite through the TS111 triple sum. It
does not prove the Mobius-delta collapse, dense-kernel match,
dense-to-diagonal identity, square-sum majorant, Selberg's sieve,
Brun-Titchmarsh, or any prime-count estimate.

TS113 opens the finite-Fubini layer below TS112:

```lean
TS113.Goldbach.selbergGcdCollapseTerm
TS113.Goldbach.selbergGcdCollapseTripleSum
TS113.Goldbach.selbergInnerGcdDivisorSum
TS113.Goldbach.selbergPairFirstGcdCollapseSum
TS113.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_tripleSum
TS113.Goldbach.selbergGcdCollapseTripleSum_reordered
TS113.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_pairFirst
TS113.Goldbach.InnerGcdDivisorCollapseReady
TS113.Goldbach.innerGcdDivisorCollapseReady
TS113.Goldbach.SelbergFiniteFubiniReindexing
TS113.Goldbach.selbergFiniteFubiniReindexing
TS113.Goldbach.SelbergFiniteFubiniReindexingTarget
TS113.Goldbach.selbergFiniteFubiniReindexingTarget
TS113.Goldbach.SelbergFiniteFubiniReindexingInfrastructure
TS113.Goldbach.SelbergFiniteFubiniReindexingInfrastructureTarget
TS113.Goldbach.mobiusCollapseInfrastructure_of_fubiniInfrastructure
TS113.Goldbach.mobiusCollapseInfrastructureTarget_of_fubiniInfrastructureTarget
TS113.Goldbach.reindexingInfrastructureTarget_of_fubiniInfrastructureTarget
TS113.Goldbach.mobiusInversionInfrastructureTarget_of_fubiniInfrastructureTarget
TS113.Goldbach.finalHorizonInputsTarget_of_fubini_trace_mellin
TS113.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_fubini_trace_mellin
TS113.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_fubini_trace_mellin
```

TS113 proves the finite reindexing from diagonal-first order to pair-first
order using `Finset.sum_comm`, and isolates the inner gcd-divisor sum for each
pair `(m,n)`. It does not prove the Mobius-delta collapse, dense-kernel match,
dense-to-diagonal identity, square-sum majorant, Selberg's sieve,
Brun-Titchmarsh, or any prime-count estimate.

TS114 opens the local inner-collapse layer below TS113:

```lean
TS114.Goldbach.selbergInnerGcdKernelCoefficient
TS114.Goldbach.selbergGcdCollapseTerm_factor
TS114.Goldbach.selbergInnerGcdDivisorSum_factor
TS114.Goldbach.SelbergInnerGcdKernelMatchObligation
TS114.Goldbach.selbergPairFirstGcdCollapseSum_eq_denseSide_of_kernelMatch
TS114.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_kernelMatch
TS114.Goldbach.SelbergInnerGcdDivisorCollapse
TS114.Goldbach.selbergInnerGcdDivisorCollapse
TS114.Goldbach.SelbergInnerGcdDivisorCollapseTarget
TS114.Goldbach.selbergInnerGcdDivisorCollapseTarget
TS114.Goldbach.SelbergInnerGcdDivisorCollapseInfrastructure
TS114.Goldbach.SelbergInnerGcdDivisorCollapseInfrastructureTarget
TS114.Goldbach.fubiniInfrastructure_of_innerCollapseInfrastructure
TS114.Goldbach.fubiniInfrastructureTarget_of_innerCollapseInfrastructureTarget
TS114.Goldbach.mobiusCollapseInfrastructureTarget_of_innerCollapseInfrastructureTarget
TS114.Goldbach.reindexingInfrastructureTarget_of_innerCollapseInfrastructureTarget
TS114.Goldbach.mobiusInversionInfrastructureTarget_of_innerCollapseInfrastructureTarget
TS114.Goldbach.finalHorizonInputsTarget_of_innerCollapse_trace_mellin
TS114.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_innerCollapse_trace_mellin
TS114.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_innerCollapse_trace_mellin
```

TS114 proves that each inner gcd-divisor sum factors as `weight m * weight n`
times a local coefficient. It also proves that if this local coefficient
matches the canonical TS107 `gcd/lcm` kernel, then the TS113 pair-first side
and the TS112 gcd-filtered side equal the TS110 dense side. It does not prove
the Mobius coefficient calculation, dense-kernel match, dense-to-diagonal
identity, square-sum majorant, Selberg's sieve, Brun-Titchmarsh, or any
prime-count estimate.

TS115 opens the one-variable Mobius-coefficient layer below TS114:

```lean
TS115.Goldbach.selbergGcdCoefficientSupport
TS115.Goldbach.selbergGcdCoefficient
TS115.Goldbach.selbergInnerGcdKernelCoefficient_eq_gcdCoefficient
TS115.Goldbach.selbergGcdCoefficient_eq_filter_sum
TS115.Goldbach.SelbergGcdCoefficientKernelMatchObligation
TS115.Goldbach.innerGcdKernelMatchObligation_of_gcdCoefficientKernelMatch
TS115.Goldbach.selbergPairFirstGcdCollapseSum_eq_denseSide_of_gcdCoefficientKernelMatch
TS115.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_gcdCoefficientKernelMatch
TS115.Goldbach.SelbergMobiusCoefficient
TS115.Goldbach.selbergMobiusCoefficient
TS115.Goldbach.SelbergMobiusCoefficientTarget
TS115.Goldbach.selbergMobiusCoefficientTarget
TS115.Goldbach.SelbergMobiusCoefficientInfrastructure
TS115.Goldbach.SelbergMobiusCoefficientInfrastructureTarget
TS115.Goldbach.innerCollapseInfrastructure_of_coefficientInfrastructure
TS115.Goldbach.innerCollapseInfrastructureTarget_of_coefficientInfrastructureTarget
TS115.Goldbach.fubiniInfrastructureTarget_of_coefficientInfrastructureTarget
TS115.Goldbach.mobiusCollapseInfrastructureTarget_of_coefficientInfrastructureTarget
TS115.Goldbach.mobiusInversionInfrastructureTarget_of_coefficientInfrastructureTarget
TS115.Goldbach.finalHorizonInputsTarget_of_coefficient_trace_mellin
TS115.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_coefficient_trace_mellin
TS115.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_coefficient_trace_mellin
```

TS115 proves that the TS114 local coefficient depends on `(m,n)` only through
`Nat.gcd m n`, rewrites that coefficient as a filtered finite divisor sum, and
shows that the resulting coefficient-match obligation implies the TS114 local
kernel match and the conditional dense-side equalities. It does not prove the
Mobius coefficient calculation, dense-kernel match, dense-to-diagonal identity,
square-sum majorant, Selberg's sieve, Brun-Titchmarsh, or any prime-count
estimate.

TS116 opens the gcd-coefficient kernel-match layer below TS115:

```lean
TS116.Goldbach.selbergDiagonalCoefficientFormula
TS116.Goldbach.selbergDiagonalCoefficientFormula_eq_unit
TS116.Goldbach.selbergGcdCoefficient_eq_formula_filter_sum
TS116.Goldbach.selbergCanonicalKernelFromGcd
TS116.Goldbach.SelbergGcdCoefficientKernelCompatibility
TS116.Goldbach.gcdCoefficientKernelCompatibility_iff_ts115_match
TS116.Goldbach.gcdCoefficientKernelMatchObligation_of_compatibility
TS116.Goldbach.innerGcdKernelMatchObligation_of_compatibility
TS116.Goldbach.selbergCanonicalGcdCollapseExpansion_eq_denseSide_of_compatibility
TS116.Goldbach.SelbergGcdCoefficientKernelMatch
TS116.Goldbach.selbergGcdCoefficientKernelMatch
TS116.Goldbach.SelbergGcdCoefficientKernelMatchTarget
TS116.Goldbach.selbergGcdCoefficientKernelMatchTarget
TS116.Goldbach.SelbergGcdCoefficientKernelMatchInfrastructure
TS116.Goldbach.SelbergGcdCoefficientKernelMatchInfrastructureTarget
TS116.Goldbach.coefficientInfrastructure_of_kernelMatchInfrastructure
TS116.Goldbach.coefficientInfrastructureTarget_of_kernelMatchInfrastructureTarget
TS116.Goldbach.innerCollapseInfrastructureTarget_of_kernelMatchInfrastructureTarget
TS116.Goldbach.fubiniInfrastructureTarget_of_kernelMatchInfrastructureTarget
TS116.Goldbach.mobiusCollapseInfrastructureTarget_of_kernelMatchInfrastructureTarget
TS116.Goldbach.mobiusInversionInfrastructureTarget_of_kernelMatchInfrastructureTarget
TS116.Goldbach.finalHorizonInputsTarget_of_kernelMatch_trace_mellin
TS116.Goldbach.paddedScaleTransferFinalAPIContractsTarget_of_kernelMatch_trace_mellin
TS116.Goldbach.paddedScaleAnalyticInfrastructureTarget_of_kernelMatch_trace_mellin
```

TS116 records that the current TS109 diagonal coefficient is the unit
placeholder, rewrites the TS115 gcd coefficient using the explicit diagonal
coefficient formula, and proves that the local compatibility obligation is
definitionally the TS115 coefficient-kernel match. It does not prove the real
Mobius coefficient calculation, dense-kernel match, dense-to-diagonal identity,
square-sum majorant, Selberg's sieve, Brun-Titchmarsh, or any prime-count
estimate.

TS117 performs a calculation audit of the TS116 compatibility layer:

```lean
TS117.Goldbach.selbergMobiusSquareTotientCoefficient
TS117.Goldbach.selbergMobiusSquareTotientCoefficient_one
TS117.Goldbach.selbergMobiusSquareTotientGcdCoefficient
TS117.Goldbach.selbergMobiusSquareTotientGcdCoefficient_eq_filter_sum
TS117.Goldbach.canonicalKernel_two_four
TS117.Goldbach.canonicalKernel_two_six
TS117.Goldbach.canonicalKernel_two_four_ne_two_six
TS117.Goldbach.no_gcd_only_coefficient_matches_canonicalKernel
TS117.Goldbach.no_selbergGcdCoefficientKernelCompatibility
TS117.Goldbach.SelbergDiagonalCoefficientCalculation
TS117.Goldbach.selbergDiagonalCoefficientCalculation
TS117.Goldbach.SelbergDiagonalCoefficientCalculationTarget
TS117.Goldbach.selbergDiagonalCoefficientCalculationTarget
TS117.Goldbach.selbergGcdCoefficientKernelMatchTarget
```

TS117 defines a standard Mobius-square/totient coefficient candidate and proves
its normalization at `d = 1`. More importantly, it proves that the current
TS109--TS116 gcd-only coefficient shape cannot match the canonical dense
`gcd/lcm` kernel for all pairs: `(2,4)` and `(2,6)` have the same gcd but
kernel values `1/2` and `1/3`. Thus TS117 does not close the Selberg
coefficient calculation; it formally diagnoses that the diagonal
change-of-variables must be refined before the dense-to-diagonal identity can
be discharged.

TS118 proves the lcm-absorption bridge indicated by TS117:

```lean
TS118.Goldbach.selbergLCMAbsorbedWeight
TS118.Goldbach.selbergGcdSquareKernel
TS118.Goldbach.selbergGcdSquareFormTerm
TS118.Goldbach.canonicalSelbergQuadraticKernel_eq_gcdSquare_div_mul
TS118.Goldbach.selbergQuadraticFormTerm_eq_gcdSquareAbsorbedTerm
TS118.Goldbach.selbergGcdSquareDenseSide
TS118.Goldbach.selbergDenseSide_eq_gcdSquareDenseSide_absorbed
TS118.Goldbach.SelbergLCMAbsorptionBridge
TS118.Goldbach.selbergLCMAbsorptionBridge
TS118.Goldbach.SelbergLCMAbsorptionBridgeTarget
TS118.Goldbach.selbergLCMAbsorptionBridgeTarget
TS118.Goldbach.selbergDiagonalCoefficientCalculationTarget
```

TS118 proves, termwise over `Rat`, that

```text
w(m) * w(n) * gcd(m,n)/lcm(m,n)
=
(w(m)/m) * (w(n)/n) * gcd(m,n)^2
```

and lifts this equality through the TS108 finite double sum. This produces a
corrected target for future diagonalization: the absorbed-weight dense form
with gcd-square kernel. TS118 does not prove the corrected diagonalization,
square-sum majorant, Selberg's sieve, Brun-Titchmarsh, or any prime-count
estimate.

TS119 opens the corrected Jordan-two diagonalization layer above TS118:

```lean
TS119.Goldbach.selbergJordanTwoFunction
TS119.Goldbach.selbergJordanTwoCoefficient
TS119.Goldbach.selbergJordanTwoFunction_eq_moebius_mul_pow_two
TS119.Goldbach.zeta_mul_selbergJordanTwoFunction
TS119.Goldbach.selbergJordanTwoCoefficient_divisor_sum_eq_square
TS119.Goldbach.selbergGcdSquareTransformedWeight
TS119.Goldbach.selbergGcdSquareTransformedWeight_expansion
TS119.Goldbach.selbergJordanTwoDiagonalSquareTerm
TS119.Goldbach.selbergJordanTwoDiagonalSide
TS119.Goldbach.selbergJordanTwoDiagonalSide_expansion
TS119.Goldbach.SelbergGcdSquareDiagonalization
TS119.Goldbach.selbergGcdSquareDiagonalization
TS119.Goldbach.SelbergGcdSquareDiagonalizationTarget
TS119.Goldbach.selbergGcdSquareDiagonalizationTarget
TS119.Goldbach.selbergLCMAbsorptionBridgeTarget
```

TS119 defines `J2 = moebius * pow 2` as an arithmetic function over `Rat`,
proves `zeta * J2 = pow 2`, and derives the local collapse

```text
sum_{d | g} J2(d) = g^2
```

using Mathlib's `ArithmeticFunction` convolution API. It also defines the
corrected diagonal side

```text
sum_d J2(d) * (sum_{d | m} a(m))^2
```

for the absorbed gcd-square form. The global finite reindexing identity between
the corrected dense side and this diagonal side remains an explicit
proposition-valued obligation.

TS120 opens the corrected global reindexing layer above TS119:

```lean
TS120.Goldbach.selbergJordanTwoDiagonalFilterTerm
TS120.Goldbach.selbergJordanTwoDiagonalTripleTerm
TS120.Goldbach.selbergJordanTwoDiagonalTripleSum
TS120.Goldbach.selbergJordanTwoDiagonalSquareTerm_triple_expansion
TS120.Goldbach.selbergJordanTwoDiagonalSide_triple_expansion
TS120.Goldbach.selbergJordanTwoDivisorPairFilter
TS120.Goldbach.selbergJordanTwoGcdFilterTerm
TS120.Goldbach.selbergJordanTwoDiagonalFilterTerm_mul_eq_pairFilter
TS120.Goldbach.selbergJordanTwoDivisorPairFilter_eq_gcdFilter
TS120.Goldbach.selbergJordanTwoDiagonalTripleTerm_eq_gcdFilter
TS120.Goldbach.selbergJordanTwoGcdFilteredTripleSum
TS120.Goldbach.selbergJordanTwoDiagonalTripleSum_eq_gcdFilteredTripleSum
TS120.Goldbach.selbergJordanTwoPairCoefficient
TS120.Goldbach.selbergJordanTwoPairFirstTerm
TS120.Goldbach.selbergJordanTwoPairFirstSide
TS120.Goldbach.selbergJordanTwoInnerGcdSum_factor
TS120.Goldbach.selbergJordanTwoGcdFilteredTripleSum_reordered
TS120.Goldbach.selbergJordanTwoDiagonalSide_eq_pairFirst
TS120.Goldbach.SelbergJordanTwoLocalCoefficientCollapse
TS120.Goldbach.selbergJordanTwoPairFirstSide_eq_gcdSquareDenseSide_of_localCollapse
TS120.Goldbach.selbergGcdSquareDenseSide_eq_jordanDiagonalSide_of_localCollapse
TS120.Goldbach.SelbergGcdSquareGlobalReindexing
TS120.Goldbach.selbergGcdSquareGlobalReindexing
TS120.Goldbach.SelbergGcdSquareGlobalReindexingTarget
TS120.Goldbach.selbergGcdSquareGlobalReindexingTarget
TS120.Goldbach.selbergGcdSquareDiagonalizationTarget
TS120.Goldbach.selbergLCMAbsorptionBridgeTarget
```

TS120 proves the finite reindexing chain

```text
corrected Jordan-two diagonal side
= diagonal-first triple sum
= gcd-filtered triple sum
= pair-first local-coefficient sum
```

using `Finset.sum_mul_sum`, the divisor equivalence
`d | m and d | n <-> d | gcd(m,n)`, and `Finset.sum_comm`. It then proves that
the remaining support-local coefficient collapse implies the corrected
absorbed gcd-square dense side equals the corrected Jordan-two diagonal side.
TS120 does not yet prove that support-local coefficient collapse, the
unconditional corrected dense-to-diagonal identity, the square-sum majorant,
Selberg's sieve, Brun-Titchmarsh, or any prime-count estimate.

TS121 discharges the TS120 finite-support issue for the corrected route:

```lean
TS121.Goldbach.selbergPositiveQuadraticSupport
TS121.Goldbach.mem_selbergPositiveQuadraticSupport
TS121.Goldbach.selbergJordanTwoPairCoefficient_eq_filter
TS121.Goldbach.selbergSupportFilter_dvd_gcd_eq_divisors_of_pos_left
TS121.Goldbach.selbergJordanTwoPairCoefficient_eq_gcdSquareKernel_of_pos_left
TS121.Goldbach.SelbergJordanTwoPositiveLocalCoefficientCollapse
TS121.Goldbach.selbergJordanTwoPositiveLocalCoefficientCollapse
TS121.Goldbach.selbergLCMAbsorbedWeight_zero
TS121.Goldbach.selbergAbsorbedPairCoefficientTerm_eq_gcdSquareTerm
TS121.Goldbach.selbergJordanTwoPairFirstSide_absorbed_eq_gcdSquareDenseSide
TS121.Goldbach.selbergGcdSquareDenseSide_absorbed_eq_jordanDiagonalSide
TS121.Goldbach.selbergOriginalDenseSide_eq_correctedJordanDiagonalSide
TS121.Goldbach.SelbergJordanTwoFiniteSupportCollapse
TS121.Goldbach.selbergJordanTwoFiniteSupportCollapse
TS121.Goldbach.SelbergJordanTwoFiniteSupportCollapseTarget
TS121.Goldbach.selbergJordanTwoFiniteSupportCollapseTarget
TS121.Goldbach.selbergGcdSquareGlobalReindexingTarget
```

TS121 proves that, when `0 < m` and `m` lies in the finite support, the support
filtered by divisors of `gcd(m,n)` is exactly `(Nat.gcd m n).divisors`. It then
uses TS119's `J2` divisor-sum identity to prove the positive local coefficient
collapse. The zero index is handled by TS118's absorbed weights: `weight 0 / 0`
is `0` in Lean's totalized field division. Consequently TS121 proves

```text
TS110 dense gcd/lcm side
= corrected TS119 Jordan-two diagonal side with absorbed weights.
```

TS121 does not prove the square-sum majorant, Selberg's sieve,
Brun-Titchmarsh, interval majorant, budget comparison, or any prime-count
estimate.

TS122 starts the corrected Selberg diagonal optimization layer:

```lean
TS122.Goldbach.finite_weighted_cauchy_rat
TS122.Goldbach.selbergOptimizationSupport
TS122.Goldbach.selbergMobiusRatCoefficient
TS122.Goldbach.selbergJordanTwoPenalty
TS122.Goldbach.selbergDiagonalEnergy
TS122.Goldbach.selbergMobiusLinearForm
TS122.Goldbach.selbergOptimizationDenominator
TS122.Goldbach.selbergDiagonalWeightedCauchy
TS122.Goldbach.selbergDiagonalEnergy_lower_bound_of_constraint
TS122.Goldbach.SelbergDiagonalOptimization
TS122.Goldbach.selbergDiagonalOptimization
TS122.Goldbach.SelbergDiagonalOptimizationTarget
TS122.Goldbach.selbergDiagonalOptimizationTarget
TS122.Goldbach.selbergJordanTwoFiniteSupportCollapseTarget
```

The core concrete theorem is the finite weighted Cauchy inequality over `Rat`:

```text
(sum_i c_i y_i)^2
<=
(sum_i c_i^2 / a_i) * (sum_i a_i y_i^2),
```

assuming `0 < a_i` on the finite support. TS122 specializes this with
`a_i = J2(i)` and `c_i = moebius(i)` on the positive Selberg support, proving
that the Mobius-normalized constraint gives

```text
1 / denominator <= corrected Jordan-two diagonal energy.
```

TS122 does not yet prove positivity of `J2` on the support, positivity of the
denominator, the attaining optimal vector, Selberg's sieve,
Brun-Titchmarsh, or any prime-count estimate.

TS123 probes and partially discharges the positivity prerequisites of TS122:

```lean
TS123.Goldbach.selbergOptimizationSupport_eq_positive_support
TS123.Goldbach.selbergOptimizationSupport_eq_positive_range_filter
TS123.Goldbach.four_mem_selbergOptimizationSupport_of_level_ge_four
TS123.Goldbach.not_squarefree_four
TS123.Goldbach.one_mem_selbergOptimizationSupport
TS123.Goldbach.selbergMobiusRatCoefficient_one
TS123.Goldbach.SelbergJordanTwoPositiveOnSupport
TS123.Goldbach.SelbergOptimizationDenominatorPositive
TS123.Goldbach.selbergOptimizationDenominator_term_nonneg
TS123.Goldbach.selbergOptimizationDenominator_term_one_pos
TS123.Goldbach.selbergOptimizationDenominator_pos_of_jordanTwo_pos
TS123.Goldbach.selbergDiagonalEnergy_lower_bound_of_jordanTwo_pos
TS123.Goldbach.selbergOptimalDiagonalVectorCandidate
TS123.Goldbach.SelbergJordanTwoPositivityProbe
TS123.Goldbach.selbergJordanTwoPositivityProbe
TS123.Goldbach.SelbergJordanTwoPositivityProbeTarget
TS123.Goldbach.selbergJordanTwoPositivityProbeTarget
TS123.Goldbach.selbergDiagonalOptimizationTarget
```

The important support diagnostic is explicit: the current TS122 support is the
positive finite window, not the squarefree-only support. TS123 proves that if
`4 <= level`, then `4` lies in the support, and also proves `not (Squarefree 4)`.

The main positivity bridge is:

```text
0 < level
and J2(d) > 0 on the support
=> 0 < optimization denominator.
```

Combining this bridge with TS122 gives the constrained diagonal lower bound
from only the local `J2` positivity input. TS123 does not yet prove the
multiplicative positivity of `J2`, the equality case for the optimal vector,
Selberg's sieve, Brun-Titchmarsh, or any prime-count estimate.

TS124 starts discharging the `J2` positivity input with concrete local
arithmetic:

```lean
TS124.Goldbach.selbergJordanTwoCoefficient_one
TS124.Goldbach.selbergJordanTwoCoefficient_prime
TS124.Goldbach.selbergJordanTwoCoefficient_pos_of_prime
TS124.Goldbach.SelbergJordanTwoPositiveOnPositiveNat
TS124.Goldbach.selbergJordanTwoPositiveOnSupport_of_positiveNat
TS124.Goldbach.selbergOptimizationDenominator_pos_of_positiveNat
TS124.Goldbach.selbergDiagonalEnergy_lower_bound_of_positiveNat
TS124.Goldbach.SelbergJordanTwoPositivityAPIProbe
TS124.Goldbach.selbergJordanTwoPositivityAPIProbe
TS124.Goldbach.SelbergJordanTwoPositivityAPIProbeTarget
TS124.Goldbach.selbergJordanTwoPositivityAPIProbeTarget
TS124.Goldbach.selbergJordanTwoPositivityProbeTarget
```

The concrete prime calculation expands the Dirichlet convolution defining
Jordan-two, rewrites the antidiagonal convolution through
`Nat.sum_divisorsAntidiagonal`, applies `Nat.sum_divisors_prime_pow`, and
normalizes the two terms. Thus TS124 proves:

```text
J2(1) = 1
J2(p) = p^2 - 1 for prime p
J2(p) > 0 for prime p.
```

It also names the future global positivity theorem:

```text
forall d > 0, J2(d) > 0
```

and proves that this single input supplies TS123 supportwise positivity,
positivity of the TS122 optimization denominator, and the constrained TS122
diagonal lower bound. TS124 does not yet prove the full multiplicative
positivity theorem, the optimal vector normalization, Selberg's sieve,
Brun-Titchmarsh, or any prime-count estimate.

TS125 extends the concrete `J2` positivity calculation from primes to positive
prime powers:

```lean
TS125.Goldbach.selbergJordanTwoCoefficient_prime_pow_succ
TS125.Goldbach.selbergJordanTwoCoefficient_pos_of_prime_pow_succ
TS125.Goldbach.selbergJordanTwoCoefficient_four
TS125.Goldbach.selbergJordanTwoCoefficient_four_pos
TS125.Goldbach.SelbergJordanTwoPositiveOnPrimePowers
TS125.Goldbach.selbergJordanTwoPositiveOnPrimePowers
TS125.Goldbach.SelbergJordanTwoPrimePowerPositivityProbe
TS125.Goldbach.selbergJordanTwoPrimePowerPositivityProbe
TS125.Goldbach.SelbergJordanTwoPrimePowerPositivityProbeTarget
TS125.Goldbach.selbergJordanTwoPrimePowerPositivityProbeTarget
TS125.Goldbach.selbergJordanTwoPositivityAPIProbeTarget
```

The main normalized formula is:

```text
J2(p^(k+1)) = p^(2*(k+1)) - p^(2*k)
```

for every prime `p` and every natural `k`. The proof uses the TS119 divisor-sum
collapse twice, rewrites prime-power divisor sums with
`Nat.sum_divisors_prime_pow`, isolates the final term with
`Finset.sum_range_succ`, and normalizes the exponents explicitly. Positivity
then follows by factoring the right-hand side as

```text
p^(2*k) * (p^2 - 1).
```

TS125 also proves the concrete non-squarefree diagnostic `J2(4) = 12` and
`J2(4) > 0`, matching the TS123 observation that `4` lies in the positive
bounded support. TS125 does not yet prove multiplicative positivity over all
positive integers, the optimal vector normalization, Selberg's sieve,
Brun-Titchmarsh, or any prime-count estimate.

TS126 opens the multiplicative route from TS125 prime-power positivity to the
global positive-integer `J2` input:

```lean
TS126.Goldbach.selbergJordanTwoFunction_isMultiplicative
TS126.Goldbach.selbergJordanTwoCoefficient_mul_of_coprime
TS126.Goldbach.selbergJordanTwoCoefficient_factorization
TS126.Goldbach.selbergJordanTwoCoefficient_pos_of_prime_pow
TS126.Goldbach.SelbergJordanTwoPositiveOnPrimePowersFactorizationShape
TS126.Goldbach.selbergJordanTwoPositiveOnPrimePowersFactorizationShape
TS126.Goldbach.SelbergJordanTwoMultiplicativePositiveProductRoute
TS126.Goldbach.SelbergJordanTwoMultiplicativityAPIProbe
TS126.Goldbach.selbergJordanTwoMultiplicativityAPIProbe
TS126.Goldbach.SelbergJordanTwoMultiplicativityAPIProbeTarget
TS126.Goldbach.selbergJordanTwoMultiplicativityAPIProbeTarget
TS126.Goldbach.selbergJordanTwoPrimePowerPositivityProbeTarget
```

The sprint proves that `J2 = moebius * pow 2` is multiplicative over `Rat`, by
combining Mathlib's multiplicativity of `moebius` and `pow 2` through the
arithmetic-function API. It also exposes Mathlib's factorization formula:

```text
J2(n) = product over n.factorization of J2(p^k)
```

for `n` nonzero, and rewrites TS125 prime-power positivity into the form

```text
p prime and 0 < k imply 0 < J2(p^k).
```

TS126 deliberately leaves the final finite-product positivity step for all
positive integers as the next local obligation. It does not yet prove global
`J2` positivity, the optimal vector normalization, Selberg's sieve,
Brun-Titchmarsh, or any prime-count estimate.

TS127 closes the global `J2` positivity input:

```lean
TS127.Goldbach.selbergJordanTwoCoefficient_pos_of_pos
TS127.Goldbach.selbergJordanTwoPositiveOnPositiveNat
TS127.Goldbach.selbergJordanTwoPositiveOnSupport
TS127.Goldbach.selbergOptimizationDenominator_pos
TS127.Goldbach.selbergDiagonalEnergy_lower_bound
TS127.Goldbach.SelbergJordanTwoFullPositivityDischarge
TS127.Goldbach.selbergJordanTwoFullPositivityDischarge
TS127.Goldbach.SelbergJordanTwoFullPositivityDischargeTarget
TS127.Goldbach.selbergJordanTwoFullPositivityDischargeTarget
TS127.Goldbach.selbergJordanTwoMultiplicativityAPIProbeTarget
```

For every positive natural number `n`, TS127 proves:

```text
0 < J2(n).
```

The proof rewrites `J2(n)` using the TS126 factorization formula, unfolds
`Finsupp.prod` to a finite product over the factorization support, extracts
`p.Prime` from `Nat.prime_of_mem_primeFactors`, extracts `0 < k` from
`Finsupp.mem_support_iff`, and applies the TS126 factorization-shaped
prime-power positivity theorem. `Finset.prod_pos` then closes the product.

This discharges the global input `TS124.Goldbach.SelbergJordanTwoPositiveOnPositiveNat`.
Consequently the TS123 supportwise positivity, the TS122 denominator positivity,
and the constrained TS122 diagonal energy lower bound are now available without
any further `J2` positivity hypothesis. TS127 does not yet construct the
optimal vector, prove the equality case in weighted Cauchy, prove Selberg's
sieve, discharge Brun-Titchmarsh, or address the spectral trace and Mellin-tail
terminal packages.

TS128 closes the finite optimal-vector algebra for the TS122 weighted Cauchy
problem:

```lean
TS128.Goldbach.finiteWeightedCauchyDenominator
TS128.Goldbach.finiteWeightedCauchyOptimalVector
TS128.Goldbach.finiteWeightedCauchyOptimalVector_linear_constraint
TS128.Goldbach.finiteWeightedCauchyOptimalVector_energy_eq
TS128.Goldbach.selbergOptimalDiagonalVector
TS128.Goldbach.selbergOptimalDiagonalVector_eq_candidate
TS128.Goldbach.finiteWeightedCauchyDenominator_selberg
TS128.Goldbach.selbergJordanTwoPenalty_ne_on_support
TS128.Goldbach.selbergOptimizationDenominator_ne
TS128.Goldbach.selbergOptimalDiagonalVector_linear_constraint
TS128.Goldbach.selbergOptimalDiagonalVector_energy_eq
TS128.Goldbach.selbergOptimalDiagonalVector_lower_bound_sharp
TS128.Goldbach.SelbergOptimalVectorNormalization
TS128.Goldbach.selbergOptimalVectorNormalization
TS128.Goldbach.SelbergOptimalVectorNormalizationTarget
TS128.Goldbach.selbergOptimalVectorNormalizationTarget
TS128.Goldbach.selbergJordanTwoFullPositivityDischargeTarget
```

For a finite weighted Cauchy problem with denominator

```text
D = sum_i c_i^2 / a_i,
```

TS128 proves over `Rat` that the vector

```text
y_i = c_i / (D * a_i)
```

has linear form `1` and weighted energy `1 / D`, provided the penalties and
denominator are nonzero. The Selberg specialization uses the TS122 support with
`c_d = mobius(d)` and `a_d = J2(d)`. TS127 supplies the required non-vanishing
facts from `J2(d) > 0` and `D > 0` for `0 < level`.

Consequently the TS123 candidate vector is now proved to satisfy the Mobius
linear constraint and to attain the TS122 Cauchy lower-bound energy exactly.
TS128 does not yet prove the Selberg sieve bound, Brun-Titchmarsh, any
prime-count estimate, or the spectral trace and Mellin-tail terminal packages.

TS129 connects the corrected dense-to-diagonal identity and the optimal-vector
budget to the Selberg-sieve majorant route:

```lean
TS129.Goldbach.selbergAbsorbedDiagonalVector
TS129.Goldbach.selbergAbsorbedDiagonalVector_zero
TS129.Goldbach.selbergCorrectedJordanDiagonalSide_eq_diagonalEnergy
TS129.Goldbach.selbergOriginalDenseSide_eq_absorbedDiagonalEnergy
TS129.Goldbach.selbergDenseSide_budget_lower_bound_of_mobius_constraint
TS129.Goldbach.selbergDenseSide_eq_optimal_budget_of_absorbedVector_eq_optimal
TS129.Goldbach.SelbergDiagonalBudgetMajorant
TS129.Goldbach.selbergDiagonalBudgetMajorant
TS129.Goldbach.SelbergSieveMajorantFromDiagonalBudget
TS129.Goldbach.selbergSieveWeightInfrastructure_of_diagonalBudget
TS129.Goldbach.SelbergDiagonalBudgetMajorantTarget
TS129.Goldbach.selbergDiagonalBudgetMajorantTarget
TS129.Goldbach.SelbergSieveMajorantFromDiagonalBudgetTarget
TS129.Goldbach.selbergSieveWeightInfrastructureTarget_of_diagonalBudgetTarget
TS129.Goldbach.selbergOptimalVectorNormalizationTarget
```

The sprint defines the absorbed diagonal vector

```text
Y_d = sum_m 1_{d | m} * (weight(m) / m)
```

and proves `Y_0 = 0`. This removes the zero-index mismatch between the full
TS119 diagonal support and the positive TS122 optimization support. As a result
TS129 proves:

```text
original dense gcd/lcm side
=
TS122 diagonal energy of Y.
```

Together with TS127/TS128 this gives the budget consequence: if `0 < level` and
the absorbed diagonal vector satisfies the Mobius normalization, then

```text
1 / D <= original dense side.
```

If the absorbed diagonal vector is the TS128 optimal vector, TS129 proves that
the original dense side is exactly `1 / D`. The remaining conversion from this
diagonal budget to an interval Selberg majorant, the sieve theorem, and the
budget comparison is kept as the package
`SelbergSieveMajorantFromDiagonalBudget`, which feeds the existing TS99
Selberg-weight infrastructure.

TS130 opens the inverse triangular reconstruction step below TS129:

```lean
TS130.Goldbach.selbergReconstructionSupport
TS130.Goldbach.mem_selbergReconstructionSupport_le_level
TS130.Goldbach.mem_selbergReconstructionSupport_pos
TS130.Goldbach.absorbedCoefficientFromDiagonalVector
TS130.Goldbach.reconstructedSelbergWeight
TS130.Goldbach.absorbedCoefficientFromDiagonalVector_zero
TS130.Goldbach.reconstructedSelbergWeight_zero
TS130.Goldbach.not_dvd_of_level_lt_on_reconstructionSupport
TS130.Goldbach.absorbedCoefficientFromDiagonalVector_eq_zero_of_level_lt
TS130.Goldbach.reconstructedSelbergWeight_eq_zero_of_level_lt
TS130.Goldbach.reconstructedSelbergWeight_support_bound
TS130.Goldbach.selbergLCMAbsorbedWeight_reconstructed_eq_absorbedCoefficient
TS130.Goldbach.ReconstructedSelbergWeightSupport
TS130.Goldbach.reconstructedSelbergWeightSupport
TS130.Goldbach.SelbergFiniteMobiusReconstructionIdentity
TS130.Goldbach.SelbergWeightReconstruction
TS130.Goldbach.selbergWeightReconstruction
TS130.Goldbach.optimalReconstructedSelbergWeight
TS130.Goldbach.optimalReconstructedWeight_mobius_constraint_of_reconstruction
TS130.Goldbach.optimalReconstructedWeight_denseSide_eq_optimal_budget_of_reconstruction
TS130.Goldbach.SelbergOptimalWeightReconstruction
TS130.Goldbach.selbergOptimalWeightReconstruction
TS130.Goldbach.SelbergOptimalWeightReconstructionTarget
TS130.Goldbach.selbergOptimalWeightReconstructionTarget
TS130.Goldbach.selbergDiagonalBudgetMajorantTarget
```

For a target diagonal vector `Y`, TS130 defines the finite Mobius-style
upward transform

```text
a_m = sum_{m | d} mu(d / m) * Y_d
```

over the positive TS122 reconstruction support, then defines original weights

```text
w_m = m * a_m.
```

The sprint proves `a_0 = 0`, `w_0 = 0`, `m > level -> a_m = 0`,
`m > level -> w_m = 0`, and `w_m / m = a_m` for `0 < m`. Thus the
reconstructed original weights have finite support inside `level`.

The exact triangular inversion assertion is named as
`SelbergFiniteMobiusReconstructionIdentity`: the absorbed diagonal vector of
the reconstructed weights recovers `Y` on the TS122 positive support. TS130
does not yet prove that identity, but it proves that if the identity holds for
the TS128 optimal vector, then the reconstructed weights satisfy the Mobius
constraint and their original dense side has exact value `1 / D`.

TS131 opens the finite Mobius reconstruction identity from TS130 one level
lower:

```lean
TS131.Goldbach.selbergMobiusReconstructionSupport
TS131.Goldbach.selbergMobiusChainCoefficient
TS131.Goldbach.selbergFiniteMobiusReconstructionExpandedSide
TS131.Goldbach.SelbergFiniteMobiusReconstructionExpansion
TS131.Goldbach.SelbergMobiusChainCoefficientCollapse
TS131.Goldbach.selbergSupport_delta_sum
TS131.Goldbach.selbergFiniteMobiusExpandedSide_eq_target_of_chainCollapse
TS131.Goldbach.selbergFiniteMobiusReconstructionIdentity_of_expansion_chainCollapse
TS131.Goldbach.SelbergFiniteMobiusReconstructionCollapse
TS131.Goldbach.selbergFiniteMobiusReconstructionCollapse
TS131.Goldbach.selbergOptimalFiniteMobiusReconstructionCollapse
TS131.Goldbach.optimalReconstructedWeight_denseSide_eq_optimal_budget_of_TS131_obligations
TS131.Goldbach.SelbergFiniteMobiusReconstructionCollapseTarget
TS131.Goldbach.selbergFiniteMobiusReconstructionCollapseTarget
TS131.Goldbach.selbergOptimalWeightReconstructionTarget
```

For fixed support indices `d` and `e`, TS131 defines the local chain
coefficient

```text
sum_m 1_{d | m} * 1_{m | e} * mu(e / m)
```

over the TS130 positive finite reconstruction support. It then names the exact
Mobius delta collapse obligation saying that this coefficient is `1` when
`d = e` and `0` otherwise. The concrete new algebra is the finite delta
selection lemma: once the expanded side has these delta coefficients, the
support sum selects `Y d`. Consequently, the expansion obligation plus the
coefficient-collapse obligation imply the TS130 reconstruction identity, and
for the TS128 optimal vector they imply the exact dense-side value `1 / D`.

TS131 does not yet prove the Fubini expansion into the coefficient-collected
side or the local chain-coefficient Mobius collapse itself; those remain the
precise finite inversion obligations for the next Selberg reconstruction
sprint.

TS132 advances the TS131 chain-coefficient collapse:

```lean
TS132.Goldbach.selbergMobiusRatCoefficient_one
TS132.Goldbach.selbergMobiusChainCoefficient_eq_zero_of_not_dvd
TS132.Goldbach.selbergMobiusChainCoefficient_eq_one_of_eq
TS132.Goldbach.SelbergMobiusProperDivisorChainCollapse
TS132.Goldbach.selbergMobiusChainCoefficientCollapse_of_properDivisorCollapse
TS132.Goldbach.selbergFiniteMobiusReconstructionIdentity_of_expansion_properDivisorCollapse
TS132.Goldbach.SelbergMobiusChainCoefficientCollapseLedger
TS132.Goldbach.selbergMobiusChainCoefficientCollapseLedger
TS132.Goldbach.SelbergMobiusChainCoefficientCollapseLedgerTarget
TS132.Goldbach.selbergMobiusChainCoefficientCollapseLedgerTarget
TS132.Goldbach.selbergFiniteMobiusReconstructionCollapseTarget
```

The diagonal case is fully proved:

```text
coefficient(d,d) = 1.
```

The non-divisor case is also fully proved:

```text
not (d | e) -> coefficient(d,e) = 0.
```

Therefore the full TS131 chain-coefficient collapse is reduced to the only
remaining arithmetic case:

```text
d | e, d != e -> coefficient(d,e) = 0.
```

This is the proper quotient-Mobius obligation: change variables from the
middle divisor `m` to a divisor of `e / d`, then apply the TS105 Mobius-delta
identity. TS132 also proves that this proper-divisor obligation, together with
the TS131 expansion obligation, implies the TS130 reconstruction identity.

TS133 advances the TS132 proper-divisor quotient case:

```lean
TS133.Goldbach.quotient_one_lt_of_proper_dvd
TS133.Goldbach.quotientMobiusDivisorSum_eq_zero_of_one_lt
TS133.Goldbach.SelbergMobiusProperDivisorQuotientReindexing
TS133.Goldbach.selbergMobiusProperDivisorChainCollapse_of_quotientReindexing
TS133.Goldbach.selbergMobiusChainCoefficientCollapse_of_quotientReindexing
TS133.Goldbach.selbergFiniteMobiusReconstructionIdentity_of_expansion_quotientReindexing
TS133.Goldbach.SelbergProperDivisorMobiusChainCollapse
TS133.Goldbach.selbergProperDivisorMobiusChainCollapse
TS133.Goldbach.SelbergProperDivisorMobiusChainCollapseTarget
TS133.Goldbach.selbergProperDivisorMobiusChainCollapseTarget
TS133.Goldbach.selbergMobiusChainCoefficientCollapseLedgerTarget
```

For positive `d` and `e`, TS133 proves:

```text
d | e, d != e -> 1 < e / d.
```

It then proves the quotient Mobius annihilation:

```text
1 < n -> sum_{r | n} mu(n / r) = 0.
```

This uses `Nat.sum_div_divisors` to pass from `mu(n / r)` to the ordinary
divisor sum, then applies the TS105 Mobius-delta identity. Thus the proper
chain coefficient collapse follows from the single remaining finite
reindexing statement:

```text
chainCoefficient(d,e) = sum_{r | e/d} mu((e/d)/r).
```

TS133 also proves that this quotient reindexing supplies the full TS131
chain-coefficient collapse, and together with the TS131 expansion obligation
supplies the TS130 finite reconstruction identity.

TS134 discharges the TS133 quotient reindexing:

```lean
TS134.Goldbach.divisor_mem_reconstructionSupport_of_mem
TS134.Goldbach.selbergMobiusChainCoefficient_eq_filteredDivisorSum
TS134.Goldbach.quotientDivisorSum_eq_filteredDivisorSum
TS134.Goldbach.selbergMobiusProperDivisorQuotientReindexing
TS134.Goldbach.selbergMobiusProperDivisorChainCollapse
TS134.Goldbach.selbergMobiusChainCoefficientCollapse
TS134.Goldbach.SelbergProperDivisorQuotientReindexingDischarge
TS134.Goldbach.selbergProperDivisorQuotientReindexingDischarge
TS134.Goldbach.SelbergProperDivisorQuotientReindexingDischargeTarget
TS134.Goldbach.selbergProperDivisorQuotientReindexingDischargeTarget
TS134.Goldbach.selbergProperDivisorMobiusChainCollapseTarget
```

It first proves that every divisor of a supported positive `e` lies in the
same positive reconstruction support. This rewrites the chain coefficient as:

```text
sum_{m | e, d | m} mu(e/m).
```

Then `Finset.sum_bij` with the map `r -> d * r` identifies that filtered
divisor sum with:

```text
sum_{r | e/d} mu((e/d)/r).
```

Consequently the proper-divisor collapse from TS132 and the full TS131
chain-coefficient collapse are now proved. The remaining local obstruction for
the finite reconstruction identity is the TS131 expansion/Fubini obligation.

TS135 discharges the TS131 finite Fubini expansion:

```lean
TS135.Goldbach.zero_not_dvd_reconstructionSupport
TS135.Goldbach.absorbedCoefficientFromDiagonalVector_expansion
TS135.Goldbach.selbergLCMAbsorbedWeight_reconstructed_expansion
TS135.Goldbach.selbergAbsorbedDiagonalVector_reconstructed_eq_mFirst
TS135.Goldbach.selbergFiniteMobiusReconstruction_mFirst_eq_expandedSide
TS135.Goldbach.selbergFiniteMobiusReconstructionExpansion
TS135.Goldbach.selbergFiniteMobiusReconstructionIdentity
TS135.Goldbach.optimalReconstructedWeight_denseSide_eq_optimal_budget
TS135.Goldbach.SelbergFiniteMobiusReconstructionExpansionDischarge
TS135.Goldbach.selbergFiniteMobiusReconstructionExpansionDischarge
TS135.Goldbach.SelbergFiniteMobiusReconstructionExpansionDischargeTarget
TS135.Goldbach.selbergFiniteMobiusReconstructionExpansionDischargeTarget
TS135.Goldbach.selbergProperDivisorQuotientReindexingDischargeTarget
```

It unfolds the absorbed diagonal vector of the reconstructed weights as:

```text
sum_m 1_{d | m} sum_e 1_{m | e} mu(e/m) * Y(e).
```

Then finite Fubini and `Finset.mul_sum` collect the coefficient of each
`Y(e)`, giving exactly the TS131 expanded side:

```text
sum_e Y(e) * chainCoefficient(d,e).
```

Combined with the TS134 chain-coefficient collapse, this proves the full TS130
finite Mobius reconstruction identity for every diagonal vector `Y`.
Specializing to the TS128 optimal vector, TS135 proves that the reconstructed
original Selberg weights attain the exact dense-side budget:

```text
TS110 dense side = 1 / TS122 optimization denominator.
```

The remaining Selberg-side work is no longer finite Mobius reconstruction. It
is the interval Selberg majorant and its application toward Brun-Titchmarsh.

TS136 connects the TS135 optimal weights to the interval-majorant interface:

```lean
TS136.Goldbach.selbergOptimalIntervalWeight
TS136.Goldbach.selbergOptimalIntervalWeight_support_bound
TS136.Goldbach.selbergOptimalIntervalWeight_one
TS136.Goldbach.selbergOptimalSieveWeightLedger
TS136.Goldbach.selbergOptimalIntervalWeight_dense_budget_exact
TS136.Goldbach.SelbergIntervalMajorantFromOptimalBudget
TS136.Goldbach.selbergIntervalMajorantFromOptimalBudget
TS136.Goldbach.SelbergIntervalMajorantFromOptimalBudgetBridgeTarget
TS136.Goldbach.selbergIntervalMajorantFromOptimalBudgetBridgeTarget
TS136.Goldbach.SelbergIntervalMajorantFromOptimalBudgetTarget
TS136.Goldbach.selbergSieveWeightInfrastructureTarget_of_intervalMajorantTarget
TS136.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_intervalMajorantTarget
TS136.Goldbach.selbergFiniteMobiusReconstructionExpansionDischargeTarget
```

For positive `level`, TS136 proves that the TS135 optimal reconstructed
weights satisfy the raw TS99 Selberg-weight requirements:

```text
support(weight) <= level
weight(1) = 1
```

The identity `weight(1) = 1` follows because the reconstruction formula at
`m = 1` is exactly the TS128 Mobius linear constraint. TS136 then proves that,
once a TS30 interval majorant, interval sieve bound, and majorant-budget
comparison are supplied, the TS135 optimal weights produce:

```text
TS129.SelbergSieveMajorantFromDiagonalBudget
TS99.SelbergSieveWeightInfrastructure
TS97.BrunTitchmarshFinalInputLedger
```

Thus the finite optimal Selberg algebra is now wired to the high-level
Brun-Titchmarsh input route. The concrete interval majorant and its comparison
with the TS22 ceiling remain the next explicit obligations.

TS137 names the concrete interval-majorant interface:

```lean
TS137.Goldbach.ConcreteSelbergIntervalMajorantData
TS137.Goldbach.concreteSelbergIntervalMajorant
TS137.Goldbach.ConcreteSelbergIntervalMajorantProofs
TS137.Goldbach.concreteSelbergSieveIntervalBound
TS137.Goldbach.concreteSelbergMajorantBudgetComparison
TS137.Goldbach.ConcreteSelbergIntervalMajorantLedger
TS137.Goldbach.concreteSelbergIntervalMajorantLedger
TS137.Goldbach.ConcreteSelbergIntervalMajorantBridgeTarget
TS137.Goldbach.concreteSelbergIntervalMajorantBridgeTarget
TS137.Goldbach.ConcreteSelbergIntervalMajorantLedgerTarget
TS137.Goldbach.selbergSieveWeightInfrastructureTarget_of_concreteIntervalMajorantTarget
TS137.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_concreteIntervalMajorantTarget
TS137.Goldbach.selbergIntervalMajorantFromOptimalBudgetBridgeTarget
```

The data object fixes:

```text
majorantValue : Nat -> Nat -> Nat -> Nat
mainTerm      : Nat -> Nat -> Nat -> Rat
errorTerm     : Nat -> Nat -> Nat -> Rat
majorantRat   : Nat -> Nat -> Nat -> Rat
majorantRat = mainTerm + errorTerm
0 <= errorTerm
```

The proof package then isolates exactly the two TS30 interval obligations:

```text
primeIntervalCard <= majorantValue
majorantValue <= brunTitchmarshCeilBudget
```

Given those two inputs, TS137 constructs the TS30 majorant, sieve theorem, and
budget-comparison packages, then feeds them through TS136 to produce the TS99
Selberg weight infrastructure and the TS97 final Brun-Titchmarsh input ledger.

TS138 instantiates the data side of the TS137 interface with the concrete
finite Selberg square majorant:

```lean
TS138.Goldbach.selbergConcreteInterval
TS138.Goldbach.selbergConcreteDivisorWeight
TS138.Goldbach.selbergConcreteSquareMajorantRat
TS138.Goldbach.selbergConcreteMajorantValue
TS138.Goldbach.selbergConcreteMainTerm
TS138.Goldbach.selbergConcreteErrorTerm
TS138.Goldbach.selbergConcreteMajorantRat
TS138.Goldbach.concreteSelbergIntervalMajorantData
TS138.Goldbach.ConcreteSelbergSquareMajorantProofs
TS138.Goldbach.concreteSelbergIntervalMajorantProofs
TS138.Goldbach.ConcreteSelbergSquareMajorantLedger
TS138.Goldbach.concreteSelbergSquareMajorantLedger
TS138.Goldbach.ConcreteSelbergSquareMajorantBridgeTarget
TS138.Goldbach.concreteSelbergSquareMajorantBridgeTarget
TS138.Goldbach.selbergSieveWeightInfrastructure_of_squareMajorant
TS138.Goldbach.brunTitchmarshFinalInputLedger_of_squareMajorant
TS138.Goldbach.selbergSieveWeightInfrastructureTarget_of_squareMajorantTarget
TS138.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_squareMajorantTarget
TS138.Goldbach.primeIntervalCard_le_concreteInterval_card
TS138.Goldbach.concreteSelbergIntervalMajorantBridgeTarget
```

The rational majorant is the explicit finite square sum

```text
sum_{n <= k <= n + h}
  (sum_{d in support, d | k} lambda_d)^2
```

where `lambda_d` is the TS136 optimal reconstructed Selberg weight.  The
natural TS30 majorant is the ceiling of this rational square sum.  TS138 proves
the TS137 rational data formula with `mainTerm = square sum`, `errorTerm = 0`,
and `majorantRat = square sum`, then packages the two remaining analytic
proofs specialized to this concrete majorant:

```text
primeIntervalCard <= selbergConcreteMajorantValue
selbergConcreteMajorantValue <= brunTitchmarshCeilBudget
```

Given those two future inputs, TS138 constructs the TS137 concrete ledger and
therefore feeds the TS99 Selberg infrastructure and TS97 final
Brun-Titchmarsh input ledger.  TS138 also proves the sanity bound
`primeIntervalCard <= interval cardinality` for the same TS22 window; this is
not the Selberg sieve theorem.

TS139 proves the finite counting bridge for the concrete TS138 square
majorant:

```lean
TS139.Goldbach.finset_card_filter_cast_le_sum_of_pointwise
TS139.Goldbach.SelbergConcretePrimePointwiseMajorant
TS139.Goldbach.primeIntervalCard_cast_le_squareMajorantRat_of_pointwise
TS139.Goldbach.primeIntervalCard_le_concreteMajorantValue_of_pointwise
TS139.Goldbach.selbergConcretePrimePointwiseMajorant_of_weight_eq_one
TS139.Goldbach.ConcreteSelbergIntervalSieveTheorem
TS139.Goldbach.concreteSelbergSieveIntervalBound
TS139.Goldbach.ConcreteSelbergSquareBudgetComparison
TS139.Goldbach.concreteSelbergSquareMajorantProofs
TS139.Goldbach.ConcreteSelbergIntervalSieveTheoremLedger
TS139.Goldbach.concreteSelbergIntervalSieveTheoremLedger
TS139.Goldbach.ConcreteSelbergIntervalSieveTheoremBridgeTarget
TS139.Goldbach.concreteSelbergIntervalSieveTheoremBridgeTarget
TS139.Goldbach.selbergSieveWeightInfrastructure_of_intervalSieveTheorem
TS139.Goldbach.brunTitchmarshFinalInputLedger_of_intervalSieveTheorem
TS139.Goldbach.selbergSieveWeightInfrastructureTarget_of_intervalSieveTheoremTarget
TS139.Goldbach.brunTitchmarshFinalInputLedgerTarget_of_intervalSieveTheoremTarget
```

The core theorem says that if every prime in the TS22 interval satisfies

```text
1 <= (sum_{d in support, d | k} lambda_d)^2
```

then

```text
primeIntervalCard <= selbergConcreteMajorantValue
```

where `selbergConcreteMajorantValue` is the ceiling of the TS138 rational
square sum.  This is a genuine finite summation result: it turns pointwise
prime admissibility into the TS30 interval sieve-bound field.  TS139 does not
claim that the pointwise prime condition is automatic; small primes or support
admissibility still need their own analytic/arithmetic input.

TS140 proves the large-prime admissibility route for the TS139 pointwise input:

```lean
TS140.Goldbach.selbergOptimizationSupport_mem_le_level
TS140.Goldbach.support_divisor_eq_one_of_prime_gt_level
TS140.Goldbach.selbergConcreteDivisorWeight_eq_one_of_prime_gt_level
TS140.Goldbach.LargePrimeSupportAdmissibility
TS140.Goldbach.selbergConcretePrimePointwiseMajorant_of_largePrimeSupport
TS140.Goldbach.largePrimeSupportAdmissibility_of_level_lt_leftEndpoint
TS140.Goldbach.selbergConcretePrimePointwiseMajorant_of_level_lt_leftEndpoint
TS140.Goldbach.primeIntervalCard_le_concreteMajorantValue_of_level_lt_leftEndpoint
TS140.Goldbach.LargePrimeAdmissibleIntervalSieveTheorem
TS140.Goldbach.concreteSelbergIntervalSieveTheorem
TS140.Goldbach.LargePrimeAdmissibilityLedger
TS140.Goldbach.largePrimeAdmissibilityBridgeTarget
```

The core finite fact is:

```text
d in support -> d <= level
k prime and level < k and d | k -> d = 1
```

Therefore, for primes above the support level, the TS138 divisor bracket is
exactly the normalized TS136 weight `lambda_1 = 1`; hence its square is at
least `1`.  A sufficient interval-level hypothesis is `level < n`, since the
TS138 interval is `[n, n + h]`.

TS141 expands the concrete TS138 square majorant into pair-first lcm form:

```lean
TS141.Goldbach.selbergConcreteDivisorTerm
TS141.Goldbach.selbergConcretePairTerm
TS141.Goldbach.selbergConcreteLcmMultiplicity
TS141.Goldbach.selbergConcreteLcmExpandedMajorantRat
TS141.Goldbach.selbergConcreteDivisorWeight_sq_expand_double
TS141.Goldbach.selbergConcreteSquareMajorantRat_expand_pairFirst
TS141.Goldbach.divisorPair_filter_eq_lcm_filter
TS141.Goldbach.selbergConcretePairTerm_eq_lcmIndicator
TS141.Goldbach.selbergConcretePairSum_eq_lcmMultiplicity
TS141.Goldbach.selbergConcreteSquareMajorantRat_expand_lcm
TS141.Goldbach.ConcreteSelbergSquareMajorantExpansionLedger
TS141.Goldbach.concreteSelbergSquareMajorantExpansionBridgeTarget
```

The exact finite identity is:

```text
sum_{k in interval} (sum_{d in support, d | k} lambda_d)^2
=
sum_{d1,d2 in support}
  lambda_d1 * lambda_d2 *
    #{k in interval | lcm(d1,d2) | k}
```

This is the Fubini/lcm expansion needed before estimating the interval
multiple count.  TS141 does not yet prove that estimate or the
Brun-Titchmarsh budget comparison.

TS142 performs the next exact finite decomposition:

```lean
TS142.Goldbach.lcmMultiplicity
TS142.Goldbach.lcmMultiplicityMainRat
TS142.Goldbach.lcmMultiplicityErrorRat
TS142.Goldbach.lcmMultiplicity_eq_main_add_error
TS142.Goldbach.selbergLCMDenseSideRat
TS142.Goldbach.selbergFractionalMainTermRat
TS142.Goldbach.selbergFractionalErrorTermRat
TS142.Goldbach.selbergConcreteSquareMajorantRat_eq_fractionalExpansion
TS142.Goldbach.selbergFractionalMainTerm_eq_intervalLength_mul_denseSide
TS142.Goldbach.LCMMultiplicityFractionalDecomposition
TS142.Goldbach.lcmMultiplicityFractionalDecompositionTarget
```

The concrete TS141 square majorant is now exactly the sum of a rational main
term and a finite discrepancy term.  TS142 deliberately keeps two genuine
estimates explicit:

```text
abs(error(d1,d2)) <= 1
selbergLCMDenseSideRat(level) = 1 / optimizationDenominator(level)
```

The second statement is not silently identified with the TS136 budget:
TS136 uses the `gcd/lcm` kernel, while the TS142 main term uses `1/lcm`.
TS142 does not yet prove either estimate, aggregate the error, estimate the
denominator asymptotically, or compare with the Brun-Titchmarsh budget.

TS143 closes the local interval discrepancy left by TS142:

```lean
TS143.Goldbach.closedIntervalMultipleCount_eq_ceil_sub_ceil
TS143.Goldbach.closedIntervalMultipleCount_error_abs_le_one
TS143.Goldbach.lcmMultiplicityErrorRat_abs_le_one
TS143.Goldbach.lcmMultiplicityErrorBound
TS143.Goldbach.LCMMultiplicityErrorBoundDischarge
TS143.Goldbach.lcmMultiplicityErrorBoundDischargeTarget
```

For every positive modulus `m`, Mathlib's exact half-open interval count gives

```text
#{k in [n,n+h] | m divides k}
= ceil((n+h+1)/m) - ceil(n/m).
```

Since each ceiling discrepancy lies in `[0,1)`, the difference from
`(h+1)/m` has absolute value at most one.  Specialized to
`m = lcm(d1,d2)`, this proves the full TS142
`LCMMultiplicityErrorBound`.  The separate `1/lcm` dense-side identification,
weighted error aggregation, denominator estimate, and Brun-Titchmarsh
comparison remain open.

TS144 audits the remaining dense-side premise and replaces it by the correct
upper-bound route:

```lean
TS144.Goldbach.one_div_lcm_ne_gcd_div_lcm_at_two
TS144.Goldbach.one_div_lcm_eq_gcd_div_mul
TS144.Goldbach.selbergLCMDenseSide_eq_gcdAbsorbedDenseSide
TS144.Goldbach.SelbergLCMDenseSideBudgetUpperBound
TS144.Goldbach.selbergEulerTotientDiagonalSide_le_jordanEnergy
TS144.Goldbach.selbergOptimalAbsorbedJordanEnergy_eq_budget
TS144.Goldbach.selbergLCMDenseSideBudgetUpperBound_of_totient_route
TS144.Goldbach.selbergFractionalMainTerm_le_optimalBudget
TS144.Goldbach.LCMDenseSideBudgetRefactor
TS144.Goldbach.lcmDenseSideBudgetRefactorTarget
```

The kernels `1/lcm` and `gcd/lcm` differ already at `(2,2)`, so the TS142
exact-budget premise cannot be imported from TS136.  On positive support,
TS144 instead proves

```text
1 / lcm(d1,d2) = gcd(d1,d2) / (d1*d2)
```

and rewrites the lcm dense side as an absorbed gcd-kernel form.  The corrected
budget is the sufficient inequality

```text
selbergLCMDenseSideRat(level) <= 1 / optimizationDenominator(level).
```

TS144 derives it conditionally from two sharply named arithmetic inputs: the
Euler-totient diagonalization of the gcd kernel and the coefficientwise
comparison `totient <= J2` on the finite positive support.  The local TS143
error bound is included unconditionally.  Weighted error aggregation,
denominator asymptotics, and the Brun-Titchmarsh comparison remain open.

TS145 discharges both arithmetic inputs left by TS144:

```lean
TS145.Goldbach.totient_prime_pow_le_jordanTwo
TS145.Goldbach.totient_le_jordanTwo
TS145.Goldbach.eulerTotientLeJordanTwoOnSupport
TS145.Goldbach.absorbedDiagonalVector_eq_eulerTransformedWeight
TS145.Goldbach.eulerDiagonalSide_eq_tripleSum
TS145.Goldbach.eulerDiagonalTripleSum_eq_pairFirst
TS145.Goldbach.eulerPairCoefficient_eq_gcd
TS145.Goldbach.gcdEulerTotientDiagonalization
TS145.Goldbach.selbergLCMDenseSideBudgetUpperBound
TS145.Goldbach.selbergFractionalMainTerm_le_optimalBudget
TS145.Goldbach.EulerTotientJordanDominationDischarge
TS145.Goldbach.eulerTotientJordanDominationDischargeTarget
```

The gcd diagonalization expands the Euler-totient square, performs finite
Fubini reindexing, and collapses the local divisor coefficient with
`Nat.sum_totient`.  The comparison `totient <= J2` is proved first on positive
prime powers and then over `Nat.factorization`.  Consequently, for every
positive level,

```text
selbergLCMDenseSideRat(level) <= 1 / optimizationDenominator(level)
```

and the TS142 fractional main term is bounded by interval length times
`1 / D`.  Weighted error aggregation, denominator asymptotics, and the final
Brun-Titchmarsh comparison remain open.

TS146 closes the finite weighted aggregation step:

```lean
TS146.Goldbach.selbergConcreteLambdaL1Rat
TS146.Goldbach.selbergWeightedLCMErrorPairBudget_eq_l1_sq
TS146.Goldbach.weightedLCMLocalError_abs_le
TS146.Goldbach.selbergFractionalErrorTerm_abs_le_pairBudget
TS146.Goldbach.selbergFractionalErrorTerm_abs_le_l1_sq
TS146.Goldbach.selbergConcreteSquareMajorantRat_le_mainBudget_add_l1_sq
TS146.Goldbach.WeightedLCMErrorAggregation
TS146.Goldbach.weightedLCMErrorAggregationTarget
```

The TS143 pointwise bound is summed without any cancellation assumption:

```text
|fractionalErrorTerm| <= sum_d1 sum_d2 |lambda(d1)| |lambda(d2)|
                      = (sum_d |lambda(d)|)^2.
```

Combining this with TS145 yields, for every positive level,

```text
squareMajorant <= intervalLength / D + (sum_d |lambda(d)|)^2.
```

Estimating the finite `L1` norm, estimating the denominator effectively, and
the final Brun-Titchmarsh comparison remain open.

TS147 unfolds the reconstructed optimal weights and removes the Mobius factor
from the absolute-value estimate:

```lean
TS147.Goldbach.selbergConcreteLambda_eq_explicit
TS147.Goldbach.abs_selbergMobiusRatCoefficient_le_one
TS147.Goldbach.abs_selbergConcreteLambda_le_diagonalEnvelope
TS147.Goldbach.selbergConcreteLambdaL1_le_explicitEnvelope
TS147.Goldbach.selbergOptimalWeightL1Envelope_eq_divisorEnvelope
TS147.Goldbach.selbergConcreteLambdaL1_le_divisorEnvelope
TS147.Goldbach.selbergConcreteSquareMajorantRat_le_mainBudget_add_divisorEnvelope_sq
TS147.Goldbach.SelbergOptimalWeightExplicitFormula
TS147.Goldbach.selbergOptimalWeightExplicitFormulaTarget
```

The pointwise formula and bound are

```text
lambda(m) = m * sum_{d in support, m | d} mu(d/m) * Y(d),
|lambda(m)| <= m * sum_{d in support, m | d} |Y(d)|.
```

Finite Fubini reindexing then gives the explicit divisor-first envelope

```text
sum_m |lambda(m)|
  <= sum_d |Y(d)| * sum_{m in support, m | d} m.
```

TS147 does not yet estimate that divisor envelope. Such an effective estimate,
the denominator estimate, and the final Brun-Titchmarsh comparison remain
open.

TS148 supplies the first unconditional effective estimate of that envelope:

```lean
TS148.Goldbach.selbergOptimizationSupport_eq_Icc
TS148.Goldbach.card_selbergOptimizationSupport
TS148.Goldbach.one_le_selbergJordanTwoPenalty
TS148.Goldbach.selbergSupportedDivisorMass_le_level_sq
TS148.Goldbach.abs_selbergOptimalDiagonalVector_le_invDenominator
TS148.Goldbach.selbergOptimalWeightDivisorEnvelope_le_level_cube_div_denominator
TS148.Goldbach.selbergConcreteLambdaL1_le_level_cube_div_denominator
TS148.Goldbach.selbergConcreteSquareMajorantRat_le_explicitPolynomialBudget
TS148.Goldbach.SelbergDivisorEnvelopePolynomialBound
TS148.Goldbach.selbergDivisorEnvelopePolynomialBoundTarget
```

The support is exactly `Icc 1 level`, hence has cardinality `level`. The
coarse finite estimates are

```text
supportedDivisorMass(level,d) <= level^2,
|Y(d)| <= 1 / D(level),
divisorEnvelope(level) <= level^3 / D(level).
```

Consequently, for positive level,

```text
squareMajorant <= intervalLength / D + (level^3 / D)^2.
```

TS149 refines the divisor mass arithmetically:

```lean
TS149.Goldbach.prime_geometric_sum_le_pow
TS149.Goldbach.sigmaOne_prime_pow_le_jordanTwo
TS149.Goldbach.sigmaOne_le_jordanTwo
TS149.Goldbach.optimizationSupport_filter_dvd_eq_divisors
TS149.Goldbach.selbergSupportedDivisorMass_eq_sigmaOne
TS149.Goldbach.selbergSupportedDivisorMass_le_jordanTwo
TS149.Goldbach.abs_selbergOptimalDiagonalVector_le_inv_den_mul_jordanTwo
TS149.Goldbach.divisorEnvelope_term_le_invDenominator
TS149.Goldbach.selbergOptimalWeightDivisorEnvelope_le_level_div_denominator
TS149.Goldbach.selbergConcreteLambdaL1_le_level_div_denominator
TS149.Goldbach.selbergConcreteSquareMajorantRat_le_refinedBudget
TS149.Goldbach.SelbergDivisorEnvelopeJordanRefinement
TS149.Goldbach.selbergDivisorEnvelopeJordanRefinementTarget
```

The supported divisor mass is exactly `sigma_1(d)`, and multiplicative
prime-power comparison gives `sigma_1(d) <= J2(d)` for positive `d`. This
cancels the Jordan penalty in the TS128 coordinate bound, so each support
index contributes at most `1 / D`. Therefore

```text
divisorEnvelope(level) <= level / D(level),
squareMajorant <= intervalLength / D + (level / D)^2.
```

TS150 packages the refined expression for direct use by the interval-sieve
interfaces:

```lean
TS150.Goldbach.refinedSelbergBudgetRat
TS150.Goldbach.refinedSelbergBudgetCeil
TS150.Goldbach.selbergConcreteSquareMajorantRat_le_refinedSelbergBudgetRat
TS150.Goldbach.selbergConcreteMajorantValue_le_refinedSelbergBudgetCeil
TS150.Goldbach.RefinedSelbergBudgetLeBrunTitchmarsh
TS150.Goldbach.selbergConcreteMajorantValue_le_brunTitchmarshCeilBudget
TS150.Goldbach.RefinedSelbergBudgetScaleComparison
TS150.Goldbach.concreteSelbergSquareBudgetComparison
TS150.Goldbach.concreteSelbergIntervalSieveTheoremLedger
TS150.Goldbach.RefinedSelbergBudgetScaleLedger
TS150.Goldbach.refinedSelbergBudgetScaleBridgeTarget
```

The TS138 natural majorant is the ceiling of the rational square sum, so TS149
and monotonicity of `Nat.ceil` give

```text
selbergConcreteMajorantValue <= ceil(refinedSelbergBudgetRat).
```

The only remaining budget input is therefore

```text
ceil(refinedSelbergBudgetRat level x Q)
  <= brunTitchmarshCeilBudget x Q.
```

Together with the TS140 large-prime admissibility package, this scale contract
constructs the complete TS139 ledger and exposes the TS99 and TS97 outputs.
Choosing `level`, proving the ceiling comparison, and satisfying `level < n`
remain separate explicit obligations.

## Remaining Analytic Infrastructure

The final TS20 ledger names the remaining analytic obligations:

| Obligation | Role |
| --- | --- |
| `MellinFourierNormBridge` | logarithmic Mellin/Fourier norm bridge |
| `MellinFourierMeasureTransport` | a.e. transport between weighted, restricted, exp, and log measures |
| `MellinFourierMeasurabilityTransport` | strong measurability for the representative Mellin/Fourier operators |
| `MellinFourierAEEqTransport` | descent of the representative operators to `AEEqFun` |
| `MellinFourierLpIsometryInfrastructure` | `Memℒp`, norm, and linearity inputs for the future `Lp` isometry |
| `MellinFourierLpNormInputs` | `Memℒp` and `snorm` preservation inputs for the future `Lp` isometry |
| `MellinFourierLpLinearityInputs` | a.e. additivity and scalar-compatibility inputs for the future `Lp` isometry |
| `MellinFourierLpIsometry` | final `LinearIsometryEquiv` specification tied to `TsigmaFun`/`TsigmaInvFun` |
| `FourierTailInfrastructure` | Plancherel, derivative-control, and high-frequency tail estimate |
| `FourierAPINormalizationLedger` | concrete Fourier API and normalization choices for a future TS40 instance |
| `TriangleSplineTailInfrastructure` | triangle-spline derivative norm, Sobolev agreement, and Mellin-tail route |
| `TriangleSplineDerivativeSnormInfrastructure` | local triangle-spline derivative `snorm <= 2` estimate |
| `TriangleSplineSupportMeasureInputs` | Lebesgue measure bound for the triangle-spline support interval |
| `TriangleSplineSobolevAgreementInfrastructure` | agreement between the TS41 Sobolev derivative slot and `triangleSplineDeriv` |
| `TriangleSplineSobolevAgreementLedger` | decomposed branch, boundary, distributional, and Sobolev-slot obligations for the triangle spline |
| `TriangleSplineSobolevSlotAssembly` | packages TS60 and TS79, leaving the exact TS41 `sobolevDerivative` slot agreement explicit |
| `TriangleSplineSobolevSlotAPIBinding` | final API-level proof that the selected TS41 `sobolevDerivative` recognizes `triangleSplineDeriv` |
| `SobolevSlotRecognitionContract` | concrete Sobolev/weak-derivative API proof feeding TS81 and closing the triangle-spline Sobolev slot |
| `MellinTailFinalAPIContracts` | compatible final package combining Sobolev recognition, Plancherel/L2, and Fourier-tail comparison for `Cm <= 1` |
| `OTSAFinalMajorantAPIContracts` | TS92 spectral trace and TS83 Mellin-tail contracts together with the TS91 scale-transfer package feeding TS33 v3 |
| `PaddedScaleTransferFinalAPIContracts` | Brun-Titchmarsh input plus final majorants feeding TS25 padded-scale infrastructure; the current scale-transfer API is discharged by TS91 |
| `FinalHorizonInputs` | TS98 root package containing the TS97 Brun-Titchmarsh input, TS95 explicit trace ledger, and TS83 Mellin-tail API contracts |
| `HorizonRootAssemblyInputs` | TS102 terminal root package containing the TS101 Selberg divisor input, TS95 explicit trace ledger, and TS83 Mellin-tail API contracts |
| `HorizonRootAssembly` | TS102 root output package joining TS98, TS84, TS25, and candidate-v3 OTSA certificate/register/provenance surfaces |
| `TriangleSplineTailAssemblyInputs` | assembly inputs joining TS48 norm control, TS49 Sobolev agreement, and tail comparison |
| `TriangleSplineFourierTailComparisonInputs` | TS40/TS49-compatible high-frequency tail comparison for the triangle spline |
| `MathlibFourierAPIBinding` | concrete binding layer between TS41 Fourier ledger slots and future Mathlib Fourier theorem instances |
| `FourierConcreteSymbolLedger` | checked concrete Mathlib Fourier symbols and remaining Plancherel-symbol gap |
| `FourierPlancherelL2Contract` | compatible Plancherel/snorm theorem needed after the TS53 symbol probe |
| `DirichletCharacterBridge` | character orthogonality and bridge error |
| `LargeSieveInfrastructure` | local large-sieve estimate with `C <= 1` |
| `BrunTitchmarshLocalWindowBudget` | pointwise short-window prime count budget |
| `BrunTitchmarshShortInterval` | stronger threshold-form short-interval budget, currently `K = 20` |
| `BrunTitchmarshScaleBridge` | domination of the exact integer window-budget scale by a chosen closed-form scale |
| `BrunTitchmarshNatIntervalBound` | natural-interval prime-count Brun-Titchmarsh theorem |
| `BrunTitchmarshFinalInputLedger` | TS97 wrapper around the exact TS22 natural-interval Brun-Titchmarsh input feeding the TS84/TS25 final assembly |
| `SelbergSieveWeightLedger` | TS99 finite Selberg weight data and normalization feeding the TS30 Selberg roadmap |
| `SelbergSieveWeightInfrastructure` | TS99 package joining Selberg weights with the TS30 sieve and budget obligations |
| `SelbergQuadraticFormLedger` | TS100 finite quadratic-kernel and divisor-algebra data feeding the TS99 Selberg-weight front |
| `SelbergQuadraticFormInfrastructure` | TS100 package joining quadratic-form data with the TS30 sieve and budget obligations through TS99 |
| `SelbergDivisorAlgebraLedger` | TS101 finite divisor-weight, convolution, and gcd/lcm-kernel data feeding the TS100 quadratic-form front |
| `SelbergDivisorAlgebraInfrastructure` | TS101 package joining divisor algebra with the TS100 quadratic-form and TS30 sieve obligations |
| `MobiusInversionLedger` | TS103 Mobius-delta, divisor-sum, convolution, and gcd/lcm-kernel data feeding the TS101 divisor-algebra front |
| `MobiusInversionInfrastructure` | TS103 package joining Mobius inversion data with the TS101 divisor-algebra and TS30 sieve obligations |
| `MobiusConcreteBinding` | TS104 concrete Mathlib binding for `ArithmeticFunction.moebius`, divisor sums, convolution, and arithmetic delta |
| `MobiusConcreteBindingInfrastructure` | TS104 package joining the concrete Mathlib binding with the remaining TS103/TS30 Selberg obligations |
| `MobiusConcreteDeltaDischarge` | TS105 concrete proof that Mathlib's Mobius divisor sum is the arithmetic delta |
| `DivisorConvolutionBridge` | TS106 bridge combining the TS104 concrete binding with the TS105 Mobius-delta discharge |
| `GCDLCMKernelAlgebra` | TS106 gcd/lcm kernel package with the canonical rational product identity proved |
| `SelbergQuadraticKernelExtraction` | TS106 ledger naming the extraction of the Selberg quadratic kernel from divisor kernels |
| `DivisorKernelAlgebraInfrastructure` | TS106 package joining convolution, gcd/lcm kernels, and remaining TS30 Selberg obligations into TS103 |
| `SelbergQuadraticKernelExtractionProof` | TS107 canonical rational `gcd/lcm` ratio extraction proof feeding the TS106 extraction target |
| `SelbergKernelExtractionInfrastructure` | TS107 package joining the extracted quadratic kernel with the remaining TS30 Selberg obligations |
| `SelbergQuadraticFormExpansion` | TS108 finite double-sum quadratic-form expansion using the canonical Selberg kernel |
| `SelbergQuadraticFormExpansionInfrastructure` | TS108 package joining the finite expansion with the remaining TS30 Selberg obligations |
| `SelbergDiagonalChangeOfVariables` | TS109 finite divisor-filtered transformed-weight package for future diagonalization |
| `SelbergQuadraticDiagonalization` | TS109 package joining the TS108 dense form with the diagonal square-sum side |
| `SelbergQuadraticDiagonalizationInfrastructure` | TS109 package joining diagonalization markers with the remaining TS30 Selberg obligations |
| `SelbergDenseToDiagonalIdentity` | TS110 proposition-valued obligation equating the TS108 dense side with the TS109 diagonal side |
| `SelbergDenseToDiagonalInfrastructure` | TS110 package joining the dense-to-diagonal identity marker with the remaining TS30 Selberg obligations |
| `SelbergDenseToDiagonalReindexing` | TS111 finite triple-sum expansion and reindexing obligation package feeding TS110 |
| `SelbergDenseToDiagonalReindexingInfrastructure` | TS111 package joining reindexing markers with the remaining TS30 Selberg obligations |
| `SelbergMobiusCollapse` | TS112 gcd-filter rewrite and Mobius-collapse obligation package feeding TS111 |
| `SelbergMobiusCollapseInfrastructure` | TS112 package joining collapse markers with the remaining TS30 Selberg obligations |
| `InnerGcdDivisorCollapseReady` | TS113 local inner gcd-divisor sum package for one pair `(m,n)` |
| `SelbergFiniteFubiniReindexing` | TS113 finite-Fubini package reordering the TS112 gcd-filtered triple sum into pair-first order |
| `SelbergFiniteFubiniReindexingInfrastructure` | TS113 package joining finite-Fubini markers with the remaining TS30 Selberg obligations |
| `SelbergInnerGcdKernelMatchObligation` | TS114 local coefficient identity needed to match the TS107 canonical `gcd/lcm` kernel |
| `SelbergInnerGcdDivisorCollapse` | TS114 package factoring the TS113 inner gcd-divisor sum and recording the remaining coefficient-collapse obligation |
| `SelbergInnerGcdDivisorCollapseInfrastructure` | TS114 package joining inner-collapse markers with the remaining TS30 Selberg obligations |
| `SelbergGcdCoefficientKernelMatchObligation` | TS115 one-variable coefficient identity needed to match the TS107 canonical `gcd/lcm` kernel |
| `SelbergMobiusCoefficient` | TS115 package reducing the TS114 local coefficient to a filtered gcd coefficient |
| `SelbergMobiusCoefficientInfrastructure` | TS115 package joining coefficient-collapse markers with the remaining TS30 Selberg obligations |
| `SelbergGcdCoefficientKernelCompatibility` | TS116 explicit local compatibility between the gcd coefficient and the canonical `gcd/lcm` kernel |
| `SelbergGcdCoefficientKernelMatch` | TS116 package exposing the diagonal coefficient formula and coefficient-kernel compatibility |
| `SelbergGcdCoefficientKernelMatchInfrastructure` | TS116 package joining kernel-match markers with the remaining TS30 Selberg obligations |
| `SelbergDiagonalCoefficientCalculation` | TS117 package proving the current gcd-only coefficient shape cannot match the pair-dependent `gcd/lcm` kernel |
| `SelbergLCMAbsorptionBridge` | TS118 package rewriting the original `gcd/lcm` dense side as an absorbed-weight gcd-square dense side |
| `SelbergGcdSquareDiagonalization` | TS119 corrected gcd-square diagonalization package using the Jordan-two coefficient and retaining the global reindexing obligation |
| `SelbergGcdSquareGlobalReindexing` | TS120 corrected global reindexing package reducing the gcd-square dense identity to a support-local Jordan-two coefficient collapse |
| `SelbergJordanTwoFiniteSupportCollapse` | TS121 package closing the corrected dense-to-diagonal identity with absorbed weights |
| `SelbergDiagonalOptimization` | TS122 package proving finite weighted Cauchy for the corrected Jordan-two diagonal energy and isolating positivity/optimal-vector obligations |
| `SelbergJordanTwoPositivityProbe` | TS123 package proving denominator positivity from supportwise `J2` positivity and recording the support-shape diagnostic |
| `SelbergJordanTwoPositivityAPIProbe` | TS124 package proving local `J2` facts at `1` and primes, and bridging global positive-integer `J2` positivity into TS123/TS122 |
| `SelbergJordanTwoPrimePowerPositivityProbe` | TS125 package proving the normalized prime-power formula and positivity for `J2(p^(k+1))` |
| `SelbergJordanTwoMultiplicativityAPIProbe` | TS126 package proving multiplicativity of `J2`, the factorization formula, and the factorization-shaped prime-power positivity input |
| `SelbergJordanTwoFullPositivityDischarge` | TS127 package proving global positive-integer `J2` positivity and feeding the TS123/TS122 optimization route |
| `SelbergOptimalVectorNormalization` | TS128 package proving the optimal diagonal vector satisfies the Mobius constraint and attains energy `1 / D` |
| `SelbergDiagonalBudgetMajorant` | TS129 package connecting the original dense side to the TS122 diagonal energy and isolating the interval sieve-majorant step |
| `SelbergSieveMajorantFromDiagonalBudget` | TS129 package whose interval majorant, sieve theorem, and budget comparison fields feed TS99 |
| `SelbergWeightReconstruction` | TS130 package reconstructing original Selberg weights from a diagonal vector and isolating finite Mobius reconstruction |
| `SelbergOptimalWeightReconstruction` | TS130 package specializing the reconstruction to the TS128 optimal diagonal vector |
| `SelbergFiniteMobiusReconstructionCollapse` | TS131 package reducing the TS130 finite reconstruction identity to an expansion side and a local chain-coefficient delta collapse |
| `SelbergMobiusChainCoefficientCollapseLedger` | TS132 package proving the diagonal and non-divisor chain-coefficient cases and isolating the proper-divisor quotient collapse |
| `SelbergProperDivisorMobiusChainCollapse` | TS133 package proving the quotient arithmetic and reducing the proper-divisor chain collapse to finite quotient reindexing |
| `SelbergProperDivisorQuotientReindexingDischarge` | TS134 package proving the finite quotient reindexing and closing the TS131 chain coefficient collapse |
| `SelbergFiniteMobiusReconstructionExpansionDischarge` | TS135 package proving the finite Fubini expansion and closing the TS130 finite Mobius reconstruction identity |
| `SelbergIntervalMajorantFromOptimalBudget` | TS136 package bridging the TS135 optimal weights and exact budget to supplied TS30 interval Selberg majorant data |
| `ConcreteSelbergIntervalMajorantLedger` | TS137 package naming concrete interval-majorant data and proofs that instantiate TS30 and feed TS136/TS99/TS97 |
| `ConcreteSelbergSquareMajorantLedger` | TS138 package instantiating the TS137 data side with the explicit finite Selberg square majorant |
| `ConcreteSelbergIntervalSieveTheoremLedger` | TS139 package converting pointwise prime square lower bounds plus budget comparison into the TS138/TS99/TS97 route |
| `SelbergSieveIntervalBound` | Selberg-sieve theorem producing an explicit local interval majorant |
| `SelbergMajorantBudgetComparison` | arithmetic comparison from Selberg majorant to TS22 BT budget |
| `ScaledLargeSieveInfrastructure` | large-sieve estimate targeting an explicit `ShortIntervalScale` |
| `ScaleToOTSAControl` | analytic cost of carrying a TS22 scale into OTSA |
| `ScaledOTSAAdmissible` | local numerical threshold for scaled OTSA constants |
| `PaddedScaleAnalyticInfrastructure` | TS25 package for the padded scale, interval BT, and OTSA admissibility |
| `OTSARationalCertificate` | rational upper-bound certificate for scaled OTSA admissibility |
| `OTSAConstantRegister` | labelled register for candidate rational OTSA constants |
| `LabelledOTSAConstantRegister` | typed-status register for smoke, candidate, and certified OTSA packages |
| `OTSAConstantProvenanceRegister` | provenance ledger for rational OTSA constant sources |
| `OTSACert_candidate_v1` | candidate-v1 rational OTSA admissibility package |
| `OTSAProvenance_candidate_v1` | candidate-v1 provenance ledger with remaining placeholders |
| `SpectralTraceMajorantContract` | TS92 rational `Ct <= 1/2` contract now assembled from a TS95 explicit-formula ledger by TS96 |
| `ExplicitFormulaTraceBridgeLedger` | TS95 zero contribution, residual terms, rational trace budget, and explicit-formula bridge ledger feeding the TS92 bridge component |
| `TraceKernelSpectralDataLedger` | TS94 kernel, spectral-weight, normalization, positivity, decay, and convergence ledger feeding the TS92 trace-kernel component |
| `ZetaZeroFamilyLedger` | TS93 zero-set, multiplicity, strip, conjugation, and functional-equation symmetry ledger feeding the TS92 zeta-zero component |
| `TraceMajorantContract` | TS32 rational trace-contribution contract supplied by a future TS92 spectral trace instance |
| `OTSACert_candidate_v2` | trace-conditional candidate-v2 rational OTSA package |
| `MellinTailMajorantContract` | conditional Mellin-tail contract with target `Cm <= 1` |
| `ScaleTransferMajorantContract` | conditional scale-transfer contract with target `Cscale <= 2` |
| `OTSACert_candidate_v3` | final-majorants conditional rational OTSA package |
| `KernelSpectralControl` | OTSA spectral-kernel control |
| `TraceContributionControl` | OTSA trace/pole control |
| `MellinTailDecay` | OTSA Mellin-tail decay |
| `OTSACouplingHypothesis` | residual coupling inequality |

These are the objects that must be instantiated by genuine analytic proofs to
turn the relative architecture into an unconditional formal proof route.

## Build

The repository uses Lean 4.15.0 / Mathlib v4.15.0.

Typical build for the current sprint chain:

```powershell
lake build TS.Goldbach.Strong.TS16.CombinatorialDischarge `
  TS.Goldbach.Strong.TS17.MellinJacksonDischarge `
  TS.Goldbach.Strong.TS18.SecondMomentDischarge `
  TS.Goldbach.Strong.TS19.OTSAResidualDischarge `
  TS.Goldbach.Strong.TS21.SecondMomentBudgetDischarge `
  TS.Goldbach.Strong.TS22.BrunTitchmarshScaleDischarge
```

Build all TS15--TS284 targets:

```powershell
lake build TS.Goldbach.Strong.TS15.ShortIntervalSecondMoment `
  TS.Goldbach.Strong.TS15.ProblemE1ShortIntervals `
  TS.Goldbach.Strong.TS15.PCB_Q1_Discharge `
  TS.Goldbach.Strong.TS15.MellinJacksonFourier `
  TS.Goldbach.Strong.TS15.OTSAResidualDecomposition `
  TS.Goldbach.Strong.TS16.CombinatorialDischarge `
  TS.Goldbach.Strong.TS17.MellinJacksonDischarge `
  TS.Goldbach.Strong.TS18.SecondMomentDischarge `
  TS.Goldbach.Strong.TS19.OTSAResidualDischarge `
  TS.Goldbach.Strong.TS21.ShortIntervalBudget `
  TS.Goldbach.Strong.TS21.BrunTitchmarshShortInterval `
  TS.Goldbach.Strong.TS21.BrunTitchmarshEnergyDischarge `
  TS.Goldbach.Strong.TS21.ThresholdComputation `
  TS.Goldbach.Strong.TS21.SecondMomentBudgetDischarge `
  TS.Goldbach.Strong.TS22.EnergyScale `
  TS.Goldbach.Strong.TS22.BrunTitchmarshScaleDischarge `
  TS.Goldbach.Strong.TS22.ClosedFormScales `
  TS.Goldbach.Strong.TS22.BrunTitchmarshIntervalBridge `
  TS.Goldbach.Strong.TS22.ScaledLargeSieveDischarge `
  TS.Goldbach.Strong.TS23.OTSAScalePropagation `
  TS.Goldbach.Strong.TS24.ClosedFormScaleBridge `
  TS.Goldbach.Strong.TS25.PaddedScaleOTSAFeasibility `
  TS.Goldbach.Strong.TS26.OTSANumericalFeasibility `
  TS.Goldbach.Strong.TS27.OTSAConstantRegister `
  TS.Goldbach.Strong.TS28.OTSAConstantsCandidate `
  TS.Goldbach.Strong.TS29.OTSAConstantProvenance `
  TS.Goldbach.Strong.TS30.BrunTitchmarshSelbergRoadmap `
  TS.Goldbach.Strong.TS31.OTSAAsymptoticMajorants `
  TS.Goldbach.Strong.TS32.OTSATraceMajorantRoadmap `
  TS.Goldbach.Strong.TS33.OTSAFinalMajorantsRoadmap `
  TS.Goldbach.Strong.TS34.MellinFourierMeasureTransport `
  TS.Goldbach.Strong.TS35.MellinFourierAEEqTransport `
  TS.Goldbach.Strong.TS36.MellinFourierLpIsometryRoadmap `
  TS.Goldbach.Strong.TS37.MellinFourierLpNormInputs `
  TS.Goldbach.Strong.TS38.MellinFourierLpLinearityInputs `
  TS.Goldbach.Strong.TS39.MellinFourierLpIsometry `
  TS.Goldbach.Strong.TS40.FourierTailRoadmap `
  TS.Goldbach.Strong.TS41.FourierAPIProbe `
  TS.Goldbach.Strong.TS42.MellinTailSplineRoadmap `
  TS.Goldbach.Strong.TS43.TriangleSplinePointwise `
  TS.Goldbach.Strong.TS44.TriangleSplineMeasurabilitySupport `
  TS.Goldbach.Strong.TS45.TriangleSplineDerivativeSnorm `
  TS.Goldbach.Strong.TS46.TriangleSplineSupportMeasure `
  TS.Goldbach.Strong.TS47.TriangleSplineSnormDischarge `
  TS.Goldbach.Strong.TS48.BoundedSupportSnormLemma `
  TS.Goldbach.Strong.TS49.TriangleSplineSobolevAgreement `
  TS.Goldbach.Strong.TS50.TriangleSplineTailAssembly `
  TS.Goldbach.Strong.TS51.TriangleSplineFourierTailComparison `
  TS.Goldbach.Strong.TS52.FourierMathlibAPIBinding `
  TS.Goldbach.Strong.TS53.FourierConcreteSymbolsProbe `
  TS.Goldbach.Strong.TS54.FourierPlancherelGapLedger `
  TS.Goldbach.Strong.TS55.TriangleSplineSobolevAgreementLedger `
  TS.Goldbach.Strong.TS56.TriangleSplineBranchFormulae `
  TS.Goldbach.Strong.TS57.TriangleSplineClassicalBranchDerivatives `
  TS.Goldbach.Strong.TS58.TriangleSplineBoundaryExteriorControl `
  TS.Goldbach.Strong.TS59.TriangleSplineOffCornerClassicalDerivative `
  TS.Goldbach.Strong.TS60.TriangleSplineAEClassicalDerivative `
  TS.Goldbach.Strong.TS61.TriangleSplineDistributionalDerivativeLedger `
  TS.Goldbach.Strong.TS62.TriangleSplineTestFunctionAPIProbe `
  TS.Goldbach.Strong.TS63.TriangleSplineConcreteDistributionalContract `
  TS.Goldbach.Strong.TS64.TriangleSplineIPPIntegrabilityInputs `
  TS.Goldbach.Strong.TS65.TriangleSplineIPPIntegrabilityDischarge `
  TS.Goldbach.Strong.TS66.TriangleSplineIPPProductSupportRestriction `
  TS.Goldbach.Strong.TS67.TriangleSplineIPPIntegralRestriction `
  TS.Goldbach.Strong.TS68.TriangleSplineIPPIntegralRestrictionProof `
  TS.Goldbach.Strong.TS69.TriangleSplineIPPBranchSplit `
  TS.Goldbach.Strong.TS70.TriangleSplineIPPBranchSplitProof `
  TS.Goldbach.Strong.TS71.TriangleSplineIPPRightBranchClosedBridge `
  TS.Goldbach.Strong.TS72.TriangleSplineIPPRightBranchClosedBridgeProof `
  TS.Goldbach.Strong.TS73.TriangleSplineIPPAffineBranchContract `
  TS.Goldbach.Strong.TS74.TriangleSplineIPPRecombinationFromAffine `
  TS.Goldbach.Strong.TS75.TriangleSplineIPPIntervalIntegralBridge `
  TS.Goldbach.Strong.TS76.TriangleSplineIPPIntervalIntegralBridgeProof `
  TS.Goldbach.Strong.TS77.TriangleSplineIPPAffineBranchProof `
  TS.Goldbach.Strong.TS78.TriangleSplineConcreteDistributionalDischarge `
  TS.Goldbach.Strong.TS79.TriangleSplineDistributionalDerivativeDischarge `
  TS.Goldbach.Strong.TS80.TriangleSplineSobolevSlotAssembly `
  TS.Goldbach.Strong.TS81.TriangleSplineSobolevSlotAPIBinding `
  TS.Goldbach.Strong.TS82.TriangleSplineSobolevAPIRealityProbe `
  TS.Goldbach.Strong.TS83.MellinTailFinalAPIGapLedger `
  TS.Goldbach.Strong.TS84.ScaleTransferMajorantRoadmap `
  TS.Goldbach.Strong.TS85.ScaleTransferVarianceLedger `
  TS.Goldbach.Strong.TS86.GrandSieveVarianceRoadmap `
  TS.Goldbach.Strong.TS87.FareySpacingRoadmap `
  TS.Goldbach.Strong.TS88.FareySeparationProof `
  TS.Goldbach.Strong.TS89.FareyCountingProof `
  TS.Goldbach.Strong.TS90.FareyCoveringProof `
  TS.Goldbach.Strong.TS91.DualLargeSieveVarianceBoundProof `
  TS.Goldbach.Strong.TS92.SpectralTraceRoadmap `
  TS.Goldbach.Strong.TS93.ZetaZeroFamilyLedger `
  TS.Goldbach.Strong.TS94.TraceKernelSpectralDataLedger `
  TS.Goldbach.Strong.TS95.ExplicitFormulaTraceBridgeLedger `
  TS.Goldbach.Strong.TS96.SpectralTraceMajorantDischarge `
  TS.Goldbach.Strong.TS97.BrunTitchmarshFinalInputLedger `
  TS.Goldbach.Strong.TS98.FinalThreeObligationAssembly `
  TS.Goldbach.Strong.TS99.SelbergSieveWeightLedger `
  TS.Goldbach.Strong.TS100.SelbergQuadraticFormLedger `
  TS.Goldbach.Strong.TS101.SelbergDivisorAlgebraLedger `
  TS.Goldbach.Strong.TS102.HorizonRootAssembly `
  TS.Goldbach.Strong.TS103.MobiusInversionLedger `
  TS.Goldbach.Strong.TS104.MobiusMathlibAPIProbe `
  TS.Goldbach.Strong.TS105.MobiusDeltaIdentityDischarge `
  TS.Goldbach.Strong.TS106.DivisorKernelAlgebraLedger `
  TS.Goldbach.Strong.TS107.SelbergQuadraticKernelExtractionLedger `
  TS.Goldbach.Strong.TS108.SelbergQuadraticFormExpansionLedger `
  TS.Goldbach.Strong.TS109.SelbergQuadraticDiagonalizationLedger `
  TS.Goldbach.Strong.TS110.SelbergDenseToDiagonalIdentityLedger `
  TS.Goldbach.Strong.TS111.SelbergDenseToDiagonalReindexingLedger `
  TS.Goldbach.Strong.TS112.SelbergMobiusCollapseLedger `
  TS.Goldbach.Strong.TS113.SelbergFiniteFubiniReindexingLedger `
  TS.Goldbach.Strong.TS114.SelbergInnerGcdDivisorCollapseLedger `
  TS.Goldbach.Strong.TS115.SelbergMobiusCoefficientLedger `
  TS.Goldbach.Strong.TS116.SelbergGcdCoefficientKernelMatchLedger `
  TS.Goldbach.Strong.TS117.SelbergDiagonalCoefficientCalculationLedger `
  TS.Goldbach.Strong.TS118.SelbergLCMAbsorptionBridge `
  TS.Goldbach.Strong.TS119.SelbergJordanTwoGcdSquareDiagonalizationLedger `
  TS.Goldbach.Strong.TS120.SelbergGcdSquareGlobalReindexingLedger `
  TS.Goldbach.Strong.TS121.SelbergJordanTwoFiniteSupportCollapse `
  TS.Goldbach.Strong.TS122.SelbergDiagonalOptimizationLedger `
  TS.Goldbach.Strong.TS123.SelbergJordanTwoPositivityProbe `
  TS.Goldbach.Strong.TS124.SelbergJordanTwoPositivityAPIProbe `
  TS.Goldbach.Strong.TS125.SelbergJordanTwoPrimePowerPositivityProbe `
  TS.Goldbach.Strong.TS126.SelbergJordanTwoMultiplicativityAPIProbe `
  TS.Goldbach.Strong.TS127.SelbergJordanTwoFullPositivityDischarge `
  TS.Goldbach.Strong.TS128.SelbergOptimalVectorNormalization `
  TS.Goldbach.Strong.TS129.SelbergDiagonalBudgetMajorantLedger `
  TS.Goldbach.Strong.TS130.SelbergOptimalWeightReconstructionLedger `
  TS.Goldbach.Strong.TS131.SelbergFiniteMobiusReconstructionCollapse `
  TS.Goldbach.Strong.TS132.SelbergMobiusChainCoefficientCollapseLedger `
  TS.Goldbach.Strong.TS133.SelbergProperDivisorMobiusChainCollapse `
  TS.Goldbach.Strong.TS134.SelbergProperDivisorQuotientReindexingDischarge `
  TS.Goldbach.Strong.TS135.SelbergFiniteMobiusReconstructionExpansionDischarge `
  TS.Goldbach.Strong.TS136.SelbergIntervalMajorantLedger `
  TS.Goldbach.Strong.TS137.ConcreteSelbergIntervalMajorantInterface `
  TS.Goldbach.Strong.TS138.ConcreteSelbergIntervalMajorantFormulation `
  TS.Goldbach.Strong.TS139.ConcreteSelbergIntervalSieveTheoremLedger `
  TS.Goldbach.Strong.TS140.LargePrimeAdmissibility `
  TS.Goldbach.Strong.TS141.ConcreteSelbergSquareMajorantExpansion `
  TS.Goldbach.Strong.TS142.LCMMultiplicityFractionalDecomposition `
  TS.Goldbach.Strong.TS143.LCMMultiplicityErrorBoundDischarge `
  TS.Goldbach.Strong.TS144.LCMDenseSideBudgetRefactor `
  TS.Goldbach.Strong.TS145.EulerTotientDiagonalizationJordanDomination `
  TS.Goldbach.Strong.TS146.WeightedLCMErrorAggregation `
  TS.Goldbach.Strong.TS147.SelbergOptimalWeightExplicitFormula `
  TS.Goldbach.Strong.TS148.SelbergDivisorEnvelopePolynomialBound `
  TS.Goldbach.Strong.TS149.SelbergDivisorEnvelopeJordanRefinement `
  TS.Goldbach.Strong.TS150.RefinedSelbergBudgetScaleInterface `
  TS.Goldbach.Strong.TS151.DependentSelbergScaleSplitInterface `
  TS.Goldbach.Strong.TS152.FiniteHeadPrimeIntervalBudgetReduction `
  TS.Goldbach.Strong.TS153.DependentSelbergBudgetFeasibilityProbe `
  TS.Goldbach.Strong.TS154.SelbergDenominatorUpperBoundObstructionProbe `
  TS.Goldbach.Strong.TS155.BrunTitchmarshThresholdObstructionGeometry `
  TS.Goldbach.Strong.TS156.BrunTitchmarshThresholdEvaluation `
  TS.Goldbach.Strong.TS157.GoldbachScaleEventualObstruction `
  TS.Goldbach.Strong.TS158.SelbergBTObstructionClosureLedger `
  TS.Goldbach.Strong.TS159.SelbergDenominatorRefactorInterface `
  TS.Goldbach.Strong.TS160.SelbergPhiDenominatorCandidate `
  TS.Goldbach.Strong.TS161.PhiPremortemSpectralPivotLedger `
  TS.Goldbach.Strong.TS162.TriangleSplineTraceKernelInstantiation `
  TS.Goldbach.Strong.TS163.TriangleSplineFourierWeightLedger `
  TS.Goldbach.Strong.TS164.TriangleSplineFourierNormalizationProbe `
  TS.Goldbach.Strong.TS165.TriangleSplineMathlibFourierScaleLedger `
  TS.Goldbach.Strong.TS166.TriangleSplineFourierIdentificationReduction `
  TS.Goldbach.Strong.TS167.TriangleSplineConvolutionRouteProbe `
  TS.Goldbach.Strong.TS168.TriangleSplineBranchIntegralRouteProbe `
  TS.Goldbach.Strong.TS169.TriangleSplineBranchClosedFormRecombination `
  TS.Goldbach.Strong.TS170.TriangleSplineRightBranchIntegralEvaluation `
  TS.Goldbach.Strong.TS171.TriangleSplineLeftBranchIntegralEvaluation `
  TS.Goldbach.Strong.TS172.TriangleSplineFourierBranchSplit `
  TS.Goldbach.Strong.TS173.TriangleSplineFourierIdentificationDischarge `
  TS.Goldbach.Strong.TS174.TriangleSplinePlancherelInterfaceProbe `
  TS.Goldbach.Strong.TS175.TriangleSplineSpatialL2EnergyEvaluation `
  TS.Goldbach.Strong.TS176.TriangleSplineTimeL2ELpNormBridge `
  TS.Goldbach.Strong.TS177.TriangleSplineTimeELpNormValue `
  TS.Goldbach.Strong.TS178.TriangleSplineSincSpectralIntegrability `
  TS.Goldbach.Strong.TS179.TriangleSplinePlancherelAPIProbe `
  TS.Goldbach.Strong.TS180.TriangleSplineTS94KernelEvidenceLedger `
  TS.Goldbach.Strong.TS181.ExplicitFormulaTraceBlueprint `
  TS.Goldbach.Strong.TS182.TriangleSplineDiscreteSieveTraceBridge `
  TS.Goldbach.Strong.TS183.TriangleSplineFiniteWeightedPrimeSumInterface `
  TS.Goldbach.Strong.TS184.TriangleSplineVonMangoldtAPIProbe `
  TS.Goldbach.Strong.TS185.ExplicitFormulaZetaZeroFamilyLedger `
  TS.Goldbach.Strong.TS186.TriangleSplineMainTermNormalizationBridge `
  TS.Goldbach.Strong.TS187.AnalyticFrontierTransformCompatibilityLedger `
  TS.Goldbach.Strong.TS188.TriangleSplineAnalyticWall1PlancherelContractBridge `
  TS.Goldbach.Strong.TS189.LogarithmicPullbackMellinFourierInterface `
  TS.Goldbach.Strong.TS190.TriangleSplineCriticalAmplitude `
  TS.Goldbach.Strong.TS191.CriticalLineAmplitudeEnergyPrimitive `
  TS.Goldbach.Strong.TS192.CriticalLinePrimitiveLowerTailLimit `
  TS.Goldbach.Strong.TS193.CriticalLineTruncatedFTCEnergyBridge `
  TS.Goldbach.Strong.TS194.CriticalLineActualAmplitudeEnergyBridge `
  TS.Goldbach.Strong.TS195.CriticalLineActualImproperEnergyObject `
  TS.Goldbach.Strong.TS196.CriticalLineCompactChangeOfVariablesProbe `
  TS.Goldbach.Strong.TS197.CriticalLineXSideIntervalConvergenceBridge `
  TS.Goldbach.Strong.TS198.CriticalLineXSideImproperEnergyObject `
  TS.Goldbach.Strong.TS199.OTSAStrategicDashboardSynthesis `
  TS.Goldbach.Strong.TS200.OTSANonCircularConsumptionInterface `
  TS.Goldbach.Strong.TS201.StrategicDecisionLedger `
  TS.Goldbach.Strong.TS202.Wall0MeasureTransportBridge `
  TS.Goldbach.Strong.TS203.TruncatedHaarTransport `
  TS.Goldbach.Strong.TS204.FinalAnalyticInputsSpecification `
  TS.Goldbach.Strong.TS205.FinalAnalyticInputsToOTSARoutingBridge `
  TS.Goldbach.Strong.TS206.ExplicitFormulaEffectiveStatement `
  TS.Goldbach.Strong.TS207.NaiveHaarEnergyDivergenceObstruction `
  TS.Goldbach.Strong.TS208.TriangleSplinePlancherelEvidenceProbe `
  TS.Goldbach.Strong.TS209.TriangleSplineSincFourthScaleReduction `
  TS.Goldbach.Strong.TS210.BoxConvolutionTriangleEvidence `
  TS.Goldbach.Strong.TS211.BoxFourierEvaluation `
  TS.Goldbach.Strong.TS212.BoxFourierConvolutionExchange `
  TS.Goldbach.Strong.TS213.CanonicalSincFourthDirectDirichletRoute `
  TS.Goldbach.Strong.TS214.CosSquareThirdDerivativeFormulaDischarge `
  TS.Goldbach.Strong.TS215.DirichletSineIntegralAPIProbe `
  TS.Goldbach.Strong.TS216.DirichletUnitFrequencyValueProbe `
  TS.Goldbach.Strong.TS217.DirichletImproperReformulationBridge `
  TS.Goldbach.Strong.TS218.SincFourthScalingEvennessDischarge `
  TS.Goldbach.Strong.TS219.CosSquareTripleIPPCutoffReformulation `
  TS.Goldbach.Strong.TS220.CosSquareIPPPrimitiveDerivativeBridge `
  TS.Goldbach.Strong.TS221.CosSquareFiniteTripleIPPDischarge `
  TS.Goldbach.Strong.TS222.CosSquareBoundaryVanishingReductionBridge `
  TS.Goldbach.Strong.TS223.CosSquareIPPPrimitiveAtTopAsymptotic `
  TS.Goldbach.Strong.TS224.CosSquareIPPPrimitiveZeroRightAsymptotic `
  TS.Goldbach.Strong.TS225.ThirdDerivativeCutoffValueReduction `
  TS.Goldbach.Strong.TS226.ThirdDerivativeFiniteLinearizationDischarge `
  TS.Goldbach.Strong.TS227.DirichletProductCutoffScalingReduction `
  TS.Goldbach.Strong.TS228.DirichletProductCutoffPartialIntegralBridge `
  TS.Goldbach.Strong.TS229.DirichletExponentialRegularizationSetup `
  TS.Goldbach.Strong.TS230.DampedDirichletEvaluationReduction `
  TS.Goldbach.Strong.TS231.LaplaceSineTransformDischarge `
  TS.Goldbach.Strong.TS232.DampedDirichletFubiniBridgeReduction `
  TS.Goldbach.Strong.TS233.CompactFubiniIdentityDischarge `
  TS.Goldbach.Strong.TS234.LaplaceBoundaryUniformLimitDischarge `
  TS.Goldbach.Strong.TS235.DampedDifferenceAtTopDischarge `
  TS.Goldbach.Strong.TS236.AuxiliaryDampingUniformBoundDischarge `
  TS.Goldbach.Strong.TS237.CorrectedFubiniExecutionAssembly `
  TS.Goldbach.Strong.TS238.AbelToCutoffBridgeFrontier `
  TS.Goldbach.Strong.TS239.DirichletCutoffAPIDirectRouteProbe `
  TS.Goldbach.Strong.TS240.DirichletTailBoundDischarge `
  TS.Goldbach.Strong.TS241.DirichletCutoffCauchyConvergenceDischarge `
  TS.Goldbach.Strong.TS242.DirichletAbelSummationIdentityDischarge `
  TS.Goldbach.Strong.TS243.DirichletCutoffAbelFinalValueIdentification `
  TS.Goldbach.Strong.TS244.DirichletProductCutoffThirdDerivativeDischarge `
  TS.Goldbach.Strong.TS245.CosSquareImproperCutoffAssembly `
  TS.Goldbach.Strong.TS246.CanonicalSincFourthAssembly `
  TS.Goldbach.Strong.TS247.TriangleSplinePlancherelEvidenceAssembly `
  TS.Goldbach.Strong.TS248.WallOneFinalAnalyticInputConsumption `
  TS.Goldbach.Strong.TS249.EffectiveExplicitFormulaConstantsDischarge `
  TS.Goldbach.Strong.TS250.ExplicitFormulaStructuralCompatibilityDischarge `
  TS.Goldbach.Strong.TS251.ExplicitFormulaMainTermContractObstruction `
  TS.Goldbach.Strong.TS252.CorrectedExplicitFormulaContractInstallation `
  TS.Goldbach.Strong.TS253.ExplicitFormulaBoundsContractObstruction `
  TS.Goldbach.Strong.TS254.FullyCorrectedExplicitFormulaContractInstallation `
  TS.Goldbach.Strong.TS255.FullyCorrectedExplicitFormulaAnalyticDecomposition `
  TS.Goldbach.Strong.TS256.RiemannZetaZeroTruncatedContribution `
  TS.Goldbach.Strong.TS257.TriangleSplineMellinSpectralSummand `
  TS.Goldbach.Strong.TS258.ZeroSummandConjugationFiniteReality `
  TS.Goldbach.Strong.TS259.ZeroMultiplicityConjugationExtension `
  TS.Goldbach.Strong.TS260.RiemannZetaVanishingOrderRealization `
  TS.Goldbach.Strong.TS261.RiemannZetaVanishingOrderConjugationReduction `
  TS.Goldbach.Strong.TS262.DoubleConjugationAnalyticity `
  TS.Goldbach.Strong.TS263.RiemannZetaSchwarzReflection `
  TS.Goldbach.Strong.TS264.ConcreteRiemannZetaZeroFamilyRealization `
  TS.Goldbach.Strong.TS265.ConcreteFiniteHeightZeroTruncation `
  TS.Goldbach.Strong.TS266.ConcreteFiniteZeroSumTriangleMajorization `
  TS.Goldbach.Strong.TS267.ExactFiniteUniformSpectralTermBound `
  TS.Goldbach.Strong.TS268.NaturalScaleComplexPowerBound `
  TS.Goldbach.Strong.TS269.ImaginarySquareDenominatorBound `
  TS.Goldbach.Strong.TS270.HighZoneMultiplicityCountingInterface `
  TS.Goldbach.Strong.TS271.HeightShellPartialSummation `
  TS.Goldbach.Strong.TS272.HighZoneIntegerShellCover `
  TS.Goldbach.Strong.TS273.LogLinearMultiplicityCountingReduction `
  TS.Goldbach.Strong.TS274.MinimalJensenInequalityBackport `
  TS.Goldbach.Strong.TS275.FiniteJensenPolynomialFactorizationReduction `
  TS.Goldbach.Strong.TS276.LinearFactorAngularAverage `
  TS.Goldbach.Strong.TS277.NonvanishingQuotientHolomorphicLogReduction `
  TS.Goldbach.Strong.TS278.HolomorphicPrimitiveOnBallBackport `
  TS.Goldbach.Strong.TS279.BufferedQuotientHolomorphicLogConstruction `
  TS.Goldbach.Strong.TS280.CanonicalBoundaryNorm `
  TS.Goldbach.Strong.TS281.PolynomialBufferedJensenRealization `
  TS.Goldbach.Strong.TS282.CompletedRiemannZetaZeroBridge `
  TS.Goldbach.Strong.TS282.RiemannXiCandidateBufferedSpec `
  TS.Goldbach.Strong.TS283.RiemannXiFiniteZeroGeometry `
  TS.Goldbach.Strong.TS284.RiemannXiMultiplicityAndLocalNormalForm
```

## Audit

Audited scope:

```text
TS/Goldbach/Strong/TS15
TS/Goldbach/Strong/TS16
TS/Goldbach/Strong/TS17
TS/Goldbach/Strong/TS18
TS/Goldbach/Strong/TS19
TS/Goldbach/Strong/TS21
TS/Goldbach/Strong/TS22
TS/Goldbach/Strong/TS23
TS/Goldbach/Strong/TS24
TS/Goldbach/Strong/TS25
TS/Goldbach/Strong/TS26
TS/Goldbach/Strong/TS27
TS/Goldbach/Strong/TS28
TS/Goldbach/Strong/TS29
TS/Goldbach/Strong/TS30
TS/Goldbach/Strong/TS31
TS/Goldbach/Strong/TS32
TS/Goldbach/Strong/TS33
TS/Goldbach/Strong/TS34
TS/Goldbach/Strong/TS35
TS/Goldbach/Strong/TS36
TS/Goldbach/Strong/TS37
TS/Goldbach/Strong/TS38
TS/Goldbach/Strong/TS39
TS/Goldbach/Strong/TS40
TS/Goldbach/Strong/TS41
TS/Goldbach/Strong/TS42
TS/Goldbach/Strong/TS43
TS/Goldbach/Strong/TS44
TS/Goldbach/Strong/TS45
TS/Goldbach/Strong/TS46
TS/Goldbach/Strong/TS47
TS/Goldbach/Strong/TS48
TS/Goldbach/Strong/TS49
TS/Goldbach/Strong/TS50
TS/Goldbach/Strong/TS51
TS/Goldbach/Strong/TS52
TS/Goldbach/Strong/TS53
TS/Goldbach/Strong/TS54
TS/Goldbach/Strong/TS55
TS/Goldbach/Strong/TS56
TS/Goldbach/Strong/TS57
TS/Goldbach/Strong/TS58
TS/Goldbach/Strong/TS59
TS/Goldbach/Strong/TS60
TS/Goldbach/Strong/TS61
TS/Goldbach/Strong/TS62
TS/Goldbach/Strong/TS63
TS/Goldbach/Strong/TS64
TS/Goldbach/Strong/TS65
TS/Goldbach/Strong/TS66
TS/Goldbach/Strong/TS67
TS/Goldbach/Strong/TS68
TS/Goldbach/Strong/TS69
TS/Goldbach/Strong/TS70
TS/Goldbach/Strong/TS71
TS/Goldbach/Strong/TS72
TS/Goldbach/Strong/TS73
TS/Goldbach/Strong/TS74
TS/Goldbach/Strong/TS75
TS/Goldbach/Strong/TS76
TS/Goldbach/Strong/TS77
TS/Goldbach/Strong/TS78
TS/Goldbach/Strong/TS79
TS/Goldbach/Strong/TS80
TS/Goldbach/Strong/TS81
TS/Goldbach/Strong/TS82
TS/Goldbach/Strong/TS83
TS/Goldbach/Strong/TS84
TS/Goldbach/Strong/TS85
TS/Goldbach/Strong/TS86
TS/Goldbach/Strong/TS87
TS/Goldbach/Strong/TS88
TS/Goldbach/Strong/TS89
TS/Goldbach/Strong/TS90
TS/Goldbach/Strong/TS91
TS/Goldbach/Strong/TS92
TS/Goldbach/Strong/TS93
TS/Goldbach/Strong/TS94
TS/Goldbach/Strong/TS95
TS/Goldbach/Strong/TS96
TS/Goldbach/Strong/TS97
TS/Goldbach/Strong/TS98
TS/Goldbach/Strong/TS99
TS/Goldbach/Strong/TS100
TS/Goldbach/Strong/TS101
TS/Goldbach/Strong/TS102
TS/Goldbach/Strong/TS103
TS/Goldbach/Strong/TS104
TS/Goldbach/Strong/TS105
TS/Goldbach/Strong/TS106
TS/Goldbach/Strong/TS107
TS/Goldbach/Strong/TS108
TS/Goldbach/Strong/TS109
TS/Goldbach/Strong/TS110
TS/Goldbach/Strong/TS111
TS/Goldbach/Strong/TS112
TS/Goldbach/Strong/TS113
TS/Goldbach/Strong/TS114
TS/Goldbach/Strong/TS115
TS/Goldbach/Strong/TS116
TS/Goldbach/Strong/TS117
TS/Goldbach/Strong/TS118
TS/Goldbach/Strong/TS119
TS/Goldbach/Strong/TS120
TS/Goldbach/Strong/TS121
TS/Goldbach/Strong/TS122
TS/Goldbach/Strong/TS123
TS/Goldbach/Strong/TS124
TS/Goldbach/Strong/TS125
TS/Goldbach/Strong/TS126
TS/Goldbach/Strong/TS127
TS/Goldbach/Strong/TS128
TS/Goldbach/Strong/TS129
TS/Goldbach/Strong/TS130
TS/Goldbach/Strong/TS131
TS/Goldbach/Strong/TS132
TS/Goldbach/Strong/TS133
TS/Goldbach/Strong/TS134
TS/Goldbach/Strong/TS135
TS/Goldbach/Strong/TS136
TS/Goldbach/Strong/TS137
TS/Goldbach/Strong/TS138
TS/Goldbach/Strong/TS139
TS/Goldbach/Strong/TS140
TS/Goldbach/Strong/TS141
TS/Goldbach/Strong/TS142
TS/Goldbach/Strong/TS143
TS/Goldbach/Strong/TS144
TS/Goldbach/Strong/TS145
TS/Goldbach/Strong/TS146
TS/Goldbach/Strong/TS147
TS/Goldbach/Strong/TS148
TS/Goldbach/Strong/TS149
TS/Goldbach/Strong/TS150
TS/Goldbach/Strong/TS151
TS/Goldbach/Strong/TS152
TS/Goldbach/Strong/TS153
TS/Goldbach/Strong/TS154
TS/Goldbach/Strong/TS155
TS/Goldbach/Strong/TS156
TS/Goldbach/Strong/TS157
TS/Goldbach/Strong/TS158
TS/Goldbach/Strong/TS159
TS/Goldbach/Strong/TS160
TS/Goldbach/Strong/TS161
TS/Goldbach/Strong/TS162
TS/Goldbach/Strong/TS163
TS/Goldbach/Strong/TS164
TS/Goldbach/Strong/TS165
TS/Goldbach/Strong/TS166
TS/Goldbach/Strong/TS167
TS/Goldbach/Strong/TS168
TS/Goldbach/Strong/TS169
TS/Goldbach/Strong/TS170
TS/Goldbach/Strong/TS171
TS/Goldbach/Strong/TS172
TS/Goldbach/Strong/TS173
TS/Goldbach/Strong/TS174
TS/Goldbach/Strong/TS175
TS/Goldbach/Strong/TS176
TS/Goldbach/Strong/TS177
TS/Goldbach/Strong/TS178
TS/Goldbach/Strong/TS179
TS/Goldbach/Strong/TS180
TS/Goldbach/Strong/TS181
TS/Goldbach/Strong/TS182
TS/Goldbach/Strong/TS183
TS/Goldbach/Strong/TS184
TS/Goldbach/Strong/TS185
TS/Goldbach/Strong/TS186
TS/Goldbach/Strong/TS187
TS/Goldbach/Strong/TS188
TS/Goldbach/Strong/TS189
TS/Goldbach/Strong/TS190
TS/Goldbach/Strong/TS191
TS/Goldbach/Strong/TS192
TS/Goldbach/Strong/TS193
TS/Goldbach/Strong/TS194
TS/Goldbach/Strong/TS195
TS/Goldbach/Strong/TS196
TS/Goldbach/Strong/TS197
TS/Goldbach/Strong/TS198
TS/Goldbach/Strong/TS199
TS/Goldbach/Strong/TS200
TS/Goldbach/Strong/TS201
TS/Goldbach/Strong/TS202
TS/Goldbach/Strong/TS203
TS/Goldbach/Strong/TS204
TS/Goldbach/Strong/TS205
TS/Goldbach/Strong/TS206
TS/Goldbach/Strong/TS207
TS/Goldbach/Strong/TS208
TS/Goldbach/Strong/TS209
TS/Goldbach/Strong/TS210
TS/Goldbach/Strong/TS211
TS/Goldbach/Strong/TS212
TS/Goldbach/Strong/TS213
TS/Goldbach/Strong/TS214
TS/Goldbach/Strong/TS215
TS/Goldbach/Strong/TS216
TS/Goldbach/Strong/TS217
TS/Goldbach/Strong/TS218
TS/Goldbach/Strong/TS219
TS/Goldbach/Strong/TS220
TS/Goldbach/Strong/TS221
TS/Goldbach/Strong/TS222
TS/Goldbach/Strong/TS223
TS/Goldbach/Strong/TS224
TS/Goldbach/Strong/TS225
TS/Goldbach/Strong/TS226
TS/Goldbach/Strong/TS227
TS/Goldbach/Strong/TS228
TS/Goldbach/Strong/TS229
TS/Goldbach/Strong/TS230
TS/Goldbach/Strong/TS231
TS/Goldbach/Strong/TS232
TS/Goldbach/Strong/TS233
TS/Goldbach/Strong/TS234
TS/Goldbach/Strong/TS235
TS/Goldbach/Strong/TS236
TS/Goldbach/Strong/TS237
TS/Goldbach/Strong/TS238
TS/Goldbach/Strong/TS239
TS/Goldbach/Strong/TS240
TS/Goldbach/Strong/TS241
TS/Goldbach/Strong/TS242
TS/Goldbach/Strong/TS243
TS/Goldbach/Strong/TS244
TS/Goldbach/Strong/TS245
TS/Goldbach/Strong/TS246
TS/Goldbach/Strong/TS247
TS/Goldbach/Strong/TS248
TS/Goldbach/Strong/TS249
TS/Goldbach/Strong/TS250
TS/Goldbach/Strong/TS251
TS/Goldbach/Strong/TS252
TS/Goldbach/Strong/TS253
TS/Goldbach/Strong/TS254
TS/Goldbach/Strong/TS255
TS/Goldbach/Strong/TS256
TS/Goldbach/Strong/TS257
TS/Goldbach/Strong/TS258
TS/Goldbach/Strong/TS259
TS/Goldbach/Strong/TS260
TS/Goldbach/Strong/TS261
TS/Goldbach/Strong/TS262
TS/Goldbach/Strong/TS263
TS/Goldbach/Strong/TS264
TS/Goldbach/Strong/TS265
TS/Goldbach/Strong/TS266
TS/Goldbach/Strong/TS267
TS/Goldbach/Strong/TS268
TS/Goldbach/Strong/TS269
TS/Goldbach/Strong/TS270
TS/Goldbach/Strong/TS271
TS/Goldbach/Strong/TS272
TS/Goldbach/Strong/TS273
TS/Goldbach/Strong/TS274
TS/Goldbach/Strong/TS275
TS/Goldbach/Strong/TS276
TS/Goldbach/Strong/TS277
TS/Goldbach/Strong/TS278
TS/Goldbach/Strong/TS279
TS/Goldbach/Strong/TS280
TS/Goldbach/Strong/TS281
TS/Goldbach/Strong/TS282
TS/Goldbach/Strong/TS283
TS/Goldbach/Strong/TS284
```

Audit commands:

```powershell
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS118
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS119
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS120
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS121
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS122
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS123
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS124
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS125
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS126
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS127
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS128
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS129
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS130
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS131
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS132
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS133
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS134
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS135
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS136
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS137
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS138
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS139
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS140
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS141
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS142
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS143
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS144
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS145
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS146
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS147
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS148
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS149
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS150
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS151
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS152
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS153
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS154
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS155
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS156
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS157
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS158
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS159
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS160
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS161
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS162
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS163
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS164
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS165
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS166
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS167
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS168
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS169
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS170
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS171
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS172
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS173
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS174
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS175
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS176
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS177
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS178
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS179
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS180
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS181
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS182
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS183
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS184
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS185
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS186
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS187
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS188
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS189
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS190
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS191
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS192
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS193
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS194
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS195
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS196
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS197
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS198
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS199
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS200
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS201
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS202
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS203
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS204
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS205
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS206
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS207
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS208
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS209
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS210
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS211
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS212
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS213
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS214
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS215
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS216
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS217
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS218
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS219
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS220
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS221
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS222
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS223
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS224
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS225
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS226
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS227
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS228
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS229
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS230
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS231
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS232
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS233
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS234
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS235
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS236
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS237
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS238
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS239
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS240
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS241
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS242
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS243
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS244
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS245
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS246
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS247
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS248
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS249
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS250
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS251
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS252
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS253
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS254
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS255
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS256
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS257
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS258
rg -n "s[o]rry|a[x]iom|[^\x00-\x7F]" TS\Goldbach\Strong\TS259
rg -n "s[o]rry|a[x]iom|o[p]aque|[^\x00-\x7F]" TS\Goldbach\Strong\TS260
rg -n "s[o]rry|a[x]iom|o[p]aque|[^\x00-\x7F]" TS\Goldbach\Strong\TS261
rg -n "s[o]rry|a[x]iom|o[p]aque|[^\x00-\x7F]" TS\Goldbach\Strong\TS262
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS263
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS263
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS264
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS264
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS265
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS265
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS266
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS266
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS267
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS267
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS268
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS268
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS269
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS269
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS270
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS270
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS271
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS271
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS272
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS272
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS273
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS273
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS274
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS274
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS275
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS275
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS276
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS276
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS277
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS277
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS278
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS278
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS279
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS279
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS280
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS280
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS281
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS281
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS282
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS282\RiemannXiCandidateBufferedSpec.lean TS\Goldbach\Strong\TS282\TS282_Audit.md
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS282\CompletedRiemannZetaZeroBridge.lean
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS283
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS283
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS284
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS284
rg -n "s[o]rry" TS\Goldbach\Strong\TS15 TS\Goldbach\Strong\TS16 TS\Goldbach\Strong\TS17 TS\Goldbach\Strong\TS18 TS\Goldbach\Strong\TS19 TS\Goldbach\Strong\TS21 TS\Goldbach\Strong\TS22 TS\Goldbach\Strong\TS23 TS\Goldbach\Strong\TS24 TS\Goldbach\Strong\TS25 TS\Goldbach\Strong\TS26 TS\Goldbach\Strong\TS27 TS\Goldbach\Strong\TS28 TS\Goldbach\Strong\TS29 TS\Goldbach\Strong\TS30 TS\Goldbach\Strong\TS31 TS\Goldbach\Strong\TS32 TS\Goldbach\Strong\TS33 TS\Goldbach\Strong\TS34 TS\Goldbach\Strong\TS35 TS\Goldbach\Strong\TS36 TS\Goldbach\Strong\TS37 TS\Goldbach\Strong\TS38 TS\Goldbach\Strong\TS39 TS\Goldbach\Strong\TS40 TS\Goldbach\Strong\TS41 TS\Goldbach\Strong\TS42 TS\Goldbach\Strong\TS43 TS\Goldbach\Strong\TS44 TS\Goldbach\Strong\TS45 TS\Goldbach\Strong\TS46 TS\Goldbach\Strong\TS47 TS\Goldbach\Strong\TS48 TS\Goldbach\Strong\TS49 TS\Goldbach\Strong\TS50 TS\Goldbach\Strong\TS51 TS\Goldbach\Strong\TS52 TS\Goldbach\Strong\TS53 TS\Goldbach\Strong\TS54 TS\Goldbach\Strong\TS55 TS\Goldbach\Strong\TS56 TS\Goldbach\Strong\TS57 TS\Goldbach\Strong\TS58 TS\Goldbach\Strong\TS59 TS\Goldbach\Strong\TS60 TS\Goldbach\Strong\TS61 TS\Goldbach\Strong\TS62 TS\Goldbach\Strong\TS63 TS\Goldbach\Strong\TS64 TS\Goldbach\Strong\TS65 TS\Goldbach\Strong\TS66 TS\Goldbach\Strong\TS67 TS\Goldbach\Strong\TS68 TS\Goldbach\Strong\TS69 TS\Goldbach\Strong\TS70 TS\Goldbach\Strong\TS71 TS\Goldbach\Strong\TS72 TS\Goldbach\Strong\TS73 TS\Goldbach\Strong\TS74 TS\Goldbach\Strong\TS75 TS\Goldbach\Strong\TS76 TS\Goldbach\Strong\TS77 TS\Goldbach\Strong\TS78 TS\Goldbach\Strong\TS79 TS\Goldbach\Strong\TS80 TS\Goldbach\Strong\TS81 TS\Goldbach\Strong\TS82 TS\Goldbach\Strong\TS83 TS\Goldbach\Strong\TS84 TS\Goldbach\Strong\TS85 TS\Goldbach\Strong\TS86 TS\Goldbach\Strong\TS87 TS\Goldbach\Strong\TS88 TS\Goldbach\Strong\TS89 TS\Goldbach\Strong\TS90 TS\Goldbach\Strong\TS91 TS\Goldbach\Strong\TS92 TS\Goldbach\Strong\TS93 TS\Goldbach\Strong\TS94 TS\Goldbach\Strong\TS95 TS\Goldbach\Strong\TS96 TS\Goldbach\Strong\TS97 TS\Goldbach\Strong\TS98 TS\Goldbach\Strong\TS99 TS\Goldbach\Strong\TS100 TS\Goldbach\Strong\TS101 TS\Goldbach\Strong\TS102 TS\Goldbach\Strong\TS103 TS\Goldbach\Strong\TS104 TS\Goldbach\Strong\TS105 TS\Goldbach\Strong\TS106 TS\Goldbach\Strong\TS107 TS\Goldbach\Strong\TS108 TS\Goldbach\Strong\TS109 TS\Goldbach\Strong\TS110 TS\Goldbach\Strong\TS111 TS\Goldbach\Strong\TS112 TS\Goldbach\Strong\TS113 TS\Goldbach\Strong\TS114 TS\Goldbach\Strong\TS115 TS\Goldbach\Strong\TS116 TS\Goldbach\Strong\TS117
rg -n "a[x]iom" TS\Goldbach\Strong\TS15 TS\Goldbach\Strong\TS16 TS\Goldbach\Strong\TS17 TS\Goldbach\Strong\TS18 TS\Goldbach\Strong\TS19 TS\Goldbach\Strong\TS21 TS\Goldbach\Strong\TS22 TS\Goldbach\Strong\TS23 TS\Goldbach\Strong\TS24 TS\Goldbach\Strong\TS25 TS\Goldbach\Strong\TS26 TS\Goldbach\Strong\TS27 TS\Goldbach\Strong\TS28 TS\Goldbach\Strong\TS29 TS\Goldbach\Strong\TS30 TS\Goldbach\Strong\TS31 TS\Goldbach\Strong\TS32 TS\Goldbach\Strong\TS33 TS\Goldbach\Strong\TS34 TS\Goldbach\Strong\TS35 TS\Goldbach\Strong\TS36 TS\Goldbach\Strong\TS37 TS\Goldbach\Strong\TS38 TS\Goldbach\Strong\TS39 TS\Goldbach\Strong\TS40 TS\Goldbach\Strong\TS41 TS\Goldbach\Strong\TS42 TS\Goldbach\Strong\TS43 TS\Goldbach\Strong\TS44 TS\Goldbach\Strong\TS45 TS\Goldbach\Strong\TS46 TS\Goldbach\Strong\TS47 TS\Goldbach\Strong\TS48 TS\Goldbach\Strong\TS49 TS\Goldbach\Strong\TS50 TS\Goldbach\Strong\TS51 TS\Goldbach\Strong\TS52 TS\Goldbach\Strong\TS53 TS\Goldbach\Strong\TS54 TS\Goldbach\Strong\TS55 TS\Goldbach\Strong\TS56 TS\Goldbach\Strong\TS57 TS\Goldbach\Strong\TS58 TS\Goldbach\Strong\TS59 TS\Goldbach\Strong\TS60 TS\Goldbach\Strong\TS61 TS\Goldbach\Strong\TS62 TS\Goldbach\Strong\TS63 TS\Goldbach\Strong\TS64 TS\Goldbach\Strong\TS65 TS\Goldbach\Strong\TS66 TS\Goldbach\Strong\TS67 TS\Goldbach\Strong\TS68 TS\Goldbach\Strong\TS69 TS\Goldbach\Strong\TS70 TS\Goldbach\Strong\TS71 TS\Goldbach\Strong\TS72 TS\Goldbach\Strong\TS73 TS\Goldbach\Strong\TS74 TS\Goldbach\Strong\TS75 TS\Goldbach\Strong\TS76 TS\Goldbach\Strong\TS77 TS\Goldbach\Strong\TS78 TS\Goldbach\Strong\TS79 TS\Goldbach\Strong\TS80 TS\Goldbach\Strong\TS81 TS\Goldbach\Strong\TS82 TS\Goldbach\Strong\TS83 TS\Goldbach\Strong\TS84 TS\Goldbach\Strong\TS85 TS\Goldbach\Strong\TS86 TS\Goldbach\Strong\TS87 TS\Goldbach\Strong\TS88 TS\Goldbach\Strong\TS89 TS\Goldbach\Strong\TS90 TS\Goldbach\Strong\TS91 TS\Goldbach\Strong\TS92 TS\Goldbach\Strong\TS93 TS\Goldbach\Strong\TS94 TS\Goldbach\Strong\TS95 TS\Goldbach\Strong\TS96 TS\Goldbach\Strong\TS97 TS\Goldbach\Strong\TS98 TS\Goldbach\Strong\TS99 TS\Goldbach\Strong\TS100 TS\Goldbach\Strong\TS101 TS\Goldbach\Strong\TS102 TS\Goldbach\Strong\TS103 TS\Goldbach\Strong\TS104 TS\Goldbach\Strong\TS105 TS\Goldbach\Strong\TS106 TS\Goldbach\Strong\TS107 TS\Goldbach\Strong\TS108 TS\Goldbach\Strong\TS109 TS\Goldbach\Strong\TS110 TS\Goldbach\Strong\TS111 TS\Goldbach\Strong\TS112 TS\Goldbach\Strong\TS113 TS\Goldbach\Strong\TS114 TS\Goldbach\Strong\TS115 TS\Goldbach\Strong\TS116 TS\Goldbach\Strong\TS117
```

Expected result: no matches.

## TS20 Manuscript

The synthesis document is available at:

```text
TS/Goldbach/Strong/TS20/TS20_Horizon_Goldbach_Synthesis.tex
```

It summarizes TS15--TS19 and records the final analytic infrastructure ledger.
It is written for XeLaTeX because it uses `fontspec`.

## Repository Note

The root project also contains older Horizon/Goldbach modules. Some older
areas may have their own independent audit status. The sprint chain documented
above is specifically the audited `TS/Goldbach/Strong/TS15`--`TS284` layer.
