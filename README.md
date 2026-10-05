## Negative-results and formalization report, 5 October 2026

Author: **Durand Serge**, Independent researcher.

- **Proved in Lean:** the generated inventory records established auxiliary
  declarations with their hypotheses and existing credit; no Goldbach proof is claimed.
- **Conditional:** retained external hypotheses and excluded material are identified
  in Appendix B.
- **Open:** the signed analytic estimate, the uncovered range and the uniform
  certificate construction remain obligations within their respective frameworks.
- **Negative results:** the report records obstructions to specified arguments and
  constraint families; it does not exclude either whole route.

[Report (PDF)](paper/main.pdf) · [Portable source](paper/main.tex) ·
[arXiv bundle](paper/arxiv_submission.tar.gz) ·
[Evidence map](paper/evidence_map.json) · [Human review checklist](paper/REVIEW_CHECKLIST.md)

Complete declaration tables: [analytic inventory](paper/analytic_lean_inventory.csv)
and [algebraic inventory](paper/algebraic_lean_inventory.csv).
The paper derives these tables from existing records without new mathematical runs.
Large binary evidence is excluded from this publication commit; its recorded hashes
are retained for a separate author-managed GitHub Release or Zenodo deposit.

---

Warning: truncated output (original token count: 106696)
Total output lines: 6683

# Horizon Goldbach

Lean 4 formal specification programme for a conditional architecture around the
binary Goldbach conjecture.

This repository does **not** claim an unconditional proof of Goldbach. Its goal
is narrower and auditable: decompose the proof architecture into Lean-checked
modules, prove the finite/combinatorial layer, and expose the remaining
analytic work as named local infrastructure obligations.

## Synthesis V3.1 and Native Numerical Addendum, 4 October 2026

The [complete revised synthesis and resumption package](publications/2026-10-goldbach-synthesis-v3-1/)
now records the completed N=100000000, K=2^27 native calculation. Five-modulus
CRT, direct canonical A32 summation and auxiliary B40 reconstruction agree
exactly. The observed normalized difference is zero; the fixed joint
quantization radius is 4.4408921429095471e-8 < 1e-6.

The [byte-exact numerical archive](research/goldbach-numerical-20261004/)
retains scripts, native checker, receipts, logs and all payloads, including
failed infrastructure attempts. The original [V3 publication](publications/2026-10-goldbach-synthesis-v3/)
is unchanged. The French Fejer handoff is a current-state entry point,
not a new theoretical result. The inventory remains 88 credited modules /
1488 auxiliary declarations, including definitions. Native Lean refinement,
the full Mellin coefficient chain, spectral H1, D_N and Goldbach remain open.

## Binary Goldbach research synthesis, 1 October 2026

Durand Serge's **version 2** research report is now available with an English
51-page PDF, abstract, tables, bibliography, standalone LaTeX source and a
versioned verification companion:

- [Read the PDF](publications/2026-10-goldbach-framework/goldbach_synthesis_v2.pdf)
- [Reproduction files, scope and licences](publications/2026-10-goldbach-framework/README.md)

The report distinguishes finite Lean identities, written analytic deductions
and explicitly conditional primitive-character inputs. The actual signed
residual estimate and a complete positive prime-pair margin remain open.
The quarter-power and eighth-power profiles are not merged. **No proof of
Goldbach, external peer review or journal acceptance is claimed.** Substantial
AI assistance is disclosed. Manuscript licence: CC BY 4.0; software and
historical evidence retain their own rights.

## Q341-Q396: certified analytic continuation and historical zero brackets

**Updated September 9, 2026. Latest documented closeout: Q395.**
The continuation is now documented in a dedicated [Q341-Q396 section](Q341-Q396/README.md)
([résumé en français](Q341-Q396/README.fr.md)).

| Milestones | Documented advance |
| --- | --- |
| TS341 / Q341 | The zero-ordinate premise is discharged by the real eta argument. |
| Q347-Q365 | Rational certificate kernels, a genuine zero in `(14,15)`, an entire Riemann-Siegel auxiliary function, and exact coefficient recurrences. |
| Q366-Q389 | Independent contour remainder, source Riemann-Siegel representation, and auxiliary-zeta transport on the entire critical line. |
| Q390-Q391 | The canonical endpoint is bound to the true formula; its normalized source remainder is proved at most `2.5e-30`, without a residual premise. |
| Q392-Q393 | All eight actual finite atoms, canonical endpoint membership and positivity, and a concrete `AnalyticLeaf` are certified. |
| Q394-Q395 | Six exact historical brackets, **410-415** (Lean indices **409-414**), contain distinct genuine zeta zeros. Multiplicity is at least **6**, or at least **7** with the separate `(14,15)` interval. |
| Q396 | Continuation mandate: a certified reciprocal kernel and brackets 405-409. **No Q396 results report has been supplied.** |

**Bridge A remains OPEN.** The other **643** historical rows, the complete sign family,
the Turing bounds, exact counting, and saturation remain open. The separate interval
`(14,15)` does not count as another exact ledger row. `TS340_UNCONDITIONAL` remains
`OPEN_FROZEN`; no unconditional proof of Goldbach or the Riemann hypothesis is claimed.

- [Full chronology of all 56 milestones](Q341-Q396/CHRONOLOGY.md)
- [Current Bridge A obligations](Q341-Q396/BRIDGE_A.md) and [machine-readable status](Q341-Q396/STATUS.json)
- [English synthesis, 28 pages](Q341-Q396/pdf/Q341-Q396-Horizon-Goldbach-Continuation-Synthesis-English.pdf)
- [Synthèse française, 28 pages](Q341-Q396/pdf/Q341-Q396-Horizon-Goldbach-Synthese-Continuation.pdf)
- [Campaign reports and verification scope](Q341-Q396/EVIDENCE.md)

This publication adds documentation and the two synthesis PDFs. The Q-campaign proof
sources and replay artifacts remain in the separately verified research packages;
this documentation update does not claim to install or rebuild them as main-branch
Lake targets. Their reported results and remaining obligations are recorded separately
from the permanent TS source tree below.

### Permanent TS chain: verified milestones through TS341

The TS292--TS339 chain, together with TS341, now proves absolute convergence of the nontrivial-zero
series, the finite-height and infinite-height triangle-spline explicit
identities, the four quantitative Perron boundary controls, the complete
singularity census, the rectangle residue theorem, scalar Mellin-Perron
inversion, and the finite dyadic quadratic moment with good-scale selection
and effective tail transfer, and its exact expansion as a weighted pair
correlation with diagonal/off-diagonal separation. TS316 additionally closes
the diagonal correlation uniformly from TS292 absolute summability, without a
separate zero-multiplicity hypothesis. TS317 exposes the exact weighted
off-diagonal exponent, closes a coarse absolute pair bound, and reduces every
sharper estimate to finite weighted Kusmin-Landau and close-pair contracts. It
also gives a coarse unconditional finite-moment bound from the TS292 linear
mass.
TS318 separates each exact off-diagonal power into its decreasing real
amplitude and pure logarithmic phase, proves a finite Abel transfer without
variation loss, and reduces the TS317 pointwise kernel contract to one named
nonresonant discrete phase-partial-sum estimate.
TS319 closes the small-frequency branch, proves conjugation symmetry and the
monotone nonresonant dyadic increment geometry, and inhabits the indexed TS318
contract with a coarse height-dependent constant. It separately records the
uniform oscillatory Kusmin-Landau statement needed for smallness.
TS320 proves that uniform statement by a purely discrete summation-by-parts
argument with absolute constant `24`, then closes the TS317 pointwise weighted
kernel contract with constant `96`. The weighted close-pair envelope remains
the spectral smallness obstruction. TS321 partitions that exact finite
envelope into the gap-at-most-one mass and disjoint unit shells, proves the
correct `1/k` shell weighting, and packages local weighted certificates into
the canonical TS317 global envelope contract. TS322 defines the exact linear
coefficient tail outside a finite zero core, routes the closed TS292 tail
rate, proves the tail tends to zero, and uniformly bounds every higher TS317
pair envelope by the finite TS321 core plus the real error `2*L*R(H)`. It does
not rationalize the core or claim the TS181 half-budget. TS323 defines the
complete rational certificate boundary, routes the TS322 pair majorant through
the TS320 constant `96`, combines it with the TS316 diagonal bound and TS315
moment identity, invokes TS314 good-scale selection, and conditionally builds
the exact TS313 normalized budget and TS181 adapter. It does not construct a
concrete numerical certificate.
TS324 defines proof-free rational zero-box payloads and separates their
decidable structural well-formedness from semantic coverage of the true finite
zero truncation. It rewrites the TS322 finite core exactly as a stepwise
weighted ordered-pair sum and proves that an executable rational double sum of
certified box masses is a non-circular upper bound, without requiring box
disjointness. TS324 leaves Boolean payload checking to TS325; analytic cover
construction and concrete TS323 certificate habitation remain open.
TS325 supplies the executable Boolean checker for the rational TS324 payload,
proves exact reflection to `PayloadWellFormed` and the declared-majorant
comparison, and conditionally routes a successful check plus an independent
analytic zero cover to a real upper bound for the TS322 finite core. It neither
decides analytic coverage nor asserts that any checked value can satisfy the
TS323 half-budget.
TS326 separates exact global and local multiplicity-count certificates, proves
that disjoint saturated local lower counts force exhaustive coverage of the
finite zero truncation, and derives each TS324 coefficient-mass certificate
from a positive rational ordinate lower bound and a total multiplicity bound
per box. It constructs the TS324 semantic cover conditionally, without
evaluating zeta or inhabiting the required global and local count certificates.
TS327 transports positive zero data to a symmetric payload through conjugation.
TS328 adds executable grouped allocation, strict imaginary-disjointness, and
saturation-arithmetic checks. TS329 turns explicit positive count certificates
into a symmetric finite-zero cover, while keeping every analytic counting
premise visible. TS330 completes the conditional TS323 certificate from a
template that deliberately omits the finite-core proof, then routes it to the
TS181 adapter. TS331 derives the necessary executable rejection threshold
`core <= 1/384` without claiming that a template is inhabited.
TS332 retains the pre-uniformized TS290 zero-count envelope, proves the local
factor-two log-linear bound above height two, and improves the infinite-zero
residual constant to `20760/19`. TS333 combines abstract finite linear and
quadratic caps with this shifted tail, including the exact quadratic
core-plus-tail partition and the bound `Q_tail <= L_tail^2`. TS334 packages
rational outer bounds for the public TS314 truncation-tail envelope and proves
the exact reference bound at height `1132490`.
TS335 proves the explicit exceptional-residue envelope `3 + 9/x`. TS336
closes the fixed-left boundary by `1440/x`. TS337 assembles the exact
reference trace-budget template while retaining the finite linear and
quadratic spectral caps as explicit premises. TS338 instantiates its abstract
zero-family ledger with the concrete Riemann zeta ledger from TS264, and TS339
turns a checked rational payload plus an independent certified analytic cover
into those two finite spectral caps. TS341 proves the signed eta identity and
closes `NoZeroOrdinateInTruncation H` for every height `H`.
TS312 routes the explicit formula into the high-level TS204 contract, and TS313
provides the certified `2/x` normalization and rational TS95/TS181 packaging
bridge.

This closes the project ledger's Wall 2 explicit-formula front and records the
Wall 3 spectral summability component. A concrete inhabitant of the TS323
rational certificate, and hence an unconditional rational trace budget at most
one half, Gallagher, OTSA, and Goldbach remain open.

### Permanent TS analytic frontier and TS340 reference contract

The permanent Lean chain currently reaches TS341 (`0e289dc`). TS335 through
TS339 and TS341 are repository theorems; there is deliberately no permanent
TS340 completion module. TS341 closes the no-zero-ordinate premise without
empirical data. The only missing analytic certificates for an unconditional
TS340 completion are the exact positive global zero count `2001050` at height
`1132490` and certified local lower counts summing to the same total.

No empirical zero table or Q512 payload is committed as proof. Native or
rational checks alone do not construct these analytic counting certificates,
and no call to `TS330.complete` is claimed unconditionally.

Published reference commits for the latest chain are TS331 `a35298f`, TS332
`76564af`, TS333 `ac34f73`, TS334 `b06e8cf`, TS335 `46a713d`, TS336
`2fa9bab`, TS337 `117144b`, TS338 `ea99d13`, TS339 `6dc620a`, and TS341
`0e289dc`.

## Permanent source tree: TS15--TS341, with TS340 counting certificates open

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
  TS285/
  TS286/
  TS287/
  TS288/
  TS289/
  TS290/
  TS291/
  TS292/
  TS293/
  TS294/
  TS295/
  TS296/
  TS297/
  TS298/
  TS299/
  TS300/
  TS301/
  TS302/
  TS303/
  TS304/
  TS305/
  TS306/
  TS307/
  TS308/
  TS309/
  TS310/
  TS311/
  TS312/
  TS313/
  TS314/
  TS315/
  TS316/
  TS317/
  TS318/
  TS319/
  TS320/
  TS321/
  TS322/
  TS323/
  TS324/
  TS325/
  TS326/
  TS327/
  TS328/
  TS329/
  TS330/
  TS331/
  TS332/
  TS333/
  TS334/
  TS335/
  TS336/
  TS337/
  TS338/
  TS339/
  TS341/
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
| TS112 | Selberg Mobius collapse ledger | `repo_committed_relative` | rewrites the TS111 pair divisor filters as a single gcd filter and packages the remain…91696 tokens truncated….Strong.TS261.RiemannZetaVanishingOrderConjugationReduction `
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
  TS.Goldbach.Strong.TS284.RiemannXiMultiplicityAndLocalNormalForm `
  TS.Goldbach.Strong.TS285.RiemannXiFiniteQuotientAssembly `
  TS.Goldbach.Strong.TS286.RiemannXiMasterAPI `
  TS.Goldbach.Strong.TS287.RiemannXiGrowthAPIProbe `
  TS.Goldbach.Strong.TS288.CompletedZetaThetaMellinCircleGrowth `
  TS.Goldbach.Strong.TS289.CompletedZetaThetaIntegralClosedBound `
  TS.Goldbach.Strong.TS290.RiemannXiLogLinearZeroCounting `
  TS.Goldbach.Strong.TS291.LogLinearZeroContributionAssembly `
  TS.Goldbach.Strong.TS292.EffectiveInfiniteZeroTailConvergence `
  TS.Goldbach.Strong.TS293.TruncatedPerronContourResidual `
  TS.Goldbach.Strong.TS294.QuantitativeCleanContourEstimates `
  TS.Goldbach.Strong.TS295.StrongCleanHeightLogDerivativeReduction `
  TS.Goldbach.Strong.TS296.ConcreteStrongHeightXiQuotientLog `
  TS.Goldbach.Strong.TS297.XiZetaHorizontalPerronBridge `
  TS.Goldbach.Strong.TS298.RightLineCutoffAndHorizontalIntegration `
  TS.Goldbach.Strong.TS299.FiniteGridStrongHeightReciprocalLoad `
  TS.Goldbach.Strong.TS300.CenteredBorelCaratheodoryAndClosedLoadDecay `
  TS.Goldbach.Strong.TS301.AnchoredMacroscopicXiQuotient `
  TS.Goldbach.Strong.TS302.FiniteMacroscopicCorrectionDecay `
  TS.Goldbach.Strong.TS303.ClosedAnchoredMacroscopicEnvelope `
  TS.Goldbach.Strong.TS304.ClosedCompletionCorrectionAndHorizontalDecay
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
TS/Goldbach/Strong/TS285
TS/Goldbach/Strong/TS286
TS/Goldbach/Strong/TS287
TS/Goldbach/Strong/TS288
TS/Goldbach/Strong/TS289
TS/Goldbach/Strong/TS290
TS/Goldbach/Strong/TS291
TS/Goldbach/Strong/TS292
TS/Goldbach/Strong/TS293
TS/Goldbach/Strong/TS294
TS/Goldbach/Strong/TS295
TS/Goldbach/Strong/TS296
TS/Goldbach/Strong/TS297
TS/Goldbach/Strong/TS298
TS/Goldbach/Strong/TS299
TS/Goldbach/Strong/TS300
TS/Goldbach/Strong/TS301
TS/Goldbach/Strong/TS302
TS/Goldbach/Strong/TS303
TS/Goldbach/Strong/TS304
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
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS285
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS285
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS286
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS286
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS287
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS287
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS288
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS288
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS289
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS289
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS290
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS290
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS291
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS291
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS292
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS292
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS293
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS293
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS294
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS294
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS295
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS295
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS296
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS296
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS297
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS297
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS298
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS298
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS299
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS299
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS300
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS300
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS301
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS301
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS302
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS302
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS303
rg --pcre2 -n "[^\x00-\x7F]" TS\Goldbach\Strong\TS303
rg -n "s[o]rry|a[x]iom|o[p]aque" TS\Goldbach\Strong\TS304
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
above is specifically the audited `TS/Goldbach/Strong/TS15`--`TS304` layer.
