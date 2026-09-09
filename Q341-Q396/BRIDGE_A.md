# Bridge A: exact remaining obligations

[Overview](README.md) · [Chronology](CHRONOLOGY.md)

Status at the Q395 closeout, as documented on September 9, 2026.

| Contract | Current state | What is still required |
| --- | --- | --- |
| Canonical endpoint | Closed in Q393. | Nothing further for this exact endpoint membership and sign theorem. It does not certify a different point. |
| Historical rows 410-415 | Six exact pairs certified. | No uniqueness or simplicity is inferred from their sign changes. |
| Rows 405-409 | Their analytic remainder is covered by Q394RangeExtended. | Ten endpoint computations, actual atom memberships, successful exact replay, and the resulting signs. |
| Full `H1000ScaledLambdaBracketFamily` | Geometry is proved; semantic signs are available for six rows. | The other 643 rows and a complete indexed family, with the historical endpoints unchanged. |
| Initial Turing bound | Open. | `initialTuringMultiplicityMass 1001 ≤ 288`. |
| Upper Turing bound | Open. | `upperTuringMultiplicityMass 1001 ≤ 361`. |
| Exact pilot count | Open. | `positiveMultiplicityMass 1000 = 649`, using the actual counting contracts. |
| TS329 saturation | Open. | Global count, local lower counts, exact sum, disjointness, and cap compatibility on the same payload. |
| First serialized bracket | Open. | Its exact `FirstBracketAnalyticLeaves`; the broader Q358 interval `(14,15)` is a distinct result. |
| Serialized refinement | Open for the historical consumer. | A certified enclosure included in the requested serialized box. A new positive box does not imply this inclusion. |
| Reference TS340 contract | Open/frozen. | Exact positive global count 2,001,050 at height 1,132,490 and matching certified local lower counts. |

## Cardinality and lower bounds

The certified family is indexed by
`{i : Fin 649 // i ∈ {409,410,411,412,413,414}}`.
It has exactly **6** rows. Disjointness gives six distinct genuine zeros and a
multiplicity lower bound of at least 6. The separate interval `(14,15)` gives a
separate lower bound of at least 7 when combined with the family. It does not
increase the historical family cardinality.

## Width obstruction: scope matters

Any symmetric output inflation of radius `2.5e-30` has width at least `5e-30`.
It cannot refine the historical right box of bracket 415, whose width is
`1572 / 10^80`. Q394 proves this obstruction for that strategy; it does not prove
that the true value fails to belong to the old box, or that every future strategy
must fail.

The direct sign-family route can proceed without proving that serialized refinement.
It does not thereby discharge the separate serialized consumer. A positive scale
transports Hardy signs to carrier signs; it does not transport the same numerical
box unchanged.

## Q396 is a target, not an added proof

The supplied mandate targets five more pairs. If it closes `m` pairs, the historical
cardinality must be proved to be `6 + m`, with `0 ≤ m ≤ 5`. Only a verified results
report and the actual theorem evidence can update the present six-row count.
