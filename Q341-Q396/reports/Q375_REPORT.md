# Q375 — Explicit Remainder and Production Pilot

## Verdict

```text
Q375_RAW_INTEGRAL_REMAINDER_BOUND_PASS : PROVEN_IN_LEAN

Q375_EXPLICIT_ARIAS_BOUND_PASS              : NOT_OBTAINED
Q375_CERTIFICATE_CHECKER_SOUND_PASS         : NOT_ATTEMPTED
Q375_CERTIFICATE_REPLAY_EXACT_PASS          : NOT_ATTEMPTED
Q375_CANONICAL_RS_ENDPOINT_PASS             : NOT_ATTEMPTED
Q375_FIRST_RS_RS_PRODUCTION_BRACKET_PASS    : NOT_ATTEMPTED
Q375_MINIMUM_MARGIN_STRESS_SEMANTIC_PASS    : NOT_ATTEMPTED
```

Classification globale: `ANALYTIC_PARTIAL_FAIL_CLOSED`.

## Resultat Lean

Lean prouve une borne semantique inconditionnelle pour le reste integral source
independant:

```lean
sourceRSRemainder_norm_le_rawIntegralBound
```

La borne `sourceRawIntegralBound` est le produit exact des integrales des deux
majorants compilables `rsOuterMajorant` et `rsInnerMajorant`. Le theoreme repose
sur la domination Q370 et l'interversion de Fubini maintenant inconditionnelles.

## Limite fail-closed

Cette borne n'est pas encore la forme fermee `explicitAriasBound t K` utilisee
par Q360. Les integrales des majorants n'ont pas ete evaluees en constantes
explicites, et aucune compatibilite Q374/Q365 n'est disponible. Aucun endpoint,
certificat Q368 ou bracket de production n'est donc revendique.

## Confiance

- 2 sources Q375, 109 lignes.
- Builds directs: 2/2 PASS.
- Agregat Lake: PASS.
- Axiomes du theorem terminal: `propext`, `Classical.choice`, `Quot.sound`.
- Scan executable interdit: vide.
