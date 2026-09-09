# Q374 — Source RSformula and Hardy Transport

## Verdict

```text
Q374_DISTINCT_EXPANSIONS_CONFIRMED : EXTERNAL_DIAGNOSTIC
Q374_SOURCE_FUBINI_PASS            : PROVEN_IN_LEAN

Q374_SOURCE_SIDE_DECAY_PASS                 : NOT_OBTAINED
Q374_PARALLEL_LINE_DEFORMATION_PASS         : NOT_OBTAINED
Q374_SOURCE_RSFORMULA_PASS                  : NOT_OBTAINED
Q374_COEFFICIENT_COMPATIBILITY_PASS         : NOT_OBTAINED
Q374_AUXILIARY_TO_ZETA_PASS                 : NOT_ATTEMPTED
Q374_CRITICAL_LINE_REFLECTION_PASS          : NOT_ATTEMPTED
Q374_CRITICAL_PHASE_TRANSPORT_PASS          : NOT_ATTEMPTED
Q374_NORMALIZED_HARDY_Z_DECOMPOSITION_PASS  : NOT_OBTAINED
```

Classification globale: `ANALYTIC_PARTIAL_FAIL_CLOSED`.

## Resultat Lean

Le module `Q374Probe.SourceFubini` expose l'interversion semantique:

```lean
Q374Probe.sourceRSRemainder_fubini
```

Elle porte sur le reste independant `Q366Probe.sourceRSRemainder` et ne depend
plus d'un temoin non habite pour le gap harmonique ou le denominateur cosinus.

## Porte de provenance

L'audit des sources primaires confirme que l'expansion source de 2024 utilise
des objets complexes du type `P_k`, `D_k` et derivees de `G`, tandis que Q365
formalise l'expansion Arias/FLINT de 2011 avec `d_j^(k)`, `C_k(p)` et
`riemannSiegelFDeriv`.

Cette distinction est un `EXTERNAL_DIAGNOSTIC`, pas un theoreme de
compatibilite. Aucune egalite entre les deux parties finies n'est revendiquee.

## Premiere feuille ouverte

La prochaine identite profonde reste la deformation complete des contours,
incluant la decroissance des cotes transverses. Sans elle, `RSformula` et le
transport vers `normalizedHardyZ` restent fermes en echec.

## Confiance

- 2 sources Q374, 30 lignes.
- Builds directs: 2/2 PASS.
- Agregat Lake: PASS.
- Axiomes du theorem terminal: `propext`, `Classical.choice`, `Quot.sound`.
- Scan executable interdit: vide.
