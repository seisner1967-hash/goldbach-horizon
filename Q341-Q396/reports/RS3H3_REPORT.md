# RS3H-III — Source F Gap to RS Pilot

## Verdict global

```text
RS3H3_ANALYTIC_PARTIAL_FAIL_CLOSED

Q373_SOURCE_F_HARMONIC_REAL_GAP : CLOSED
Q370_PRODUCT_BOUND              : CLOSED_UNCONDITIONALLY
Q370_FUBINI                     : CLOSED_UNCONDITIONALLY
Q374_SOURCE_FUBINI              : CLOSED
Q375_RAW_INTEGRAL_BOUND         : CLOSED

Q374_SOURCE_RSFORMULA           : OPEN
Q375_EXPLICIT_ARIAS_BOUND       : OPEN
Q375_CANONICAL_ENDPOINT         : NOT_ATTEMPTED
BRIDGE_A                        : OPEN
CARRIER_MEMBERSHIP              : UNPROVED
TS340_UNCONDITIONAL             : OPEN_FROZEN
```

Le sprint a ete gele volontairement a 12:21, avant le gel planifie de 13:48 et
l'echeance de 14:03. Toutes les feuilles accessibles avaient alors un verdict
compile; les routes restantes exigent des travaux analytiques profonds qui ne
pouvaient plus recevoir implementation, build et audit complets dans la fenetre.

## PROVEN_IN_LEAN

1. Extension de bord de `sourceG`, avec limites en `0` et `1`.
2. Formules et non-negativite sur le bord reel.
3. Positivite stricte de `Re sourceH` dans les deux demi-plans.
4. Queue uniforme explicite et extraction compacte d'un gap uniforme positif.
5. Specialisation du gap vers l'interface historique Q370.
6. Majorant produit du noyau double sans temoin analytique residuel.
7. Fubini semantique pour `sourceRSRemainder` sans premisse de gap residuelle.
8. Borne de norme du reste par le produit exact de deux integrales de majorants.

## EXTERNAL_DIAGNOSTIC

Les expansions 2024 et Q365/2011 sont distinctes dans leurs objets et
conventions documentaires. Aucun theoreme Lean de compatibilite n'est disponible.

## NOT_OBTAINED

1. Decroissance complete des cotes transverses et deformation finale.
2. `RSformula` source.
3. Compatibilite des coefficients source 2024 avec Q365.
4. Transport fonction auxiliaire vers zeta puis `normalizedHardyZ`.
5. Reduction du produit d'integrales a `explicitAriasBound`.
6. Endpoint et bracket de production.

## Build et confiance

```text
Lean                          : 4.15.0
Mathlib                       : 9837ca9d65d9de6fad1ef4381750ca688774e608
Nouvelles sources de preuve   : 21
Build direct                  : 21/21 PASS
Agregat Lake                  : PASS, 2269 jobs
Axiomes terminaux             : propext, Classical.choice, Quot.sound
Scan interdit executable      : EMPTY
git diff --check              : PASS
HEAD                          : 433e29e
origin/main                   : 433e29e
Worktree                      : DETACHED
Operation Git permanente      : NONE
```

Le worktree contient les artefacts jetables non suivis des campagnes
anterieures et de RS3H-III; aucune revendication de worktree vide n'est faite.
La minoration cosinus Q370 conserve sa classification historique
`POST_DEADLINE` de RS3H-II.

## Premiere frontiere suivante

La prochaine campagne doit choisir une seule cible profonde:

```text
Q376_SOURCE_SIDE_DECAY_AND_PARALLEL_DEFORMATION
```

Elle ne devra ouvrir `RSformula` qu'apres fermeture de la deformation. Le
chantier distinct de compatibilite des expansions restera fail-closed.
