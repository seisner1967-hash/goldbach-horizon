# Q341-Q396 : des contrats analytiques aux brackets historiques certifiés

[Accueil du dépôt](../README.md) · [English](README.md) · [Chronologie complète](CHRONOLOGY.md) · [Frontière Bridge A](BRIDGE_A.md)

**État documenté au 9 septembre 2026 : Q395 est la dernière clôture disponible. Q396 est un mandat dont le rapport de résultats n’a pas été fourni.**

Cette section rend visibles les avancées conservées dans les paquets de recherche
après TS341. Le dépôt était resté au commit `433e29e` parce que ces campagnes
prévoyaient de préserver le travail local et les archives sans opération Git permanente.

## Résultats acquis dans les campagnes documentées

| Étapes | Résultat | Limite exacte |
| --- | --- | --- |
| Q341-Q365 | Obligation d’ordonnée zéro, noyaux de certificats rationnels, zéro dans `(14,15)`, fonction entière et coefficients Riemann-Siegel. | Les diagnostics numériques et les théorèmes conditionnels restent distingués des preuves de signes. |
| Q366-Q380 | Reste défini indépendamment, représentation de Cauchy, déplacement de contour et formule source Riemann-Siegel. | À Q380, le raccord auxiliaire-zêta restait encore ouvert. |
| Q381-Q389 | Mordell, theta-Mellin, puis identité auxiliaire-zêta sur toute la droite critique et transport vers `normalizedHardyZ`. | L’ancien seed exceptionnel n’est pas utilisé pour fermer la droite critique. |
| Q390-Q391 | Géométrie du point canonique et preuve sans prémisse d’un vrai reste normalisé au plus `2,5 × 10⁻³⁰`. | Point `751937898017/1073741824`, `K=63`, `ell=10` ; aucun théorème générique d’Arias pour tous les points n’est revendiqué. |
| Q392-Q393 | Les huit atomes sont certifiés ; appartenance, positivité et `AnalyticLeaf` concret au point canonique. | Il s’agit de la borne droite du bracket 415. |
| Q394-Q395 | Six brackets historiques fermés, 410-415, avec de vrais zéros distincts. | Les indices Lean sont 409-414. Les 643 autres lignes ne sont pas certifiées. |

La multiplicité est prouvée **au moins 6** sous la hauteur 1000. L’intervalle séparé
`(14,15)` porte ce minorant à **7**, sans ajouter de ligne au ledger historique.
Un changement de signe ne prouve à lui seul ni unicité, ni simplicité, ni compte global exact.

## Ce qui reste ouvert

- Les cinq brackets 405-409, déjà couverts par la borne uniforme `5 × 10⁻³⁰` sur `[685,7003/10]`, attendent leurs signes.
- La famille sémantique complète de 649 lignes, les deux bornes de Turing, le compte exact et la saturation restent à établir.
- Le raffinement vers les anciennes boîtes sérialisées et les feuilles du premier bracket étroit sont des obligations distinctes.
- Le contrat TS340 à la hauteur 1 132 490, avec un compte positif exact de 2 001 050, reste ouvert.

```text
BRIDGE_A            : OPEN
TS340_UNCONDITIONAL  : OPEN_FROZEN
Q396                : MANDAT ; RÉSULTATS NON FOURNIS
```

Le mandat Q396 vise l’optimisation de l’inverse certifié du dénominateur des jets,
puis les dix endpoints des brackets 405-409. Fermer les cinq paires porterait la
sous-famille à 11 lignes ; cela n’est pas encore compté comme un résultat.

## Documents

- [Synthèse française, 28 pages](pdf/Q341-Q396-Horizon-Goldbach-Synthese-Continuation.pdf)
- [Synthèse anglaise, 28 pages](pdf/Q341-Q396-Horizon-Goldbach-Continuation-Synthesis-English.pdf)
- [Chronologie des 56 jalons](CHRONOLOGY.md)
- [Rapports et portée des vérifications](EVIDENCE.md)
- [Statut structuré](STATUS.json)

Cette publication ajoute les documents et les deux synthèses. Elle ne présente pas
les modules des paquets Q comme des cibles Lake désormais intégrées et recompilées
sur `main`. Les preuves et leurs procédures de rejeu restent dans les paquets de
recherche vérifiés. Aucune preuve inconditionnelle de Goldbach n’est revendiquée.
