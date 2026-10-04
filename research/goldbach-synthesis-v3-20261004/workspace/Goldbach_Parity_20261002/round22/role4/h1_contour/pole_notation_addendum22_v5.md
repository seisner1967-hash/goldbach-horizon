# Raccord du pôle et normaliseur — SOURCE ONLY

Cette nouvelle note complète les documents déjà liés sans les modifier.
Dans `euler_mellin_addendum22.md`, la lettre locale α désignait le facteur
`1/(2π)`. Cette désignation était une collision de notation : **α conserve
exclusivement la coupure canonique de la monographie**. Le facteur analytique
sera désigné `Cπ = 1/(2π)` ou écrit explicitement. Aucun acquis arithmétique,
énoncé compilé, capture, addendum antérieur ou reçu v4 n'est modifié.

Trois nouvelles sources ajoutent 31 déclarations avec 31 impressions
qualifiées : `ZetaPoleRemoval22.lean` (13), `ThermalPoleMellin22.lean` (11),
`ThermalPoleDifference22.lean` (7). Le total H1 de ROLE4 est maintenant 114
déclarations SOURCE ONLY. Ce total décrit du texte de preuves, sans crédit
de compilation ou de certification globale.

Le premier module définit la vraie fonction amovible A : la valeur 1 au
point 1 est justifiée par le résidu de ζ fourni par mathlib. La continuité,
la dérivabilité ponctuée et la singularité amovible donnent l'analyticité.
Les deux logarithmes dérivés proviennent de la vraie ζ, du produit d'Euler
direct, de la série Λ déjà dérivée et de l'équation fonctionnelle.

Les deux autres modules construisent un majorant produit
`1_S(x) x^(-c) |G(c+it)|` réellement intégrable. L'inversion Mellin point
par point, puis Fubini, donnent pour le pôle rationnel :

- sur `c>1`, `Cπ ∫ G(c+it)/(c+it−1) dt = ∫_(1,∞) fY(x) dx` ;
- sur `d<1`, `Cπ ∫ G(d+it)/(d+it−1) dt = −∫_(0,1) fY(x) dx` ;
- leur différence est exactement `Y`, par la valeur Mellin de `fY` à `s=1`.

Les conditions utilisées sont `Y≥1`, `1<c≤3/2`, `−1/2≤d<1`. Les domaines
fixés `(1,∞)` et `(0,1)` acquittent les conditions d'intégrabilité de la
puissance réelle. Les valeurs de l'intégrale complexe utilisent la branche
sur les réels positifs. La partition `(0,1]∪(1,∞)` et l'absence d'atomes
traitent le point 1 ; aucune identité de déplacement de contour n'est admise.

Les lectures intégrales des sources sont respectivement `97fe59`, `31e025`
et `8fc202`. Elles ne remplacent aucune compilation. Le raccord ψ/C5,
l'assemblage global C3, les queues C6/C8, la trace de tous les zéros, le
coefficient additif N, la cible D_N et la victoire restent à acquitter.

La revue statique des quatre sources ψ de ROLE3 (`a84072`, `41e749`) n'a
identifié aucun trou analytique dans P1/duplication. Les APIs ont été lues
de façon ciblée (`60792f`, `81a454`, `c40ad1`), avec des chemins inexacts
dans la première recherche corrigés avant les vérifications utiles. Cette
revue ne constitue pas un PASS Lean. Le prochain batch auteur minimal
de cinq modules analytiques sera gelé séparément et restera sans exécution
jusqu'à une autorisation ROOT propre. Après l'échec technique du composant,
ROOT a expressément autorisé la préparation d'une gate auxiliaire liée à la
provenance Γ H2 et au reçu réel de l'échec JSON, sans nouveau crédit numérique.
