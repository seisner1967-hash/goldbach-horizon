# Agent 6 — filtre de la boucle 2

`round2_checks.py` s'est terminé avec code de sortie 0, statut `PASS`, au paramètre **N = 100 000 000**, alpha = 100 et Q = 999 999. `round2.json` contient les résultats exacts et `round2_run.log` conserve la sortie. Les anciens `parity_checks.py` et `numerical.json` sont lus uniquement ; leurs SHA256 sont comparés avant et après l'exécution.

## Poids avec Ω comptant les multiplicités

Le poids testé est

    W(n) = (Ω(n)-2)(Ω(n)-3)/2,

où Ω(n) est la somme des exposants de la factorisation première. Sur 1 < n < (alpha+1)^4 et lorsque chaque premier divisant n dépasse alpha, on a 1 <= Ω(n) <= 3. W vaut alors le détecteur premier, sans hypothèse de carré-liberté.

Le banc réalise **24 371 contrôles de ce poids**, dont **22 978 occurrences non carré-libres**. Le domaine contient les p,p²,p³ et p²q sélectionnés, tous les entiers rugueux n <= 3000, les deux axes de 4096 faces additives déterministes lorsque compatibles avec la rugosité, et les familles exhaustives suivantes à N = 10^8 :

- **1204** carrés de premiers p > 100 avec p² < N ;
- **65** cubes de premiers p > 100 avec p³ < N ;
- **21 648** produits p²q < N avec p,q > 100 premiers distincts.

Les counts par Ω sont 893, 1678 et 21 800 pour Ω = 1,2,3. Certains exemples se répètent entre domaines ; les 24 371 sont le nombre d'appels exacts au contrôle, pas une revendication de 24 371 entiers distincts.

Le script et le reçu indépendants de l'Agent 4, `chen_multiplicity_checks.py` et `chen_multiplicity.json`, ont aussi été lus. Leur domaine annoncé et leurs **24 121 entiers distincts** sont cohérents : 1204 premiers échantillonnés jusqu'à 10 000, puis les mêmes 1204 carrés, 65 cubes et 21 648 produits mixtes exhaustifs. Les bornes p² < N et p²q < N impliquent que tous les premiers nécessaires à ces trois familles sont dans la liste complète jusqu'à 10 000.

La rugosité du seul r ne suffit pas : r = 101*103*107 = 1 113 121 et k = 3 donnent m = 3 339 363, Ω(m) = 4, W(m) = 1 et détecteur premier = 0. Le premier 3 détruit la rugosité complète de m. Ce contre-exemple est testé avec les facteurs réels et les multiplicités.

## Contre-exemple symbolique de l'annulation locale

Tous les logarithmes sont représentés par des dictionnaires premier -> coefficient rationnel. Aucun évaluateur flottant de logarithmes n'intervient.

Pour m = 303 = 3*101 et n = N-m = 99 999 697, le préfixe exact est k = 1,2,3. Le terme k = 2 est exclu par le masque d'unité car 2 divise N. Les k admis sont 1 et 3, et la face stricte alpha*k < m est conservée. Le calcul donne exactement

    D_{100,999999}(303) = -log 3,
    W_N(99 999 697) = -log 3 - (1/2)log 101,
    μ(303)(D-W) = (1/2)log 101.

La factorisation première complète de n est **7*41*348431**. L'égalité n = 7*14285671 est vraie, mais 14285671 = 41*348431 est composite. Ainsi Λ(n) = 0 et fII(n) = -log n. Le terme S_full correspondant est

    -(1/2)(log 7 + log 41 + log 348431) log 101 < 0.

Pour le partenaire premier m = 101, n = 99 999 899 = 17*5882347, le préfixe vaut 1 et D = W = -log 101. Le kernel du partenaire est donc nul : il ne compense pas ce terme négatif par une fermeture ponctuelle automatique.

La proposition d'une diagonale locale uniformément nulle ou favorable est ainsi falsifiée dans ce test précis. Cette falsification ne réfute aucune compensation entre tuples ni aucune future borne globale sur D_N. Le tuple P = 4, Q = 0 de la première boucle est un diagnostic indépendant et reste conservé dans son ancien reçu.

## Journal et provenance

Un premier passage du nouveau banc a arrêté l'exécution sur une attente erronée de factorisation : le cofacteur 14285671 avait été placé comme premier dans l'oracle de sortie. La factorisation certifiée a révélé 41*348431 ; l'oracle a été corrigé. Le signe de la contribution et les kernels D,W n'ont pas changé. L'exécution finale réussit.

SHA256 du nouveau script : `619a3e8d0828b3d053fb436d343c0b30a1b4b836cbd03e9c873ecee94b70627b`.

SHA256 de l'ancien script, conservé : `6f201c898eb6bfc4e05703d02cdca4e211d1a7311cb11a0644192c90990cb8b2`.

Le filtre numérique du poids avec multiplicité est **PASS**. La certification Lean et l'effet sur le budget signé global restent des obligations séparées.
