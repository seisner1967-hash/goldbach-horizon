# Agent 6 — boucle 3, contrôle multi-fibre

Le banc principal `multifibre_checks.py` a terminé avec **code 0, PASS**, au vrai paramètre **N = 100 000 000**, alpha = 100 et Q = 999 999. Les anciens fichiers numériques sont comparés par SHA256 avant et après le calcul et restent inchangés. `multifibre.json` conserve les domaines et certificats ; `multifibre_run.log` conserve la sortie.

## Les termes scalaires réels

Le calcul conserve les kernels D/W, le préfixe `min(Q,(m-1)//alpha)`, la face stricte alpha*k < m, les masques d'unité et fII(n) = Λ(n)-log n. Les axes carrés-libres sont vérifiés ; la rugosité du premier axe est W = 2.

- **3084 paires** passent les sélecteurs dans le domaine exhaustif p = 3,7,11,13,17,19 et 1 <= m <= floor(20000/p), avec p ne divisant pas m. Les sommes réelles des deux sites ont **1602 signes négatifs, 1266 positifs et 216 coefficients exactement nuls**. Les faces quittant la rugosité alpha ne sont pas supprimées ; ce statut est enregistré.
- Le transport exact, avec **face supérieure non appariée conservée**, réussit pour un scalaire tronqué à m <= 1000 et p = 3,7. Le sélecteur supplémentaire μ(N-m)^2 est explicite dans ce test fini.
- Le bloc complet m = 101,303,707,2121 est **strictement négatif**. Les deux extrêmes ont terme nul ; les deux sites centraux donnent une contribution négative. Les quatre axes complémentaires et les quatre premiers axes sont carré-libres et unités.

L'audit a corrigé le signe proposé initialement pour m = 707 :

    K(303) = (1/2)log 101,
    K(707) = (1/3)log 101 -(1/2)log 7 +(1/2)log 3.

Le premier axe du sommet, 99 997 879, est premier, certifié par factorisation entière utilisant la liste complète des premiers jusqu'à sqrt(10^8). Les autres premiers axes du bloc ont les factorisations 17*5882347, 7*41*348431 et 577*173309.

## Origine des certificats de signe

Les logarithmes sont d'abord des vecteurs de coefficients rationnels devant les log p ; les termes S_full sont des formes quadratiques rationnelles en ces logarithmes. Pour borner log p, le programme écrit p = 2^k*x avec 1 <= x < 2, puis utilise

    log x = 2 sum_{j>=0} z^(2j+1)/(2j+1), z = (x-1)/(x+1).

Après L termes, le reste est compris entre 0 et `2*z^(2L+1)/((2L+1)*(1-z*z))`. Tous ces calculs sont des `Fraction`. Les bornes sont arrondies vers l'extérieur par division entière sur un dénominateur commun ; les sommes de produits conservent ainsi des intervalles rationnels certifiés. **Aucun logarithme flottant ne décide le signe.** Le certificat du bloc se trouve strictement entre -64 et -63 ; ses bornes exactes sont dans le JSON.

Un passage préliminaire a rencontré la limite Python de conversion d'entiers de plus de 4300 chiffres lors de l'export d'une grande fraction. L'arrondi rationnel vers l'extérieur sur dénominateur commun a résolu ce problème de représentation en préservant l'enveloppe exacte. Aucune identité arithmétique n'a échoué lors de cette exception.

## Cellule spectrale séparée

À **N = 10^8**, le quotient eta = -a/(s*t) modulo N est testé sur a <= 120 et s,t <= 60, avec masques carrés-libres et unités séparés. L'histogramme entier direct égale exactement la convolution des trois supports poussés ; il a **2214 résidus non nuls**.

La factorisation ne résiste pas à la suppression d'un masque couplé : avec a < s, le coefficient réel à eta = 122399 est -2, tandis que le produit factorisé donne -4. La séparabilité est donc une hypothèse réelle de l'identité, et les faces mobiles originales ne sont pas déclarées séparables par ce test.

Les diagnostics auxiliaires **q = 11**, **q = 829** et **N = 1658** sont distincts du scan à N = 10^8. Les histogrammes de phases Legendre-Kloosterman égalent ceux du carré de Gauss et donnent exactement -11 et 829. Le tuple HH à N = 1658 donne une masse ponctuelle non nulle sous le caractère de conducteur 829. Aucune affirmation sur un cutoff analytique u^8 ou son onset n'est tirée de ces petites valeurs.

## Reçu supplémentaire

`mixed_difference_checks.py` a terminé avec **code 0, PASS** et laisse le banc principal inchangé. Sur **121 blocs admissibles**, p = 3, q = 7 et 21*base <= 20000, il vérifie les différences de produits E5 avec tous les termes mixtes, et la formule E6 pour la courbure fII. La positivité du rapport logarithmique lisse est certifiée par l'identité entière

    (N-pb)(N-qb)-(N-b)(N-pqb) = N*b*(p-1)*(q-1) > 0.

Le résultat principal ne prouve aucune compensation globale de D_N : les scans portent sur leurs domaines finis explicites, et les histogrammes spectraux n'apportent pas de gain uniforme en conducteur.

## SHA256

- `multifibre_checks.py` : `f1a2ac839f149d240ecbc25b1ace0acf6130c483425c2c1443a86e0b73e688b5`.
- `multifibre.json` : `312c27b0cdf99d039dcdeb11efe2efb577bf0fe06c1b31d23b39fc95537246d1`.
- `mixed_difference_checks.py` : `435410918e854573d9d697b40670890df834ebc328e0cb24a38e149421116e56`.
- `mixed_difference.json` : `3c5510a346cb624e119e07656871fc2356acf74c52499212ab0d0b02b8c1df1a`.

Les fichiers JSON consignent aussi les SHA256 des sources et des reçus antérieurs vérifiés.
