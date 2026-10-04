# Agent 6 : diagnostics numériques exacts

Le banc `parity_checks.py` s'est terminé avec code de sortie 0 et statut `PASS`, sous Python 3.12.14, au vrai paramètre additif **N = 100 000 000**. Le reçu complet est `numerical.json` et la sortie conservée est `numerical_run.log`. Les identités arithmétiques emploient uniquement des entiers ; le temps écoulé est la seule donnée flottante.

Les sources lues sont la monographie locale et les deux fichiers de continuation `sources/exact_checks.py` et `sources/Goldbach_Continuation_Cofacteur_Court_2026-10-01.txt`. Les sources ont été conservées intactes.

## Cadre retenu

Le profil quart de puissance donne alpha = 100 et Q = (N-1)//alpha = 999 999. Le profil huitième de puissance donne alpha = 10 et Q = 9 999 999. Ces deux profils restent distincts.

H_y(n) est le coefficient entier de la convolution μ_{>y} * μ_{>y} * ζ. Le kernel D_{alpha,Q}(m), avec logarithmes et face stricte, est distinct de D_N. La monographie définit D_N = -S_full + 2 max(e,0) après fourniture du bridge couvert. Le banc ne calcule ni le bridge, ni e, ni la somme signée globale et ne revendique aucune borne sur D_N. Le seuil numérique u >= 1024 de l'assemblage extérieur ne s'applique pas à N = 10^8.

## Domaines finis et résultats

- Les coefficients H, leur regroupement par diviseurs et le transport du signe carré-libre sont contrôlés sur n = 1,...,3000 et y = 1,2,6,10,100, puis sur les 8192 axes n et m = N-n d'un échantillon déterministe de 4096 faces additives. Total : 47 768 contrôles de convolution littérale.
- Les identités P-Q = H_y(a)H_y(r), P+Q = U_y(a)U_y(r), et 2 min(P,Q) = U_y(a)U_y(r)-|H_y(a)H_y(r)| sont contrôlées pour les couples carré-libres premiers entre eux a,r <= 80, puis sur 935 tuples réellement admissibles à N = 10^8 et les quatre valeurs y = 2,6,10,100. Cela donne 7588 contrôles de petit domaine et 3740 contrôles au N demandé.
- L'identité de parité XOR est contrôlée sur 4866 produits de facteurs premiers entre eux, avec reconstruction exacte des produits CRT dépassant N.
- **Candidat A :** 1_prime(m) = (μ²(m)-μ(m))/2 - T3_alpha(m), sous m > 1 carré-libre alpha-rugueux et m < N <= alpha^4. Le banc parcourt **exhaustivement les 535 693 triprimes** 100 < p < q < r et pqr < 10^8. Tous les troisièmes premiers sont < 10 000, donc la liste complète de premiers jusqu'à 10 000 suffit. Le total avec petit domaine et faces additives est 539 648 contrôles.
- **Candidat B :** 1_prime(m) = 3 - 2 Ω(m) + Ω(m)(Ω(m)-1)/2, sous les mêmes hypothèses et donc 1 <= Ω <= 3. Les mêmes 539 648 contrôles réussissent.
- **Candidat C :** l'identité finie de Heath-Brown μ = 4M - 6(M*M*ζ) + 4(M*M*M*ζ*ζ) - (M*M*M*M*ζ*ζ*ζ), M = μ_{<=alpha}, réussit sur 18 866 cas avec n < alpha^4. Sa version avec reste +(μ-M)^{*4}*ζ^{*3} réussit sur 12 001 cas, y compris hors du support où le reste peut être supprimé.

Ces domaines sont exhaustifs pour les triprimes décrits et pour les petits domaines spécifiés. Les 4096 faces additives sont un échantillon reproductible, et ne sont pas présentées comme une vérification de toutes les faces n = 1,...,N-1. Aucune somme logarithmique n'est remplacée par une comparaison flottante.

## Hypothèses dont l'omission est falsifiée

L'annulation automatique à racine CRT fixée est fausse au N demandé. Le tuple

    a = 21 = 3*7, b = 13, r = 99 999 727 = 7951*12577, k = 1
    n = 273, m = 99 999 727, n+m = 100 000 000
    y = 2, W = 2, alpha = 100, module CRT a*r = 2 099 994 267

respecte les sélecteurs d'unité et de carré-liberté, le core a,b <= m et r > alpha. Il donne P = 4, Q = 0 et H_y(a)H_y(r) = 4. Il n'existe donc aucune masse négative interne à apparier pour ce tuple. Ce contre-exemple est compatible avec une future compensation entre tuples ou racines distinctes.

Pour le candidat A, l'omission de T3 est falsifiée par m = 101*103*107 = 1 113 121 : le poids de parité impaire vaut 1 alors que le détecteur premier vaut 0. La rugosité du seul r est insuffisante : r = 101*103 et k = 3 donnent m = 31 209, carré-libre mais non 100-rugueux ; le même oubli produit un poids premier erroné.

Pour le candidat B, l'extension à Ω = 4 est fausse : m = 101*103*107*109 = 121 330 189 a poids 1 et détecteur premier 0. Ce produit est hors du support m < 10^8. Le cas m = 1 est exclu dans le théorème.

Pour le candidat C, supprimer le reste hors de son support est faux dès alpha = 2 et n = 3^4 = 81 : les incidences sont [0,1,5,15], le polynôme vaut -1, μ(81) = 0 et le reste vaut 1. Le cas analogue alpha = 100, n = 101^4 = 104 060 401 dépasse N = 10^8 et a la même décomposition. Le terme de reste ne peut donc pas être omis à partir de ce seuil sans autre argument.

## Journal des corrections du banc

Deux exécutions préliminaires se sont arrêtées sur le garde-fou volontaire `factor(n) <= N`. Les produits CRT a*r, puis da*dr, peuvent dépasser N même lorsque a,r,da,dr sont dans le domaine de factorisation certifié. Les deux appels ont été remplacés par une reconstruction exacte de leurs tables d'exposants premiers à partir des deux factorisations certifiées. Il s'agit de corrections de domaine du banc ; aucune identité candidate n'a été contredite par ces exceptions. L'exécution finale réussit.

## Portée pour le juge Lean

Les candidats A, B et C passent le filtre numérique dans leurs domaines annoncés. A et B isolent explicitement une correction triprime ou un moment de Ω ; C est une identité de Heath-Brown standard, sans revendication de nouveauté. Aucune de ces validations ne fournit la compensation signée globale ni le budget D_N. La victoire demeure réservée au fichier Lean répondant au critère mathématique du protocole.

Reproduction :

    & 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\numerical\parity_checks.py'

SHA256 du script final : `6f201c898eb6bfc4e05703d02cdca4e211d1a7311cb11a0644192c90990cb8b2`.
