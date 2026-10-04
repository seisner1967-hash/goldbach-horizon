# Agent 2 — inversion quartique de Möbius à frontière conservée

Documents lus : CONTRACT.md, agent1.md, monographie (sections 5–6 et appendice A), continuation du 1 octobre 2026. Le support complet, les vrais coefficients et les modules CRT ar sont conservés. La famille des identités finies de Heath–Brown est déjà dans le corpus (appendice A, phase 6) : aucune nouveauté mathématique n'est revendiquée pour cette identité.

## Candidat C : identité arithmétique sur tous les entiers du domaine

Soit alpha >= 1 un entier. Les fonctions arithmétiques valent zéro en 0. On note la convolution de Dirichlet par *, delta son unité, zeta la fonction constante 1 sur les entiers positifs et mu la vraie fonction de Möbius, donc mu*zeta=delta. Posons

M = mu * 1_{n<=alpha}  (ici le produit écrit est POINT PAR POINT),
L = mu - M,
E = delta - zeta*M = zeta*L.

L'identité générale, sans hypothèse de taille sur n, est

mu = 4 M - 6 M^{*2}*zeta + 4 M^{*3}*zeta^{*2}
          - M^{*4}*zeta^{*3} + L^{*4}*zeta^{*3}.                 (C0)

Le dernier terme est le reste exact, pas une erreur supposée petite. Chaque facteur L est nul sur n<=alpha. Le reste est donc nul pour

1 <= n < (alpha+1)^4.                                           (C1)

Pour 1<=n<N<=alpha^4, on obtient en particulier

mu(n) = 4 M(n) - 6 (M^{*2}*zeta)(n)
         + 4 (M^{*3}*zeta^{*2})(n)
         - (M^{*4}*zeta^{*3})(n).                               (C2)

Les unités sont incluses. Le terme j est la somme sur toutes les factorisations ORDONNÉES

a1*...*aj*b1*...*b_{j-1}=n,
1<=ai<=alpha, 1<=bi,

avec poids mu(a1)*...*mu(aj) et coefficient (-1)^(j-1) binom(4,j). Aucune hypothèse de rugosité ni de carré-liberté de n n'est introduite. C'est la différence de portée pertinente avec les candidats A et B.

## Preuve exacte

Puisque zeta*mu=delta, on a delta-E=zeta*M et donc M=mu*(delta-E). Dans l'anneau commutatif des fonctions arithmétiques,

M*(delta+E+E^{*2}+E^{*3}) = mu*(delta-E^{*4}).

L'expansion des quatre puissances de delta-zeta*M donne les coefficients 4,-6,4,-1. De plus

mu*E^{*4} = mu*zeta^{*4}*L^{*4} = zeta^{*3}*L^{*4}.

Cela prouve C0. Si un terme de L^{*4}*zeta^{*3} en n est non nul, les quatre arguments des L sont au moins alpha+1. Leur produit est au moins (alpha+1)^4 ; les arguments des trois zeta sont positifs. Donc n>=(alpha+1)^4, ce qui prouve C1. La preuve du support porte sur les quatre facteurs L, pas sur une assertion générale concernant les grands cofacteurs.

## Application à la frontière r>alpha

Dans le noyau divisoriel original, k*r=m, k<=Q et alpha*k<m équivalent à r>alpha, avec les contraintes divisorielles conservées. Comme r<=m<N<=alpha^4, C2 s'insère point par point dans le facteur mu(r). Le facteur mu(m)^2, le sélecteur d'unité, le masque rugueux de la première variable, les poids logarithmiques et tous les caps demeurent dehors, exactement comme ils étaient. La même identité peut être insérée à m dans le terme harmonique lorsque celui-ci porte mu(m).

Pour une fonction de poids c(r) comprenant le support réel, il vient littéralement

sum_{alpha<r<N} c(r) mu(r)
 = 4 sum c(r) M(r)
   -6 sum c(r) (M^{*2}*zeta)(r)
   +4 sum c(r) (M^{*3}*zeta^{*2})(r)
   -  sum c(r) (M^{*4}*zeta^{*3})(r).

Le premier terme est nul sur r>alpha. Dans les trois autres, il faut conserver r=a1...aj b1...b_{j-1} dans c(r) et dans le module CRT original ar. Les paramètres ai sont courts ; leur produit et le module CRT ne sont pas forcément courts. Remplacer ar par un produit de seulement certains ai serait une modification injustifiée.

L'identité retire donc une occurrence de mu sur un long argument au profit de deux à quatre facteurs mu courts et de un à trois facteurs libres. Elle donne une décomposition multi-linéaire exacte sur le support complet. Elle ne donne pas une contraction du moment additif signé : c(r) couple toujours la factorisation au premier de l'autre axe et aux faces mobiles.

## Tests falsifiables transmis à l'Agent 6

N=100000000 et alpha=100. Tester exactement les coefficients entiers de C2 sur un domaine déterministe déclaré, y compris r=102 (présence de petits facteurs malgré r>alpha), des premiers r>alpha, des carrés et des produits de quatre facteurs dont certains sont courts.

Pour un premier p>alpha, les trois incidences de C2 valent respectivement 1, 2 et 3, car les ai sont tous 1 et p peut être placé dans un des facteurs bi. Donc -6+4*2-3=-1, comme mu(p). Pour n=1, 4-6+4-1=1.

Test négatif du domaine : n=101^4=104060401, juste hors N=10^8. Dans C0, le reste vaut exactement 1 (les quatre facteurs L sont tous 101 et les trois facteurs zeta tous 1). mu(n)=0 ; C2 sans reste y vaut -1. Cela réfute toute extension au-delà du domaine autorisé en oubliant C0. Un test plus petit et indépendant utilise alpha=2, n=3^4=81.

Ces tests sont des tests de l'identité finie, jamais une preuve d'annulation sur tous les N.

## Tentative de transport transversal CRT : défaut conservé

Un transport bijectif entre tuples admissibles ne change pas la somme des poids signés ; un transport partiel décompose exactement la somme initiale en contribution transportée plus défaut de support. Si les logarithmes et les poids diffèrent, le défaut inclut aussi leurs différences. Une écriture en différences télescopiques s'annule seulement sur les cycles intégralement admissibles avec les poids correspondants. Les extrémités rencontrant r=alpha, les caps ou un masque deviennent des charges de bord.

L'exemple P=4,Q=0 à (a,r,y)=(15,77,2) interdit de présumer que le défaut se neutralise fibre par fibre. Le lemme nouveau nécessaire serait une borne unilatérale de la charge transportée et du défaut, à la fois, avec les modules ar originaux. Aucun transport explicite muni de cette borne n'a été obtenu ; il ne faut pas déclarer le défaut nul par choix de coordonnées.

## Lemme manquant et statut

Après C2, le lemme à obtenir est une borne de la combinaison signée des trois incidences sur la convolution additive complète : coefficients -6,+4,-1, vraies variables courtes ai, facteurs libres bi, modules CRT ar, coprimalité, logarithmes et faces mobiles. Une majoration séparée par valeurs absolues peut perdre les annulations exactes. Une distribution uniforme dans les seules petites variables ne contrôle pas automatiquement le produit r ni son couplage à N-n.

Le raccord couvert doit également demeurer celui de la monographie : D_N=-Sfull+2 max(e,0). Ni C0 ni C2 ne prouve une minoration suffisante de Sfull ni le paiement de max(e,0). La cible D_N<=N/(256 log N log log N) reste une obligation arithmétique indépendante.

Statut : candidat exact falsifiable, standard dans son origine, dont l'insertion frontière conserve le domaine complet. Formalisation recommandée après filtre numérique. Résultat partiel si compilé, aucune victoire revendiquée.
