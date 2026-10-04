# Agent 1 — boucle 4 : uniformité supérieure et rang du support HH

## Résultat

Le mécanisme étudié est différent des transports locaux : conserver les quatre coefficients de Möbius dans un système affine de complexité finie et appliquer l'uniformité supérieure. L'identification exacte n'est pas obtenue. Une rigidité de rang prouve pourquoi les charts entièrement affines du support à N fixé n'ont pas les directions indépendantes requises. Les charts rationnels ou non linéaires ne sont pas exclus, mais leurs quotients arithmétiques et sélecteurs restent à contrôler. Aucune nouvelle borne de D_N n'est déduite.

## Entrées primaires effectivement lues

Dans [I, version arXiv v4](https://arxiv.org/html/2204.03754v4), théorème 1.1(i), la corrélation de mu avec une nilsuite de degré et dimension fixés est `O(delta^(-O(1))*H/log^A X)` pour `H>=X^(5/8+epsilon)`, avec coût explicite de complexité delta et constantes potentiellement inefficaces. Le théorème 1.5 donne l'uniformité Gowers; le théorème 1.7 et la remarque 1.8 traitent des formes affines à coefficients bornés et à gradients deux à deux indépendants. La [version publiée Cambridge](https://www.cambridge.org/core/journals/forum-of-mathematics-pi/article/higher-uniformity-of-arithmetic-functions-in-short-intervals-i-all-intervals/6DF08E2A3EFABB2DD0DA6CDA38649B18) a aussi été consultée.

Dans [II, version v2](https://arxiv.org/html/2411.05770v2), théorème 1.1(i)–(ii), le seuil `H>=X^(1/3+epsilon)` vient avec un ensemble exceptionnel de positions x. C'est un résultat pour presque tous les intervalles. Il ne transforme pas une fibre choisie par chaque N en intervalle garanti non exceptionnel.

Ces paragraphes résument les théorèmes externes. Les dérivations suivantes sont propres à l'application au support original.

## Support exact à identifier

Le développement HH est

`b*u*v*x + k*s*t*z = N`,

avec coefficients `mu(u)*mu(v)*mu(s)*mu(t)` et `u,v,s,t>y`. Les variables sont strictement positives. Le poids réel conserve `log b*log(s*t*z)`, la carré-liberté du produit complémentaire, le masque rugueux de la première variable, l'unité modulo N, les intervalles des axes, la face `r>alpha`, les caps et le module CRT `a*r`, où `a=u*v*x`, `r=s*t*z`.

Il ne suffit pas que les quatre fonctions mu soient appliquées à des coordonnées distinctes de l'espace ambiant. La moyenne réelle est sur l'hypersurface multiplicative ci-dessus, avec ses sélecteurs. La remplacer par une moyenne sur le cube ambiant introduit un poids de contrainte non linéaire. Les théorèmes de systèmes affines ne donnent pas une borne contre n'importe quel tel poids.

## Candidat G1 : charts affines conservant les quatre signes

Supposons que toutes les variables `b,u,v,x,k,s,t,z` deviennent des formes affines de paramètres libres `h in Q^d`, et que leur identité HH soit satisfaite identiquement sur un domaine de dimension pleine. Une identité polynomiale satisfaite sur un ouvert s'étend en identité sur Q^d.

La proposition de rang pertinente est la suivante.

**Lemme de rigidité affine.** Soient `A_1,...,A_l` et `B_1,...,B_m` des formes affines sur Q^d, d>=2, satisfaisant

`prod_i A_i(h) + prod_j B_j(h) = N != 0` pour tout h.

Supposons qu'il existe un point h0 où les deux produits sont non nuls. Alors tous les gradients non nuls de ces formes appartiennent à une même droite vectorielle, ou tous les gradients sont nuls.

La non-dégénérescence est essentielle. Une branche contenant un facteur identiquement nul pourrait garder des gradients arbitraires sans contribuer à l'identité. Le point h0 existe sur tout chart contenant un tuple HH strictement positif.

### Preuve du cœur par intersection de deux hyperplans

Si un gradient de A_i et un gradient de B_j étaient indépendants, leurs hyperplans affines `A_i=0` et `B_j=0` se rencontreraient. Au point d'intersection, les deux produits seraient nuls, donnant N=0 : contradiction. Donc tous les gradients de branches opposées sont dépendants.

Si une branche possède un facteur non constant alors que l'autre branche a tous ses facteurs constants, son produit serait constant, non nul grâce à h0. Un produit de polynômes affines non nuls est constant seulement lorsque chaque facteur est constant (degré total additif dans l'anneau intègre Q[h]). C'est une contradiction. Dès qu'un facteur varie, chaque branche possède donc un gradient non nul.

En choisissant un gradient non nul dans chaque branche, les dépendances croisées forcent tous les gradients de la première branche, puis tous ceux de la seconde, sur la même droite. Cela prouve le lemme.

Dans deux paramètres, le cœur est falsifiable en arithmétique rationnelle : pour

`A=a*X+b*Y+c`, `B=d*X+e*Y+f`, `det=a*e-b*d != 0`,

leur point commun est

`X=(b*f-c*e)/det`, `Y=(c*d-a*f)/det`.

Ces formules permettent un certificat Lean court : si une identité `A*R+B*S=N` vaut pour tous X,Y avec N non nul, alors det=0, même si R et S sont seulement des fonctions partout définies. Une telle preuve est un certificat du défaut de rang, pas un contournement de la parité.

### Conséquence exacte pour HH

Appliquer le lemme aux quatre facteurs de chaque branche HH impose que les gradients des quatre arguments `u,v,s,t` soient colinéaires dans un chart entièrement affine. Ils ne constituent donc pas le système affine à gradients deux à deux indépendants exigé par le théorème primaire. L'augmentation du nombre de paramètres libres ne change pas ce fait.

Ce résultat porte sur les charts affines et sur leur identité à N fixé. Il n'interdit pas toute approche d'uniformité, toute variété non linéaire ou toute moyenne sur N. Il interdit seulement l'identification proposée sans nouveau transfert.

## Candidat G2 : fixer des facteurs et garder une ligne arithmétique exacte

Fixer `b,u,x,k,s,z` donne

`A*v+B*t=N`, avec `A=b*u*x`, `B=k*s*z`.

Sur le support d'unité, `gcd(A,B)=1`. En effet, un diviseur commun d'A et de B divise n, m et N, alors que `gcd(n,N)=1`. Toute solution entière est donc de la forme

`v=v0+B*h`, `t=t0-A*h`.

Les deux coefficients variables deviennent `mu(v0+B*h)` et `mu(t0-A*h)`. Leurs gradients sont proportionnels en une variable; ils ne satisfont pas l'hypothèse du système affine externe. Une faible norme Gowers individuelle ne suffit pas à contrôler la corrélation de deux fonctions testées sur ces deux formes parallèles.

Le coût du domaine est aussi concret. Dans le secteur central `x=z=1`, `u,v,s,t` de taille `N^(3/8)`, `b,k` de taille `N^(1/4)`, on a A,B de taille `N^(5/8)`. Une fenêtre de v ou t de largeur `N^(3/8)` donne une fenêtre de h de longueur au plus `O(N^(-1/4))`. En général cette fibre contient au plus un point. L'estimation maximale sur progressions du théorème I est normalisée par la longueur H de l'intervalle ambiant, pas par le nombre de points d'une progression aussi espacée. Elle ne crée pas d'annulation sur une fibre à un point.

Il faut donc conserver d'autres variables pour obtenir une moyenne substantielle, mais cela réintroduit le produit et le défaut de rang du candidat G1.

## Candidat G3 : conserver un chart rationnel ou un poids polynomial

Par exemple,

`t=(N-b*u*v*x)/(k*s*z)`

conserve l'égalité exacte lorsque le quotient est entier. Il impose simultanément

`k*s*z | N-b*u*v*x`,

les bornes de t, ses masques et le coefficient `mu((N-b*u*v*x)/(k*s*z))`.

Ce coefficient est une fonction de Möbius évaluée sur un quotient à paramètres mobiles. Il n'est pas une nilsuite de complexité bornée et n'est pas mu évaluée sur une forme affine dans les variables libres. Le théorème de décorrélation ne peut pas l'absorber comme observable sans une preuve supplémentaire. Une représentation artificielle d'un mot arithmétique fini par une nilsuite de complexité croissante pourrait perdre le gain à travers `delta^(-O(1))`.

Une ouverture différente consiste à garder le poids polynomial `b*u*v*x+k*s*t*z-N` et à introduire une phase de Fourier de la contrainte. Les phases en une coordonnée sont alors polynomiales, mais les autres trois signes, le module et les masques se couplent à cette coordonnée. Une estimation d'un seul facteur mu contre une phase ne fournit pas le gain de densité du niveau additif N. Une estimation simultanée, conservant ce niveau et tous les signes, serait un nouveau lemme à démontrer.

## Test falsifiable de la linéarisation à N=10^8

Le tuple

`b=13, u=3, v=7, x=1, k=1, s=7951, t=12577, z=1`

satisfait exactement `273+99999727=100000000`. Les deux produits sont carrés-libres, unités modulo N, et la première variable est 2-rugueuse; `r=99999727>100`. Il fournit le point positif requis par la non-dégénérescence.

Dans le secteur `x=z=1`, la différence mixte exacte est

`Delta_u(h) Delta_v(j) [b*u*v+k*s*t-N] = b*h*j`.

Pour `u:3->11`, `v:7->17`, on obtient `13*8*10=1040`, non zéro. Les arguments u et v aux quatre coins sont des premiers distincts; leur seule variation ne reste toutefois pas sur le niveau N. Remplacer le produit par sa linéarisation en oubliant cette différence mixte déplace le niveau additif. Ce test porte sur l'identification géométrique, pas sur une fréquence asymptotique.

Le banc numérique doit aussi inclure le cas dégénéré `u=X, v=Y, x=0` avec branche complémentaire constante N : rang total 2 et identité valide, mais aucun point où les deux produits sont non nuls. Cela vérifie que l'hypothèse ajoutée n'est pas superflue.

## Lemme réellement restant et relation à D_N

Le raccord du cadre demeure

`D_N=-Sfull+2*max(e,0)`.

Aucun des candidats G1–G3 ne fournit une minoration de Sfull. Le théorème primaire d'uniformité est une information arithmétique indépendante, mais il ne s'applique pas au vrai HH par la seule identification des quatre signes.

Un apport nouveau pourrait prendre l'une des deux formes précises suivantes :

1. Un transfert exact du niveau multiplicatif HH vers un système de formes affines à gradients indépendants, avec contrôle quantitatif de ses quotients, masques, frontières et coûts de complexité. Les charts entièrement affines ne peuvent réaliser ce transfert à N fixé.
2. Une estimation de la corrélation sur le niveau multiplicatif lui-même, gardant les quatre coefficients mu et la densité de la contrainte, dans le sens unilatéral requis. Cette estimation n'est pas un corollaire des seules normes Gowers individuelles.

Le second article fournit des moyennes et ensembles exceptionnels; pour l'employer à chaque N, il faudrait en outre contrôler le poids réel porté par ses fibres exceptionnelles. Leur petite mesure ne signifie pas que la fibre choisie n'en fait pas partie.

## Verdict

Mécanisme Gowers/nilsuites : exploré avec les théorèmes primaires.

Chart affine exact de complexité finie pour les quatre signes : identification refusée par rigidité de rang, sous non-dégénérescence explicite.

Chart rationnel ou polynomial : non exclu, mais corrélation arithmétique nouvelle restante.

Gain quantitatif sur l'objet D_N original : NON OBTENU.

Il n'y a aucune revendication de no-go global, de nouveauté analytique ni de victoire Lean.
