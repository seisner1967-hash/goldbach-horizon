# Agent 1 — boucle 5 : déterminant, classes de réseau et vrai poids de Möbius

## Verdict préalable

Une bijection entière exacte vers des matrices de déterminant N, puis vers une classe de réseau cyclique et un changement de base de déterminant un, est obtenue ci-dessous. Les quatre signes restent attachés au changement de base. Ils ne sont pas constants dans une classe de réseau. Cette représentation ne fournit aucun gain quantitatif nouveau pour D_N; sa formalisation serait PARTIAL.

Documents consultés : audits des Agents 3 et 4 de la boucle 4, et contraintes Arbor par `arbor_state.py view --format constraints` (lecture seule). Les défauts composites de Gauss, les faces et le module CRT ar ne sont pas supprimés.

## Bijection déterminant exacte, à paramètres b,k,x,z fixés

Tous les facteurs sont strictement positifs. Posons

`B=b*v*x`, `D=k*t*z`,

`M = [[u,s],[-D,B]]`.

Alors

`det M = u*B+s*D = b*u*v*x+k*s*t*z`.

La correspondance entre tuples `(u,v,s,t)` et matrices est bijective lorsque les paramètres positifs b,k,x,z sont fixés, en conservant les restrictions

`b*x | B`, `k*z | D`,

`v=B/(b*x)`, `t=D/(k*z)`.

Ces quotients sont entiers exacts. Une matrice générale de déterminant N ne représente pas un tuple admissible si ces divisibilités ou les autres sélecteurs échouent.

Le support original est toujours celui du tuple reconstitué : `u,v,s,t>y`, `a=u*v*x`, `r=s*t*z`, `n=u*B`, `m=s*D`, `r>alpha`, `k<=Q`, face stricte, carrés-libres et unités, fenêtres et core. Le poids réel est

`chi(tuple) * mu(u)*mu(v)*mu(s)*mu(t) * log b * log r`.

Le module CRT demeure `a*r`, pas det M, ni une entrée de la matrice.

## Réduction entière à une classe cyclique

Sous `gcd(n,N)=1` et `n+m=N`, on a `gcd(n,m)=1`. Chaque facteur de n ou m est une unité modulo N; en particulier B,D,u,s. De plus `gcd(B,D)=1`.

Choisissons le représentant canonique

`lambda = s*B^{-1} mod N`, `0<=lambda<N`.

lambda est une unité modulo N. On a les divisibilités exactes

`N | s-lambda*B`, `N | u+lambda*D`.

Pour la seconde, multiplier par B donne

`B*(u+lambda*D)=N+D*(lambda*B-s)`,

puis annuler B modulo N, puisque B est une unité.

Définissons les quotients entiers

`A=(u+lambda*D)/N`, `C=(s-lambda*B)/N`,

`H_lambda=[[N,lambda],[0,1]]`,

`G=[[A,C],[-D,B]]`.

Alors

`A*B+C*D=1`, `det G=1`, `M=H_lambda*G`.                (H1)

La classe de réseau engendrée par les colonnes est

`L_lambda={(X,Y) in Z² : X=lambda*Y mod N}`,

et l'information sur les bases demeure dans G.

## Énoncé entier précis proposé pour Lean

Les variables N,lambda,u,s,B,D,A,C sont des entiers. Sous

`N>0`, `u*B+s*D=N`,

`N | u+lambda*D`, `N | s-lambda*B`,

prendre A et C comme les quotients entiers ci-dessus. Le certificat doit prouver

`N*A-lambda*D=u`,

`N*C+lambda*B=s`,

`A*B+C*D=1`,

et les quatre égalités d'entrées de `H_lambda*G=M`.

Le sens inverse prend `A*B+C*D=1` et définit

`u=N*A-lambda*D`, `s=N*C+lambda*B`.

Il prouve `u*B+s*D=N` et les divisibilités par N. Avec N non nul, les deux constructions récupèrent A,C,u,s exactement. La preuve de l'existence canonique de lambda utilise l'inverse de B modulo N et doit être distinguée de ce cœur conditionné par les deux divisibilités.

Pour la bijection des tuples, ajouter

`b,k,x,z>0`, `B,D>0`, `b*x|B`, `k*z|D`,

et reconstruire v,t par leurs quotients. Définir explicitement `support_G` comme `support_tuple(u,v,s,t,b,k,x,z)`, avec les substitutions affichées. L'égalité de poids à formaliser est une substitution littérale :

`mu(N*A-lambda*D) * mu(B/(b*x))`

` * mu(N*C+lambda*B) * mu(D/(k*z))`

` * log b * log((N*C+lambda*B)*(D/(k*z))*z)`.

Elle conserve `chi` évalué sur ce même tuple et le module `a*r`. Il ne faut pas ajouter un théorème affirmant que le poids ne dépend que de lambda.

## Falsification exacte de la constance sur classe

À N=100000000, le point fourni est

`b=13,u=3,v=7,x=1,k=1,s=7951,t=12577,z=1`.

Il donne

`M=[[3,7951],[-12577,91]]`,

`lambda=73626461`,

`G=[[9260,-67],[-12577,91]]`,

avec `9260*91-67*12577=1` et `M=H_lambda*G`.

Les quatre arguments de mu sont des premiers; le signe développé vaut +1.

Appliquons le changement de base entier

`T=[[1,-78],[0,1]]`, `det T=1`.

La nouvelle matrice `M'=M*T` a

`u'=3`, `D'=12577`, `s'=7717`, `B'=981097`,

et conserve le réseau L_lambda. Les divisibilités requises donnent

`v'=B'/13=75469=163*463`, `t'=12577`.

Le nouveau signe réel est

`mu(3)*mu(75469)*mu(7717)*mu(12577)=-1`.

Il s'agit d'une falsification de la constance du coefficient sur une classe de réseau, utilisant les vraies valeurs de mu. Les deux tuples ont bien les sélecteurs de base :

| tuple | n | m | a | r | signe développé |
|---|---:|---:|---:|---:|---:|
| original | 273 | 99999727 | 21 | 99999727 | +1 |
| transformé | 2943291 | 97056709 | 226407 | 97056709 | -1 |

Les deux n et m sont carrés-libres et unités modulo N; n est 2-rugueux. Les facteurs signés dépassent y=2. Le core `a,b<=m`, la face r>100 et le cap k=1<=999999 sont conservés. Les logarithmes et les modules ar changent réellement. Une fenêtre dyadique qui sélectionne un seul tuple doit le faire dans chi; elle n'est pas déclarée invariante.

Des changements de base plus petits montrent aussi le besoin des masques : le shear -26 donne une première variable divisible par 3², et le shear -52 une première variable divisible par 5, donc non unité modulo N. La classe du réseau seule ne sait pas enlever ces éléments.

L'Agent 6 teste H1, les divisibilités, les factorisations, les masques et la conservation de lambda. Un changement de signe dans la même classe ne réfute PAS une annulation après sommation pondérée des bases; il réfute seulement son invariance automatique.

## Ce qu'une somme de classes signées représente exactement

Le véritable cumul serait

`sum_{lambda unit mod N} sum_{G in SL2(Z)} weight_N,b,k,x,z(lambda,G)`,

avec support_G fini et tous les anciens sélecteurs. On peut définir la somme intérieure comme un poids de classe après avoir réellement additionné toutes les bases admissibles. Cette périodisation est bien définie; l'exemple précédent ne l'interdit pas. Mais le contrôle signé de cette somme intérieure est alors une obligation nouvelle, pas un coefficient scalaire déjà connu.

Aucune identification avec une observable automorphe fixe, de normes contrôlées, n'a été obtenue. Les valeurs de mu, les quotients entiers et les masques sont encore des données arithmétiques à dépendance N. Aucun gain spectral ni norme Hecke n'est importé dans ce rapport.

## Coût quantitatif avant toute revendication

Le seul nombre de classes lambda autorisées est `phi(N)`, soit 40000000 à N=10^8. Une prise de valeurs absolues sur ces classes ne crée aucun gain. L'indice de réseau N ne remplace pas le module CRT ar dans les erreurs arithmétiques.

Dans le modèle central `x=z=1`, u,v,s,t ont taille `N^(3/8)` et b,k taille `N^(1/4)`. Pour b,k,u,s fixés, l'équation

`b*u*v+k*s*t=N`

donne une progression en v de pas k*s, parce que `gcd(b*u,k*s)=1` sur toute solution unitaire. Sa fenêtre v a largeur de l'ordre de `N^(3/8)`, contre un pas de l'ordre de `N^(5/8)`. Le comptage élémentaire est donc au plus un point par choix b,k,u,s.

Payer ces choix séparément donne un coût `N^(1/4+1/4+3/8+3/8)=N^(5/4)`, avant les logarithmes; avec leurs amplitudes, `O(N^(5/4)*L²)` pour cette route brute. Cette borne n'est pas proposée comme optimale : les bornes positives antérieures peuvent être meilleures. Elle montre que la seule bijection de réseau n'a pas fourni le gain de puissance ou de logarithmes requis. Il manque au moins un gain N^(1/4), puis le budget logarithmique, pour améliorer ce coût brut jusqu'à la cible.

## Relation au résidu et lemme indépendant restant

Le raccord reste `D_N=-Sfull+2*max(e,0)`. La bijection H1 réordonne les vrais termes HH; elle n'estime ni leur écart au modèle, ni leur cumul unilatéral après les termes non couverts. Pour utiliser une méthode de Hecke, il faudrait un théorème contrôlant les sommes de bases avec leurs quatre vrais signes, leurs quotients et leurs faces, avec un coût inférieur à l'amplitude disponible. C'est précisément l'information indépendante absente.

## Proposition différente pour une prochaine boucle, non exécutée ici

Une piste analytique distincte est un critère d'orthogonalité par **autocorrélations de dilatations premières** du profil arithmétique complet, plutôt qu'une compensation favorable entre deux fibres. Le [théorème 2 de Bourgain–Sarnak–Ziegler](https://arxiv.org/pdf/1110.0992) contrôle une somme contre une fonction multiplicative bornée si les corrélations du profil aux arguments p*m et q*m sont petites. Son application aux horocycles ne donne pas de taux.

Pour notre objet, il faudrait construire et normaliser le profil réel F_N conservant tous les poids, puis prouver une estimation indépendante de `sum_m F_N(p*m)*conj(F_N(q*m))`, p!=q, avec toutes les extrémités. Le théorème fini exige un ensemble de premiers et des seuils dépendant de la précision; la conclusion qualitative seule ne paie pas `N/(256 log N log log N)`. Cette piste évite la fausse fermeture de signe locale, mais n'est pas encore un résultat quantitatif. Elle est proposée comme mécanisme différent à examiner, sans présumer ses hypothèses.

## Statut

Bijection HNF entière avec poids attaché à G : candidat exact envoyé pour filtre et formalisation.

Poids constant sur classe lambda : FAUX par le shear -78.

Annulation pondérée dans chaque classe ou spectralement entre classes : NON RÉFUTÉE, mais NON ÉTABLIE.

Gain quantitatif nouveau sur D_N : NON OBTENU.

Aucune victoire n'est revendiquée à partir de la représentation 2x2 ou de sa compilation éventuelle.
