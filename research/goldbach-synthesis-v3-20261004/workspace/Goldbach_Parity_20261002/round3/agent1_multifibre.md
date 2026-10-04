# Agent 1 — boucle 3 : transport entre deux et quatre fibres additives

## Résultat de cette boucle

Le transport `m -> p*m`, donc `n -> N-p*m`, donne une identité exacte entre fibres différentes. Son extension à quatre fibres possède deux restes réels : les extrémités `d*m>=N` et les différences des poids premiers et des noyaux. Une orbite complète à quatre fibres, avec les véritables poids Type-II, est déjà défavorable à N=10^8. La compensation favorable bloc par bloc est donc fausse, même sans extrémité géométrique. Ce diagnostic ne réfute pas une compensation globale entre blocs.

Contrats antérieurs consultés : `one_sided_root_discrepancy_and_fixed_modulus_contract.txt`, `one_sided_actual_scalar_round3.txt` et `hh_four_signs_and_fibre_pressure_test.txt` du sprint15. Le module CRT `a*r`, les faces et les vrais coefficients restent requis. La simple positivité d'une énergie quadratique ne donne pas un signe au scalaire centré linéaire.

## Fonctions conservant le support

Fixons N, alpha et Q. Pour `0<m<N`, définissons

`B_N(m) = D_{alpha,Q}(m) - W_{alpha,Q}(N-m,m)`,

`f_N(m) = Lambda(N-m) - log(N-m)`,

`F_N(m) = chi_N(m) * f_N(m) * B_N(m)`.

Ici `chi_N(m)` contient tous les sélecteurs réellement présents : au minimum `gcd(N-m,N)=1`, et, lorsqu'un secteur particulier est étudié, ses fenêtres, faces, détecteurs carrés-libres et masque rugueux de la première variable. Il est évalué à chaque nouvelle fibre; on ne suppose pas qu'il est invariant.

Le scalaire direct U=V=1 est

`Sfull = sum_{0<m<N} mu(m) * F_N(m)`.

Les m non carrés-libres ont une contribution nulle. L'unité modulo N est préservée par `m->p*m` lorsque p ne divise pas N, parce que `gcd(N-m,N)=gcd(m,N)`. La carré-liberté de m est préservée si p ne divise pas m. La primalité de N-m, le masque rugueux de N-m, ses factorisations et ses faces ne sont pas préservés automatiquement.

## Candidat E : transport à deux fibres, avec extrémité explicite

Soit p premier ne divisant pas N. Sur les bases carrées-libres m avec p ne divisant pas m, on a exactement, lorsque p*m<N,

`mu(m)F_N(m) + mu(p*m)F_N(p*m)`

`       = mu(m) [F_N(m)-F_N(p*m)]`.                         (E1)

La partition de TOUTE la somme est

`Sfull = sum_{m squarefree, p∤m, p*m<N} mu(m) Delta_p F_N(m)`

`      + sum_{m squarefree, p∤m, m<N<=p*m} mu(m) F_N(m)`,     (E2)

où `Delta_p F(m)=F(m)-F(p*m)` et les sélecteurs originaux sont déjà dans F. Le second membre conserve une charge d'extrémité; elle n'est pas nulle par bijectivité. Pour p>=3, cette extrémité contient une longue plage de bases, et aucun petit coût ne résulte du seul changement de variables.

Ce transport ne peut pas être appliqué à un seul rectangle HH en déclarant sa fenêtre invariante : si le rectangle n'admet qu'un des deux termes, l'autre F vaut zéro et la différence devient exactement la charge de support à payer.

## Extension à quatre fibres

Soient p et q premiers distincts ne divisant pas N. Chaque entier carré-libre admet une base unique b première à p*q et un multiplicateur dans `{1,p,q,p*q}`. Posons

`A_N(b) = { d in {1,p,q,p*q} : d*b<N }`.

Alors

`Sfull = sum_{b squarefree, gcd(b,p*q)=1} mu(b)`

`          * sum_{d in A_N(b)} mu(d)*F_N(d*b)`.             (E3)

Pour les blocs complets `p*q*b<N`, la contribution est

`mu(b) [F_N(b)-F_N(p*b)-F_N(q*b)+F_N(p*q*b)]`

`           = mu(b) Delta_p Delta_q F_N(b)`.               (E4)

Les autres blocs donnent le reste exact de E3, avec seulement les multiplicateurs admissibles. Rien ne permet de remplacer A_N(b) par les quatre éléments sur ces blocs incomplets.

La transition change à la fois la première variable et le cofacteur complémentaire. Les modules CRT de chaque tuple sont ses propres produits `a*r`; aucun module commun à l'orbite n'a été établi.

## Terme de poids premier réellement restant

Sur un bloc complet, sans retirer les logarithmes ni les noyaux, écrivons `f_d=f_N(d*b)` et `B_d=B_N(d*b)`; les chi peuvent être incorporés à B_d. L'identité exacte du produit est

`Delta_p Delta_q(f*B)(b)`

` = B_1 Delta_p Delta_q f(b) + f_{pq} Delta_p Delta_q B(b)`

`   + (f_{pq}-f_p)(B_p-B_1)`

`   + (f_{pq}-f_q)(B_q-B_1)`.                            (E5)

Les deux derniers termes sont des commutateurs de poids; ils ne sont pas des erreurs négligeables par définition. Les différences B contiennent les variations de la face stricte, des caps et des masques `gcd(k,(N-d*b)*N)=1`.

La différence du seul poids de première variable est

`Delta_p Delta_q f(b)`

` = Lambda(N-b)-Lambda(N-p*b)-Lambda(N-q*b)+Lambda(N-p*q*b)`

`   + log[(N-p*b)(N-q*b)/((N-b)(N-p*q*b))]`.              (E6)

Le dernier logarithme est strictement positif pour un bloc complet b>0 : la différence entre son numérateur et son dénominateur est

`N*b*(p-1)*(q-1)>0`.

Cette courbure du logarithme est exacte, mais elle n'impose pas le signe de E4 : mu(b), B_1, les poids Lambda déplacés et les commutateurs E5 demeurent. Une courbure archimédienne favorable ne remplace pas une corrélation arithmétique des quatre formes `N-d*b`.

## Test exact à N=10^8 : une orbite complète défavorable

Prenons `N=100000000`, `alpha=100`, `Q=999999`, `b=101`, `p=3`, `q=7`.

Les quatre m sont 101,303,707,2121. Ils sont positifs, inférieurs à N, carrés-libres et premiers à N. Les premières variables sont aussi carrées-libres et premières à N :

| m | n=N-m | factorisation de n | fII(n) |
|---:|---:|---|---|
| 101 | 99999899 | 17*5882347 | -log n |
| 303 | 99999697 | 7*41*348431 | -log n |
| 707 | 99999293 | 577*173309 | -log n |
| 2121 | 99997879 | premier | 0 |

Le banc Agent 6 vérifie les factorisations et la primalité de la dernière valeur. Les noyaux sont calculés avec leurs préfixes littéraux, pas avec une approximation réelle.

Posons `K_N(m)=mu(m)*B_N(m)`. On a exactement

`K_N(101)=0`,

`K_N(303)=(1/2)*log 101`,

`K_N(707)=(1/3)*log 101 -(1/2)*log 7 +(1/2)*log 3`.       (E7)

Pour m=707, la vérification intermédiaire est

`D(707)=-log 7`,

`W(N-707,707)=-(1/2)*log 3 -(1/2)*log 7 -(1/3)*log 101`.

Le coefficient divisoriel à k=7 contient `1-1/phi(7)=5/6`. Une première communication avait mis 1/6 et inversé le signe du coefficient log 101; l'Agent 6 a détecté l'erreur, corrigée ici avant tout filtre accepté.

Les deux valeurs non nulles utiles de K sont strictement positives. Pour K_N(707), multiplier par 6 donne

`6*K_N(707) = log[101^2 * 3^3 / 7^3] > 0`,

car `101^2*27 > 343` (comparaison d'entiers exacte).

Le terme m=101 est nul par son noyau; celui m=2121 est nul par son poids fII. Le bloc complet est donc

`S_block = -(1/2)*log(99999697)*log 101`

`          - log(99999293)*[(1/3)*log 101 -(1/2)*log(7/3)]`

`        < 0`.                                         (E8)

Il n'y a aucune extrémité `d*b>=N` dans cette falsification. Les quatre n sont 2-rugueux, et tous les détecteurs carrés-libres n et m valent un. E8 réfute l'hypothèse « une orbite complète à quatre fibres du vrai scalaire Type-II est toujours favorable ». Il ne réfute aucune borne agrégée sur tous les blocs et n'affirme aucun résultat asymptotique à partir de N=10^8.

## Raccord exact et apport indépendant encore absent

Après le pont couvert original,

`D_N = -Sfull + 2*max(e,0)`.

E3 transforme exactement Sfull en blocs complets et charges de support, puis E5 isole leurs différences de poids premiers et de noyaux. La cible ne suit pas de ces transformations.

Un nouvel apport utile devrait estimer uniformément en N la projection signée des quatre valeurs Lambda de E6, avec les commutateurs E5 et les blocs incomplets de E3, dans le seul sens requis par le raccord. Cette information est une corrélation additive de formes affines; la primalité ne se transporte pas sous m->p*m. Une moyenne sur N ou une estimation de chacun des coefficients par une norme arbitraire ne fournit pas automatiquement ce contrôle pour chaque N.

La borne Type-I déjà acquise peut contrôler la partie logarithmique agrégée selon son contrat; elle ne contrôle pas par elle-même les Lambda déplacés. L'inversion quartique de mu fournit les coefficients courts exacts sur les bases, mais ne démontre pas une indépendance de ces quatre valeurs Lambda.

Imposer directement un majorant à l'ensemble E3 équivalent à la cible serait seulement la renommer. Une hypothèse générale sur la distribution des premiers dans ces formes et contre les vrais coefficients serait un apport indépendant, mais aucune preuve ni conséquence quantitativement suffisante n'a été obtenue ici. Il n'y a donc pas de pont conditionnel nouveau dont l'hypothèse soit établie ou indépendamment plus faible que le problème restant.

## Verdict de l'itération

Transport deux/four fibres : exact, caps et charges conservés.

Compensation favorable bloc par bloc : FAUSSE par E8.

Suppression des extrémités ou des différences de Lambda : injustifiée.

Nouvelle information quantitative sur le cumul signé complet : NON OBTENUE.

Recommandation : conserver E1–E8 et le banc de falsification; ne pas compiler une implication qui supposerait déjà la minoration de Sfull. Une formalisation éventuelle d'E3 serait un certificat de partition, pas une victoire.
