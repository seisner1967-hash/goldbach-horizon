# Agent 1 — deuxième boucle : commutateur des fibres et reste harmonique

## Résultat

Une identité de transport multiplicatif exacte a été dérivée sur la frontière originale, sans supposer m rugueux. Elle ne supprime pas le terme positif critique : le facteur harmonique `1/phi(k)` laisse un commutateur non nul, même lorsque les deux éléments de l'orbite sont admis. L'inversion quartique de l'Agent 2 conserve ce commutateur. Aucun nouveau lemme quantitatif suffisant pour la cible n'a été obtenu dans cette boucle.

## Objet original conservé

Écrivons `m=N-n`, avec `gcd(n,N)=1`, `alpha>=1` et `Q>=1`. Posons

`A(k) = 1_{k<=Q} 1_{alpha*k<m}`,

`I(k) = 1_{k|m}`,

`C(k) = 1_{gcd(k,n*N)=1}`.

Le défaut littéral est

`D(m)-W(n,m) = sum_k A(k) mu(k) log(k/m) [I(k)-C(k)/phi(k)]`.

Les divisions dans les logarithmes sont réelles, les caps et la face stricte restent entiers. Dans une expansion CRT de la première variable, le module est toujours `a*r`, avec `r=m/k`. Le transport ci-dessous modifie r et change donc ce module : chaque terme conserve son propre `a*r`.

## Candidat D : transport à un premier avec commutateur explicite

Supposons m carré-libre et `m=p*M`, où p est premier. Alors `p` ne divise ni M ni n*N. Pour un entier t premier à p, regroupons les termes `k=t` et `k=p*t`. Ils ont les propriétés exactes

`mu(p*t)=-mu(t)`,

`phi(p*t)=(p-1)*phi(t)`,

`I(t)=I(p*t)=1_{t|M}`,

`C(t)=C(p*t)`.

Avec `L=log(t/m)`, `A0=A(t)`, `A1=A(p*t)`, `I0=1_{t|M}` et `C0=C(t)`, leur contribution est exactement

`mu(t) * { I0 [A0*L-A1*(L+log p)]`

`           - C0/phi(t) [A0*L-A1*(L+log p)/(p-1)] }`.       (D0)

Cette formule couvre aussi `A1=0` ou `A0=0` : aucun défaut de frontière n'est perdu. Lorsque les deux éléments sont admis, elle devient

`mu(t) * { -I0*log p + C0/phi(t) * [(2-p)/(p-1)*L + log p/(p-1)] }`.  (D1)

Le premier terme est le crédit logarithmique exact de l'orbite divisorielle complète. Le second contient un coefficient de L non nul pour p>2. Sur le support unitaire et N pair, un premier p divisant m est justement impair. La seule valeur p=2 qui annulerait ce coefficient n'est donc pas disponible dans ce secteur.

Il s'agit d'un commutateur concret entre le transport multiplicatif et la projection harmonique : les valeurs totientes aux deux termes diffèrent d'un facteur p-1. Le retrancher serait changer le noyau original.

Les facteurs carrés-libres n'ont pas été introduits pour simplifier le problème : les contributions de `mu(m)` sont déjà nulles lorsque m n'est pas carré-libre. D0 est donc pertinent pour tout le support non nul de ce coefficient.

## Falsification exacte d'une fermeture favorable

Prenons le N demandé pour les diagnostics :

`N=100000000`, `alpha=100`, `Q=999999`,

`m=303=3*101`, `n=99999697=7*14285671`.

On a `gcd(n,N)=1`, m carré-libre, et n n'est pas une puissance première (la valuation en 7 vaut 1 et n>7). Le préfixe littéral est `k=1,2,3` car `100*k<303`. Le terme k=2 est nul : il ne divise pas m et ne satisfait pas l'unité. Les deux termes k=1 et k=3 sont admis.

On calcule exactement

`D(303) = -log 3`,

`W(n,303) = -log 3 - (1/2)*log 101`,

`mu(303)*(D-W) = (1/2)*log 101 > 0`.                  (D2)

Le terme Type-II authentique à U=V=1 est `fII(n)=Lambda(n)-log n=-log n`. Cette seule contribution à Sfull vaut donc

`-(1/2)*log(n)*log(101) < 0`.

Elle est défavorable à une minoration point par point de Sfull. Ceci est une falsification de la proposition « l'orbite complète, ou la projection du vrai coefficient, rend chaque terme de frontière favorable ». Ce n'est PAS une réfutation de la borne globale de D_N. Les autres valeurs de n peuvent compenser, et N=10^8 est sous les seuils analytiques de la monographie.

Dans une fibre de première variable prenant `a=7`, les modules CRT des deux termes sont `7*303=2121` et `7*101=707`. Utiliser un module unique après ce transport serait une modification du domaine.

## Pourquoi l'inversion quartique ne neutralise pas D2

Sur r>alpha, l'Agent 2 donne

`mu(r)=-6(M^2*zeta)(r)+4(M^3*zeta^2)(r)-(M^4*zeta^3)(r)`.

Pour le premier long `r=101`, les trois incidences sont 1,2,3; la combinaison est exactement `-6+8-3=-1`. La cancellation élimine des multiplicités de factorisation, mais ne change ni le coefficient final ni sa projection contre le noyau réel. D2 subsiste.

Sous la forme `E=delta-zeta*M`, l'inversion écrit `mu=M*(delta+E+E^2+E^3)` dans le domaine où `E^4` est nul. La nilpotence porte sur la convolution **multiplicative** des fonctions arithmétiques. Le noyau additif `N-n`, les unités et les caps ne commutent pas avec cette convolution. La simple nilpotence ne produit donc pas une petite valeur de sa projection additive.

## Diagonales énergétiques

La section 5 de la monographie impose de distinguer D00, Da et Dk. Retrancher les décalages non nuls en a enlève Da, et non seulement D00. Même si l'on conserve cette soustraction correctement, une identité de carrés réorganise un moment; elle ne donne pas le signe du commutateur D1. La projection du vrai coefficient Möbius est une information plus fine qu'une borne de norme arbitraire, mais D2 montre qu'elle n'est pas favorable terme par terme.

Les complétions de fibres connus donnent `fullRow+smallRow=primeRow`. Elles n'effacent pas les termes incomplets de Da ni les faces où `A0!=A1`. Il faudrait une nouvelle estimation de la corrélation réelle, après ces soustractions, pour obtenir un gain. Aucun tel gain n'est déduit des identités.

## Relation terminale exacte et lemme restant

Après le pont couvert de la monographie,

`D_N = -Sfull + 2*max(e,0)`.

Une insertion de D0 ou de l'identité quartique laisse donc cette même égalité, et la contribution défavorable D2 se retrouve avec le signe opposé dans `-Sfull`. La cible exige

`Sfull >= 2*max(e,0) - N/(256*log N*log log N)`.

Poser cette inégalité comme hypothèse d'un transfert serait une reformulation exacte de la cible; cela ne fournirait aucune information nouvelle. Poser un majorant sur la somme entière des D1 serait également le même problème sous de nouvelles coordonnées si aucun théorème arithmétique indépendant ne le soutient.

Le lemme véritablement nouveau à obtenir est une borne unilatérale du cumul des commutateurs D1 ET des défauts de face D0, pondérés par les vrais coefficients de la première variable, et après toutes les soustractions de diagonales exigées. Il doit conserver les modules `a*r` individuels. Une majoration absolue distincte de ces termes risque de perdre précisément la compensation recherchée.

Une hypothèse générale de distribution tordue de premiers contre ces coefficients serait un apport arithmétique distinct, mais sa preuve reste absente. Aucun énoncé indépendamment plus faible, déjà établi dans le corpus, n'a été identifié qui contrôle le commutateur; il ne faut pas en fabriquer un en renommant la cible.

## Statut de l'itération

Identité D0 : dérivée exactement et falsifiable par calcul algébrique; aucune erreur de domaine identifiée.

Hypothèse candidate de fermeture favorable point par point : FAUSSE par D2.

Effacement du commutateur par quartique ou retrait de la seule diagonale : NON DÉDUIT; terme explicite restant.

Nouvelle borne signée quantitative : NON OBTENUE.

Formalisation supplémentaire de D0 : facultative comme certificat algébrique; elle ne serait pas une victoire et n'est pas nécessaire pour constater l'échec de la fermeture.
