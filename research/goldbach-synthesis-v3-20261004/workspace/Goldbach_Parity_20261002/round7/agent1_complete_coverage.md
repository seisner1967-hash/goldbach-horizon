# Agent 1 — couverture logarithmique complète, boucle 7

**Verdict : identité exacte recevable, gain de parité non obtenu.** Le défaut de couverture de la boucle 6 disparaît réellement, mais il se transforme en un secteur de petit cofacteur qui ne peut pas être payé séparément en valeur absolue au budget demandé. Aucun nouveau fichier Lean auxiliaire n'est demandé. Aucun acquis du cadre n'est retiré.

Les contraintes Arbor ont été relues par `view --format constraints`, ainsi que la monographie, §§6, 10.1, 12.6, 12.10 et l'audit `round6/agent3_contract_audit.md`. Le nœud 9.1 poursuit la piste 9 en réparant explicitement sa couverture ; il ne repropose pas le transfert sans R réfuté à la boucle 6.

## 1. Profil et objectif conservés

On prend le profil quartique, alpha = ceil(N^(1/4)), Q = floor((N-1)/alpha), m=N-n, u=log N, ell=log u. Pour 1<=m<N,

```
F_N(m) = 1_(N-m>1) 1_(gcd(N-m,N)=1)
         [Lambda(N-m)-log(N-m)] [D(m)-W(N-m,m)],
S_full = sum_(1<=m<N) mu(m) F_N(m).
```

Les sommes D et W sont littérales : k<=Q, alpha*k<m, et respectivement k|m ou gcd(k,(N-m)*N)=1. Aucun masque mu(N-m)^2 n'est ajouté. En particulier, fII(p^a)=-(a-1)log p reste présent pour les puissances premières propres sur le premier axe. F_N(m)=0 si m<=alpha, car aucun entier k>=1 ne satisfait la face stricte.

Le pont complet demeure

```
S_full = -E_cov + e + S_unc,
D_N = -S_full + 2 max(e,0).
```

L'identité ci-dessous s'applique aussi à une tête S_X avec tous ses termes m<=X, mais la queue X<m<N resterait alors à payer. Le présent contrat prend le profil complet pour ne pas créer cette nouvelle queue.

## 2. Identité à couverture complète

Pour tout entier m>1, l'identité de convolution standard est

```
mu(m) log m = -sum_(d|m) mu(m/d) Lambda(d)
            = -sum_(p^j|m, p prime, j>=1) mu(m/p^j) log p.
```

Par conséquent, exactement,

```
S_full = -sum_(p^j*l<N, p prime, j>=1, l>=1)
             mu(l) [log p / log(p^j*l)] F_N(p^j*l).       (L1)
```

Le terme m=1 est zéro par le noyau réel. Toutes les faces, unités, paramètres et coefficients de F sont évalués à l'argument p^j*l. Le quotient logarithmique ne remplace aucun endpoint. Aucune moyenne sur N n'intervient.

La cancellation des puissances peut être démontrée avant toute suppression. Elle donne l'autre identité exacte

```
mu(m) log m = -sum_(p|m, p prime, p∤m/p) mu(m/p) log p,
S_full = -sum_(p*l<N, p prime, p∤l)
             mu(l) [log p / log(p*l)] F_N(p*l).           (L2)
```

Preuve de la première ligne : si m est carré-libre, chaque mu(m/p)=-mu(m) et sum_(p|m)log p=log m. Si q^2|m, le terme p=q est exclu par p∤m/p, et tous les autres quotients m/p conservent q^2, donc leur Möbius vaut zéro. Les deux membres sont alors zéro. Cette preuve conserve exactement le support de mu(m) ; elle ne filtre pas le premier axe. L2 est ainsi équivalente à L1, plutôt qu'une suppression injustifiée des puissances.

La normalisation fournit une vraie couverture : pour m carré-libre, sum_(p|m)log p/log m=1. Pour un m premier, le poids de son unique premier est exactement 1. Il n'existe donc plus de R d'incidence comme dans la boucle 6. Le prix est l'obligation d'utiliser les premiers jusqu'à N et de conserver l=1.

Une troncature p<=Y a cependant un défaut exact

```
S_full = -sum_(p<=Y, p*l<N, p∤l)
             mu(l) [log p/log(p*l)] F_N(p*l) + R_Y,
R_Y = sum_m mu(m)F_N(m)
            [1-sum_(p|m, p<=Y)log p/log m].              (L3)
```

Dans R_Y, les m non carré-libres valent zéro. Chaque premier m>Y reçoit le poids entier 1. Une coupure destinée à rendre tous les premiers « courts » ne peut donc effacer ce secteur.

## 3. Contrat de falsification numérique transmis à l'Agent 6

Les vérifications se font à N=100000000, alpha=100, Q=999999. Elles portent sur les coefficients rationnels des logarithmes avant division par le log commun, et sur les noyaux réels. Leur domaine fini ne remplace pas l'onset analytique u>=1024.

* m=303=3*101 : les deux tuples (p,l)=(3,101),(101,3) couvrent exactement ce point. Leur coefficient total vaut (log 3+log 101)/log 303=1. On retrouve S_303=-log(99999697)log 101/2. La réparation de couverture est effective.
* m=311 premier : L1 et L2 ont un unique tuple actif, (p,j,l)=(311,1,1). On retrouve exactement -F_N(311)=-log(99999689)log(311/3)/2<0. Effacer l=1 serait une erreur arithmétique, pas une simplification analytique.
* m=29^2=841 ou m=101^2=10201 : dans L1, les deux coefficients avant le signe global sont mu(p)/2=-1/2 et mu(1)/2=+1/2. Ils s'annulent, conformément à mu(m)=0. L2 vaut zéro parce que p∤l est faux pour (p,l)=(p,p). On ne doit pas conserver seulement le terme j=1 sans sa condition de coprimalité.

Le reçu numérique indépendant de l'Agent 6 doit être distingué de ce contrat. Ce rapport ne prétend pas avoir effectué son rejeu ni certifié une somme complète de N-1 termes.

## 4. Représentation intégrale : une queue payable, le moment intact

Pour m>1,

```
1/log m = integral_(0 to infinity) m^(-t) dt.
A(t) = sum_(p^j*l<N) mu(l) log p F_N(p^j*l)(p^j*l)^(-t),
S_full = -integral_(0 to infinity) A(t) dt.              (L4)
```

Les sommes sont finies ; aucune permutation d'une série infinie non convergente n'est requise. On peut utiliser L2 avec p∤l dans la définition équivalente d'A(t). En fait, si

```
S(t) = sum_m mu(m)F_N(m)m^(-t),
```

alors A(t)=S'(t). La représentation L4 intègre donc la dérivée du moment original. La forme intégrale, à elle seule, n'apporte pas un théorème d'orthogonalité.

Il existe néanmoins un budget indépendant et correct pour la queue t>=T. Pour chaque m,

```
sum_(d|m) Lambda(d)|mu(m/d)| <= sum_(d|m)Lambda(d)=log m.
```

Comme F_N(m)=0 pour m<=alpha,

```
|integral_(T to infinity) A(t)dt|
 <= sum_m |F_N(m)|m^(-T)
 <= alpha^(-T) sum_m |F_N(m)|.                          (L5)
```

L'enveloppe L2 réelle obtenue à la boucle 6 donne

```
||F_N||_2^2 <= 20u^4(N-1)(1+u)^3,
sum_m |F_N(m)| <= sqrt(20)u^2(N-1)(1+u)^(3/2).
```

Pour u>1 et ell>0, un choix suffisant est

```
T = (4/u)log[1024 sqrt(20) u^3(1+u)^(3/2) ell],
```

si la quantité entre crochets est >1. Puisque alpha>=N^(1/4), L5 est alors <=N/(1024u ell). Ce paiement utilise les vrais coefficients et ne présume pas la cible. Il n'est pas un majorant optimal.

Le morceau 0<=t<T reste obligatoire. Dans ce morceau, le tuple l=1,j=1 reçoit le poids 1-p^(-T), proche de 1 pour les grands premiers. Asymptotiquement T est d'ordre 18ell/u ; ainsi p de taille N conserve presque tout son poids. Déplacer la queue intégrale vers une zone absolument convergente ne fournit pas le contrôle du morceau proche de t=0.

## 5. Le secteur l=1 est grand : obstruction à son paiement absolu

Dans L2, posons

```
C1 = sum_(p<N, p prime) F_N(p),
S_rest = -sum_(p*l<N, l>=2, p∤l)
             mu(l) [log p/log(p*l)]F_N(p*l).
S_full = -C1 + S_rest,
D_N = C1 - S_rest + 2max(e,0).                         (L6)
```

Les termes premiers p<=alpha valent zéro et les unités restent incorporées dans F. C1 n'est pas un coefficient libre.

Un audit qualitatif à partir des préfixes acquis montre davantage qu'un point non nul : sur la sous-famille des entiers pairs N non divisibles par 3, C1>=cN log N éventuellement, pour une constante c>0. Cette conclusion ne donne pas un onset évalué à 1024 ou à N=10^8 ; elle réfute la stratégie qui voudrait payer C1 séparément par N/(256u ell). Voici les détails.

**Noyau sur les grands premiers.** Pour p>=N^(1/3), le préfixe exact R=min(Q,floor((p-1)/alpha)) satisfait R>=N^(1/12)/4 pour N assez grand. Avec K=(N-p)N, K est pair et log K<=2u. Donc K<=R^C pour un C fixe, par exemple C=26 une fois log R>=u/13. La Lemma 10.1 et sa phase exacte donnent uniformément

```
W(N-p,p) = W_K(R)+log(R/p)A_K(R) = -S(K)+o(1).
```

La multiplication de l'erreur de A_K par log(R/p)=O(u) est payée en choisissant le D fixe de la lemma suffisamment grand. Le terme exponentiel de la lemma reste o(1), car log R est proportionnel à u, tandis que sqrt(log K)=O(sqrt u).

Le produit singulier vérifie S(K)=O(ell) uniformément pour K<=N^2. On le voit en séparant ses premiers à u : le produit des p<=u est O(log u) par la borne ordinaire de Mertens ; au-dessus de u il y a au plus 2u/ell premiers divisant K, et la somme de leurs logarithmes locaux est O(1/ell). Ce sont des estimations ordinaires du masque réel.

Comme D(p)=-log p sur ce secteur,

```
D(p)-W(N-p,p) <= -u/4
```

éventuellement. De plus, Lambda(n)-log n<=0 pour tout n>1, puissances premières propres comprises. Donc F_N(p)>=0 pour tous ces grands premiers unitaires.

**Un secteur positif quantifiable.** Prenons p dans [N/3,N/2] avec p congru à N modulo 3. Alors n=N-p est divisible par 3 et n>=N/2. Il n'est pas premier ; si c'est une puissance première, c'est une puissance de 3 et Lambda(n)=log 3. Ainsi

```
log n-Lambda(n) >= u-log 6 >= u/2,
F_N(p) >= u^2/8
```

éventuellement. Le théorème ordinaire des nombres premiers dans chacune des deux classes réduites modulo 3 donne environ N/(12u) tels premiers dans l'intervalle. On prend le maximum des deux seuils qualitatifs afin de couvrir le choix variable N modulo 3. Exclure les premiers divisant N enlève au plus un point dans cet intervalle (un diviseur premier de N strictement supérieur à N/3 devrait être N/2 ; l'endpoint N/3 est impossible lorsque 3∤N). Il en reste au moins N/(24u) éventuellement, d'où une contribution >=Nu/192.

**Petits premiers.** La contribution potentiellement négative de p<N^(1/3) est au plus

```
N^(1/3) sup|F_N|
 <= u^2[2N^(5/6)+3N^(1/3)(1+u)] = o(Nu),
```

avec la vraie enveloppe uniforme de la boucle 6. Pour N assez grand, elle est <=Nu/384. Les autres grands premiers contribuent positivement. Par conséquent C1>=Nu/384 éventuellement sur cette sous-famille.

Le quotient de ce minorant par le budget cible est au moins (2/3)u^2 ell et diverge. Le point est la taille d'un secteur individuel, pas une impossibilité pour la somme complète : S_rest peut compenser C1. Cette compensation est précisément l'information signée que l'application proposée ne produit pas.

La preuve précédente utilise l'input ordinaire PNT-AP au module fixe 3 et les préfixes à masque polynomial écrits dans le cadre ; elle n'utilise ni une nouvelle hypothèse de Goldbach, ni une moyenne sur N, ni une distribution à grand conducteur. Elle ne fait pas appel à Theorem 10.2, dont le profil alpha eighth (30) est distinct du profil quartique présent. Elle reste une dérivation analytique écrite, sans prétendre être formalement vérifiée sous Lean.

## 6. Où le détecteur arithmétique réapparaît

Sur un premier p>alpha admis par les masques,

```
-F_N(p) = [Lambda(N-p)-log(N-p)] [log p+W(N-p,p)].
```

Le développement contient

```
sum_p Lambda(N-p)log p,
```

c'est-à-dire le détecteur à second axe premier, avec les vraies puissances propres du premier axe et les faces conservées. Il est le secteur correspondant de R_unit, tandis que les termes log(N-p)log p et les corrections W portent leurs propres masses. Aucune transformation de ces quatre termes en une petite erreur n'est justifiée par L1, L2 ou L4.

Le contrôle acquis de petites sommes de mu(l)chi(l) avec masque multiplicatif fixe n'est pas une estimation du coefficient

```
[Lambda(N-p*l)-log(N-p*l)] [D(p*l)-W(N-p*l,p*l)]
```

qu'il faudrait sommer avec mu(l). La normalisation logarithmique est régulière, mais laisse ce couplage additif et ses faces mobiles dans chaque corrélateur. L=1 n'a aucune somme de Möbius sur laquelle appliquer un input de préfixe. Les diagonales d'un éventuel carré d'amplification doivent conserver les mêmes coefficients ; postuler qu'elles sont petites déplacerait l'obligation.

La conclusion de la boucle n'est donc pas « toute couverture complète échoue ». Elle est : cette couverture complète, suivie d'une estimation absolue du secteur l=1 ou d'une invocation seule des préfixes Möbius acquis, ne fournit pas le gain recherché. Le paiement intégral L5 est utile mais laisse L6 ouvert. Une prochaine identité devrait apporter une compensation arithmétique indépendante entre C1 et S_rest, au même niveau N fixé, plutôt que leur simple recombinaison.

## 7. Décision pour la formalisation et la suite

La liste précise des budgets encore nécessaires est

```
C1-S_rest+2max(e,0) <= N/(256u ell).
```

Introduire cette inégalité, ou une hypothèse équivalente de corrélation, dans le futur théorème Lean ne serait pas un contournement de parité. Les identités L1/L2 sont standard et ne satisfont pas seules la condition de victoire. La queue intégrale L5 n'est qu'un poste payé ; elle ne rend pas la cible plus petite.

Il n'y a pas de deuxième idée conceptuelle soumise comme mécanisme éligible dans ce rapport : une déformation de Mellin, un carré de Gram ou un nouveau vocabulaire de poids sans estimation indépendante reproduirait le même moment. La progression de cette boucle consiste à réparer la couverture, localiser son vrai coût et fournir un rejet quantitatif de son paiement absolu. La victoire reste fausse et le problème complet actif.
