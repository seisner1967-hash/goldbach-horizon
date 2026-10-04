# Boucle 10 — opérateur cofacteur signé sur le véritable axe premier

Agent 2. Ce rôle écrit seulement le présent rapport. Le bloc de sonde 10, le retour final 9, le rapport pondéré 9 et l'audit 3 de boucle 9, notamment son §7, ont été lus. Aucune ancienne archive, banque ou source n'est modifiée ou rejouée.

**Résultat partiel.** Une extraction arithmétique exacte du grand premier dans m=p*c transforme le physique du bracket apparié en une valeur de Mangoldt du cofacteur, avec le modèle original conservé. Un second calcul indépendant paie la mobilité du facteur singulier sur le véritable premier n : sa correction est au plus 3u(1+u)^2, donc inférieure à 10^(-12)N/(u ell) au seuil source u>=10^24. Le moment à deux premiers et la compensation globale restent ouverts. Ni cette identité ni ce petit paiement ne constituent une victoire sur la parité.

## 1. Premiers principes et quatre lignes

L'oscillation restante est celle des véritables valeurs de Möbius, corrélées avec n=N-m premier. Le modèle est apparié au physique au même front a=ceil(N^(7/16)); Q demeure floor((N-1)/alpha), alpha=ceil(N^(1/4)). Une fibre physique modulo un diviseur de k porte la phase native 1. Il faut donc chercher une relation arithmétique dans les coefficients, pas une cancellation de cette phase.

Dans la zone m=p*c, c<=a<p et p premier, les diviseurs contenant p ont un cofacteur <=a et sont inactifs. Tous les autres diviseurs sont des diviseurs de c et sont actifs. Leur somme logarithmique complète est exactement Lambda(c), plutôt qu'une nouvelle petite énergie postulée. Les contributions c=1 et c premier ont des signes opposés ; les conserver ensemble expose la compensation recherchée.

Le contre-exemple dépassé est celui d'un coefficient mobile remplacé par un Gram nu : aucune séparation de ce coefficient n'est faite ici. L'extraction du principal harmonique emploie seulement le préfixe réel W(nN,R) déjà autorisé, avec son endpoint. Elle ne transforme pas une somme de deux premiers en un préfixe Möbius ni en BV ordinaire.

Mechanism: Appariement des diviseurs dans m=p*c, c<=a<p, puis extraction du principal harmonique sur le vrai premier unitaire n=N-pc, avec compensation physique-modèle conservée.

Hypothesis: Möbius, Mangoldt et totient usuels; c<=Q, unités et fronts source; input (54) acquis pour le bulk m>=ceil(N^(3/4)), sans petite énergie ni hypothèse de corrélation supplémentaire.

Observable: Bracket local mu(c)[W_positive(n,pc)-Lambda(c)-1_(c=1)log p]*log n; facteur singulier S(nN)=S(N)(1+1/(n-2)), dont la correction globale est <=3u(1+u)^2 sur des n distincts.

Conflicts: Aucun double paiement avec la partition Buchstab d'Agent 1; c=1, non-squarefree, p<=a ou c>a, cap Q et fibres incomplètes gardés; la somme avec p et N-pc tous deux premiers reste non estimée.

## 2. Objet apparié réellement retenu

On conserve N pair, u=log N, ell=log u, n=N-m, Lambda_N(n)=Lambda(n)1_(n>1)1_(gcd(n,N)=1). Le premier axe proprement premier utilise n premier et gcd(n,N)=1, donc n>=3, et gcd(m,N)=1. Le raw avant cette partition garde toutes les propres puissances premières unitaires; aucun mu(n)^2 n'y est ajouté.

Pour chaque point du premier axe, définir, avec les mêmes fronts stricts dans les deux termes,

```
P_a(m)=mu(m)*sum_(1<=k<=Q,k|m,a*k<m)mu(k)*log(m/k),
W_positive(n,m)=sum_(1<=k<=Q,a*k<m,gcd(k,n*N)=1)
                     mu(k)*log(m/k)/phi(k),
b_a(n,m)=log n*[P_a(m)-mu(m)*W_positive(n,m)].       (E1)
```

Le masque gcd(k,N)=1 du physique est automatique ici, car k|m et gcd(m,N)=1. Le masque du modèle reste explicite : k ne divise pas nécessairement m et peut diviser n. Le signe de W_positive correspond au logarithme positif log(m/k); le noyau W source construit avec log(k/m) vaut son opposé. Cette convention empêche un changement de signe caché.

Le terme k=1 est actif exactement lorsque m>a. Dans ce cas ses contributions physique et modèle sont toutes deux mu(m)log m et s'annulent au même point. Si m<=a, tous les fronts sont inactifs. Ainsi E1 est exactement le bracket k>=2 de la route retenue, sans nouveau paiement k=1.

```
B_prime^a=sum_(n premier,gcd(n,N)=1,1<=m=N-n<=N-2)b_a(n,m).
```

Les non-squarefree m valent zéro dans E1 à cause de mu(m) déjà présent dans le bracket entier. Cela n'autorise aucun masque nouveau sur une coupe courte antérieure. Les quatre signes de la composante HH restent ceux de la décomposition source si E1 y est développé; ce rapport ne les remplace pas par des coefficients libres.

## 3. Identité arithmétique de grand premier, avec cap

Soient p premier et c>=1 avec

```
c<=a<p, c<=Q, m=p*c<N-1,
n=N-p*c premier, gcd(n,N)=1.                         (E2)
```

Puisque c<p, gcd(p,c)=1. Puisque m est unitaire à N, p et c sont unitaires à N. Un diviseur k de pc est de la forme d ou p*d avec d|c. Pour k=d, pc/d>=p>a, et d<=c<=Q : TOUS ces diviseurs sont actifs et sous le cap. Pour k=p*d, c/d<=c<=a : TOUS ces diviseurs sont inactifs, qu'ils dépassent Q ou non. Les égalités c=a et r=a demeurent littéralement traitées par le front strict.

Les deux identités arithmétiques usuelles donnent

```
sum_(d|c)mu(d)=1_(c=1),
sum_(d|c)mu(d)*log(c/d)=Lambda(c),
mu(pc)=-mu(c).
```

Par conséquent,

```
P_a(pc)=-mu(c)*[Lambda(c)+1_(c=1)log p],
b_a(n,pc)=mu(c)*log n*
           [W_positive(n,pc)-Lambda(c)-1_(c=1)log p].  (E3)
```

E3 vaut aussi pour c non carré-libre : mu(c)=mu(pc)=0 et le bracket entier est nul. La somme brute sum_(r|pc,r>a)mu(r)log r, sans le masque ou le raccord entier, ne doit pas être substituée à P_a sur ce support. Pour c>1 carré-libre, E3 se lit

```
b_a(n,pc)=log n*[Lambda(c)+mu(c)*W_positive(n,pc)].    (E4)
```

En effet, si Lambda(c) est non nulle sur ce support, c est premier et mu(c)=-1. Pour c=1, la formule séparée est

```
b_a(N-p,p)=log(N-p)*[W_positive(N-p,p)-log p].        (E5)
```

La masse physique négative -log p sur c=1 et la masse positive Lambda(c) sur c premier ne sont pas abandonnées avant le bilan. Si c est composite carré-libre, le physique complet de E3 s'annule exactement : seul mu(c)W_positive subsiste. Une faveur uniforme de ce dernier terme serait fausse sans son signe réel.

Le raccord précis du noyau brut est P_a(pc)=mu(pc)^2*T_a(pc), sous la géométrie E2, avec T_a(pc)=sum_(r|pc,r>a)mu(r)log r. Pour c>1, T_a(pc)=Lambda(c) même si c est une propre puissance première. Le garde demeure indispensable : mu(pc)^2*T_a(pc)=mu(c)^2*Lambda(c). Il n'est ni une supposition de squarefreeness du premier axe n ni un nouveau masque du raw. Le contrat entier E3 est préférable pour Lean parce qu'il porte directement la vraie valeur mu(m) et reste nul sur c non carré-libre.

### Partition et injection nécessaires

Appelons S la zone E2 et R son complément dans l'axe premier réel. Elle utilise le plus grand premier p de m. Il est unique dans S : deux facteurs premiers >a forceraient le cofacteur d'un des deux à être >a. Il n'existe donc pas deux représentations admissibles du même m ou du même n. Le reindexage (p,c) -> m=pc -> n=N-m est injectif sur S.

La partition exacte est B_prime^a=B_S+B_R. R garde les m sans grand premier >a et les m dont le cofacteur du plus grand premier dépasse a, ainsi que m=1. Elle ne reçoit aucun gain ici. La partition Buchstab d'Agent 1 peut décrire les mêmes points autrement; on ne somme pas ses secteurs avec S comme deux restes indépendants et on ne paie pas deux fois une même face.

## 4. Principal harmonique sur l'axe premier réel

Le facteur singulier du cadre, pour N pair, est

```
S(N)=2C2*prod_(l|N,l>2)(l-1)/(l-2).
```

Pour tout n premier unitaire à N, n>=3 et n ne divise pas N. La seule nouvelle base première du masque nN est donc n, avec exactement

```
S(nN)=S(N)*(n-1)/(n-2)=S(N)+S(N)/(n-2).             (E6)
```

Ce n'est pas une égalité de modèles de primes avec une série singulière; c'est l'identité finie de facteurs du facteur singulier défini dans le cadre. Le multiplicateur mobile n est payé dans la section suivante, non remplacé gratuitement par N.

Sur le bulk m>=M=ceil(N^(3/4)), l'input (54) acquis et le plancher réel

```
R_a=min(Q,floor((m-1)/a))
```

donnent R_a>=N^(1/5), K=nN<=N^3 et

```
W_positive(n,m)=+S(nN)+epsilon(n,m),
|epsilon(n,m)|<=G54/u,
G54=4*10^8*u^5*exp(-sqrt(u)/60)+160*u^2*exp(-u/40).   (E7)
```

La borne utilise l'affaiblissement explicite -sqrt(u)/60 du véritable exposant source -sqrt(u/60). Le terme d'endpoint log(R_a/m)A_K(R_a) est retenu, comme dans l'audit 9; aucun préfixe vide n'a de principal ajouté. Les conditions de plancher et cap ont été vérifiées dans cet audit au domaine u>=10^6, contenu dans l'onset source 10^24.

**Correction de signe avant clôture.** L'input (54) donne W_kernel=-S(nN)+erreur, avec W_kernel construit par log(k/m). Puisque W_positive=-W_kernel, son principal est +S(nN). La première rédaction interne de E7 avait repris le signe du noyau source dans le noyau positif; elle a été corrigée ici et signalée à root et au rôle 6 avant gel. E3 et le paiement absolu E8–E10 n'ont pas été affectés.

E7 ne s'applique pas à une phase additive mobile ni à un nouveau rough mask. C'est précisément le masque réel gcd(k,nN)=1 et le noyau harmonique entier déjà autorisés par (54).

## 5. Paiement indépendant de la mobilité singulière

Considérons n premiers unitaires DISTINCTS, dans n>=3, n<N, avec coefficients sigma_n de module <=1. Le cas de S a sigma_n=mu(c), ou son opposé selon l'orientation; le cas global a sigma_n=mu(m). Les n petits restent présents. Alors

```
R_sing=S(N)*sum_n sigma_n*log n/(n-2),
|R_sing|<=S(N)*u*sum_(j=1..N-2)1/j
         <=S(N)*u*(1+u).                             (E8)
```

Le premier majorant compte positivement tous les entiers j=n-2. Il conserve explicitement le n=3, de dénominateur 1; aucune approximation n-2~n n'est nécessaire. L'injection de la section 3 empêche une multiplicité de représentations (p,c). La borne ne peut pas être multipliée par un nombre de p puis prétendre garder son coût polynomial.

Le cadre donne S(N)<=N/phi(N). On peut rendre la suite entièrement effective avec les identités élémentaires déjà utilisées pour le moment totient :

```
N/phi(N)=sum_(d|N)mu(d)^2/phi(d)
        <=sum_(d<=N)1/phi(d)<=3*(1+u).
```

Ainsi le nouveau poste vaut

```
|R_sing|<=3*u*(1+u)^2.                              (E9)
```

La borne de la somme de 1/phi(d) vient de son produit eulérien positif <=e et de la somme harmonique <=1+log N. Elle n'utilise ni PNT, ni BV, ni corrélation Möbius-primes. Elle est uniforme même lorsque N a beaucoup de facteurs premiers.

À u0=10^24, u0<2^80, 1+u0<2^81 et ell0<2^6. Le ratio de E9 à N/(u ell) est

```
3*u^2*(1+u)^2*ell*exp(-u).
```

Son facteur polynomial au point u0 est <2^(2+160+162+6)=2^330. Comme u0>10000 et e>2, le ratio est <2^(-9670)<10^(-12). Sa dérivée logarithmique par rapport à log u vaut

```
2+2u/(1+u)+1/ell-u,
```

qui est négative pour tout u>=u0. On obtient donc le paiement effectif indépendant

```
|R_sing|<10^(-12)*N/(u*ell), u>=10^24.               (E10)
```

Ce nouveau paiement concerne seulement la mobilité de S(nN), pas la masse principale S(N), ni son moment signé. Il ne réutilise pas le poste properpower de boucle 9 comme un second crédit. N=10^8 est hors de ce domaine; un test fini de E6 ne certifie pas E10.

## 6. Information restante après extraction, avec tous les coûts

Sur S dans le bulk, E3, E6 et E7 donnent

```
B_S,bulk = T_semiprime - G_prime + S(N)*C_S
             + R_S + E_S,
T_semiprime=sum_(p,c dans Sbulk,c premier)log n*log c,
G_prime=sum_(p dans Sbulk,c=1)log n*log p,
C_S=sum_(p,c dans Sbulk)mu(c)*log n,
R_S=S(N)*sum_(p,c dans Sbulk)mu(c)*log n/(n-2),
E_S=sum_(p,c dans Sbulk)mu(c)*log n*epsilon(n,pc).    (E11)
```

T_semiprime garde p ET n=N-pc premiers. G_prime garde les deux premiers p et N-p; sa contribution physique est de signe favorable, avec son modèle c=1 toujours présent dans C_S. C_S conserve c=1, tous les c composites carré-libres des deux signes et les zéros non carré-libres. Aucun de ces trois termes principaux n'est supposé petit séparément.

R_S reçoit E9/E10 par injection. Puisque log n<=u et chaque n figure au plus une fois, |E_S|<=N*G54, sans facteur additionnel du nombre de p. Pour le modèle hors bulk, le majorant positif direct donne au plus 3*M*u^2*(1+u)<=6*N^(3/4)*u^2*(1+u). Aucun principal n'est inventé pour ce préfixe court. Les contributions physiques hors bulk et celles de R restent dans leur bracket réel, à contrôler, plutôt que dans ce seul majorant de modèle.

À l'onset source, NG54 et cette petite face du modèle ont les mêmes décroissances explicites que la moitié des termes de J3 de boucle 9. Ils sont les erreurs de cette extraction du modèle de B_a, distinctes du Z_face déjà dans le ledger; appliquer E11 les conserve comme charges et ne fournit pas un second crédit pour Z_face. Si l'extraction globale E12 est employée, ses erreurs couvrent celles de S comme sous-secteur; on n'ajoute pas une deuxième charge E_S ou R_S. Le nouveau paiement propre de ce rapport est E10. Une comptabilité finale doit choisir un seul raccord et conserver les marges réellement utilisées.

### Pourquoi les principaux ne sont pas encore payés

Pour c premier, T_semiprime est une masse positive de solutions de deux conditions premières p et N-pc, pondérée par log c log n. Une borne BV pour Lambda(N-cv) seule, ou un préfixe mu(c) à petit conducteur, ne fournit pas une estimation de cette masse avec v=p premier. L'ordre de la somme n'efface pas cette seconde condition première.

Pour c composite carré-libre, l'identité physique produit bien zéro, mais le signe du modèle vaut +mu(c)S(N) au principal. Les mu(c)=-1 donnent une contribution favorable; les mu(c)=+1 donnent la contribution opposée. Une borne unilatérale utile demanderait une compensation de ces mêmes termes pondérés par la condition p et N-pc premiers. L'inégalité brute qui efface tous les signes perd précisément cette information.

La relation entre T_semiprime et G_prime n'est ni une bijection ni une injection des solutions. Les points c=1 et c premier ont des valeurs différentes de m et n. Postuler que T_semiprime-G_prime+S(N)C_S est petit serait déjà postuler le moment ouvert de cette zone. Une upper-bound sieve de chacun des deux premiers conserve l'aveuglement à la parité et n'est pas une preuve de cette compensation.

Sur le bulk global, l'identité équivalente est

```
B_prime,bulk^a=P_bulk-S(N)*sum_(n dans bulk)mu(N-n)*log n
                -R_global-E_global.                (E12)
```

E9 paie R_global et (54) paie E_global. La combinaison SIGNÉE des deux principaux de E12 reste ouverte; les deux termes ne sont pas séparément des erreurs de BV. E11 en isole un sous-secteur arithmétique sans prétendre résoudre E12.

## 7. Contrat falsifiable et candidature formelle limitée

Le rôle 6 a reçu E1–E6 avec N=100000000, a=3163, alpha=100 et Q=999999. Les unités sont celles de nN, et les fronts a*k<m sont testés en entiers. Les logarithmes peuvent être conservés comme combinaisons rationnelles de logarithmes premiers; la comparaison E3 ne requiert pas de décimales.

Domaines minimaux demandés : c=1 avec les deux axes premiers; c premier; c composite carré-libre de chaque signe; c non carré-libre; puis un point dont c>a ou p<=a pour réfuter toute extrapolation de E3. Le modèle W_positive est complet jusqu'au cap source et à son front mobile, pas une sélection des diviseurs de m. E6 doit aussi être vérifiée pour n petit, dont n=3 quand compatible avec la géométrie; les factors locaux sont rationnels exacts et C2 se simplifie.

Le reçu courant `round10/paired_cofactors.json`, lu sans rejouer un ancien banc, porte PASS_FINITE_IDENTITIES_ONLY. Sa partie small_cofactor porte PASS_IDENTITY_ONLY pour la formule entière E3, et sa partie singular porte PASS_IDENTITY_ONLY pour E6, avec C2 factorisé symboliquement. Les témoins réellement premiers sont :

| c | p | m | n=N-m | mu(c) | Raccord |
|---:|---:|---:|---:|---:|---|
| 1 | 1000037 | 1000037 | 98999963 | +1 | E5, deux premiers, k=1 annulé conjointement |
| 7 | 3167 | 22169 | 99977831 | -1 | Lambda(c)=log 7, modèle complet |
| 21 | 3169 | 66549 | 99933451 | +1 | physique nul, modèle de signe positif au principal |
| 231 | 3191 | 737121 | 99262879 | -1 | physique nul, signe opposé du modèle |
| 9 | 3181 | 28629 | 99971371 | 0 | T brut=log 3, bracket entier nul |

Les observations de signes finis sont des observations à N=10^8, pas des validations des principaux asymptotiques à u>=10^24. En particulier, seuls certains de ces m atteignent le bulk M=1000000; E3 n'a pas besoin du bulk, tandis que E7 le requiert.

Deux extrapolations ont leur falsificateur exact : m=3167*3169=10036223, n=89963777 premier, c=3167>a, donne T_a=0 au lieu de Lambda(c)=log3167. Pour p=3,c=23,m=69,n=99999931 premier, p<=a donne encore T_a=0 au lieu de log23. Ce sont des violations des hypothèses de la formule étendue, pas des erreurs du compilateur.

Le reçu singulier garde n=3 et son ratio 2. Il réfute l'extension non unitaire n=5 : S(5N)/S(N)=1 et non 4/3; il réfute l'extension properpower n=9 : ratio 2 et non 8/7. Il conserve aussi une erreur de multiplicité concrète au point m=22169 : compter à la fois (p,c)=(3167,7) et (7,3167) doublerait la correction de n=99977831. La géométrie canonique c<=a<p n'en conserve qu'une.

Aucun ancien Gram ou paiement properpower n'est rejoué. Le contrat E3 pourrait donner une candidature Lean ARITHMÉTIQUE utile : p premier, c<=a<p, c<=Q et axes unitaires impliquent exactement la formule du bracket physique-modèle. Il ne prend pas une petite énergie ou la cible comme hypothèse. Sa compilation seule ne serait pas une victoire, puisque E11/E12 ne sont pas quantitativement contrôlés. Les lemmes mathlib `sum_moebius_mul_log_eq`, la somme de Möbius sur les diviseurs et la multiplicativité réelle de Möbius sont les raccords proposés; aucune identité analytique nouvelle n'est postulée comme axiome.

## 8. Bilan réservé et obligations ouvertes

La route authoritative reste

```
D_N=B_prime^a+B_pp^a+P_band^{>=2}+Z_face^{>=2}
       +I_alpha+2max(e,0).
```

I_alpha est payé une fois avec son contrat source. Z_face et B_pp possèdent leurs paiements écrits indépendants 9, sans nouvelle certification Lean. Le paiement physique P_band conserve son seuil BV supplémentaire non évalué. Le pont 2max(e,0) reste non payé. Le présent calcul ne supprime aucun de ces postes ni les propres puissances premières du raw.

Obligation nouvelle exactement localisée : une majoration UNILATÉRALE indépendante de la combinaison E11, avec le complément R et les faces courtes, ou de la combinaison globale E12. Ni une identité de diviseurs, ni E10, ni la norme d'un opérateur nu ne donne cette majoration. Le défaut ne constitue pas une impossibilité globale des méthodes de poids; il précise le moment que devrait traiter un prochain mécanisme.

Statuts : ARITHMETIC_COFACTOR_IDENTITY; INDEPENDENT_SINGULAR_MASK_CORRECTION_PAYMENT_WRITTEN; TWO_PRIME_SIGNED_COMPENSATION_OPEN; PHYSICAL_BAND_ONSET_UNEVALUATED; COVERED_BRIDGE_OPEN; VICTORY_FALSE.

TERMINÉ. Rapport définitif de ce rôle; son SHA-256 est transmis séparément à root pour éviter une empreinte autoréférente. Les résultats numériques sont des identités finies seules; E10 reste une preuve mathématique écrite à auditer indépendamment, sans certification Lean ni victoire.
