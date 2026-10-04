# Boucle 14 — déplacements multiples, charges entières et défaut de préfixes

**FINAL conceptuel. Rôle 1.** Le seul fichier écrit par ce rôle est le présent rapport. Aucun producteur numérique, ancien PASS ou Lean n'est exécuté. Tous les artefacts 1–13 restent immuables. Les contrats numériques ci-dessous sont neufs et confiés au rôle 6 ; leur résultat ne doit pas être inventé dans ce rapport gelé.

**Résultat.** Une fenêtre de déplacements donne deux degrés réels, deux restes et une normalisation exacte ; elle ne couvre pas automatiquement les parents. Une extension à tous les déplacements descendants transforme, dans chaque bloc `(c,q)`, la capacité en un défaut de préfixes calculable sans postuler Hall. Une borne indépendante paie les parents proches du front `p=a`. Aucune estimation du défaut intérieur des incidences premières n'est établie. Le mécanisme reste partiel, sans sélection quantitative globale ni victoire.

## 1. Sources relues et quatre lignes

Entrées lues en entier : `round14/PROBE_BLOCK.md`, `round13/agent1_exchange.md`, `round13/agent3_formalisation.md`, `round13/agent4_formalisation.md`, les deux sources définitives `PrimeSemiprimeSwitch.lean` et `HarmonicKernelVariation.lean`, et le retour définitif12. La compilation indépendante13 appartient au Juge ; elle n'est pas relancée ici. Les 23+16 théorèmes13 restent des acquis locaux.

**Mechanism :** Remplacer le déplacement unique `p→p−2` par les arêtes réelles `p→p−2h=rs`, contrôler les deux multiplicités, puis compléter aux arêtes `rs<p` dans chaque bloc `(c,q)` ; l'appariement ordonné conserve exactement les parents non servis et les images non utilisées.

**Hypothesis :** Les coupes, primalités et unités explicites donnent les mêmes préfixes physiques opposés ; aucune incidence première ni densité n'est postulée. Le graphe complété a des voisinages emboîtés par sa définition, et son défaut est démontré par récurrence entière plutôt qu'introduit comme hypothèse Hall.

**Observable :** Deux degrés sur une fenêtre complète, retrait du front entier, vrai défaut maximal de préfixes, charge logarithmique des parents non servis, masse favorable des images non utilisées, et défaut physique avec ses deux kernels, son cap et ses fronts.

**Conflicts :** Pas de couverture automatique, pas de petit défaut supposé, pas de transfert d'un comptage de semipremiers sans premier complément, pas de paiement de tout le complément par une petite variation. P5 reste sur K2 entier avant retrait exact. Le score demeure 0.

## 2. Domaine fixé et vrais coefficients

Conserver

\[
u=\log N,\quad\ell=\log u,\quad
\alpha=\lceil N^{1/4}\rceil,\quad
Q=\lfloor(N-1)/\alpha\rfloor,\quad
a=\lceil N^{7/16}\rceil,\quad
M=\lceil N^{3/4}\rceil.
\]

N est pair, et le domaine analytique source reste `u≥10^24`. Les identités entières prennent seulement leurs gardes ; les bornes élémentaires écrites ci-dessous utilisent `u≥16`. Définir le nouveau rayon, sans remplacer a ou Q,

\[
H=\lceil N^{1/64}\rceil. \tag{C1}
\]

Les kernels restent les objets source

\[
D_a(m)=\sum_{k\mid m,\ 1\le k\le Q,\ ak<m}\mu(k)\log(k/m),
\qquad
W_a(n,m)=\sum_{1\le k\le Q,\ ak<m,\ (k,nN)=1}
\frac{\mu(k)}{\varphi(k)}\log(k/m).
\]

Pour un premier complément unitaire `n=N−m`, le point extrait vaut

\[
b(m)=\log n\,[-\mu(m)(D_a(m)-W_a(n,m))]. \tag{C2}
\]

U1 conserve le préfixe **entier**

\[
-\mu(m)(D_a-W_a)=\mu(m)^2[-\Lambda(m)-U_a(m)]+\mu(m)W_a,
\quad U_a(m)=\sum_{d\mid m,d\le a}\mu(d)\log d.
\]

Le présent graphe porte sur une sous-famille `c premier` du secteur J2 et sur ses images J1. Il ne représente ni tout J2, ni le raw entier. Le raw `Λ_N(n)` garde ses puissances propres. Les quatre Möbius des cellules HH, le moment bilatéral apparié `S(cN)`, `c=1`, le complément long et `−S(N)N` ne sont pas remplacés par ce graphe.

## 3. Fenêtre entière, degrés et deux déficits

Une arête est un tuple `(c,p,q,r,s,h)` avec :

1. `c,p,q,r,s` premiers distincts, `c<r<s≤a<p<q` ;
2. `(cpqrs,N)=1`, `cr,cs≤a<rs`, `crs>a` ;
3. `1≤h≤H`, `rs=p−2h` ;
4. `m0=cpq`, `m1=crsq`, `M≤m_i≤N−2` ;
5. les deux `n_i=N−m_i` sont réellement premiers unitaires et `n_i>Q`.

Toutes les arêtes satisfaisant ces gardes appartiennent à `E_H`. Aucun h ni aucun premier complément n'est supprimé pour rendre un signe favorable. La famille des parents P contient tous les `cpq` avec c premier≤a, p<q premiers>a, unités, bulk et premier complément>Q ; elle comprend les parents de degré zéro. T peut être l'union des images des arêtes, ou un ensemble plus grand d'images valides : chaque image supplémentaire garde degré zéro et son coefficient restant1. Le test sur un bloc emploie P_all et T complets de C11. Par le même filtre de diviseurs réel que13,

\[
U_a(m_0)=-\log c,\quad U_a(m_1)=+\log c,
\quad\mu(m_0)=-1,\quad\mu(m_1)=+1,
\quad\Lambda(m_i)=0.
\]

Donc, avec les **deux vrais** `W_i`,

\[
b_P=\log n_0(\log c-W_0),\qquad
b_T=\log n_1(-\log c+W_1). \tag{C3}
\]

L'arête descendante donne

\[
n_1=n_0+2hcq,
\quad
b_P+b_T=-(\log c-W_0)\log(n_1/n_0)
             +\log n_1(W_1-W_0). \tag{C4}
\]

La canonicalité du parent récupère c,p,q. Pour chaque h, la factorisation ordonnée r<s de `p−2h` est unique : son degré `d_P` est au plus H. La canonicalité de l'image récupère c,r,s,q ; pour chaque h, `p=rs+2h` est unique : son degré `d_T` est aussi au plus H. L'injection image13, valable pour h fixé, **n'est pas** une injection sur l'union de tous les h. La charge image doit être normalisée.

Avec le poids explicite `η=1/H` sur chaque arête, les deux degrés donnent l'identité exacte

\[
\sum_{P}b_P+\sum_T b_T
=\frac1H\sum_{e\in E_H}(b_{P(e)}+b_{T(e)})
 +\sum_P\left(1-\frac{d_P}{H}\right)b_P
 +\sum_T\left(1-\frac{d_T}{H}\right)b_T. \tag{C5}
\]

Les deux coefficients restants sont non négatifs. L'image non utilisée demeure une contribution favorable au source ; son coefficient n'est pas oublié. Le parent non servi demeure nuisible au source. C5 ne dit pas que son degré vaut H, ni qu'un seul voisin suffit avec ce poids. Une normalisation plus efficace exige une capacité démontrée, pas une disparition du deuxième déficit.

### Coût partiel de la fenêtre

Pour `u≥16`, `a≥4H` : en effet `H≤2N^(1/64)` et `N^(27/64)≥e^(27/4)>8`. Ainsi `p≥4h`, et la preuve13 s'étend avec les fronts littéraux `R_i=min(Q,floor((m_i−1)/a))` :

\[
0<\log(m_0/m_1)\le4h/a,\qquad
R_0-R_1\le2hN/a^2+1,
\]
\[
|W_1-W_0|\le21H uN^{-1/32}. \tag{C6}
\]

Le masque n_i est supprimé du kernel seulement après les deux primalités `n_i>Q`, et `(k,N)=1` demeure. La tête commune garde k1 ; toute la queue et son `+1` sont présents. Comme `sum_E η=sum_P d_P/H≤#P≤N`, le coût apparié normalisé est

\[
E_H\le21HN^{31/32}u^2
\le42N^{63/64}u^2. \tag{C7}
\]

Au source, le ratio `42u³ell exp(−u/64)` est inférieur à `10^−12` : à `u0=10^24`, le logarithme préexponentiel est inférieur à200 et `u0/64>10^22`; ensuite `3/u+1/(u log u)−1/64<0`. Il s'agit d'une preuve écrite de coût partiel, **pas** d'une estimation du terme parent restant de C5. Aucun nouveau Lean de cette petite erreur seule n'est proposé comme percée.

## 4. Un défaut de front réellement payé

La fenêtre est géométriquement tronquée lorsque `a<p≤a+2H`. Définir F comme **tous** ces parents de la sous-famille c premier, avec ou sans premier image. Les incidences du premier axe ne sont pas remplacées par des probabilités. Il y a au plus2H entiers p dans cette bande. Pour chaque c,p, il y a au plus `N/(cp)` choix de q, même en oubliant sa primalité pour majorer. Avec `c≤N/a²` et la somme harmonique,

\[
\#F\le\frac{2HN}{a}\sum_{1\le c\le N/a^2}\frac1c
\le\frac{2HN}{a}(1+u). \tag{C8}
\]

Chaque parent est compté une fois par sa factorisation ordonnée. Cette borne comprend les parents à image composite et ceux sans semipremier ; elle ne les assimile pas à un sous-ensemble déjà apparié.

La borne acquise élémentaire `sum_(k≤N)1/φ(k)≤3(1+u)` implique directement `|W_a|≤3u(1+u)`, sans PNT, BV ou U4. Pour ces parents `|U_a|=log c≤u`, donc

\[
|b_P|\le u^2[1+3(1+u)]\le7u^3\quad(u\ge1).
\]

Il s'ensuit le paiement indépendant de la **masse entière du front**

\[
\sum_{P\in F}|b_P|
\le14\frac{HN}{a}u^3(1+u)
\le28N^{37/64}u^3(1+u). \tag{C9}
\]

La somme de totients utilisée est celle démontrée par écrit dans round10/agent3, §5 ; il n'y a pas d'hypothèse de signe de W. Au source, le coût normalisé est

\[
28u^4(1+u)\ell\exp(-27u/64)<10^{-12}. \tag{C10}
\]

Au seuil, le logarithme préexponentiel est inférieur à300 et `27u0/64>10^23`. Sa dérivée est `4/u+1/(1+u)+1/(u log u)−27/64≤6/u−27/64<0` dès `u≥16`. Le paiement ne gagne rien sur les parents intérieurs sans voisins : ils sont dans le complément exact. C9 est un poste nouveau de front, pas une minoration du nombre de partenaires.

## 5. Complétion de tous les déplacements : graphe d'ordre réel

La fenêtre très courte n'est pas nécessaire pour conserver le signe principal au source. U4 est uniforme sur le bulk à premier complément `n>Q` ; sa route par deux erreurs peut **remplacer** C7 et non s'y ajouter. On peut donc autoriser tous les déplacements descendants en conservant les vrais vertices.

Fixer un bloc `(c,q)` de premiers unitaires, `c≤a<q`, et poser

\[
A=cq,\qquad L=\min\left(q-1,\left\lfloor\frac{N-Q-1}{cq}\right\rfloor\right).
\]

Parents :

\[
\mathcal P_{c,q}=\{p:\ a<p\le L,\ p\text{ premier},\ (p,N)=1,
\ N-Ap\text{ premier}\}.
\]

Images :

\[
\mathcal T_{c,q}=\{t=rs:\ a<t\le L,\ r<s\text{ premiers},\
cr,cs\le a,\ (rs,N)=1,\ N-At\text{ premier}\}.
\tag{C11}
\]

Conserver `(c q,N)=1`; la primalité du complément et l'unité de m donnent `(n,N)=1`. Les gardes `n>Q` sont assurées par L ; elles ne sont jamais supprimées sur une fenêtre inventée. Les coupes `rs>a` et `cs≤a` impliquent `r>c`, donc les facteurs de l'image sont réellement distincts. `crs>a` suit aussi, et reste une garde explicite dans le contrat de test. Puisque c,q et les facteurs unitaires sont impairs, p et t sont impairs.

Toute arête est maintenant `t<p`, avec le déplacement entier unique `h=(p−t)/2≥1`. Les diviseurs courts et les coefficients C3 ne changent pas. Pour `u≥16`, `m=cpq` ou `cqt` satisfait automatiquement `m>c a²≥N^(7/8)>N^(3/4)`, donc `m≥M`; L impose `m≤N−Q−1≤N−2`. Les deux premiers axes sont réels. La réduction du masque sous n>Q conserve le Q original.

Un parent plus grand possède tous les voisins d'un parent plus petit. Ce fait est une conséquence de `t<p`, pas une hypothèse de capacité. Il permet de démontrer le défaut fini exactement.

### Démonstration entière du défaut

Trier les parents `p1<...<pk`, définir `T_j=# {t in T : t<p_j}`, puis traiter les parents dans cet ordre. Prendre une image disponible s'il y en a une ; chaque image est utilisée au plus une fois. Si plusieurs existent, prendre la plus petite pour fixer un algorithme déterministe. `M_j` est le nombre de parents servis après le j-ième, et `D_j=j−M_j`.

Avec `D_0=0`, on a exactement

\[
D_j=\max(D_{j-1},\ j-T_j),\qquad
D_j-D_{j-1}\in\{0,1\}. \tag{C12}
\]

Preuve : les `M_(j−1)` images déjà prises sont toutes inférieures à p_j. Si `T_j>M_(j−1)`, il reste une image et le parent est servi ; sinon `T_j=M_(j−1)` et il est non servi. Cette alternative donne C12. Par récurrence,

\[
D_k=\max\left(0,\max_{1\le j\le k}(j-T_j)\right)
=\max_{a\le x\le L}\bigl(P(x)-T(x)\bigr)_+, \tag{C13}
\]

où les deux fonctions comptent leur ensemble **entier** jusqu'à x. Au point premier p_j, une image semipremière ne peut égaler p_j, donc `t≤p_j` et `t<p_j` donnent le même T_j. Entre deux parents, P est constant et T ne décroît pas : le maximum est atteint à un parent. La preuve ne suppose pas que ce maximum est nul.

La masse logarithmique exacte des parents non servis par cet algorithme est

\[
U_{c,q}=\sum_{j=1}^k\log(N-cqp_j)(D_j-D_{j-1}). \tag{C14}
\]

Après le front payé, reprendre C12–C14 avec `P_int=P\F` ; toutes les images T restent présentes. Le défaut de P_all n'est **pas** celui de P_int. Les images qui n'ont aucun parent plus grand demeurent des vertices non utilisés et ne sont pas retirées du bilan.

### Vrai bilan de cette capacité

Pour le matching G ainsi construit et ses deux restes U_P,U_T,

\[
\sum_{P}b_P+\sum_T b_T
=\sum_{(p,t)\in G}(b_P+b_T)+\sum_{U_P}b_P+\sum_{U_T}b_T. \tag{C15}
\]

Les termes sont les vrais C2 ; aucune charge image ne peut être prise deux fois. Au source seulement, écrire `W=-S(N)+δ`, `|δ|≤ε_W`, avec l'acquis

\[
\epsilon_W=4\cdot10^8u^4e^{-\sqrt u/60}+160u e^{-u/40}.
\]

Le principal d'un pair vaut `−(log c+S(N))log(n_t/n_p)<0`. La référence S(N) est ici celle de W sous n>Q ; elle ne remplace jamais le modèle S(cN) du moment bilatéral. La somme des deux erreurs sur le matching est au plus `ε_W N u`, puisque tous ses vertices m sont distincts. Les blocs `(c,q)` sont disjoints : le parent retrouve son unique petit c et ses deux grands p<q ; l'image retrouve ses petits c<r<s et son unique grand q. Les parents et les images ont des signes Möbius opposés.

Plus généralement, le principal **entier** de C15 s'écrit exactement

\[
(\log c+S(N))\left[
U_{c,q}-\sum_{U_T}\log n_t
-\sum_{G}\log(n_t/n_p)\right]. \tag{C16}
\]

Les deux masses négatives sont gardées. Les erreurs U4 de tous les vertices sélectionnés coûtent au plus `ε_W N u`. Son ratio `ε_W u²ell` est inférieur à `10^−12` au source : le premier logarithme préexponentiel est inférieur à400 alors que `sqrt(u0)/60>10^10`, et le second inférieur à200 alors que `u0/40>10^22`. Les dérivées correspondantes sont négatives ensuite. Cette route réemploie NG54 sur des supports disjoints ; elle n'est pas un nouveau gain à additionner à NG54 du secteur entier ou à C7.

## 6. Obligation arithmétique exacte qui demeure

Le mécanisme a remplacé une couverture postulée par un défaut calculable ; il n'a pas estimé ce défaut. Après paiement de F, il faut une information indépendante sur les préfixes intérieurs

\[
P_{c,q}^{\rm int}(x)=\#\{p\le x:\ p,N-cqp\text{ réellement premiers, gardes C11}\},
\]
\[
T_{c,q}(x)=\#\{rs\le x:\ r<s\text{ premiers},\ cr,cs\le a<rs,
\ (cqrs,N)=1,\ N-cqrs\text{ réellement premier}\}.
\tag{C17}
\]

Le `max` de leurs différences de préfixes est non linéaire. Une estimation de la différence finale des **cardinaux non pondérés** ne garantit pas la couverture injective descendante des parents précoces. Cette nécessité concerne seulement le matching proposé : la parenthèse C16 est exactement `sum_P log n−sum_T log n`, indépendante du matching. Les images tardives non utilisées gardent leur masse négative et peuvent donc compenser autrement si l'on démontre une comparaison pondérée globale indépendante ; aucune impossibilité de cette voie n'est alléguée. Un comptage de produits rs sans `N−cqrs` premier ne compte aucune capacité physique suffisante. Pour un bloc non vide, `cq<N/a≤N^(9/16)` ; aucune restriction `cq≤N^(1/2)` n'est acquise. Le coefficient cq comprend q réellement premier, tandis que les images gardent `r,s≤a/c`, `r>c`, squarefreeness et unités. Un résultat sur un premier et son voisin semipremier, cité sans identification des supports, n'apporte pas automatiquement l'autre incidence `N−cqrs`, les deux caps de facteurs, ce conducteur cq ni l'unité N. On ne l'importe pas sous le nom de Chen. Ni un seuil BV effectif supplémentaire ni une densité de ce sous-ensemble ne sont déduits.

Cette obligation est une comparaison de **deux familles d'incidences premières explicitement différentes**, mesurable par C13–C14 ; elle est indépendante comme énoncé de comptage et peut échouer sur un préfixe fini. Elle n'est pas établie ici et n'est pas utilisée comme hypothèse pour annoncer le résultat ciblé. Même la servir entièrement ne paierait pas J0, J1 hors T, les autres cofacteurs c de J2, nonbulk, célibataires/faces, terme couvert, référence bilatérale, onset BV physique supplémentaire ou `2max(e,0)`.

## 7. Ledger et retrait sans double crédit

Conserver exclusivement

\[
D_N=B_{\rm prime}^a+B_{\rm pp}^a+P_{\rm band}^{\ge2}
+Z_{\rm face}^{\ge2}+I_\alpha+2\max(e,0).
\]

P5 reste sur K2 du **J2 bulk entier** avant retrait. Avec `κ_m=(log c+S(N))log n`, `e_m=−δ_m log n`, pour un matching disjoint P* et le front F disjoint,

\[
B_{J2,bulk\setminus(F\cup P^*)}
=K_2-\sum_F\kappa_m-\sum_{P^*}\kappa_m
+\left(R_{J2,bulk}-\sum_F e_m-\sum_{P^*}e_m\right). \tag{C18}
\]

La parenthèse porte exactement sur le complément restant. C9 paie B_F et non une multiplicité fictive de ses parents. Le matching utilise ses deux vertices une fois ; la fenêtre normalisée C5 demande au lieu de C18 un retrait pondéré `d_P/H`, avec l'erreur pondérée correspondante. Ces deux routes sont alternatives. L'erreur du secteur entier ne s'ajoute pas à nouveau aux mêmes vertices. Aucune charge favorable `−sum_U_T`, aucun `−sum_G log(n_t/n_p)` et aucun bénéfice P5 entier ne sont effacés pour déclarer une capacité. Le secteur physique `q|k` garde sa phase source1 ; la présente extraction ne transforme aucune cellule HH ni ce terme en une phase libre.

## 8. Contrats numériques14 neufs et falsifiables

Paramètres exacts : `N=100000000`, `alpha=100`, `a=3163`, `Q=999999`, `M=1000000`. H=2 est certifié par `1^64<N≤2^64`, sans flottants. N est hors du seuil source : aucun signe asymptotique ni paiement analytique n'est certifié numériquement.

### F1 — fenêtre H2 entière à degré zéro

Le rôle6 a trouvé au préflight un **nouveau** q=3581, avec `(m,n)=(35698989,64301011)` pour c3,p3323 et `(34023081,65976919)` pour c3,p3167. Ses primalités, unités et supports sont des données de préflight à confirmer dans son nouveau gate strict, pas un PASS fabriqué dans ce rapport. Vérifier indépendamment que q3581, p3323 et3319 sont premiers. Pour le parent neuf `(c,p,q)=(3,3323,3581)`, les deux shifts entiers sont

\[
p-2=3321=3^4\cdot41,\qquad p-4=3319\text{ premier}.
\]

h1 viole squarefreeness et la distinction du facteur c ; h2 n'est pas un produit de deux premiers distincts. Ainsi d_P=0 sur **toute la fenêtre** `{1,2}` avant de demander un premier image. Le promoteur « tout parent possède une image dans E_H » est un `ERROR_FALSIFIER` si le parent est réellement présent. Le promoteur « un masque jouet peut remplacer les n premiers » n'est jamais un candidat accepté. Garder le vrai bracket de ce parent, sans imposer son signe fini.

### F2 — graphe complété du même bloc, front et intérieur distincts

Pour le même q3581, confirmer `N−3·3167q` réellement premier unitaire. Il s'agit d'un **nouveau vertex q** et de nouveaux m,n ; aucun ancien point n'est rejoué. Le front exact du bloc est `L=min(3580,floor((N−Q−1)/(3·3581)))=3580`. Pour ce parent p3167, aucune image t strictement entre a3163 etp3167 n'est unitaire N :3164 et3166 sont pairs,3165 est divisible5. Le déficit de préfixe de P_all est donc au moins1 au point3167. Cela réfute une couverture universelle du graphe entier, mais **ne réfute pas** une estimation de P_int après retrait du front payé `{a<p≤a+2H}`.

Pour le q fixé, énumérer les ensembles C11 **complets**, jusqu'au L littéral, toutes primalités/unités certifiées. Produire les deux variantes P_all etP_int, le même T, leurs arêtes t<p, l'appariement déterministe, C12–C14, les deux restes et C15 sur les vrais D/W. Les sorties doivent garder les deux kernels, leurs deux fronts stricts et k1 joint. Une image avec `N−cqrs` composite n'est pas incluse comme capacité. Le déficit intérieur observé peut être nul ou non nul : aucun verdict de signe ou de couverture intérieure n'est fixé à l'avance.

### F3 — multiplicité et principal

Sur le bloc complet q3581, prendre `E_H={(p,t) in P_all×T : 1≤(p−t)/2≤2}`, puis vérifier `d_P,d_T≤H` et C5 sur tous ses vertices, y compris ceux de degré zéro. Si aucune arête existe pour F1, ce vertex garde coefficient restant1 ; son exemple ne suffit pas à valider une charge image sur d'autres vertices. Pour toute arête retrouvée, vérifier les diviseurs courts complets, les quatre facteurs de l'image, la relation `n_t=n_p+2hcq`, C3/C4, et le modèle formel `−(log c+S)log(n_t/n_p)` avec S symbolique. Le principal favorable n'est pas substitué aux deux vrais W dans le PASS.

Les statuts attendus sont `PASS_IDENTITY_ONLY`, `ERROR_FALSIFIER` pour les promotions précises, et `OPEN_ARITHMETIC_COVERAGE`. Aucun `UNRESOLVED` ne peut servir de certificat de signe. Les gates sont distincts des compilations ; un échec d'une formule arithmétique n'est pas un échec Lean. C6–C10 et le paiement U4 ne sont pas des tests analytiques finis.

## 9. Obligation Lean et décision

Si un gate neuf est positif, les obligations formelles sont les gardes variables h, les canonicalités à h fixé, les bornes de degrés, C5 avec les deux déficits, puis la récurrence finie C12–C15 sur des ensembles réellement arithmétiques. Ces preuves de charge et de comptage fini ne doivent prendre ni une hypothèse `D_k≈0` ni la petitesse du résidu comme prémisse.

Elles ne constituent toutefois pas, seules, une sélection quantitative utile pour briser la parité. Une formalisation du défaut exact ou du petit coût C7 sans information nouvelle sur C17 reproduirait le problème de capacité sous une forme calculable. Le gain indépendant établi est limité au front entier C9. **Aucune estimation de la masse intérieure non appariée n'est prouvée.** La cible `D_N≤N/(256u log u)` reste ouverte ; victoire fausse, score0. Le rapport est FINAL conceptuel et gelé ; le rôle6 puis le coordinateur lieront leurs reçus séparés sans le modifier.
