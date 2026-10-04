# Agent 3 — audit du contrat de formalisation, boucle 6

**Statut : REJECTED_BEFORE_COMPILATION.** Aucun fichier Lean n'est soumis pour cette tentative. Le rejet concerne le transfert qui omet le défaut de couverture, ainsi que l'application proposée de la calibration BSZ inchangée. Les identités finies correctes restent valables. Aucune erreur du compilateur Lean n'est inventée, aucun acquis de la monographie n'est retiré, et aucune impossibilité générale de la méthode de Kátai n'est affirmée.

Le nœud 9 conserve explicitement R_X et les diagonales : **son identité exacte n'est pas réfutée** (`IDENTITY_NOT_FALSIFIED`). Son mécanisme quantitatif favorable n'est pas obtenu (`QUANTITATIVE_GAIN_NOT_OBTAINED`). Le contre-exemple vise uniquement le raccourci qui supprime R_X (`SHORTCUT_FALSIFIED_BEFORE_COMPILATION`). Ces verdicts n'autorisent pas à pruner toute la piste de dilatation.

## Objets et sources vérifiés

L'audit porte sur `agent1_finite_dilation.md`, `katai_checks.py`, `katai.json` et `exact_tools.py` de cette boucle, sur le calcul littéral `numerical/round2_checks.py`, et sur les définitions de la monographie extraite, §6, pp. 12–14. Les documents sont des sources de notations ; la condition de victoire vient de la demande de l'utilisateur.

Pour le profil quartique, on conserve exactement alpha = ceil(N^(1/4)), Q = floor((N-1)/alpha), m = N-n et

```
D(m) = sum_(k|m, 1<=k<=Q, alpha*k<m) mu(k) log(k/m),
W(n,m) = sum_(1<=k<=Q, gcd(k,n*N)=1, alpha*k<m)
                   mu(k)/phi(k) log(k/m),
F_N(m) = 1_(0<m<N) 1_(N-m>1) 1_(gcd(N-m,N)=1)
         [Lambda(N-m)-log(N-m)] [D(m)-W(N-m,m)].
```

L'extension est zéro hors de cette face. Le préfixe harmonique est l'entier min(Q, floor((m-1)/alpha)), et non floor(m/alpha). Le masque d'unité dépend de l'argument dilaté : dans F_N(pm), il est gcd(N-pm,N)=1, avec son propre préfixe. Le facteur mu(m) est extérieur à F_N. Il n'existe pas de nouveau masque mu(N-m)^2. Les puissances premières propres restent présentes, avec fII(p^j)=-(j-1)log p. La convention à n=1 donne fII(1)=0 ; l'exclusion explicite n>1 n'ajoute donc aucune contribution au scalaire de la monographie.

Le pont complet conservé est

```
S_full = sum_(1<=m<N) mu(m) F_N(m),
S_full = -E_cov + e + S_unc,
D_N = E_cov-S_unc+|e| = -S_full + 2 max(e,0).
```

Pour X<N-1, S_X n'est qu'une tête et S_tail = sum_(X<m<N) mu(m)F_N(m) reste obligatoire. Une cellule HH développée n'est pas le profil raw complet : les autres composantes et leurs raccords ne sont pas automatiquement supprimés.

## Identités finies : audit positif, sans gain nouveau

Le contrat mathématique prend une **partie finie de premiers distincts** P, X entier avec 1<=X<N, et a_X = X^(-1) sum_(p in P) floor(X/p)>0. En Lean, `Finset` et une preuve de primalité de chacun de ses membres seraient nécessaires. Les tuples numériques utilisés sont distincts ; la fonction Python ne teste pas elle-même l'absence de doublons, ce qui ne gêne pas ses cas actuels mais doit être fixé dans une interface générale.

Avec c_P(j)=sum_(p in P)1_(p|j), R_X=sum_(j<=X)mu(j)F_N(j)(a_X-c_P(j)), M=floor(X/min(P)) et

```
B_X(t) = sum_(p in P, p*t<=X, p∤t) F_N(p*t),
T_X = sum_(1<=t<=M) mu(t) B_X(t),
```

on obtient exactement a_X S_X = -T_X + R_X. Le changement de variables j=pt est injectif pour chaque p. Pour p∤t, mu(pt)=-mu(t), y compris lorsque t n'est pas carré-libre ; pour p|t, mu(pt)=0. Omettre p∤t dans B_X changerait donc l'identité. Aucune multiplicativité complète de mu n'est utilisée.

Les coefficients sont réels. En développant le carré,

```
Q_sf = sum_(t<=M) mu(t)^2,
G_sf = sum_(t<=M) mu(t)^2 B_X(t)^2
     = sum_p E_p + 2 sum_(p<q) C_pq,
```

où E_p conserve t<=floor(X/p) et p∤t, et C_pq conserve t<=floor(X/max(p,q)) et gcd(t,p*q)=1. Les deux évaluations du profil, leurs masques mobiles et leurs fronts internes restent dans C_pq. Les diagonales E_p ne sont pas jetées. Le coefficient mu(t)^2 vient de la somme de Cauchy, pas d'un changement de F_N.

La Cauchy pondérée |T_X|<=sqrt(Q_sf*G_sf) est correcte : écrire mu(t)B_X(t)=mu(t)[mu(t)^2 B_X(t)] utilise explicitement mu^3=mu et mu^4=mu^2. Ces propriétés se prouvent à partir des valeurs de la fonction arithmétique mu ; elles ne constituent pas de nouvelles hypothèses analytiques.

La variance de couverture est exactement

```
V_X = sum_(j<=X)(a_X-c_P(j))^2
    = sum_p floor(X/p) + 2 sum_(p<q) floor(X/(p*q)) - X*a_X^2.
```

La coprimalité de deux premiers distincts justifie le dénominateur pq. Il en résulte |R_X|<=||F_N||_2 sqrt(V_X), puis la majoration de |S_X| donnée par l'Agent 1. Ces relations sont des identités et des inégalités standard ; elles ne prouvent aucune petite corrélation, ni une petite couverture pour le profil réel.

## Contre-exemple exact au transfert sans couverture

J'ai recalculé en lecture seule le cas N=100000000, alpha=100, Q=999999, X=303 et P={2,5}. Jusqu'à X, le seul argument où F_N est non nul est m=303.

Pour les m unitaires jusqu'à 300, seuls k=1,2 peuvent être actifs et k=2 est exclu des deux noyaux. À m=301, k=3 ne divise pas m et est exclu du noyau harmonique parce qu'il divise N-m. Le point 302 est non unitaire. Au dernier point,

```
303 = 3*101,
99999697 = 7*41*348431,
D(303)-W(99999697,303) = (1/2)log101,
mu(303)=1,
Lambda(99999697)=0,
S_303 = -(1/2)log(99999697)log101 < 0.
```

La factorisation en deux facteurs premiers distincts 7 et 41 suffit déjà à exclure une puissance première. Le calcul en coefficients rationnels de produits de logarithmes donne exactement

```
S : (log7 log101), (log41 log101), (log101 log348431),
    coefficient -1/2 pour chacun ;
a_303 = 211/303 ;
R : les mêmes trois monômes, coefficient -211/606 pour chacun ;
B_X = 0, G_sf = 0, R_303 = (211/303)S_303 != 0.
```

Le signe négatif a aussi été certifié par des intervalles rationnels de logarithmes. Il n'est pas inféré d'un flottant.

La raison de B_X=0 est structurelle : si p|N, alors F_N(pt)=0 partout, par le masque d'unité. Simultanément, tout argument où F_N est non nul est premier à N, donc c_P(j)=0 pour P={2,5}. Les corrélations nulles ne voient ainsi aucune masse effective, et **R_X porte toute la somme**. L'étape erronée serait de supprimer R_X dans a_X S_X=-T_X+R_X, ou de conclure S_X>=-sqrt(Q_sf G_sf)/a_X. Cette dernière conclusion exigerait ici S_303>=0, et est fausse.

Ce témoin ne contredit pas un théorème BSZ correctement appliqué à tous ses premiers, ni une borne globale future. N=10^8 est un test fini ; il n'appartient pas au domaine analytique log N>=1024 du cadre. La queue de 99 999 696 arguments après 303 n'a pas été évaluée. Le défaut constaté ne dépend toutefois d'aucun test de cette queue : le transfert sans couverture est une identité/inégalité finie proposée, et son oubli est déjà réfuté.

Le reçu `katai.json` lu pendant cet audit contient X=512 et X=1024, et non X=303. Ces autres témoins confirment eux aussi le défaut, mais ne sont pas présentés comme le reçu de mon recalcul minimal. L'Agent 6 a été informé de cette différence de traçabilité.

## Norme et calibration : obligations non résolues

Les enveloppes de l'Agent 1 sont compatibles avec les noyaux réels : |fII|<=log N, |log(k/m)|<=log N sur les termes actifs, et A_Q=sum_(k<=Q)1/phi(k). L'identité 1/phi(k)=k^(-1)sum_(d|k)mu(d)^2/phi(d), l'encadrement de son produit eulérien et tau(m)^2<=d_4(m) donnent les majorants L2 et uniformes annoncés. Ils ne permettent pas d'affirmer |F_N|<=1. Leur coût est un majorant disponible, et non une minoration de la vraie norme.

La source primaire [Bourgain–Sarnak–Ziegler, théorème 2 et §2](https://arxiv.org/pdf/1110.0992) porte sur un profil uniformément borné par 1, des corrélations de tous les couples requis et des longueurs suffisamment grandes. Dans sa construction, un paramètre a fixé détermine j0=a^(-1)log^3(1/a), j1=j0^2 et D0=(1+a)^j0. Le poste affiché 4a nécessite une nouvelle calibration lorsqu'on vise une précision dépendant de N. Ici, avec une vraie enveloppe H>=1, le choix proposé a<=1/(1024 H log N log log N) donne à N=10^8 a<1/32768 et log D0>500>log N. Aucun entier de la plage ne possède alors de premier dans les bins utilisés. La couverture asymptotique à paramètre fixé ne peut pas être importée après ce changement. C'est le rejet de cette calibration inchangée, et non une interdiction de toute partition finie différente.

## Contrat minimal pour une prochaine formalisation admissible

Une nouvelle identité exacte est recevable comme **mécanisme à tester** si elle relie les coefficients arithmétiques réels, et non des signes ou des poids libres, tout en conservant les unités, les faces strictes, la coprimalité, les puissances premières et les raccords couverts/non couverts. Pour qu'elle soutienne la victoire demandée, il faut aussi un gain démontré qui traite la contribution effectivement utile sur r>alpha.

Dans la présente piste, cela demanderait les éléments suivants, établis et non postulés :

1. Une famille finie explicite de premiers utiles et une identité d'amplification sur le profil complet, ou un découpage en cellules avec un recombinaison exacte. Les premiers divisant N, qui annulent le profil dilaté, ne peuvent pas être présentés comme une couverture utile.
2. Une estimation arithmétique indépendante des corrélateurs réels, avec leurs deux fronts, leurs diagonales et leurs coefficients fII et D-W ; une borne arbitrairement introduite sur C_pq serait déplacer l'obligation.
3. Un paiement prouvé du défaut R_X, de la queue éventuelle, des cellules écartées et du terme 2 max(e,0), avec des constantes et un domaine explicites. Une estimation signée de leur combinaison peut remplacer des estimations absolues, si cette combinaison reste exactement celle du pont.
4. La justification de toute normalisation H, troncature d'amplitudes et de toute erreur de bord. Un résultat qualitatif o(N), ou une hypothèse de corrélation « pour M assez grand » sans seuil uniforme applicable aux longueurs utilisées, ne fournit pas la précision demandée pour la famille F_N.

L'obligation exacte de fermeture de cette amplification est

```
D_N = (T_X-R_X)/a_X - S_tail + 2 max(e,0).
```

Une voie suffisante, sans prétendre être nécessaire, serait de prouver indépendamment des budgets E_G, E_R, E_tail, E_e tels que sqrt(Q_sf G_sf)<=E_G, |R_X|<=E_R, |S_tail|<=E_tail, 2 max(e,0)<=E_e, puis de vérifier (E_G+E_R)/a_X + E_tail + E_e <= N/(256 log N log log N). Les preuves des budgets, et non leur introduction comme hypothèses, seraient la substance nouvelle. Une identité standard suivie de cette liste d'hypothèses ne remplit pas la condition de victoire.

## Traçabilité et décision

Empreintes des entrées au moment de l'audit :

```
agent1_finite_dilation.md e2533090213ef0573bcb7fb73f496355d4f90a3283cada50735370b953dcce7f
katai_checks.py          81b4a735e3c07629b329770f9f13245d71143b8edf3a559f09a1b2d6e034bf0f
katai.json               15a05926ffd99fa208c8192c5ea316b2bd560c1bf0476dc1663aa67026a15e15
exact_tools.py           f48bb0b2b608aa734944cbfe978c19ad55f5aa249068dcc313a1de6da5a393cc
```

Le vérificateur de conservation confirme les 160 fichiers antérieurs inchangés, registre de référence bff50b025ed0ca2f072739edcfc04e91c94acd8f7d9cff24b27c53a2f5928684. Cet audit ajoute seulement ce rapport. Son résultat ne doit pas augmenter le nombre de théorèmes Lean validés, et aucune compilation n'est alléguée. Le candidat favorable est rejeté avant compilation conformément au protocole ; le problème quantitatif originel reste ouvert dans ce travail.
