# Agent 1 — boucle 6 : dilatations finies du profil réel

## Verdict et portée

Le transfert qui déduit un gain sur le résidu de corrélations nulles, sans payer sa couverture, est réfuté sur le profil arithmétique réel à N=100000000. Une tête exacte suffit : S_303 est strictement négatif, tandis que toutes les dilatations par 2 et 5 sont nulles. Le défaut porte alors toute la tête. La calibration de la construction BSZ publiée, tentée au budget demandé, place en outre son premier intervalle de premiers au-delà de N. Ces deux diagnostics rejettent cette application proposée avant compilation.

Ils ne réfutent ni toute méthode de Kátai, ni une nouvelle partition finie convenablement calibrée. Aucun gain nouveau sur D_N, aucune petite corrélation arithmétique sur les premiers utiles p ne divisant pas N, et aucune victoire Lean ne sont établis. Une identité de Gram générique ne sera pas soumise comme percée.

Les contraintes Arbor ont été lues sans modification. Les artefacts antérieurs et le cadre fixé sont conservés. Les seuls résultats externes utilisés ci-dessous viennent de la source primaire [Bourgain–Sarnak–Ziegler, arXiv:1110.0992v1](https://arxiv.org/pdf/1110.0992).

## Le profil global exact, sans nouveau masque

Posons u=log N, ell=log u, alpha=ceil(N^(1/4)), Q=floor((N−1)/alpha), m=N−n, et rho(n)=1_(n>1) 1_(gcd(n,N)=1). Les noyaux complets sont

```
D(m) = sum_(k|m, 1<=k<=Q, alpha*k<m) mu(k) log(k/m),
W(n,m) = sum_(1<=k<=Q, gcd(k,n*N)=1, alpha*k<m)
                    mu(k)/phi(k) log(k/m),
K(n,m) = D(m)−W(n,m).
```

Pour chaque m, le préfixe littéral est R(m)=min(Q,floor((m−1)/alpha)). La face alpha*k<m est stricte. Le profil étendu par zéro hors de 1<=m<N est

```
F_N(m) = rho(N−m) [Lambda(N−m)−log(N−m)] K(N−m,m).
S_full = sum_(1<=m<N) mu(m) F_N(m).
```

Il n'y a pas de facteur mu(N−m)^2 dans F_N. Les puissances premières propres sont conservées : fII(p^j)=−(j−1)log p pour j>=2. Les masques carrés-libres de certaines cellules HH ne deviennent pas un masque du profil global. Le facteur mu(m) reste extérieur.

Le pont autoritatif de la monographie, §6, Remark 6.3, demeure

```
D_N = −S_full + 2 max(e,0).
```

Un gain absolu sur S_full ne paie donc pas automatiquement e. Pour une tête X<N−1, il faut aussi conserver S_tail=sum_(X<m<N) mu(m)F_N(m), avec S_full=S_X+S_tail. Le calcul S_303 ci-dessous ne prétend pas contrôler cette queue.

## Audit fini de l'amplificateur et de son défaut

Pour une partie finie non vide P de nombres premiers et 1<=X<=N−1, définissons

```
c_P(n) = sum_(p in P) 1_(p|n),
a_X = (1/X) sum_(p in P) floor(X/p),
S_X = sum_(1<=n<=X) mu(n) F_N(n),
R_X = sum_(1<=n<=X) mu(n) F_N(n) [a_X−c_P(n)].
```

On exige a_X>0. Si M=floor(X/min P), la multiplicativité réelle de mu donne

```
B_X(m) = sum_(p in P, p*m<=X, p∤m) F_N(p*m),
a_X S_X = −sum_(m<=M) mu(m) B_X(m) + R_X.
```

En effet mu(pm)=−mu(m) si p∤m, et mu(pm)=0 si p|m. Le terme R_X est présent exactement; ce n'est pas une petite erreur démontrée. Les termes non couverts c_P(n)=0 et ceux de multiplicité excessive y restent tous.

Pour mesurer le coût sans supposer de cancellation, le carré réel de B conserve les diagonales. En notant Q_sf=sum_(m<=M) mu(m)^2,

```
G_sf = sum_(m<=M) mu(m)^2 |B_X(m)|^2,
E_p = sum_(m<=floor(X/p), p∤m) mu(m)^2 |F_N(pm)|^2,
C_pq = sum_(m<=floor(X/max(p,q)), gcd(m,p*q)=1)
                              mu(m)^2 F_N(pm) F_N(qm),
G_sf = sum_p E_p + 2 sum_(p<q) C_pq.
```

Les F_N sont réels. Le facteur mu(m)^2 de ces sommes provient du coefficient dans Cauchy; il ne modifie pas F_N. Les deux faces pm<=X et qm<=X ainsi que leurs propres préfixes R(pm), R(qm) restent dans C_pq.

Le coût de couverture élémentaire est exact :

```
V_X = sum_(n<=X) [a_X−c_P(n)]^2
    = sum_p floor(X/p) + 2 sum_(p<q) floor(X/(p*q)) − X*a_X^2.

|S_X| <= [ ||F_N||_(2,1..X)*sqrt(V_X) + sqrt(Q_sf*G_sf) ] / a_X.
```

Cette dernière inégalité est seulement un audit des charges. Elle n'est ni un candidat de victoire, ni une estimation arithmétique indépendante. Aucune borne hypothétique sur C_pq n'est ajoutée.

## Falsification exacte : corrélations nulles et masse entièrement non couverte

Si p|N, alors F_N(pm)=0 pour tous les m avec pm<N : gcd(N−pm,N)=gcd(pm,N)>=p annule rho. Pour P constitué de tels premiers, B_X=G_sf=E_p=C_pq=0. Mais sur le support non nul de F_N(n), gcd(n,N)=1, donc c_P(n)=0. Par conséquent

```
R_X = a_X S_X.
```

Le transfert ne transporte aucune masse. Voici une instance non nulle à vérifier avec les vrais noyaux, sans signe formel arbitraire.

Prenons N=100000000, alpha=100, Q=999999, X=303 et P={2,5}. Pour m<=300 avec gcd(N−m,N)=1, m est impair, seuls k=1,2 peuvent être actifs, et k=2 est absent de D comme de W. Le terme k=1 coïncide; ainsi K=0. Les points non unitaires ont déjà F_N=0.

À m=301, k=3 est actif mais 3|(N−301); il est exclu de W et ne divise pas 301, donc K=0. Le point 302 est non unitaire. Enfin

```
m=303=3*101,
n=N−303=99999697=7*41*348431,
K(n,303)=−(1/2)log(3/303)=(1/2)log101,
mu(303)=1,
Lambda(n)=0.
```

La présence des deux facteurs premiers distincts 7 et 41 suffit pour Lambda(n)=0. On obtient l'égalité exacte

```
S_303 = −(1/2)log(99999697)log101 < 0,
a_303 = (151+60)/303 = 211/303,
B_303 = G_sf = 0,
R_303 = −(211/606)log(99999697)log101 = (211/303) S_303 != 0.
```

Cela réfute précisément « corrélations nulles donc gain sans défaut de couverture ». Cela ne réfute aucune annulation dans la somme globale complète. L'Agent 6 a reçu les égalités pour un contrôle symbolique par coefficients rationnels de produits de logarithmes.

## Normalisation réelle et prix des enveloppes disponibles

Puisque 0<=Lambda(n)<=log n, on a |fII(n)|<=u. Posons A_Q=sum_(k<=Q)1/phi(k). Chaque logarithme actif a une valeur absolue au plus u, d'où

```
|F_N(m)| <= u^2 [tau(m)+A_Q].
```

Les identités et inégalités élémentaires suivantes donnent une enveloppe finie indépendante :

```
1/phi(k) = (1/k) sum_(d|k) mu(d)^2/phi(d),
A_Q <= (1+log Q) product_p [1+1/(p(p−1))]
    <= e(1+log Q) < 3(1+log Q),
tau(m)^2 <= d_4(m),
sum_(m<=X) d_4(m) <= X(1+log X)^3.
```

La borne du produit utilise sum_p 1/(p(p−1))<=sum_(j>=2)1/(j(j−1))=1. Pour tau^2<=d_4, l'inégalité locale est (j+1)^2<=binomial(j+3,3). En conséquence

```
||F_N||_2^2 <= 2u^4 X[(1+log X)^3+A_Q^2]
             <= 20u^4 X(1+u)^3,
sup_(m<N) |F_N(m)| <= u^2[2sqrt(N)+3(1+u)].
```

Ces majorants sont coûteux, mais ils sont effectivement applicables au profil complet. Ils ne prouvent pas que sa vraie norme est aussi grande. Pour X=N−1 et P={3,7,11,13}, les comptes entiers donnent

```
sum_p floor(X/p) = 64402263,
sum_(p<q) floor(X/(p*q)) = 13453211,
a_X = 7155807/11111111,
V_X = 553690769907794/11111111.
```

Le facteur sqrt(V_X/X)/a_X vaut environ 1.0961. Avec l'enveloppe L2 ci-dessus, la couverture seule reste donc d'ordre N*u^(7/2), contre N/(256u*ell). Ces décimales sont une boussole; les comptes et fractions précédents sont exacts.

Une troncature à hauteur H ne résout pas gratuitement la normalisation : sa queue en valeur absolue est au plus ||F_N||_2^2/H. Pour la payer par N/(1024u*ell) au moyen de cette enveloppe, une hauteur suffisante est

```
H >= 20480*u^5*(1+u)^3*ell.
```

C'est une calibration conservatrice suffisante, pas une nécessité optimale. Elle rend la précision relative demandée au profil normalisé encore plus petite. Il faudrait une estimation spécifique de la distribution des amplitudes pour améliorer ce coût.

## Ce que BSZ dit, et ce que sa calibration permet ici

Le théorème 2 de la source primaire suppose |F|<=1 et des corrélations de dilatations au plus tau*M pour tous les couples distincts de premiers jusqu'à exp(1/tau), pour M suffisamment grand. Il conclut 2sqrt(tau log(1/tau))*L pour L suffisamment grand. Les seuils dépendent du paramètre. Le théorème 1 sur les horocycles ne fournit pas de taux. La preuve du théorème 2 emploie, pour un paramètre a fixé, j0=a^(-1)log^3(1/a), j1=j0^2, D0=(1+a)^j0 et D1=(1+a)^j1, avec un poste asymptotique affiché 4a avant le terme de corrélation. Source : théorème 2 et §2, équations (2.1), (2.14), (2.20), (2.21).

Appelons H une vraie majoration uniforme de |F_N|, et delta=1/(256H*u*ell). Même en accordant tout le budget au gain sur S_full et en laissant e encore impayé, tenter de payer le poste affiché 4a*H*N impose la calibration

```
a <= delta/4 = 1/(1024H*u*ell).
log D0 = [log(1+a)/a] log^3(1/a),
log D1 = [log(1+a)/a] a^(-1) log^6(1/a).
```

Le choix final publié a=sqrt(tau) demande également 2sqrt(tau*log(1/tau))<=delta, donc tau*log(1/tau)<=delta^2/4. Il ne permet pas de garder un tau fixe quand delta tend vers zéro. Dans les bins j, les corrélateurs sont évalués à des longueurs de l'ordre floor(N/(1+a)^j), jusqu'au bas de l'ordre N/D1. Pour invoquer les hypothèses asymptotiques à toutes ces longueurs, il faudrait un seuil de corrélation effectif et uniforme M0 sur les couples sélectionnés, puis au minimum N/(1+a)^(j1+1)>=M0. Ni ce seuil uniforme, ni les estimations finies de couverture de ces bins ne sont fournis par l'application proposée.

À N=100000000, H>=1 est déjà imposé par le point réel m=311 décrit plus bas. Comme u>16 et ell>2, cette calibration donne a<1/32768. Pour 0<a<1, log(1+a)>=a/2; log(1/a)>10. Donc

```
log D0 > 500 > log(100000000).
```

Le secteur des entiers <=N possédant un premier dans (D0,D1) est vide. La fraction de couverture affirmée asymptotiquement pour a fixé ne peut pas être importée à ce N après cette substitution. Remplacer D0 ou D1 par un seuil tronqué demanderait une nouvelle preuve finie de couverture et le paiement de ses diagonales et de ses extrémités.

Même asymptotiquement, pour H>=1 et a d'ordre 1/(u*ell), log D1 est au moins de l'ordre u*ell^7, alors que log N=u. Cette construction inchangée ne produit donc pas la précision variant avec N envisagée. Les constantes d'asymptotique et les seuils M,L ne sont pas des constantes finies uniformes pour la famille F_N. Étendre chaque F_N par zéro puis laisser L tendre vers l'infini rendrait son corrélateur trivialement petit à terme; cela ne donne aucune estimation à L=N.

Pour orientation seulement, le point m=311 impose H>=42.7468 environ, delta<=1.7028e−6 et a<=4.2568e−7; à la borne proposée, log D0 est environ 3156.85. La preuve précédente par inégalités strictes, et non ces décimales, suffit au rejet de la calibration.

## Secteur non couvert : profil raw et cellules HH distingués

Le profil global ne supprime pas automatiquement les grands m premiers. À N=100000000,

```
m=311 premier,
n=99999689=113*199*4447,
K(n,311)=−(1/2)log(311/3),
F_N(311)=(1/2)log(99999689)log(311/3)>1.
```

Le point est unitaire. Le préfixe est k<=3; k=2 est exclu et k=3 est actif dans W mais ne divise pas m. Ce calcul a été confirmé par l'Agent 6. Il réfute seulement la suppression de ce point raw, pas une assertion sur la composante HH isolée.

Dans une cellule HH divisible, H_y=mu_(>y)*mu_(>y)*zeta est au contraire nul en 1 et en tout nombre premier lorsque y>=1. Un m premier n'y donne aucune fibre r contributive. Pour m=p*q carré-libre avec p!=q, la seule fibre possible est r=m; elle donne H_y(m)=2 si p,q>y, et zéro sinon. Les semipremiers qui vérifient ces conditions subsistent donc réellement.

Le tuple initial de la boucle 5 donne un exemple HH exact non couvert par P={3,7,11,13} :

```
b=13, u=3, v=7, x=1, k=1, s=7951, t=12577, z=1,
n=273, m=r=99999727=7951*12577,
b*u*v*x + k*s*t*z = 100000000.
```

Pour y=2, H_y(21)=H_y(r)=2, et la fibre développée porte 4log13*log99999727>0, avec les sélecteurs d'unités, de carrés-libres et de cap conservés. Pourtant c_P(m)=0. Ainsi la structure HH ne paie pas d'elle-même le secteur semipremier non couvert. Pour passer d'une analyse HH à S_full, les autres composantes, les têtes et les défauts doivent également rester dans le pont.

## Obligation restante et décision de protocole

Les seules petites corrélations démontrées ici sont celles qui résultent du masque p|N. Elles ne couvrent aucun point où F_N est non nul. Pour p,q ne divisant pas N, le corrélateur réel contient simultanément

```
mu(m)^2 * 1_(gcd(m,p*q)=1)
* rho(N−pm) rho(N−qm)
* fII(N−pm) fII(N−qm)
* K(N−pm,pm) K(N−qm,qm),
```

sur sa double face exacte. Aucun acquis cité ne fournit ici de gain signé quantitatif sur ce profil, ni de contrôle favorable de son défaut de couverture. La relation multiplicative de mu ne retire pas les coefficients additifs fII ni les noyaux mobiles. Leur estimation est l'obligation réelle; l'inscrire comme hypothèse serait déplacer la cible.

La tentative favorable « dilatations nulles et transfert sans couverture » est rejetée sur S_303 avant Lean. La calibration standard BSZ est également rejetée dans sa portée précise. Il n'y a aucun nouveau fichier Lean à demander pour ces conclusions, aucun contrôle nouveau de D_N et aucun rapport de victoire. Un prochain mécanisme devrait d'abord fournir une estimation arithmétique indépendante sur des dilatations utiles ou un paiement démontré de leur masse non couverte, avec le même pont complet.
