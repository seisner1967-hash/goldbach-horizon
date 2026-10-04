# Agent 1 — compensation 3-adique des incidences premières, boucle 11

**Rapport mathématique final : compensation indépendante écrite du modèle sur les incidences conjointes ; incidences célibataires, faces et entropies encore ouvertes.** La paire entière n'est pas favorable en général. Les deux indicatrices premières et les deux noyaux réels sont conservés dans le premier contrat. Aucun paiement du préfixe bas n'est assimilé au paiement de l'annulus, aucune marge de paires premières n'est inventée, aucune victoire n'est alléguée. Le gate numérique final et le rejeu du Juge restent indépendants ; le statut Lean nouveau est encore pending.

Entrées lues : `round11/PROBE_BLOCK.md`, retour final `round10_feedback.md`, audits finaux `round10/agent3_formalisation.md` et `agent4_formalisation.md`, source §§6.2–6.3, 10.2 autour de (44), 12.7 autour de la borne S(N)<3ell. La boucle 10 et tous les antérieurs sont gelés ; ce rôle écrit exclusivement le présent fichier.

## 1. Analyse de principes et deux directions

La compensation réellement recherchée porte sur H2-S(N)M2 avec les secteurs J0/J1 et les blocs favorables. Le nombre J_c n'est pas une densité supposée régulière en c : il impose p,q,N-c*p*q premiers, p<q canoniques et les vraies unités. La variable mu(c) est courte, mais son poids n'est pas un préfixe de Möbius ordinaire.

Première direction : appairer c et 3c sous le même couple p<q et conserver les deux incidences premières. Lorsque les deux premiers n=N-c*p*q et n3=N-3c*p*q existent, leur modèle principal se combine en un logarithme de quotient, au lieu de deux masses de taille log N. Ce logarithme est estimable positivement par un crible des deux formes linéaires n,3n-2N, sans uniformité J_c. Les célibataires et les faces ne possèdent pas ce gain et restent explicites.

Deuxième direction, auditée puis rejetée comme fermeture : compléter le préfixe court par sa partie r<=alpha et le raccorder au principal de référence. Le paiement de l'annulus ne contrôle pas cette partie basse. Son principal S(N)N reste présent ; la recombinaison redonne le manque de compensation avec le vrai détecteur -R_pair et le moment premier–Möbius. Cette direction n'apporte donc aucun nouveau gain estimé, et n'est pas un candidat Lean de substitution.

Le bloc négatif -R_pair est toujours conservé sans minoration. Les puissances propres du premier axe restent dans le raw et dans son poste B_pp ; l'extraction présente ne prétend pas les faire disparaître.

## 2. Quatre lignes pour l'arbre

Mechanism: Appariement 3-adique des vrais c et3c avant les normes, avec deux indicatrices premières distinctes, entropies et faces ; le modèle signé des incidences conjointes devient S(N)mu(c)log(n3/n).

Hypothesis: Uniquement la multiplicativité réelle de Möbius, les noyaux source, (54), S(N)<3ell et le crible positif fini des deux formes n,3n-2N au masque3N ; aucune uniformité de J_c, aucun petit moment pondéré et aucune positivité globale postulés.

Observable: Nouvelle identité de paire avec les deux W réels, témoin conjoint c1/p3167/q3169 dont la paire entière est positive, singleton c1/p3167/q3191 et face c7 à conserver ; le modèle conjoint seul reçoit un paiement effectif inférieur à 10^-12 N/(u ell).

Conflicts: Extraction partielle pour N pair avec 3 ne divisant pas N ; les célibataires, les faces3c>C, Lambda(c),Lambda(3c), le préfixe r<=alpha et J0/J1 ne sont pas payés par ce gain, et aucun crédit rough n'est dépensé deux fois.

## 3. Cadre exact et partition injective de J2

N est pair, u=log N, ell=log u, alpha=ceil(N^(1/4)), Q=floor((N-1)/alpha) original, a=ceil(N^(7/16)), M=ceil(N^(3/4)). Les deux fronts du moment B_prime sont a*k<m. W désigne le noyau source avec log(k/m), de principal négatif ; il n'est pas W_positive.

Le présent appariement suppose **3 ne divisant pas N** et a>3. Les autres N pairs restent hors de ce sous-mécanisme et conservent leur moment initial. Si 3 divise N, le point m3=3c*p*q est non unitaire, et son n3 est non unitaire ; on ne crée pas une paire fictive unitaire. Aucune généralisation à un premier variable n'est faite.

Dans J2, écrire de manière canonique m=c*t, t=p*q, a<p<q premiers, gcd(t,N)=1, c carré-libre et gcd(c,N*t)=1. On a c<N/a^2<=N^(1/8)<a. Tout facteur premier de c est donc <=a. U1 est effectivement compilée en boucle10 ; son application U2 au secteur J2 complet est pour l'instant validée écrite et auditée10, sans son propre théorème Lean. Cette application donne, pour n=N-c*t premier unitaire,

```
log n*C_(c*t)=log n[Lambda(c)+mu(c)W(n,c*t)].
```

On utilise cette identité dans une **nouvelle partition de paires**, pas comme une nouvelle preuve de victoire. Le bulk de J2 exige n>Q ; m>=M est automatique dans ce domaine source puisque t>a^2>=N^(7/8)>N^(3/4), avec les marges entières déjà dominées au seuil retenu.

Pour chaque couple p<q, posons

```
C_t=floor((N-Q-1)/t),
X_t={c : 1<=c<=C_t, c squarefree, gcd(c,N*t)=1},
theta_N(x)=1_(x prime, gcd(x,N)=1)*log x.
```

Les logarithmes employés ensuite ont des arguments >Q>=2. Le front c<=C_t est exactement c*t<=N-Q-1, soit N-c*t>Q. Il garde tous les arrondis. Le premier n peut être composite dans la grille X_t ; son indicatrice et theta sont alors zéro, sans remplacer son W par un modèle premier.

Définir les bases 3-libres

```
D_t={d in X_t : 3 ne divisant pas d, 3*d<=C_t},
F_t={d in X_t : 3 ne divisant pas d, C_t<3*d}.
```

Tout c de X_t qui est divisible par3 a un exposant de3 exactement1, donc s'écrit c=3d avec d dans D_t. Les autres c sont les d dans D_t ou F_t. Cette partition est injective et disjointe. Elle ne suppose aucune incidence première dans l'un ou l'autre point. Les unités c,3c,p,q à N sont conservées, puisque 3 est premier à N. Les facteurs répétés restent nuls par le coefficient entier ; ils ne sont pas admis dans cette partition carré-libre.

## 4. Première identité réelle proposée à Lean

Pour d dans D_t, écrire n=N-d*t et n3=N-3*d*t, i=1_(n prime unitaire), j=1_(n3 prime unitaire). Les deux points sont positifs et >Q. Poser W1=W(n,d*t), W3=W(n3,3*d*t). Définir d'abord le vrai bracket source local, plutôt qu'une nouvelle fonction autonome :

```
bracket_prime(n,m)=theta_N(n)*[-mu(m)(D_a(m)-W_a(n,m))].
```

Le premier certificat doit raccorder ce bracket, le cap original et ses unités physiques à l'application J2 de U1. La nouvelle identité du **bracket entier** est ensuite

```
bracket_prime(n,d*t)+bracket_prime(n3,3*d*t)=A_d+A_3d
 =Lambda(d)*i*log n+Lambda(3d)*j*log n3
   +mu(d)[i*log n*W1-j*log n3*W3],                 (P1)

A_c=theta_N(N-c*t)[Lambda(c)+mu(c)W(N-c*t,c*t)].
```

La relation mu(3d)=-mu(d) provient de 3 premier, 3 ne divisant pas d et du raccord carré-libre réel. Les deux W de P1 ont leurs vrais caps, unités et fronts ; ils ne sont pas supposés égaux. P1 peut être certifiée par les vrais mu et Lambda et les deux indicatrices premières. Le premier certificat doit afficher en même temps la somme des P1 et les A_d des faces F_t : supprimer ces faces ou remplacer j par i ne serait pas le contrat.

Sur chacun des deux points, k=1 est annulé conjointement dans DIV et HARM avant d'utiliser l'extraction J2. Les modèles k libres restent entiers : P1 n'est pas un remplacement de W par une somme sur les diviseurs de d. Le facteur mu(m)^2 est seulement celui déjà dérivé du bilan entier en boucle10 ; aucun mu(n)^2 n'est ajouté au raw.

Ce mécanisme n'introduit aucune phase de caractères : le facteur natif chi(n)conjugate chi(N) demeure1 sur la fibre physique q|k. Les sélecteurs de conducteur et les unités des noyaux sources ne sont pas remplacés par un twist sur c, p ou q.

Différence avec le nœud4 pruned : l'ancien commutateur autour de101,303,707,2121 cherchait un transport/invariance du noyau. Ici les deux contraintes premières sont littérales, les incidences célibataires sont conservées, les fronts3d<=C_t restent présents et aucun W ne reçoit une invariance pointwise. Même lorsqu'une paire est conjointe, le bracket entier peut être positif par son entropie.

## 5. Principal commun, célibataires et faces exacts

Sur un point actif premier n>Q, le masque de W est exactement celui de N et les endpoints entiers sont ceux acquis. Ainsi W=-S(N)+delta avec |delta|<=epsilon_W=G54/u. Cette estimation ne concerne pas W aux points composites de la grille ; ils sont multipliés par leur indicatrice zéro. Définir le principal

```
K2=sum_(t=p*q canonical) sum_(c in X_t)
                       [Lambda(c)-S(N)mu(c)]theta_N(N-c*t).
```

Ce K2 contient **une fois** H2-S(N)M2 et le crédit rough c=1, -S(N)Theta_2. Il remplace leur écriture séparée ; on ne lui ajoute pas encore un -S(N)Theta_2 de l'ancienne route. L'erreur des vrais W sur tout ce bulk est <=N*G54, comptée une fois, par injection de m et n.

Avec H2=sum Lambda(c)theta_N(N-c*t), le découpage géométrique donne

```
K2=H2+S(N)[Delta_common+Delta_single+Delta_face],    (P2)

Delta_common=sum_(t,d in D_t)
                  mu(d)*i*j*log(n3/n),
Delta_single=sum_(t,d in D_t)
                  mu(d)[(1-i)j log n3-i(1-j)log n],
Delta_face=-sum_(t,d in F_t)mu(d)theta_N(N-d*t).
```

P2 est l'identité élémentaire exacte

```
j log n3-i log n
 =ij(log n3-log n)+(1-i)j log n3-i(1-j)log n.
```

Elle conserve les deux indicatrices ; elle ne remplace pas un singleton par un quotient de deux logarithmes. Les quatre signes sont visibles : pour mu(d)=+1, le commun et le singleton seulement n sont négatifs, le singleton seulement n3 positif ; pour mu(d)=-1, les signes s'inversent. Les faces portent également leur vrai mu(d). H2 reste positif sur les c premiers, notamment l'entropie Lambda(3)log n3 de la paire d=1.

## 6. Paiement indépendant du modèle conjoint central

Dans le sous-domaine d*t<=N/6, n>=5N/6 et n3>=N/2. Lorsque i=j=1,

```
0<log(n/n3)<=log(5/3)<1.
```

Le modèle principal conjoint vaut S(N)mu(d)log(n3/n). On conserve le sous-bloc mu(d)=+1 négatif. Son sous-bloc positif mu(d)=-1 est estimé par un comptage positif des deux **vrais** premiers.

Le nombre de ces incidences est injectif en n : la décomposition de m=N-n en c et ses deux facteurs >a est canonique, p<q, puis la base3-libre d est unique. Aucun facteur de multiplicité en p, q ou c ne s'ajoute.

Pour 3 ne divisant pas N, les racines modulo un premier de la forme n(3n-2N) sont

```
rho(2)=1, rho(3)=1,
rho(l)=1 si l|N ; rho(l)=2 sinon, pour l>3.
```

Ce sont exactement les racines du masque3N. En particulier S(3N)=2S(N). La seconde forme reste non nulle modulo3 : le cas non unitaire3 ne reçoit pas cette formule. Pour z=N^(1/8), les deux vrais premiers dans le domaine central dépassent z. La construction Selberg finie de (44), répétée avec ces mêmes nombres de racines, donne

```
I_common,central <= C_sieve*S(3N)*N/u^2+sqrt(N),
C_sieve=134217728/2541.                              (P3)
```

Le calcul CRT conserve le +1 : pour chaque congruence dans un intervalle de longueur L<=N, le compte est <=L/r+1. Son double reste est <=z^4. Le minorant G de la source est uniforme dans le masque et ne demande aucune distribution première dans une progression ; il conserve les facteurs de3N. Son domaine log z>=16 est satisfait au seuil source.

Le principal positif central est donc au plus

```
E_common,central=2*C_sieve*S(N)^2*N/u^2+S(N)*sqrt(N).
```

Le passage au budget effectif exige davantage que S(N)<10sqrt(u). La source §12.7, monographie autour des lignes2175–2176, donne **S(N)<3ell** dans le domaine source, en utilisant la borne universelle Rosser–Schoenfeld et sa version2.50637. On ne l'infère pas d'un échantillon numérique. Ainsi

```
E_common,central <=18*C_sieve*ell^2*N/u^2
                       +3ell*sqrt(N)
                  <10^-12*N/(u ell), u>=10^24.       (P4)
```

Après normalisation, le premier terme est 18*C_sieve*ell^3/u, et 18*C_sieve<10^6, ell0<56 et u0=10^24 donnent moins de2*10^-13. Le second est 3u ell^2 exp(-u/2), très inférieur à10^-13. Les dérivées logarithmiques 3/ell-1 et 1+2/ell-u/2 sont négatives ensuite. Ce gain concerne une vraie compensation de modèles sur une incidence conjointe, pas une uniformité de J_c.

## 7. Extension écrite au commun entier, avec AP incomplète

On peut également payer les incidences conjointes hors du domaine central sans perdre le +1. Pour une paire conjointe du bulk, Q<n3<n<N et log(n/n3)<=log(N/n3). Pour Q<=Y<=N, les n avec n3<=Y appartiennent à un intervalle de longueur <=Y/3, et tous les premiers retenus sont >Q>N^(1/8)>=Y^(1/8) au domaine source. Choisir z=Y^(1/8) dans le même crible fini donne

```
I_common(n3<=Y)<=C_sieve*S(3N)*Y/(log Y)^2+sqrt(Y).
```

Le compte de chaque classe garde <=Y/(3r)+1<=Y/r+1. Ni un endpoint de BV, ni une règle supprimant +1 sur les multiples positifs n'est utilisé ici. Comme Q>=N^(3/4)/8, log Y>=log Q>=2u/3 au domaine source. La représentation positive par couches

```
sum_common log(N/n3)
 =integral_(Q..N) I_common(n3<=Y)*dY/Y
 <=(9/4)*C_sieve*S(3N)*N/u^2+2sqrt(N)
```

est exacte pour les points retenus. Elle fournit, en gardant la partie mu(d)=+1 négative,

```
S(N)Delta_common <= -S(N)A_common,+ +E_common,
A_common,+=sum_(paired,i=j=1,mu(d)=+1)log(n/n3)>=0,
E_common=(9/2)*C_sieve*S(N)^2*N/u^2+2S(N)sqrt(N)
 <=(81/2)*C_sieve*ell^2*N/u^2+6ell sqrt(N)
 <10^-12*N/(u ell), pour u>=10^24.                 (P5)
```

En effet (81/2)*C_sieve<3*10^6 et ell0^3<2*10^5, donc le premier ratio normalisé est <6*10^-13 ; le second est <10^-13. Les deux mêmes décroissances assurent la marge. Le budget P5 remplace P4 si l'on utilise le commun entier ; on n'additionne pas ces deux paiements.

## 8. Bilan apparié et obligations non payées

Dans la route unique de boucle10, la nouvelle représentation du moment premier donne le majorant partiel

```
B_prime^a <= B_J0+B_J1,c>1
             -R_pair+[S(N)+epsilon_W]Theta_prime
             +H2+S(N)Delta_single+S(N)Delta_face
             -S(N)A_common,+
             +E_common+N*G54+E_corner.              (P6)
```

Le même E_corner paie une fois l'union rough premier/J2 hors bulk, comme auparavant. N*G54 paie une fois les vrais W de tout J2. Le nouveau E_common paie le seul modèle conjoint positif après appariement. -R_pair et -S(N)A_common,+ sont conservés, sans minoration supposée. P6 n'ajoute pas un crédit rough semipremier indépendant puisque celui-ci est déjà entré dans K2, P1/P2 et ses faces.

Les quantités H2, Delta_single, Delta_face et les secteurs J0/J1 gardent leurs vrais signes. Le singleton n3 seul pour mu(d)=+1 peut être positif de taille log n3, et la face d premier avec mu(d)=-1 peut être positive de même taille. Le crible des incidences **conjointes** ne compte pas ces cas et ne les paie pas. Une égalité ou petitesse de ces termes ne devient pas une nouvelle hypothèse.

Le ledger source reste D_N=B_prime^a+B_pp^a+P_band+Z_face+I_alpha+2max(e,0). Les paiements acquis ne sont comptés qu'une fois ; le seuil BV supplémentaire de P_band et le pont couvert2max(e,0) demeurent ouverts. P6 ne certifie pas D_N.

## 9. Seconde direction : compléter le préfixe bas et son principal

Poser U_a(m)=sum_(r|m,r<=a)mu(r)log r. L'identité compilée10 conserve

```
U_a=U_alpha+U_(alpha,a],
B_prime^a=-R_pair,all-T_low,prime-T_ann,prime+V_a,prime,
T_low,prime=sum_(n prime unitaire)log n*mu(m)^2*U_alpha(m),
T_ann,prime=sum_(n prime unitaire)log n*mu(m)^2*U_(alpha,a](m),
V_a,prime=sum_(n prime unitaire)log n*mu(m)W_a(n,m).
```

T_ann,prime est bien la bande physique correspondante, pas le préfixe entier. Son raccord avec la bande Mangoldt globale conserve aussi la sous-somme properpower ; on ne les supprime pas pour importer gratuitement son paiement. Le bas T_low,prime contient tous les r<=alpha. Sa référence source est le Jref global avec son masque rho et ses postes proprement partitionnés, et son principal est **S(N)N**, pas zéro. Une complétion par la seule allowance d'annulus est donc rejetée.

Le témoin du nouveau contrat de préfixe est m=30108669=3*3167*3169, n=69891331 premier : alpha=100, a=3163. Ses seuls diviseurs non triviaux <=a sont3. Donc

```
U_alpha(m)=U_a(m)=-log3,
U_(alpha,a](m)=0,
L_a(m)=log3.
```

Son entropie positive vient entièrement d'un r<=alpha. Elle ne peut être facturée au paiement de l'annulus. Ce témoin est utilisé pour cette nouvelle distinction, sans ancien banc rejoué.

Après conservation des properpowers et corrections de rho, la recombinaison complète est celle des équations (16)–(18) source : elle garde le principal S(N)(N-F_N), le vrai -Rsf et les erreurs déclarées. Une minoration de Rsf ou une compensation avec F_N manque toujours. Cette seconde direction ne donne donc aucun résultat arithmétique indépendant nouveau et n'est pas proposée comme victoire ou axiome Lean.

## 10. Contrat fini et falsificateurs nouveaux

Le rôle6 prépare un banc11 neuf. À N=10^8, a=3163,Q=999999, p3167,q3169,t=10036223, d=1 : n=89963777 et n3=69891331 sont réellement premiers et unitaires. Ce sont des entrées anciennes dans une **nouvelle identité de paire** ; aucun ancien banc passé n'est exécuté. Le modèle principal commun est S(N)log(n3/n)<0, mais la paire entière contient log3*log n3, et doit être testée avec les deux W réels.

Nouveaux témoins transmis par le rôle6 :

* Singleton : d=1,p3167,q3191,t=10105897<=N/6. n=89894103=3*13*1429*1613 est composite, n3=69682309 est premier. La vraie différence normalisée d'incidence est +log n3, pas log(n3/n). Elle reste dans Delta_single.
* Face : d=7,p3167,q3169. m=70253561,n=29746439 premier ; 3m=210760683>N. Le point3d n'appartient pas au front C_t et aucun log n3 positif n'est invoqué. La face A_7 est conservée.
* Préfixe bas : le point d3 ci-dessus garde U_alpha=-log3 et annulus zéro. Il réfute l'assimilation du petit préfixe entier à la bande payée.

Le reçu courant neuf `round11/paired_axes.json`, issu de `paired_axes_checks.py`, donne PASS_NEW_PAIR_IDENTITY_ONLY. Les noyaux réels n'y sont pas remplacés par leur principal. Il certifie par intervalles rationnels le modèle principal normalisé conjoint NEGATIVE et la paire entière POSITIVE ; le raccourci « toutes les paires entières c/3c sont favorables » reste ERROR_FALSIFIER. Le singleton a un principal normalisé POSITIVE, alors que le faux quotient de logarithmes est NEGATIVE ; cette assimilation reste ERROR_FALSIFIER. La face c7 est également conservée comme ERROR_FALSIFIER de la complétion automatique3c<=C_t. Ces observations sont attribuées au reçu courant : son gel et son rejeu indépendants restent au rôle6/Juge, sans PASS analytique inventé.

Les certificats exacts et signes rationnels de ce nouveau banc sont indépendants du budget P5, qui ne s'applique pas numériquement à log(10^8). Ils ne testent pas D_N, n'inventent aucune obstruction globale et ne démontrent aucune impossibilité de compensation entre les célibataires et les autres secteurs.

Le contrat Lean proposé est le raccord du vrai bracket à P1, les deux indicatrices et les deux W réels, puis la partition P2 avec célibataires et faces explicites. La conséquence analytique indépendante P5 est une preuve écrite sous le crible source et S(N)<3ell ; elle doit être auditée indépendamment et ne doit pas être remplacée par un nouvel axiome de petitesse. Même P1/P2 compilées ne seraient pas une victoire : le reste signé de P6 et les postes ouverts du ledger doivent encore être contrôlés.

Classification : `ACTUAL_PRIME_INCIDENCE_PAIRING`, `SINGLETON_FACE_ENTROPY_RETAINED`, `COMMON_MODEL_COMPENSATION_WRITTEN_INDEPENDENT`, `LOW_PREFIX_COMPLETION_NOT_A_CLOSURE`, `GLOBAL_SIGNED_CONTROL_NOT_OBTAINED`, `VICTORY_FALSE`. Aucun ancien banc PASS ou compilation archivée n'a été relancé et aucun fichier antérieur n'a été modifié par ce rôle.
