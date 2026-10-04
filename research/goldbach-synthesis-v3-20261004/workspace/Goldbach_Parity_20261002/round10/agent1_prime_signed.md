# Agent 1 — réduction unilatérale par les grands facteurs, boucle 10

**Rapport mathématique final : contrôle unilatéral partiel obtenu, contrôle du moment premier entier encore ouvert.** Le résultat nouveau est un contrôle unilatéral explicite d'un bloc du vrai moment premier, puis une réduction arithmétique de son complément à deux grands facteurs. Les termes favorables sont conservés, aucun seuil acquis n'est déplacé et aucune victoire Lean n'est alléguée. Le reçu numérique final et le rejeu du Juge restent indépendants du présent rapport.

Entrées lues : `round10/PROBE_BLOCK.md`, le retour final `round9_feedback.md`, l'audit final 9 de l'Agent 3 §7, et les notations source. Les fichiers antérieurs sont gelés. On distingue les identités arithmétiques nouvelles, les conséquences écrites d'inputs déjà acquis et les quantités qui restent ouvertes.

## 1. Analyse de principes

Le vrai premier axe est n=N-m premier, avec n>1 et gcd(n,N)=1. Sa masse est log n, et le coefficient entier du bilan est -mu(m)[D_a(m)-W_a(n,m)]. Le signe de mu(m) ne disparaît donc pas lorsqu'on sait que n est premier. La branche physique et son vrai modèle ont tous deux le front a*k<m. Sur la fibre physique la phase native vaut toujours 1 ; aucune nouvelle oscillation de caractère n'est obtenue.

La variable qui devient courte dans le mécanisme proposé est le produit c des facteurs premiers de m qui sont <=a. Lorsque m possède deux facteurs premiers >a, on a c<N/a^2<=N^(1/8). Cette variable courte porte encore un vrai poids de comptage de trois premiers, n=N-c*p*q, p et q. Un préfixe ordinaire de mu(c) ne contrôle pas ce poids.

La masse favorable n'est pas une norme à payer : si m est premier ou semipremier avec tous ses facteurs >a, le noyau harmonique sur le bulk donne un signe favorable explicite. La masse nuisible reste visible : si m=c*p*q avec c premier et p,q>a, son coefficient est log c-W_a, positif lorsque W_a<0. La frontière n'est donc pas uniformément favorable. Le témoin c=3 de cette nouvelle famille doit réfuter toute généralisation erronée du signe.

## 2. Quatre lignes pour l'arbre

Mechanism: Bascule exacte du long vers ses diviseurs courts, puis partition de Buchstab selon le nombre de facteurs premiers strictement >a9, avec bloc rough favorable conservé et petit cœur c explicite dans le bloc à deux grands facteurs.

Hypothesis: Seulement les noyaux et masques source, l'estimation (54), S(N)<=N/phi(N) et des inégalités élémentaires ; aucun petit moment de mu(c) pondéré par trois premiers n'est supposé.

Observable: Identité du coefficient entier C_m, signes opposés des nouveaux témoins rough semipremier et c=3 à N=10^8, et majorant unilatéral U7 avec comptes premiers réellement pondérés.

Conflicts: Le bloc c premier à deux grands facteurs est nuisible et reste dans H2 ; j=0 et j=1 nonrough restent entiers, aucun masque mu(n)^2 n'est ajouté, k=1 s'annule conjointement et les secteurs qui recoupent l'Agent 2 ne sont pas additionnés deux fois.

## 3. Définitions exactes et bascule des diviseurs courts

On conserve N pair, u=log N, ell=log u, alpha=ceil(N^(1/4)), Q=floor((N-1)/alpha) et

```
a=a9=ceil(N^(7/16)), M=ceil(N^(3/4)).
D_a(m)=sum_(k|m, 1<=k<=Q, a*k<m)mu(k)log(k/m),
W_a(n,m)=sum_(1<=k<=Q, gcd(k,nN)=1, a*k<m)
                                      mu(k)log(k/m)/phi(k).
P_N={1<=m<=N-2 : n=N-m prime, gcd(n,N)=1},
C_m=-mu(m)[D_a(m)-W_a(N-m,m)],
B_prime^a=sum_(m in P_N)log(N-m)*C_m.
```

W désigne ici le noyau source, avec log(k/m)<0. Il ne désigne pas son opposé utilisé dans certains autres rapports. Les deux fronts sont a*k<m, et Q reste le Q original.

Posons le préfixe de diviseurs, sans masque sur le premier axe,

```
U_a(m)=sum_(r|m, r<=a)mu(r)log r,
L_a(m)=-mu(m)D_a(m).
```

La bascule complète fournit

```
L_a(m)=mu(m)^2 sum_(r|m,r>a)mu(r)log r
      =mu(m)^2[-Lambda(m)-U_a(m)],
C_m=L_a(m)+mu(m)W_a(N-m,m).                       (U1)
```

Pour mu(m)=0, les deux membres L_a et C_m sont nuls ; le facteur mu(m)^2 n'est introduit qu'après expression du bilan entier. Pour m carré-libre, mu(m)mu(k)=mu(m/k) pour chaque diviseur k, et log(k/m)=-log(m/k). Tout diviseur r>a donne k=m/r avec a*k<m. Aucun tel k ne peut dépasser Q : k>Q implique k*alpha>N-1, puis m>a*k>=alpha*k>N-1, contradiction. L'identité reste donc exacte avec le Q source, sans nouvel élargissement du cap.

La seconde égalité de U1 utilise l'identité complète sum_(r|m)mu(r)log r=-Lambda(m), avec m=1 traité par zéro. Cette identité standard n'est pas présentée seule comme mécanisme gagnant : ce qui suit en utilise les signes et la géométrie particulière a^3>N.

Le k=1 est retiré conjointement seulement après U1. Lorsque m>a, son morceau physique vaut mu(m)log m et son morceau mu(m)W vaut -mu(m)log m ; ils s'annulent au même point. Si m<=a, les deux sont inactifs. C_m est donc exactement le coefficient du bilan k>=2 ; un k=1 isolé n'est pas omis.

## 4. Partition unique par les grands facteurs

Aux points actifs non nuls, m est carré-libre. Soit j(m) le nombre de ses facteurs premiers strictement >a. Comme a^3>=N^(21/16)>N>m, on a j=0,1 ou2. Le point m=1 est nul. Cette partition est une décomposition de l'expression entière, pas un nouveau filtre du raw.

* J0 : j=0, tous les facteurs premiers sont <=a. On garde U_a(m) littéral ; on ne remplace pas les fibres coupées par une fibre complète.
* J1 : j=1, m=c*p, p>a, tous les facteurs de c sont <=a. On distingue c=1 de c>1. Pour c>a, U_a(c) reste tronqué. Le secteur 1<c<=a recoupe le secteur non trivial développé par l'Agent 2 et n'est compté qu'une fois.
* J2 : j=2, m=c*p*q, a<p<q premiers, c carré-libre, gcd(c,pq)=1 et tous les facteurs de c sont <=a. On conserve gcd(c*p*q,N)=1 et le premier n=N-c*p*q. Puisque p,q>a,

```
1<=c<=floor((N-2)/(a+1)^2)<N/a^2<=N^(1/8)<a.
```

Dans J2, les diviseurs r<=a de m sont donc exactement tous les diviseurs de c. Il s'agit d'une complétude prouvée pour ce seul secteur. Ainsi U_a(m)=-Lambda(c), Lambda(m)=0 et mu(m)=mu(c), d'où

```
L_a(c*p*q)=Lambda(c),
C_(c*p*q)=Lambda(c)+mu(c)W_a(N-c*p*q,c*p*q).       (U2)
```

Cette formule garde tous les facteurs de coprimalité. Pour c=1, Lambda(c)=0 et mu(c)=1, donc C=W_a. Pour c premier, C=log c-W_a. Pour c carré-libre composite, C=mu(c)W_a : les petits c de Möbius positif restent utiles et ceux de Möbius négatif restent nuisibles quand W_a est négatif. Remplacer Lambda(c) par log c pour tout c serait faux.

Le raccord carré-libre est indispensable. Par exemple, un cœur c=9 peut garder U_a(c*p)=-Lambda(9)=-log3 non nul lorsque p>a et 9<=a. Le coefficient entier est néanmoins L_a=mu(c*p)^2Lambda(9)=0 et C=0. La formule U2 sans son domaine carré-libre ne doit donc pas être appliquée à un cœur non carré-libre ni à p=q. Cela conserve l'annulation Möbius sans détruire artificiellement un préfixe non pondéré.

Dans J1, c=1 donne m premier et U1 donne

```
C_m=-log m-W_a(N-m,m).                            (U3)
```

Le bloc c=1 de J1 est le seul recoupement de la présente extraction rough avec le cas premier séparé de l'Agent 2. J2 est disjoint de son secteur 1<c<=a<p, puisque retirer l'un de p,q de c*p*q laisse encore l'autre grand facteur >a. Aucune allowance des deux extractions n'est additionnée sur un même point.

## 5. Lemme de signe indépendant sur le bulk rough

Le bulk de cette seule application est

```
Omega_bulk={m in P_N : m>=M, n=N-m>Q}.
```

Sur un tel point, le premier n dépasse tous les k du cap ; le masque fini de W_a est exactement gcd(k,N)=1. Son préfixe est

```
R=min(Q,floor((m-1)/a)).
```

Les marges entières utilisées dans l'audit9 donnent R>=N^(5/16)/8>=N^(1/5) pour u>=10^6. Le quotient réel et son endpoint restent ceux de (53). Appliquons (54) avec K=N, sans remplacer un masque mobile sur les autres points :

```
W_a(N-m,m)=-S(N)+delta_m,
|delta_m|<=epsilon_W(u),
epsilon_W(u)=4*10^8*u^4*exp(-sqrt(u)/60)
                +160*u*exp(-u/40).                  (U4)
```

L'exposant -sqrt(u)/60 est le majorant affaibli explicite de -sqrt(u/60) du PDF. Il garde la portée u>=10^6 et les prémisses de (54). À u>=10^24, epsilon_W<=1/4. Les facteurs positifs au premier seuil sont sous 2^349 et 2^88, tandis que les exponentielles sont inférieures à 2^(-10000) ; les dérivées logarithmiques 4-sqrt(u)/120 et 1-u/40 sont négatives ensuite.

On a les bornes uniformes indépendantes

```
1<=S(N)<=N/phi(N)<10*sqrt(u) pour N pair,u>=8.       (U5)
```

La borne inférieure suit du produit C2 : ses facteurs aux premiers impairs forment un sous-produit de prod_(j>=2)(1-1/j^2)=1/2, donc 2C2>=1, puis chaque facteur local de N est >=1. L'inégalité S(N)<=N/phi(N) est (19). Pour son majorant explicite, écrire N/phi(N)=2prod_(p|N,p>2)p/(p-1). Les p<=u ont log[p/(p-1)]<=1/(p-1) ; comme p est impair, leur somme est <=(1+log u)/2 en la majorant par les dénominateurs pairs. Les p>u sont au plus u/log u et leur somme est <=u/[(u-1)log u]<=1. Ainsi N/phi(N)<=2e^(3/2)sqrt(u)<10sqrt(u). Tous les premiers divisant N restent couverts.

Le **lemme de signe utile**, sur Omega_bulk et u>=10^24, est alors

```
m premier (donc m>a)      => C_m<=-u/2,
m=p*q,a<p<q premiers     => C_m<=-3/4.              (U6)
```

Pour la première ligne, U3/U4 donnent C_m<=-log m+S(N)+epsilon_W <=-3u/4+10sqrt(u)+1/4<=-u/2. Pour la seconde, U2 avec c=1 donne C_m=W_a<=-S(N)+epsilon_W<=-3/4. Ces estimations n'exigent ni représentation de Goldbach pour chaque N ni une conjecture de positivité. Si une classe est vide, sa masse favorable est simplement zéro.

## 6. Coins de la partition et majorant unilatéral réel

On appelle U le secteur m premier rough (J1,c=1) réuni à tout J2. Pour les points hors Omega_bulk dans ce seul U, on a n<=Q ou m<M ; leur nombre est au plus Q+M<=3N^(3/4). Sur U, |L_a(m)|<=u par U2/U3. Sans masque principal et même pour un préfixe vide, la borne directe est |W_a|<=u sum_(k<=Q)1/phi(k)<=3u(1+u). Comme log n<=u, chaque masse du bilan est <=u^2[1+3(1+u)]<=7u^3 pour u>=1. Une marge entière simple est donc

```
|B_(U hors bulk)|<=E_corner,
E_corner=30N^(3/4)u^3.                              (U-corner)
```

Cette charge est nouvelle et distincte du properpower acquis, puisque n est premier ici. Elle est également distincte de Z_face et de I. Elle n'est pas comptée une deuxième fois dans J2. On a E_corner<N/(1024u ell) pour u>=65536 : normaliser donne 30720u^4ell exp(-u/4)<=30720u^5exp(-u/4), puis log30720<16<=u/4096 et log u<=u/4096 donnent au plus exp(-1018u/4096)<1. Au seuil source u>=10^24, la même comparaison décroissante donne E_corner<10^(-12)N/(u ell). C'est un paiement écrit explicite, pas un calcul fini au seuil.

Définissons les comptes favorables réellement pondérés

```
Theta_prime=sum_(m in Omega_bulk,m prime)log(N-m),
Theta_2=sum_(m in Omega_bulk,m=p*q,a<p<q prime)log(N-m).
R_pair=sum_(m in Omega_bulk,m prime)log m*log(N-m).
```

Gardons B_J0 et B_J1,c>1 comme les sommes exactes de log n*C_m sur leurs secteurs entiers, sans oubli de leurs coins. Pour c>=2, carré-libre, c<=floor((N-2)/(a+1)^2), définissons

```
J_c=sum_(a<p<q primes, m=c*p*q in Omega_bulk,
          all prime factors of c<=a, gcd(c*p*q,N)=1)log(N-c*p*q),
H2=sum_(c>=2)Lambda(c)J_c,
M2=sum_(c>=2)mu(c)J_c.
```

Le premier axe dans J_c est vraiment premier et unitaire par Omega_bulk. Les couples p<q sont non ordonnés, donc chaque m de J2 possède un c unique et est compté une fois. U2/U4 donnent la réduction exacte du bulk nonrough de J2

```
B_(J2,c>=2,bulk)=H2-S(N)M2+R2,
|R2|<=epsilon_W*sum_(J2,c>=2,bulk)log n
     <=N*u*epsilon_W=N*G54(u).                      (U-J2)
```

La dernière inégalité utilise les points m, pas une somme artificiellement multipliée par le nombre de facteurs. Au seuil source, N*G54(u)<10^(-12)N/(u ell), sous les mêmes prémisses explicites. Ce coût ne s'ajoute pas au bloc c=1 déjà conservé avec U6 : R2 ne contient que c>=2.

La forme la plus précise conserve la masse négative réelle de paires premières, sans lui attribuer une minoration inconnue :

```
B_prime^a <= B_J0+B_J1,c>1+H2-S(N)M2
               -R_pair+[S(N)+epsilon_W]Theta_prime
               -[S(N)-epsilon_W]Theta_2
               +E_corner+N*G54(u).                 (U7-sharp)
```

Les comptes Theta et R_pair portent les unités et les fronts déclarés. Aucun théorème de positivité de Goldbach ni marge de paires premières ne les minore ici. En utilisant U6, on obtient aussi le véritable majorant unilatéral simplifié, en conservant ses contributions favorables,

```
B_prime^a <= B_J0+B_J1,c>1+H2-S(N)M2
               -(u/2)Theta_prime-(3/4)Theta_2
               +E_corner+N*G54(u).                 (U7)
```

U7 est une nouvelle réduction signée avec coefficients et charges indépendants. Elle n'est pas une borne de la cible. En particulier, H2 est une masse positive : seuls les c premiers contribuent à Lambda(c), et le coefficient principal de leurs J_c vaut log c+S(N). Les termes mu(c)=+1 de M2 restent négatifs et ne sont pas remplacés par leur valeur absolue.

## 7. Obligation qui reste ouverte

Le nouveau moment court est M2=sum mu(c)J_c, c<N^(1/8), mais J_c compte réellement les trois premiers p,q,N-c*p*q, avec tous les fronts précédents. Ni le Mertens ordinaire de mu(c), ni BV de Lambda seule, ni la phase native constante sur la branche physique ne fournit une approximation uniforme de J_c qui permettrait son paiement. Le poste positif H2 et les autres secteurs J0/J1 ne se compensent pas par un signe pointwise acquis.

L'extrapolation « tout J2 est favorable » est fausse : c premier donne C=log c-W_a et son principal log c+S(N)>0. Une positivité nouvelle de M2 ou une petite énergie postulée ne serait pas une preuve du mécanisme. Aucun de ces énoncés n'est adopté comme hypothèse.

Le ledger de l'unique route source demeure

```
D_N=B_prime^a+B_pp^a+P_band^{>=2}+Z_face^{>=2}
                       +I_alpha+2max(e,0).
```

Les properpowers, la face harmonique et I gardent leur paiement une seule fois. Le seuil BV supplémentaire de P_band reste non évalué et 2max(e,0) reste à payer. U7 ne les absorbe pas. Aucune impossibilité globale n'est déduite de la présente absence de contrôle signé.

## 8. Contrat fini nouveau et lemme de formalisation

À N=10^8, a=3163,Q=999999,M=1000000. Le rôle 6 a trouvé les nouveaux témoins suivants dans `round10/witnesses.json` :

| Secteur | m | n=N-m | Coefficient attendu |
|---|---:|---:|---|
| Rough premier bulk | 1000037 premier | 98999963 premier | -log1000037-W_a |
| Rough semipremier bulk | 10036223=3167*3169 | 89963777 premier | W_a |
| Petit cœur premier, deux grands facteurs | 30108669=3*3167*3169 | 69891331 premier | log3-W_a |
| Non carré-libre bulk | 30089667=3*3167^2 | 69910333 premier | 0 |

La primalité et les facteurs ont été vérifiés par le rôle 6. Le nouveau script `round10/paired_cofactor_checks.py`, avec reçu `round10/paired_cofactors.json`, compare les coefficients exacts et certifie les signes finis par intervalles rationnels issus d'artanh, à 96 bits pour les signes non nuls. W_kernel est négatif sur les quatre lignes ; C est négatif sur les deux premières, positif sur c=3 et exactement zéro sur le point non carré-libre. Aucune validité de U6 à u=log(10^8) n'est déduite du seuil source. Le carré pur m=p^2 rough ne peut fournir de premier n>Q à ce N, puisque N mod3=1 et p^2 mod3=1 ; ce défaut de recherche reste un rejet de témoin, pas un contre-exemple à U1.

Le reçu conserve la tentative fausse « tout J2 favorable » comme ERROR_FALSIFIER sur m=30108669,c=3. Sa réfutation est arithmétique avant Lean ; aucune erreur du compilateur n'est inventée. Les autres nouveaux tests confirment la géométrie qui reste ouverte :

* J1 à fibre incomplète : c=3183=3*1061>a, p=3307, m=10526181, n=89473819 premier. On a U_a(c)=-log3-log1061=-log3183, tandis que -Lambda(c)=0. Donc L=log3183 et C=log3183-W_kernel>0 par le signe rationnel certifié. Remplacer cette fibre par une fibre complète serait réellement faux.
* J0 bulk : m=1174173=3*7*11*13*17*23, n=98825827 premier. Le coefficient physique exact est L=5log3+5log7+3log11+3log13+4log17+3log23. Le coefficient entier C est positif selon l'intervalle rationnel ; J0 n'est donc pas supprimé par le lemme rough.
* Cœur non carré-libre : m=28629=9*3181,n=99971371 premier. Son préfixe non pondéré peut porter Lambda(9)=log3, mais L=C=0, conformément au raccord entier de U1.

Ces observations finies ne réfutent pas une compensation globale et ne certifient pas les bornes asymptotiques. Elles confirment des identités et réfutent seulement les extrapolations pointwise identifiées. Les comptes favorables Theta/R_pair ne reçoivent aucune minoration numérique extrapolée.

Le banc nouveau doit : calculer D_a,W_a et C_m avec les mêmes masques ; comparer U1 en logarithmes premiers à coefficients rationnels ; vérifier U2/U3 sur les domaines indiqués ; comparer C_m ALL-k à son retrait conjoint >=2 ; conserver le coefficient nul du point non carré-libre malgré le préfixe non pondéré éventuellement non nul ; certifier les signes réels par intervalles rationnels et conserver la tentative fausse « tout J2 favorable ». Il doit garder également un secteur j=1,c>a à fibres incomplètes dans la vérification générale, sans lui appliquer U2. Aucun ancien banc PASS n'est relancé.

Le contrat substantif pour les formalistes est U1 accompagné de la classification a^3>N, U2/U3 et de la conséquence unilatérale U7-sharp/U7. Le lemme analytique de signe U6 dérive de (53)/(54) et des bornes U5, avec son domaine source ; il ne doit pas être remplacé par un nouvel axiome analytique. Compiler l'identité standard seule ne serait pas une victoire. La fermeture exige encore le contrôle réel du reste signé de U7 et des postes du ledger restants.

Classification : `EXACT_NATIVE_PRIME_COFACTOR_PARTITION`, `INDEPENDENT_ROUGH_BLOCK_ONE_SIDED_SIGN`, `INDEPENDENT_PRIME_CORNER_PAYMENT`, `SIGNED_THREE_PRIME_SHORT_CORE_MOMENT_UNPAID`, `PHYSICAL_BAND_ONSET_UNEVALUATED`, `COVERED_E_UNPAID`, `VICTORY_FALSE`. Aucun fichier antérieur, source, test déjà passé ou état Arbor n'a été modifié ou réexécuté par ce rôle.
