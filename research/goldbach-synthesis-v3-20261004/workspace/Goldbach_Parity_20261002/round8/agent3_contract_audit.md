# Agent 3 — audit intégral du raccord physique, boucle 8, nœud 11

**Verdict : résultat analytique partiel sur la tête physique, compensation globale non obtenue.** Les identités R1–R7 et les budgets R8–R15 sont cohérents dans leurs domaines et sous les inputs acquis explicitement conservés. Ils donnent une estimation indépendante de la tête alpha<r<=H. Le seuil classique BV nécessaire à cette nouvelle application reste non évalué. R16 conserve un reste signé essentiel. Aucun fichier Lean de substitution, aucun nouvel axiome de gain et aucun diagnostic fictif de compilateur ne sont produits.

## 1. Sources, seuil et scalaire initial

L'audit a lu `agent1_signed_compensation.md`, les deux scripts et reçus numériques disponibles `compensation_*` et `head_regrouping_*`, ainsi que les §§6.2, 12.1 et 12.7 de la monographie. Les pages sources rendues 32, 33 et 36 ont été examinées visuellement : l'onset adaptatif est bien **u>=10^24**, avec u=log N, et non u>=1024. Les constantes numériques légitimes 1024 des boucles précédentes ne sont pas concernées. Les pièces jointes sont les sources du cadre ; la condition de victoire demeure la demande de l'utilisateur.

On garde le profil quartique, alpha=ceil(N^(1/4)), Q=floor((N-1)/alpha), n=N-m, et les noyaux littéraux : k<=Q, alpha*k<m, k|m pour D, gcd(k,nN)=1 pour W. Le préfixe W est min(Q,floor((m-1)/alpha)). Lambda_N(n)=Lambda(n)1_(n>1)1_(gcd(n,N)=1) conserve toutes les puissances premières propres à base unitaire. Le raw ne reçoit aucun facteur mu(n)^2.

Le I de R1 est exactement le I acquis : h1(n)=log n, même masque unitaire et même D-W. Afficher n>1 ne change rien, puisque log1=Lambda(1)=0. L'identité fII=Lambda-log donne point par point

```
S_full=S_Lambda-I,
D_N=-S_Lambda+I+2max(e,0).                            (R1)
```

Le paiement |I|<3*10^(-6)N/(u ell) appartient au contrat adaptatif de §12.7, avec les prémisses de contour et completion conservées et u>=10^24. Il n'est pas un nouveau paiement de cette boucle, ni un PASS numérique à N=10^8. Il est utilisé globalement, pas réaffecté à des secteurs individuels puis ajouté une deuxième fois. Le e reste celui du pont original.

## 2. Bascule, fronts et ligne k=1 : R2–R6

La bascule mu(k)mu(kr)=mu(k)^2mu(r)1_(gcd(k,r)=1) est correcte pour tous les k,r positifs. Si k a un carré premier, les deux côtés sont nuls. Si k est carré-libre et partage un premier avec r, mu(kr)=0. Dans le cas premier à r, la multiplicativité coprime fournit l'égalité, y compris lorsque mu(r)=0.

Le domaine physique de D devient r>alpha, kr<=N-2, gcd(r,kN)=1, avec k<=Q et gcd(k,N)=1. Le changement de logarithme log(k/(kr))=-log r donne le signe négatif du physique. Dans le modèle, -log(k/m)=log(m/k) donne le signe positif. Ainsi

```
S_Lambda=-sum_k mu(k)^2 P_k+sum_k mu(k)M_k/phi(k).     (R2)
```

Le front N-2 est la traduction de n>1. Les termes n=1 perdus par rapport à un front N-1 ont déjà Lambda zéro. Les masques du modèle conservent gcd(m,N)=1 et gcd(N-m,k)=1 ; ils ne sont pas remplacés par le masque physique.

Pour k=1, P1=M1 : même domaine m=r>alpha, n>1, unités, coefficient mu et logarithme log m. Cette ligne du scalaire centré s'annule avant les valeurs absolues. Il s'agit du k=1 de cette bascule, pas du l=1 de la couverture logarithmique de la boucle 7. Après sa suppression simultanée dans les deux branches,

```
D_N=P^{>=2}-M^{>=2}+I+2max(e,0).                     (R3)
```

Le modèle M^{>=2} n'est pas le modèle complet payé par un éventuel acquis sur Z_ref ; sa ligne k=1 a aussi été retirée. Ce changement ne permet pas d'importer son paiement sans raccord.

Dans la tête, H=floor(N^(3/8)) et K_r=min(Q,floor((N-2)/r)). Pour r entier >alpha et Q(alpha+1)>N-1, on a Qr>N-1, donc floor((N-2)/r)<Q. La réduction exacte de K_r au plancher physique est justifiée. R4 conserve toutefois ce plancher, pas N/r.

Le masque Lambda_N permet de rendre gcd(k,N)=1 redondant uniquement dans la somme physique R4 : si un premier divise k et N, il divise N-rk et la Mangoldt masquée est nulle. Cela ne supprime aucune puissance première à base unitaire.

L'expansion mu(k)^2=sum_(d^2|k)mu(d) est exacte. La restriction gcd(k,r)=1 impose gcd(d,r)=1 ; les d partageant N ne donnent que des Lambda_N nulles et peuvent également être exclus. Après **gcd(d,rN)=1**, la condition t|rad(r) est coprime à d et l'écriture k=d^2*t*v est correcte. Sans cette restriction, l'intersection de d^2|k et t|k demanderait lcm(d^2,t), pas d^2*t.

R5 expose ainsi q=r*d^2*t, avec gcd(q,N)=1. Le dernier préfixe est exactement psi_N(N-1;q,N) : n=N-qv, v>=1, qv<=N-2. Le point n=N est exclu par X=N-1 et n=1 a Mangoldt zéro. Aucun lower-prefix additionnel n'est perdu.

La tête tout-k contient k=1. Pour rejoindre R3, il faut soustraire son morceau P_head_1. Le paiement |P_head_1|<=H*u^2 de R6 est correct : au plus H arguments, |mu|<=1, Lambda<=u et log r<=u. Ce paiement est ajouté une seule fois dans R15.

## 3. Fibres répétées exactes : R7

Sur les coefficients non nuls, r,d,t sont carrés-libres, gcd(d,r)=1 et t|r. Le changement de variables est bijectif :

```
b=d*t, c=r/t, g=t,
r=c*g, d=b/g, t=g, g|b,
q=b^2*c,
b,c squarefree, gcd(b,c)=1, gcd(b*c,N)=1.
```

Le coefficient devient mu(r)mu(d)mu(t)=mu(b)mu(c)mu(g). Le front du r original demeure alpha<c*g<=H. D'où le poids R7,

```
w(b^2*c)=mu(b)mu(c)
          sum_(g|b, alpha<c*g<=H)mu(g)log(c*g).
```

Chaque q cube-free ainsi obtenu détermine b,c de manière unique. Pour c>alpha et cb<=H, la fibre entière donne log c si b=1, puis -Lambda(b) si b>1. Le rapport garde correctement les autres fibres comme sommes coupées. La formule complète n'est pas appliquée aux fronts c<=alpha ou cb>H.

La coupe B_cut=floor(N^(1/32)) est distincte du B acquis dans §12.1. Sur b<=B_cut, c<=H et q<=B_cut^2*H<=N^(7/16). La somme tronquée ne reçoit pas un masque mu(m)^2 supplémentaire : même si le coefficient physique complet s'annule sur un m non carré-libre, une coupe peut être non nulle et avoir besoin de sa queue.

## 4. Deux queues distinctes : R8 et R9

On a |w(b^2*c)|<=u*tau(b). Pour le préfixe particulier n=N-qv, le nombre de v positifs est floor((N-2)/q), donc psi_N(N-1;q,N)<=Nu/q. **L'absence de +1 est valide ici seulement**, par ce comptage de multiples positifs ; elle ne transporte pas cette borne à un intervalle arbitraire d'AP.

Notons A_tau(z)=sum_(b<=z)tau(b)<=z(1+log z). En appliquant Abel, et en supprimant seulement le terme endpoint négatif d'un majorant positif,

```
sum_(b>B)tau(b)/b^2 <= 2(2+log B)/B,
sum_(b>B)tau(b)(1+log b)/b^2
 <= [2(log B)^2+7log B+8]/B.
```

La seconde constante se vérifie par l'intégrale de (1+log x)(1+2log x)/x^2 sur [B,infinity). Les restrictions carrés-libres, unités, coprimalité et fibres peuvent être élargies après passage à ces majorants positifs.

La queue **physique** multiplie Nu/q par |w|, puis utilise sum_(c<=H)1/c<=1+u. Elle donne bien

```
E_phys <= 2Nu^2(1+u)(2+u)/B_cut.                     (R8)
```

La queue **du principal AP** multiplie X/phi(q) par |w|. Comme gcd(b,c)=1,

```
phi(b^2*c)=b*phi(b)*phi(c),
sum_(c<=H)1/phi(c)<=3(1+u),
b/phi(b)<=3(1+log b).
```

Elle donne donc

```
E_main <= 9Nu(1+u)(2u^2+7u+8)/B_cut.                 (R9)
```

Le facteur u^2 de R8 n'est pas échangé contre le facteur u de R9. Les deux pertes existent séparément : l'une retire la queue du physique, l'autre remet celle du principal eulérien complet. Le principal infini est absolument convergent en d ; la coupe retenue ne requiert aucun remplacement d'une queue signée par zéro.

## 5. Principal eulérien, moments et Abel : R10–R12

Pour gcd(r,N)=1, la factorisation du principal utilise gcd(d,r)=1 et phi(r*t)=t*phi(r) pour t|rad(r). Le produit en d est C_sf(rN), et sum_(t|rad(r))mu(t)/t=phi(r)/r. Ainsi le coefficient principal est exactement C_sf(rN)/r, comme en R10.

N pair exclut p=2 du produit C_sf et du tilt. Pour p∤N, posons beta_p=(1-1/[p(p-1)])^(-1). Les facteurs locaux de a_N/C_sf(N) sont 1-beta_p*z ; ceux de mu_N sont 1-z. Leur quotient est

```
1+(1-beta_p)(z+z^2+...),
h_N(p^j)=-1/[p(p-1)-1] pour j>=1.
```

Pour p|N, h_N(p^j)=0. La convolution a_N=C_sf(N)(h_N*mu_N) est correcte, avec C_sf(N)<=1.

Les deux constantes R11 sont justifiées. Pour le moment 1/d, le terme local non constant est

```
1/[(p(p-1)-1)(p-1)] <= 1/(p-1)^3.
```

Le changement d'indice j=p-1>=2 majore le logarithme du produit par sum_(j>=2)j^(-3)<=1/4. Cela donne un moment <exp(1/4)<2. Il ne faut pas remplacer cette comparaison par 1/p^3, qui n'est pas une borne locale correcte ; le rapport peut se lire correctement avec l'indice j=p-1.

Pour le moment 1/sqrt(d), le terme local est 1/([p(p-1)-1](sqrt(p)-1)). Pour p>=3, il est au plus 3/[sqrt(p)(p-1)^2], puis 3/(p-1)^(5/2). Son logarithme total est au plus

```
3 sum_(j>=2)j^(-5/2)
<=3[2^(-5/2)+(2/3)2^(-3/2)]
=7/(4sqrt2)<4/3<log4.
```

D'où le moment <4. L'exclusion du facteur p=2, assurée par N pair, est essentielle à ces marges.

Le préfixe acquis de mu_N est appliqué dans son vrai domaine x>=N^(1/8), x<=N, masque N avec log N<=2u, sous les prémisses du §12.7. Pour t>=alpha>=N^(1/4), séparer h_N à sqrt(t) donne : les arguments t/d de la tête restent >=sqrt(t)>=N^(1/8), et la queue triviale est bornée par t^(-1/4)sum|h_N(d)|/sqrt(d). Les moments R11 donnent exactement

```
|sum_(r<=t)a_N(r)|/t <= eps_M(u),
eps_M=26u^2 exp(-sqrt(u)/96)+2exp(-u/64)+4exp(-u/16).
```

Abel est ensuite effectué avec **les deux endpoints alpha et H**. Pour alpha>e, le poids log t/t décroît, et le coût est au plus

```
eps_M[log H+log alpha
      +integral_alpha^H (log t-1)/t dt]
<=eps_M[u^2/2+2u] <= 2u^2 eps_M
```

dans le domaine adaptatif. Avec X<N, cela confirme |J_head|<=2Nu^2 eps_M de R12. Aucun préfixe de la somme mu(r)Lambda(N-kr) longue n'est invoqué dans cette étape.

## 6. BV all-prefix pondéré et masque premier : R13–R14

Dans la coupe, q=b^2*c est unique et |w(q)|<=u*tau(b)<=u*tau(q). La classe N modulo q est réduite puisque gcd(q,N)=1. Le vrai psi conserve ses puissances premières. Le passage à psi_N retire uniquement les puissances dont la base p divise N, avec masse par modulus au plus

```
sum_(p|N,p^j<=N)log p <= omega(N)u <= u^2/log2.
```

Les proper powers à base unitaire restent dans psi_N. La somme de ces frais pondérés est au plus (u^3/log2)Q0(1+u). Cela donne R13, sans ajouter un nouveau masque carré-libre.

L'erreur E(q) est bien un maximum sur tous les préfixes x<=N et toutes les classes réduites. Pour q<=sqrt N et u>=1, la borne élémentaire conserve son +1 : psi(x;q,a)<=(N/q+1)u<=2Nu/q. Le principal est au plus 3N(1+log q)/q<=4.5Nu/q. Leur somme est <8Nu/q ; la marge de R14 est donc valide.

Le partage tau(q)<=u^L et tau(q)>u^L donne respectivement u^(L+1)Delta_BV et

```
8Nu^(2-L)sum_(q<=Q0)tau(q)^2/q
<=8Nu^(2-L)(1+log Q0)^4.
```

La dernière inégalité suit de tau(q)^2<=d_4(q) et du produit de quatre sommes harmoniques. On retrouve toutes les puissances de u de R14.

L'input indépendant est le BV classique **all-prefix**, déjà rappelé dans la monographie autour de (36). Une source primaire directe de cette forme est [R. C. Vaughan, The Bombieri–Vinogradov Theorem, §1](https://personal.science.psu.edu/rcv4/Bombieri.pdf), qui conserve le supremum sur les préfixes et le maximum sur les classes réduites. Il n'est pas remplacé par un simple endpoint moyen, ni par une estimation de parity correlation.

Pour L=A+8 et un BV d'exposant 2A+11=A+L+3, la petite partie vaut au plus C_(2A+11)N/u^(A+2). La grosse partie vaut au plus 2^7 N/u^(A+2), car (1+u)^4<=16u^4. Le nombre 2^7 est correct. Enfin Q0<=N^(7/16) satisfait sqrt N/u^(B_A) pour N suffisamment grand, pour chaque B_A fixé. Les constantes et ce seuil supplémentaire ne sont pas évalués ici. L'onset acquis de I ne prouve pas à lui seul leur validité à u=10^24.

## 7. Résultat partiel et reste réel : R15–R16

L'identité complète est estimée en quatre postes : principal entier R12, vraie queue physique R8, queue du principal R9 et erreur AP R13/R14. Le signe des coefficients n'est pas postulé favorable. Cela donne

```
|P_head_all|<=E_H,
E_H=2Nu^2 eps_M+E_phys+E_main+E_AP,
|P_head^{>=2}|<=E_H+H*u^2.                            (R15)
```

Le retrait de k=1 est donc réellement payé. Puisque B_cut est de taille N^(1/32), H de taille N^(3/8) et Q0<=N^(7/16), les pertes élémentaires sont des puissances de N sous le terme principal. Le Mertens masqué donne une décroissance exponentielle en sqrt(u), et BV permet toute puissance logarithmique fixée avec seuil propre. **P_head_all=O_A(N/u^A) est ainsi une conséquence analytique partielle justifiée**, sous les inputs acquis ; la même conclusion vaut après le retrait de k=1.

Ce résultat écrit n'est pas une preuve Lean et ne reçoit pas la condition de victoire. La fermeture demeure exactement

```
D_N=P_head^{>=2}
    +[P_tail^{>=2}-M^{>=2}]
    +I+2max(e,0).                                    (R16)
```

Le bracket n'est pas contrôlé par les quatre postes de tête. Pour k=3, il garde par exemple mu(r)Lambda(N-3r)log r sur r>H, avec toutes les unités et faces. BV ne supprime pas ce coefficient Möbius, et un twist natif modulo k vaut 1 sur cette fibre physique. Les paiements de I, EJ et Z_ref ne peuvent pas être ajoutés plusieurs fois ou réaffectés à une branche amputée sans son raccord.

Un candidat gagnant doit donc fournir un gain signé indépendant sur le bracket de R16, payer 2max(e,0), puis calibrer tous les frais sur le domaine revendiqué. Introduire la petite taille du bracket comme hypothèse analytique serait déplacer la cible. La tête apporte un progrès local réel sans prétendre résoudre ce reste.

## 8. Tests finis et falsifications ciblées

Les deux scripts lus utilisent des coefficients entiers ou rationnels de logarithmes premiers. Le reçu `compensation.json` porte sur les têtes X=303 et X=1024, des arguments isolés, 65 536 couples de bascule et des domaines k tronqués explicitement. `head_regrouping.json` porte sur douze m choisis, des fibres complètes/coupées et les comptages positifs. Ils ne calculent ni toute la tête ni un budget analytique à N=10^8.

Les témoins essentiels sont présents et cohérents :

- r=303, k=63, n=99980911 premier : le coefficient exact est 0. La formule illégale d^2*t sans gcd(d,r)=1 donne -1 ; la version lcm et la version à d restreint redonnent 0. L'expansion actuelle R5 garde la restriction nécessaire.
- m=112211=11*101^2, n=99887789 premier : le coefficient de tête complet est 0. À B_cut=1, la tête vaut -log101 et la queue +log101 ; leurs produits par Lambda_N(n) sont non nuls et se compensent. Le masque mu(m)^2 ne peut pas être imposé à la coupe.
- m=173, n=99999827 premiers : la tête tout-k garde -log173*log99999827 à k=1, tandis que sa version k>=2 enlève ce terme. Il faut la soustraction R6 ou la cancellation centrée complète, et non l'oubli de cette ligne.

Ces falsifications concernent des raccourcis exclus de la version présente. Aucune faute logique ou constante fausse n'a été trouvée dans R1–R16 tels que lus. Le mécanisme actuel passe le gate algébrique fini dans cette portée ; il ne passe pas le gate de victoire globale, puisqu'il garde le bracket non estimé.

## 9. Traçabilité et décision de protocole

Empreintes des dernières entrées disponibles pendant cet audit :

```
agent1_signed_compensation.md caf6519306cc308d6e6401b3774efcf0286cc43fcc875164aa73c79613bfb2fb
compensation_checks.py       b6dc5fbb7e35b5bad93c54513970845c5bf721573a7e2513742d20ebc4a62262
compensation.json            44fb25267eb3088037ef6d16bb3998a42a94952576662f279c35527aa702364c
head_regrouping_checks.py    4e2b87f912177f05871bdefd6d532db99ca02ec1ac888cda5bfb9032ad3eb65e
head_regrouping.json         f85071f0d1f6f1ecfd1d9612caf8d874bd9669933fd47fc00ae9ffffbc3cd7eb
```

Chaque reçu correspond à l'empreinte du script indiquée dans son propre contenu. Le registre round8 a été chargé explicitement par chemin pour éviter un module `conservation` homonyme des boucles précédentes : **227 artefacts antérieurs inchangés**, registre b973b6ea8ce1fdef2a704e1e0bcc977ee7ac5b140e71d17cc3d90c165317243a. Seul le présent rapport est ajouté par ce rôle ; les autres fichiers et Arbor sont inchangés.

Le rejeu final des scripts et le verdict du Juge restent indépendants. Cet audit ne compile aucun Lean, ne valide aucun nouvel axiome et n'augmente pas le compteur des théorèmes Lean. La classification est `ANALYTICAL_PARTIAL_HEAD_GAIN`, avec `GLOBAL_SIGNED_BOUND_NOT_OBTAINED` et `VICTORY_FALSE`.
