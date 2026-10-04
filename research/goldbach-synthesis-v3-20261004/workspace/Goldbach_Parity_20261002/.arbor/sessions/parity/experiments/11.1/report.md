# Agent 3 — audit du transport conjoint, boucle 9

**Verdict : V1 réfutée avant compilation ; V2 et J1–J6 cohérents dans leurs portées.** Le défaut harmonique J3 possède un paiement indépendant explicite dès l'onset source u>=10^24. La bande physique J4 possède un paiement qualitatif avec seuil BV supplémentaire non évalué. Le reste signé de J5/J6 n'est pas estimé. Aucun fichier Lean standard de substitution, aucune hypothèse postulant la cible et aucune erreur fictive du compilateur ne sont produits.

## 1. Sources et objets conservés

J'ai lu le rapport final `agent1_joint_long.md`, le script gelé `new_contract_checks.py`, son reçu `new_contracts.json`, le rapport final du rôle 6, l'équation (54) et le §6.3 de la monographie. La page 27 originale rendue dans `source54_page27.png` a été examinée visuellement ; l'équation (53) et ses prémisses sont lisibles dans ce même rendu.

Le cadre source est inchangé : N pair, u=log N, ell=log u, alpha=ceil(N^(1/4)), Q=floor((N-1)/alpha), mêmes I_alpha et e. Le paramètre auxiliaire est a9=ceil(N^(7/16)) ; il ne remplace pas alpha dans le déficit initial et **Q reste le Q source**. Les deux noyaux auxiliaires D_a et W_a gardent les mêmes diviseurs et unités ; seule la face stricte a*k<m varie. Lambda_N garde n>1, gcd(n,N)=1 et les puissances premières propres à base unitaire. Aucun facteur mu(n)^2 n'est ajouté au raw.

Le pont couvert source, sous son contrat complet, demeure D_N=-S_full+2max(e,0), avec S_full=S_Lambda^alpha-I_alpha. L'onset adaptatif lu dans le PDF est u>=10^24. L'usage du paiement global acquis de I_alpha conserve ses prémisses et ne le paie qu'une fois. La comptabilité directe alternative du §6.3 n'autorise pas à supprimer le e couvert sans preuve de raccord ni à additionner les pertes des deux routes.

## 2. Masque omis dans V1 et correction V2

Le défaut de V1 est réel et précisément localisé. La condition gcd(r,kN)=1 n'implique pas gcd(k,N)=1. À N=100000000,

```
n=2, m=99999998, r=161, k=621118,
kr=N-2, alpha<r<=3163, k<Q,
gcd(r,kN)=1, gcd(k,N)=2.
```

Le coefficient mu(k)^2mu(r) vaut 1 ; V1 ajoute log2*log161. Le point source est pourtant nul par Lambda_N(2)=0. Ce contre-exemple impose le rejet avant compilation, conformément au protocole. L'erreur porte sur une unité omise ; elle n'est pas une erreur Lean ni une nouvelle contradiction des acquis.

V2 conserve Lambda_N et les unités explicites de k et r. La variante numérique avec Lambda_N et seulement gcd(k,r)=1 est équivalente : Lambda_N(N-kr) non nul entraîne gcd(kr,N)=1, donc les deux unités à N. L'autre variante utilise Lambda ordinaire mais conserve gcd(k,N)=1 et gcd(r,kN)=1. Le script compare ces deux expressions, ce qui correspond correctement à la correction mathématique.

## 3. Transport exact et cancellation conjointe : J1/J2

Pour k|m, le front de D_alpha-D_a9 est exactement alpha*k<m<=a9*k, soit alpha<r=m/k<=a9. La bascule acquise mu(k)mu(kr)=mu(k)^2mu(r)1_(gcd(k,r)=1) donne le signe négatif du physique, car log(k/(kr))=-log r. Le modèle reste une somme libre en m avec gcd(k,(N-m)N)=1 ; il n'est pas assimilé aux seuls multiples de k.

La différence de scalaires est ainsi

```
S_Lambda^alpha-S_Lambda^a9=-P_bande^all-Z_face^all.     (J1)
```

Cette identité est pointwise et reste exacte sur une sélection ou une tête seulement si la même sélection est conservée dans les deux bandes. Le front n>1 donne kr<=N-2 ; le point n=1 est déjà Mangoldt zéro. La condition de cap source Q(alpha+1)>N-1 permet toujours le préfixe complet pour r>alpha. Aucun nouveau Q n'est requis.

Sur k=1, P_bande,1=sum_(alpha<m<=a9)mu(m)Lambda_N(N-m)log m et Z_face,1=-P_bande,1. Leur cancellation est au même point et sous les mêmes masques. Retirer les deux ensemble donne

```
C_face=P_bande^{>=2}+Z_face^{>=2}
      =P_bande^all+Z_face^all,
S_Lambda^alpha=S_Lambda^a9-C_face.                    (J2)
```

Pour chaque seuil auxiliaire, P1^a=M1^a également. Ces cancellations du k=1 de la bascule ne suppriment pas le l=1 de la couverture logarithmique de la boucle 7. Le reçu distingue correctement ALL-k et k>=2, notamment au point m=2121.

## 4. Audit intégral du paiement harmonique J3

### 4.1 Préfixes entiers et masque réel

Posons M9=ceil(N^(3/4)). Sur m>=M9 et sous u>=10^6, a9<=2N^(7/16), alpha<=2N^(1/4). Les planchers donnent

```
floor((m-1)/a9) >= N^(5/16)/8,
floor((m-1)/alpha) >= N^(1/2)/8.
```

Par exemple, la première borne vient de (N^(3/4)-1)/(2N^(7/16))-1, puis d'une marge entière très inférieure à N^(5/16). Le Q source est au moins N^(3/4)/8 dans ce domaine, donc le min avec Q ne réduit aucune des deux bornes annoncées. Pour R_a9>=N^(1/5), il suffit ensuite de N^(9/80)>=8 ; pour R_alpha, de N^(3/10)>=8. Ces conditions sont largement incluses dans u>=10^6. Les deux préfixes sont donc positifs et dans le domaine explicite de (54).

Aux points actifs, n=N-m>1 et K=nN est positif, pair et <N^2, donc <=N^3. Le même K est employé pour les deux seuils, avec son vrai masque gcd(k,nN)=1. On n'utilise pas S(N) à la place de S(nN).

La phase exacte est

```
W_a(n,m)=W_K(R_a)+log(R_a/m)A_K(R_a).
```

Comme 1<=R_a<m, |log(R_a/m)|<=u. L'endpoint est ainsi retenu et payé. Sur ce bulk, m>a9 ; le terme k=1 est actif dans les deux préfixes et sa différence est zéro. Le retrait >=2 ne crée donc pas une nouvelle charge.

### 4.2 Lecture exacte de (54) et affaiblissement valide

La lecture visuelle du PDF donne

```
u[|W_K(R)+H_K(0)|+u|A_K(R)|]
 <=4*10^8*u^5*exp(-sqrt(u/60))+160*u^2*exp(-u/40),
K<=N^3, R>=N^(1/5), u>=10^6.
```

J3 utilise exp(-sqrt(u)/60). Ce n'est pas la transcription littérale de l'exposant source : c'est un **affaiblissement correct**, puisque sqrt(u/60)>=sqrt(u)/60. Avec le G54 plus large du rapport, |W_a+S(K)|<=G54/u suit donc bien de (54) et de l'endpoint. Pour K pair, H_K(0)=S(K).

Les deux principaux S(K) s'annulent exactement dans W_alpha-W_a9. Par conséquent la différence harmonique par point est <=2G54/u. Multiplier par |mu(m)|<=1 et Lambda_N<=u, puis compter au plus N points, paie le bulk par 2NG54. Aucun petit corrélateur Möbius–Mangoldt n'est supposé dans ce paiement.

### 4.3 Petite face et constantes de J3

Pour m<M9, on ne donne aucun principal à un préfixe vide. Chacun des deux noyaux k>=2 est directement borné par u*sum_(k<=Q)1/phi(k)<=3u(1+u). Le facteur Lambda_N<=u et les deux noyaux donnent 6M9*u^2(1+u). Comme M9<=2N^(3/4), la charge est au plus 12N^(3/4)u^2(1+u).

Les deux régions réunies donnent exactement la marge annoncée :

```
|Z_face^{>=2}|<=E_Z9,
E_Z9/N=8*10^8*u^5*exp(-sqrt(u)/60)
       +320*u^2*exp(-u/40)
       +12*u^2*(1+u)*exp(-u/4).                     (J3)
```

Les coefficients 8*10^8 et 320 viennent des **deux** préfixes, et le 12 de la petite face avec son ceil. Le calcul ne supprime ni les puissances propres unitaires ni les fronts mobiles.

### 4.4 Allowance explicite et décroissance

Normaliser J3 par N/(u ell) multiplie les trois termes par u ell. À u0=10^24, u0<2^80 et ell0<56<2^6. Les facteurs positifs sont respectivement sous 2^516, 2^255 et 2^331 :

```
8*10^8*u0^6*ell0 <2^(30+480+6),
320*u0^3*ell0 <2^(9+240+6),
12*u0^3*(1+u0)*ell0 <2^(4+240+81+6).
```

Leurs exposants négatifs sqrt(u0)/60, u0/40 et u0/4 sont tous >10000. Comme e>2, chaque terme normalisé est <2^(-1000). Leur somme est <10^(-12).

Les dérivées logarithmiques, par rapport à log u, sont respectivement 6+1/ell-sqrt(u)/120, 3+1/ell-u/40 et 3+u/(1+u)+1/ell-u/4. Elles sont négatives dès u0 et restent négatives : les termes positifs sont bornés tandis que les termes négatifs croissent en magnitude. Cela confirme

```
E_Z9 <10^(-12)N/(u ell) pour tout u>=10^24.
```

Cette nouvelle allowance est un paiement écrit indépendant, sous les inputs source de (54). Elle n'est ni un calcul Lean ni une validation numérique à N=10^8.

## 5. Bande physique recalibrée : J4

La tête de la boucle 8 est réutilisée avec H=a9, sans changer son support inférieur alpha, les unités, Lambda_N, la coprimalité, les planchers et le cap Q. Son reindexage conserve

```
q=b^2*c,
w=mu(b)mu(c)sum_(g|b,alpha<c*g<=a9)mu(g)log(c*g),
b,c squarefree, gcd(b,c)=1, gcd(b*c,N)=1.
```

Les fibres coupées sont gardées. L'expansion préalable a toujours gcd(d,rN)=1, nécessaire à q=r*d^2*t. La coupe B9_aux=floor(N^(1/64)) est distincte du B acquis et du B_cut de la boucle 8. Elle expose q<=B9_aux^2*a9<=2N^(15/32). Pour u suffisamment grand, cette borne est <=sqrt N ; le facteur 2 est réellement conservé.

Les queues restent deux charges séparées. La vraie queue physique utilise le comptage positif n=N-qv, donc psi_N<=Nu/q sans +1. La queue principale utilise phi(b^2*c)=b*phi(b)*phi(c). Les deux applications d'Abel de la boucle 8 ne dépendent pas d'une fibre complète, et donnent E_phys9 et E_main9 avec leur dénominateur B9_aux. Une coupe sur un m non carré-libre n'est pas artificiellement annulée par mu(m)^2.

Le principal eulérien et les moments <2 et <4 restent ceux du même tilt h_N. Leur convolution utilise les préfixes mu_N à arguments >=N^(1/8), après le split à sqrt(t) pour t>=alpha. L'endpoint supérieur a9 reste <N et log a9<=u dans le domaine utilisé. Abel avec alpha et a9 conserve ainsi le majorant 2Nu^2 eps_M.

Sur les moduli retenus, |w|<=u*tau(q). L'erreur AP emploie le vrai BV all-prefix. Le partage de tau(q) à u^L, tau(q)^2<=d_4(q), et le retrait des puissances à base p|N donnent la marge E_AP9 du rapport. Dans cette borne AP générale, le +1 est gardé avant son absorption ; il n'est pas supprimé au motif que les queues physiques spéciales n'en ont pas besoin. Les puissances propres à base unitaire restent dans psi_N.

Le point k=1 du physique tout-k doit encore être retiré, avec charge <=a9*u^2. Il ne s'agit pas d'une seconde charge globale de I ni d'une nouvelle charge de Z après la cancellation J2. On obtient donc bien

```
|P_bande^{>=2}|<=2Nu^2 eps_M+E_phys9+E_main9
                 +E_AP9+a9*u^2.                    (J4)
```

Pour chaque puissance logarithmique fixée A, le niveau 2N^(15/32) est sous sqrt N/u^(B_A) éventuellement ; les queues sont des puissances de N et les moments Mertens donnent leur gain indépendant. La conclusion qualitative O_A(N/u^A) est cohérente. **Le nouveau seuil BV et ses constantes ne sont pas évalués**, et aucune validité effective de J4 dès u=10^24 ne résulte du seul paiement acquis de I_alpha. Cette portée diffère de celle explicite de J3.

## 6. Ledger source et ligne native longue : J5/J6

Le signe de J5 suit de J1/J2 : S_Lambda^alpha=S_Lambda^a9-P_bande^{>=2}-Z_face^{>=2}. Après la cancellation k=1 au seuil a9, S_Lambda^a9=-P^{a9,>=2}+M^{a9,>=2}. Le déficit initial est donc exactement

```
D_N=P^{a9,>=2}-M^{a9,>=2}
    +P_bande^{>=2}+Z_face^{>=2}
    +I_alpha+2max(e,0).                             (J5)
```

Le même I_alpha figure une fois ; aucun I_a9 n'est créé avec son paiement. Le même e couvert reste nécessaire. L'appairage concerne la même face stricte a9*k<m, pas une bijection du modèle libre vers les multiples kr physiques.

Pour 3∤N, k=3 et m>3a9, la bascule donne P3=-B0 : les multiples de 9 sont déjà Möbius zéro. Le modèle exclut la classe m congruente N modulo 3 par gcd(N-m,3)=1 ; les deux classes restantes donnent M3=B0+B_{-N}. Le coefficient externe mu(3)/phi(3)=-1/2 donne au déficit

```
E3=P3+M3/2=(B_{-N}-B0)/2.                           (J6)
```

Toutes les sommes gardent Lambda_N, log(m/3), m<=N-2 et le front strict. La phase native du physique est 1, car N-3r est congru à N modulo 3. Les préfixes acquis de mu*chi et le BV de Lambda seule n'estiment pas les B_c avec le coefficient additif Lambda_N(N-m).

Les deux signes numériques de J6 réfutent uniquement une faveur pointwise uniforme. Ils ne prouvent aucune impossibilité de compensation globale. Le contrôle signé du bracket long, avec 2max(e,0), reste l'obligation quantitative manquante. Le postuler dans un futur théorème ne satisferait pas la condition de victoire.

## 7. Transfert direct du paiement des puissances propres au bracket apparié

Le bracket W12 du rapport 2 est B_H=P_tail^{H,>=2}-M^{alpha,>=2}, avec deux fronts distincts. Le bracket J5 est B_a9=P^{a9,>=2}-M^{a9,>=2}, avec le front a9 dans les deux termes. Ce sont deux objets différents. On ne compare pas leurs valeurs absolues et on n'ajoute pas leurs allowances comme deux paiements du même reste. Le transfert suivant est une nouvelle application directe des deux majorants positifs de W11 au seul B_a9.

Partitionner son premier axe en n premier et n=p^j avec p premier et j>=2, en gardant Lambda_N, n=N-m, les unités et tous les k>=2 du cap Q. Noter B_prime^{a9} et B_pp^{a9} les deux sous-sommes. Pour un n=p^j fixé, le physique au front a9 possède au plus tau(m) diviseurs k. Ses conditions r=m/k>a9>=1 et m<N donnent 0<log r<=u, et |mu(k)^2 mu(r)|<=1. Sa masse absolue est donc au plus

```
u*Lambda(n)*tau(m).
```

Le modèle au même front a9 possède, pour chaque k actif, m>a9*k, donc 0<log(m/k)<=u. Ses coefficients de Möbius et indicatrices unitaires sont de valeur absolue au plus 1. Sa masse absolue est au plus

```
u*Lambda(n)*sum_(k<=Q)1/phi(k).
```

Les fronts et les unités ne font que restreindre ces deux masses positives. Le raisonnement vaut même pour toute paire de fronts >=1 avec le même Q et Lambda_N ; il n'utilise aucune cancellation de B_H. Il ne supprime aucune puissance propre à base unitaire et n'introduit aucun mu(n)^2.

Les bornes W8–W10 sont vérifiables élémentairement avec leurs constantes :

- L'identité 1/phi(k)=(1/k)sum_(d|k)mu(d)^2/phi(d) et le produit eulérien positif donnent sum_(k<=Q)1/phi(k)<=e(1+log Q)<3(1+u). Le produit est au plus e puisque sum_p 1/[p(p-1)]<=sum_(j>=2)1/[j(j-1)]=1. Ici Q<=N.
- Pour z>=1, tau(z)<=2^2040*z^(1/8). Pour p>=256, a+1<=2^a<=p^(a/8). Pour p<256, (a+1)p^(-a/8)<(1-p^(-1/8))^(-2)<256, car 2^(-1/8)<15/16, équivalent à 15^8>2^31. Au plus 255 petits premiers donnent 256^255=2^2040 ; aucun exposant a n'est limité artificiellement.
- Le compte positif des n=p^j<N, j>=2, a au plus sqrt(N) bases pour chaque j, au plus u/log2 exposants, et Lambda(p^j)<=u. Ainsi sum_pp Lambda(n)<=sqrt(N)*u^2/log2. Garder les bases p|N dans ce majorant est une surmajoration positive des termes annulés par Lambda_N.

Comme m<N, ces trois bornes appliquées aux deux masses du nouveau bracket donnent directement

```
|B_pp^{a9}|<=sqrt(N)*u^3/log2
             *[2^2040*N^(1/8)+3(1+u)].              (PP-a9)
```

Pour contrôler la constante, normaliser PP-a9 par N/(1024u ell). Si u>=65536, log2>=1/2, ell<=u et 1+u<=2u donnent un rapport au plus

```
2048*u^5*2^2040*exp(-3u/8)
 +12288*u^6*exp(-u/2).
```

On a log u<=u/4096 dans ce domaine : log(65536)=16log2<16 et log(u)/u décroît. De même log2048 et log12288 sont <16<=u/4096, et 2040<=u/32 avec log2<1. Les deux termes sont donc respectivement au plus exp(-1402u/4096) et exp(-2041u/4096). Leur somme est <=2exp(-u/4)<1. Ceci établit indépendamment

```
|B_pp^{a9}|<=N/(1024u ell) pour u>=65536,
donc en particulier pour u>=10^24.                 (PP-a9-paid)
```

Ce paiement explicite ne requiert ni BV ni un gain supposé sur le moment signé premier. Au seuil source, J5 devient exactement

```
D_N=B_prime^{a9}+B_pp^{a9}
    +P_bande^{>=2}+Z_face^{>=2}
    +I_alpha+2max(e,0).
```

Le poste B_pp^{a9} reçoit PP-a9-paid une fois. L'ancien B_pp^H de W12 ne figure pas dans ce ledger et n'y reçoit aucune seconde charge. Le même I_alpha et le même e original restent ceux de J5. La bande physique J4 conserve son seuil BV non évalué, malgré ce paiement élémentaire du nouveau reste properpower.

Le moment ouvert B_prime^{a9} porte exactement les deux fronts a9 et Lambda_N(N-m) sur N-m premier. Il n'est pas W13 au couple H/alpha. La formule J6 de classes modulo 3 s'applique au front a9 de ce nouveau bracket, mais n'en fournit pas l'estimation signée. Un gain de parité utile et le budget de 2max(e,0) restent manquants ; PP-a9-paid est un résultat analytique partiel écrit, pas une certification Lean ni une victoire.

## 8. Portée des reçus finis et décisions

Le reçu gelé vérifie V2 sur douze points déclarés et sur m=1..1024. La queue n'est pas énumérée. Les variantes unitaires sont comparées indépendamment et le retrait conjoint k=1 est enregistré. V1 garde son statut ERROR_FALSIFIER. Ces PASS concernent les identités finies, pas Delta_BV, E_P9 ou D_N.

Les témoins du rapport sont cohérents avec leurs bonnes sommes :

- m=311 a un raw actif mais Lambda_N(N-m)=0 ; il n'est pas un témoin de prime du premier axe.
- m=1017399, n=9949^2 : Lambda_N=log9949 reste active malgré mu(n)^2=0. La bande physique est nulle, mais les deux préfixes harmoniques 10173 et 321 donnent une variation non nulle. Après extraction de log9949, le coefficient non nul de log9973 suffit par indépendance rationnelle des logarithmes premiers ; on ne présume pas une indépendance algébrique de monômes logarithmiques arbitraires.
- m=2121 : P_bande ALL-k=0, mais P_bande^{>=2}=Lambda_N(N-m)log2121. Le retrait k=1 doit être effectué dans les deux bandes. Le raw du point est zéro lorsque n est premier, ce qui distingue S_full de S_Lambda.
- m=32421 et m=9507 : les valeurs respectives de J6 sont +(1/2)log99967579*log10807 et -(1/2)log99990493*log3169, avec leurs cofacteurs >a9. Le candidat m=31209 a Lambda_N zéro et reste rejeté.

Aucune faute logique ou constante fausse supplémentaire n'a été trouvée dans J1–J6 corrigés tels que lus. Le rejet concret demeure celui de V1 et des raccourcis pointwise documentés. La version corrigée passe le gate algébrique fini dans ses domaines ; la victoire reste fausse, sans prétendue erreur Lean.

## 9. Traçabilité et classification

Entrées finales lues et empreintes vérifiées :

```
agent1_joint_long.md 2456a7620e436bf569aa973022579db2a4d1eeb097cae6df5339027ea00354ab
agent6.md            b5cc44da24fb60f44460e342cb6ede463733eac02d9b014b4aebadb946aaca83
new_contract_checks.py e0b8fb5a56757b7773d8be30365d78af36aa7ab7aa6b999735923dfc0bc79b1c
new_contracts.json     ac5bad36c2527886c6f3ac10150aa44c8f20550d683ef5a0eedab5160a60271d
source54_page27.png    890eef47a566adb22c7ef10a9f5594e19c9c84dc4499bac38efe714910660c1e
agent2_weighted_operator.md 43bd75aa25f7ef905936ee10405e05442fbeb48283cf6576cb273c9f8b8c3d8a
agent4_contract_audit.md    9f82aa8b1422d781c46539909d2a4f57b0ef8af670cf3aefe89a780edb6932ef
```

Le reçu correspond à l'empreinte interne de son script, annonce explicitement aucun appel Lean et aucune victoire, et garde le falsificateur V1. Le registre9 chargé par chemin explicite confirme **307 artefacts antérieurs inchangés**, dont 54 fichiers de round8, avec PNG et .olean inclus ; registre SHA-256 4a637dc44cd1fe2d7ae5850b4999ab052c069084143d69aa52484f66e250fe0f. Aucun ancien banc n'a été exécuté par cet audit.

Ce rôle ajoute uniquement le présent rapport, sans mutation Arbor ni modification des rapports gelés, des sources, PNG ou .olean. Le rejeu final du Juge reste indépendant. Classification : `INDEPENDENT_EXPLICIT_HARMONIC_FACE_PAYMENT`, `INDEPENDENT_DIRECT_PROPERPOWER_PAYMENT`, `PHYSICAL_BAND_QUALITATIVE_THRESHOLD_UNEVALUATED`, `GLOBAL_SIGNED_BOUND_NOT_OBTAINED`, `VICTORY_FALSE`.
