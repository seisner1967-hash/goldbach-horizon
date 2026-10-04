# Agent 1 — transport conjoint de la face longue, boucle 9

**Statut : transport conjoint exact corrigé et paiement indépendant du défaut harmonique ; fermeture de parité encore ouverte.** Le progrès distinct de la boucle 8 est le paiement du modèle qui accompagne un déplacement de la face de racine. Le déplacement du seul physique ne suffirait pas. La première formule envoyée oubliait un masque unitaire et a été réfutée avant compilation ; cette version et son témoin sont archivés ci-dessous. Aucun ancien fichier ni acquis n'est modifié, et aucun nouveau fichier Lean standard n'est proposé comme victoire.

Sources de contrat lues avant l'idéation : `round9/PROBE_BLOCK.md`, `.arbor/sessions/parity/.coordinator/messages/round8_feedback.md`, le TreeView courant au format constraints, les audits finaux de la boucle 8 et les §§6.2–6.3, 12.2, 12.7 de la monographie. Les sources restent des notations et acquis ; la condition de victoire est celle de l'utilisateur.

## 1. Analyse de principes et différence avec R15

Après le paiement acquis global de I, le physique porte mu(r)Lambda(N-kr)log r. Le coefficient mu(k)^2 du facteur k est positif. Le modèle porte toujours mu(k)mu(m)Lambda(N-m), avec sa propre sélection gcd(k,(N-m)N)=1 ; le mot « modèle » ne permet pas d'en effacer ce coefficient. La phase native est 1 sur k|m et ne fournit aucune nouvelle oscillation sur cette branche.

La boucle 8 a payé une tête physique à r<=N^(3/8), mais son R16 conserve le modèle entier à la face source alpha. Le long bracket restant ne peut être traité comme si son modèle possédait déjà une face r>N^(3/8). Le présent mécanisme déplace **les deux faces**, introduit le défaut exact de ce déplacement et paie le défaut harmonique par une estimation indépendante. Ce paiement ne demande pas une petite corrélation de mu et Lambda : on y majore seulement |mu|, et l'on emploie le préfixe harmonique acquis avec son endpoint.

La masse Nu du secteur l=1 de la boucle 7 n'est pas repayée en valeur absolue. I reste le I source payé une seule fois. Le seuil auxiliaire n'altère ni alpha, ni Q, ni le déficit D_N d'origine. Il donne une représentation appariée de son reste, pas une nouvelle définition plus facile de ce reste.

Le transport doit dépasser les contre-exemples antérieurs : aucune invariance point par point du noyau n'est présumée ; le bloc 101,303,707,2121 ne reçoit pas un signe favorable automatique ; les nonunités ne sont pas effacées après la bascule ; et aucun twist de Jacobi ne remplace la ligne native. Les charges de bande, physiques et harmoniques, sont conservées avant toute estimation.

## 2. Quatre lignes pour l'arbre

Mechanism: Transport conjoint de la face de racine dans l'opérateur physique moins harmonique, avec Q source fixe et modèle du secteur long réellement apparié.

Hypothesis: La bande physique alpha<r<=a9 est contrôlée par le gain tête/BV correctement recalibré, et la différence W_alpha-W_a9 est payée indépendamment par (54) avec ses endpoints ; le bracket au-delà de a9 reste signé.

Observable: Identité S_Lambda^alpha-S_Lambda^a9=-P_bande-Z_face à N=10^8, seuil a9=3163, témoins de variation non nulle, cancellation k=1 jointe et ligne k=3 ayant les deux signes.

Conflicts: Le seuil auxiliaire ne modifie ni alpha/Q originaux ni I/e du ledger ; l'invariance n'est pas point par point, BV ne contrôle pas mu(r)Lambda(N-3r), et le modèle amputé ne reçoit aucun paiement ancien sans raccord.

## 3. Objets auxiliaires, mêmes points et mêmes masques

On conserve N pair, alpha=ceil(N^(1/4)), Q=floor((N-1)/alpha), n=N-m et les noyaux sources. Posons Lambda_N(n)=Lambda(n)1_(n>1)1_(gcd(n,N)=1). Les puissances premières propres unitaires du premier axe restent présentes.

Pour un seuil entier a>=alpha, définissons uniquement des objets auxiliaires

```
D_a(m)=sum_(k|m, 1<=k<=Q, a*k<m)mu(k)log(k/m),
W_a(n,m)=sum_(1<=k<=Q, gcd(k,nN)=1, a*k<m)
                                      mu(k)log(k/m)/phi(k),
S_Lambda^a=sum_(1<=m<N)mu(m)Lambda_N(N-m)[D_a(m)-W_a(N-m,m)].
```

Le Q de ces trois objets est le Q source, pas floor((N-1)/a). Les premiers critères sont toujours les mêmes diviseurs et unités ; seule la face auxiliaire a*k<m varie. Le profil raw original F_N, alpha et Q ne sont pas édités.

Fixons

```
a9=ceil(N^(7/16)), M9=ceil(N^(3/4)),
B9_aux=floor(N^(1/64)).
```

Ces symboles sont distincts du B=ceil(L^20) fixé dans le cadre et du B_cut de la boucle 8. À N=10^8, a9=3163 et M9=1000000. Le recours à a9 est une représentation supplémentaire, pas un transport automatique des acquis vers un autre profil.

## 4. Version initiale fausse et correction

La première formule envoyée au rôle 6 écrivait

```
P_bande^V1=sum_(alpha<r<=a9, kr<=N-2, k<=Q, gcd(r,kN)=1)
                              mu(k)^2mu(r)Lambda(N-kr)log r.
```

Elle omettait gcd(k,N)=1 tout en remplaçant Lambda_N par Lambda. La condition gcd(r,kN)=1 n'implique pas cette unité de k.

Le témoin exact à N=100000000 est

```
n=2, m=99999998=2*7*23*310559,
r=161=7*23, k=621118=2*310559.
```

On a alpha<r<=3163, k<Q, kr=N-2, gcd(r,kN)=1 et mu(k)^2mu(r)=1. Le terme V1 vaut log2*log161>0. Pourtant Lambda_N(2)=0 : tous les termes S_Lambda et Z_face du même point sont zéro. Ce témoin réfute réellement V1 avant Lean. Son défaut est un masque omis, pas une obstruction de parité. Une cancellation fictive avec d'autres termes n'est pas invoquée.

La version V2 conserve explicitement Lambda_N :

```
P_bande^all=sum_(1<=k<=Q, gcd(k,N)=1)
               sum_(alpha<r<=a9, kr<=N-2, gcd(r,kN)=1)
                  mu(k)^2mu(r)Lambda_N(N-kr)log r,
Z_face^all=sum_(1<=m<N)mu(m)Lambda_N(N-m)
                          [W_alpha(N-m,m)-W_a9(N-m,m)].
```

Lambda_N rend certaines unités affichées redondantes, mais elles restent présentes pour identifier exactement la branche source. On pourrait utiliser Lambda ordinaire seulement en conservant les deux unités requises de k et r à N.

## 5. Identité de transport et cancellation jointe k=1

La différence D_alpha-D_a9 conserve exactement les tuples alpha<m/k<=a9. La bascule réelle mu(k)mu(kr)=mu(k)^2mu(r)1_(gcd(k,r)=1), déjà acquise, donne

```
S_Lambda^alpha-S_Lambda^a9=-P_bande^all-Z_face^all.       (J1)
```

Cette égalité est valable point par point ou sur une tête m<=X, si les deux bandes gardent cette même tête. Dans un usage global, X=N-1 et n=1 reste nul par Lambda. La condition source Q(alpha+1)>N-1 permet le préfixe complet de la bascule ; elle est satisfaite dans la famille de cap retenue, et ne change pas lorsqu'a9 augmente.

Sur k=1,

```
P_bande,1=sum_(alpha<m<=a9)mu(m)Lambda_N(N-m)log m,
Z_face,1=-P_bande,1.
```

Ils s'annulent au même point. Il faut retirer les deux termes ensemble. En notant >=2 les deux bandes après ce retrait,

```
C_face=P_bande^{>=2}+Z_face^{>=2}
      =P_bande^all+Z_face^all,
S_Lambda^alpha=S_Lambda^a9-C_face.                      (J2)
```

Pour chacun des deux seuils, la branche k=1 de S_Lambda s'annule également entre DIV et HARM : P_1^a=M_1^a. Cela n'est pas la suppression du secteur l=1 de la couverture logarithmique de la boucle 7.

## 6. Paiement explicite indépendant de la face harmonique

On estime Z_face^{>=2}, après sa cancellation k=1, en deux régions. Sur m>=M9, le k=1 est actif aux deux seuils et se retire déjà dans W_alpha-W_a9. Les deux préfixes exacts

```
R_a(m)=min(Q,floor((m-1)/a))
```

sont positifs. Pour u>=10^6, des marges entières sûres donnent R_a9>=N^(5/16)/8 et R_alpha>=N^(1/2)/8, donc chacun est au moins N^(1/5). Le min avec Q ne les abaisse pas sous ces bornes : Q est de taille N^(3/4), et les marges de rounding précédentes sont beaucoup plus petites. Le masque K=(N-m)N est pair, positif sur les points actifs, et K<N^2<N^3.

La phase source exacte (53) donne

```
W_a(N-m,m)=W_K(R_a)+log(R_a/m)A_K(R_a).
```

L'endpoint n'est pas omis : |log(R_a/m)|<=u. Posons le majorant explicite de (54)

```
G54(u)=4*10^8*u^5*exp(-sqrt(u)/60)
       +160*u^2*exp(-u/40).
```

Ses prémisses réellement acquises sont K<=N^3, R>=N^(1/5), u>=10^6, avec l'input ordinaire Mertens et les moments écrits au §12.2. On obtient |W_a+S(K)|<=G54(u)/u pour les deux seuils. La même singular factor S(K) s'annule dans leur différence, et Lambda_N<=u suffit pour payer le bulk sans hypothèse de corrélation.

Pour m<M9, on n'attribue aucune main S(K) à un préfixe vide. La borne directe sur les sommes k>=2 est |W_a^{>=2}|<=u*sum_(k<=Q)1/phi(k)<=3u(1+u). Les deux noyaux et Lambda_N<=u paient au plus 6M9*u^2*(1+u), puis M9<=2N^(3/4) fournit la marge suivante :

```
|Z_face^{>=2}|<=E_Z9,
E_Z9/N = 8*10^8*u^5*exp(-sqrt(u)/60)
          +320*u^2*exp(-u/40)
          +12*u^2*(1+u)*exp(-u/4).                    (J3)
```

Ce paiement est indépendant de la cible. Il ne prétend pas que chaque différence de noyau est zéro ou favorable. Il préserve les masques mobiles et les deux faces strictes.

À l'onset source u0=10^24, J3 donne notamment E_Z9<10^(-12)N/(u ell). Pour vérifier cette marge, multiplier les trois termes par u ell : au point u0, u0<2^80, ell0<56<2^6, les facteurs positifs sont respectivement sous 2^516, 2^255 et 2^331, tandis que leurs exposants négatifs sont bien au-delà de 10000. Chacun est inférieur à 2^(-1000). Les enveloppes normalisées décroissent pour u>=u0 : leurs dérivées logarithmiques sont respectivement 6+1/ell-sqrt(u)/120, 3+1/ell-u/40, et 3+u/(1+u)+1/ell-u/4, toutes négatives. Cette vérification porte sur la nouvelle face harmonique, pas sur un transfert automatique du paiement de I.

## 7. Bande physique : gain recalibré et domaine distinct

P_bande^all est la tête physique de la boucle 8 avec son endpoint H remplacé par a9. Le raccord est conservé : mêmes Lambda_N, unités, coprimalités et cap Q. Le coefficient répété devient

```
w_{alpha,a9}(b^2*c)=mu(b)mu(c)
                       sum_(g|b,alpha<c*g<=a9)mu(g)log(c*g).
```

Les fibres coupées restent dans ce coefficient. Une coupe auxiliaire b<=B9_aux, distincte des paramètres acquis, expose q<=B9_aux^2*a9<=2N^(15/32). Les deux queues physiques/principales et les moments eulériens de la boucle 8 conservent leur preuve avec cet endpoint ; le poids reste <=u*tau(q) pour u assez grand. Le seuil du BV all-prefix pondéré doit être recalibré à cette portée ; il n'est pas payé par le seul onset de I.

Pour rendre les charges visibles, notons

```
eps_M=26u^2 exp(-sqrt(u)/96)+2exp(-u/64)+4exp(-u/16),
E_phys9=2N u^2(1+u)(2+u)/B9_aux,
E_main9=9N u(1+u)(2u^2+7u+8)/B9_aux,
Q9=2N^(15/32),
Delta_BV(N,Q9)=sum_(q<=Q9)
                 max_(x<=N,a unit modq)|psi(x;q,a)-x/phi(q)|.
```

Comme à R14, avec L>0, une marge de l'erreur AP est

```
E_AP9<=u^(L+1)Delta_BV(N,Q9)
        +8N u^(2-L)(1+u)^4
        +(u^3/log2)Q9(1+u).
```

Le dernier coût conserve la perte Lambda_N versus Lambda ; les puissances premières unitaires restent dans les vrais psi. La borne AP générale y conserve son +1 avant son absorption ; l'absence de +1 dans les queues de multiples positifs n'est pas importée à un intervalle quelconque.

Par conséquent la bande k>=2 paie

```
|P_bande^{>=2}|<=E_P9,
E_P9=2N u^2 eps_M+E_phys9+E_main9+E_AP9+a9*u^2.         (J4)
```

Le dernier terme retire exactement le point k=1 contenu dans le préfixe physique complet. Il est un petit endpoint physique ici, pas un deuxième paiement global de I. La partie correspondante de Z a déjà été cancellée avant J3.

Pour chaque A fixé, les mêmes inputs indépendants donnent qualitativement E_P9=O_A(N/u^A), avec un seuil BV supplémentaire **non évalué**. J4 ne devient donc pas une allowance effective dès u=10^24 par simple substitution. La nouvelle information effective indépendante est J3 ; le nouveau transport joint est J1/J2 ; le physique conserve la portée qualitative correctement raccordée de R15.

## 8. Le bracket long réellement apparié et le ledger source

Définissons P^{a9,>=2} comme la somme physique pondérée par mu(k)^2 avec r>a9, 2<=k<=Q, unités et coprimalités réelles, et M^{a9,>=2} comme la somme du modèle pondérée par mu(k)/phi(k) avec m>a9*k et les unités de W_a9. Les deux portent Lambda_N, et leur différence ne devient pas un coefficient libre. Alors S_Lambda^a9=-P^{a9,>=2}+M^{a9,>=2}.

Le pont du cadre source reste exactement

```
D_N=P^{a9,>=2}-M^{a9,>=2}
       +P_bande^{>=2}+Z_face^{>=2}
       +I_alpha+2max(e,0).                            (J5)
```

I_alpha est le I source, payé une fois sous ses prémisses à u>=10^24. On n'introduit pas I_a9 avec le paiement d'I_alpha, et e est le e couvert d'origine. La comptabilité directe du §6.3 pourrait recombiner certaines charges autrement ; elle ne supprime pas 2max(e,0) dans le D_N couvert sans preuve de son raccord. Les allowances de ces routes ne sont pas ajoutées une deuxième fois.

Le modèle de J5 est « apparié » seulement au sens de la **même face stricte a9*k<m**. Le modèle demeure une somme libre en m ; il ne possède pas de bijection supposée vers les seuls multiples kr du physique. Aucun gain de parité sur ce bracket ne découle de ce mot.

## 9. Limite du transport et variable oscillante qui reste

La face harmonique J3 peut rester payable pour des seuils a<=sqrt N : sur m>=N^(3/4), les préfixes sont encore au moins de taille N^(1/4), donc (54) conserve son domaine. Le goulot de cette application est le paiement physique sous distribution, pas une variation incontrôlée du modèle.

Pour un seuil a de taille N^theta et une coupe b<=N^epsilon, le modulus exposé vaut au plus N^(theta+2epsilon), à des marges de rounding près. Le BV employé exige theta+2epsilon<1/2, ou une calibration polylogarithmique au bord. Si a approche sqrt N avec un écart dépendant de N, on ne peut garder gratuitement la même epsilon ni importer des constantes fixes ; les queues N/B9_aux et le niveau BV changent ensemble. Une alternative avec a=sqrt N/u^J et B_aux=u^C demanderait J>=2C+B_BV(A), plus les seuils des théorèmes et les budgets de queues. Ces constantes ne sont pas évaluées ici.

À a=sqrt N sans marge, la présente preuve ne contrôle pas les moduli a*b^2 pour une coupe croissante b. Cela ne prouve pas une impossibilité mathématique du transport ou du résidu ; cela identifie le domaine du seul input BV utilisé. Le bracket de J5 reste à estimer même avant cette limite.

Une ligne explicite de ce bracket montre le problème. Pour 3∤N, k=3, posons, avec front 3*a9<m<=N-2,

```
B_c=sum_(m congruent c mod3)mu(m)Lambda_N(N-m)log(m/3).
```

Dans cette seule ligne, P_3 désigne la somme intérieure physique sans le facteur externe mu(3)^2=1, et M_3 la somme intérieure du modèle sans le facteur externe mu(3)/phi(3)=-1/2. La contribution de la ligne au déficit -S_Lambda^a9 est donc exactement

```
E_3=P_3^{a9}+M_3^{a9}/2=(B_{-N mod3}-B_0)/2.           (J6)
```

La classe m congruente N est exclue par l'unité du premier axe à 3 dans le modèle ; les multiples de 9 sont annulés par leur Möbius. Le physique n=N-3r est congru à N modulo 3 et sa phase native est constamment 1. Le préfixe acquis de mu(m)chi(m) au module 3 n'est pas un théorème sur B_c, qui conserve Lambda_N(N-m). BV sur Lambda seule ne compare pas ces deux moments. Postuler J6 petit serait postuler un morceau du travail manquant.

## 10. Témoins finis du contrat corrigé

Les sondes transmises au rôle 6 sont des tests exacts à N=10^8, sous l'onset analytique. Elles ne certifient ni Delta_BV, ni E_P9, ni D_N. Le rejeu indépendant des reçus demeure celui du Juge.

**Masque de V1.** Le point n=2, r=161, k=621118 réfute la version non unitaire. V2 le met à zéro par Lambda_N ou par l'unité explicite de k. Il doit rester dans le reçu comme falsificateur de la proposition initiale.

**Variation du modèle.** m=1017399=3*17*19949 est carré-libre et unitaire, n=9949^2. Lambda_N(n)=log9949 et fII(n)=-log9949 : la puissance propre reste donc active. Les cofacteurs r>100 de m sont 19949,59847,339133,1017399, tous au-delà de 3163. La bande physique est nulle, y compris après le retrait k=1. Ses préfixes harmoniques exacts sont R_alpha=10173 et R_a9=321. Le reçu du rôle 6 confirme que Z_face^{>=2} contient le coefficient +1/9972 devant log9949*log9973 ; après extraction du facteur log9949, ce coefficient rationnel non nul devant log9973 dans une combinaison de logarithmes premiers prouve que la variation n'est pas zéro. Ce point est donc un témoin de bande modèle, sans ajouter un masque carré-libre au premier axe.

**Variation physique non nulle.** Au point m=32421=3*101*107, n=99967579 premier, les quatre racines de bande 101,107,303,321 donnent, avec leurs vrais cofacteurs k, la somme -log101-log107+log303+log321=2log3. Le reçu confirme P_bande^{>=2}=P_bande^all=2log3*log99967579, non nul. La racine 10807 de k=3 est au-delà d'a9 et reste dans le secteur long de J6 ; cette partition ne supprime donc pas la même ligne du résidu.

**Même m, fronts différents.** m=2121, n=99997879 premier, rend D_a9=W_a9=0. D_alpha(2121)=0 exactement par les diviseurs k=1,3,7,21, mais W_alpha n'est pas zéro ; son coefficient de log101 vaut -83/720. C'est un témoin d'invariance point par point fausse pour S_Lambda. Dans la décomposition all-k, P_bande vaut zéro ; après retrait k=1, P_bande^{>=2}=Lambda_N(n)log2121 et le modèle retire la même charge opposée. Ces objets ne doivent pas être confondus. Le profil raw original du même point a fII(n)=0, ce qui distingue encore S_Lambda de S_full.

**Deux signes de J6.** Le rôle 6 a trouvé le point nuisible m=32421=3*101*107, n=99967579 premier. On a mu(m)=-1, m>3a9, donc E_3=+log99967579*log10807/2>0. Le point favorable m=9507=3*3169, n=99990493 premier, a mu(m)=+1 et E_3=-log99990493*log3169/2<0. Les deux sont unitaires, et leurs cofacteurs sont réellement au-delà de a9. Le candidat m=31209 a été rejeté : n=13*419*18353 est composite et son Lambda vaut zéro.

Ces témoins réfutent seulement une faveur point par point de la ligne k=3 ou une suppression de bande/modèle. Ils ne réfutent pas une compensation globale. Le banc du rôle 6, `round9/new_contract_checks.py` avec reçu `round9/new_contracts.json`, confirme les deux variantes V2 sur 12 points déclarés et la tête complète m=1..1024, avec cancellation k=1. V1 reste ERROR_FALSIFIER. Les puissances et facteurs répétés restent dans les domaines. Le faux candidat premier m=311 a également été rejeté : N-m=113*199*4447, donc Lambda_N=0 ; il demeure dans le reçu de falsification et n'est pas remplacé par une prétendue ligne première. Ces PASS sont uniquement des contrôles finis d'identités, sans certification d'un budget analytique ni appel au compilateur Lean.

## 11. Contrat de formalisation et décision

Le contrat exact recevable est V2 avec J1/J2, les mêmes unités et fronts, puis son insertion J5 dans le pont couvert original. Toute version sans Lambda_N ou sans l'unité de k doit être rejetée sur le témoin n=2 avant compilation. Les budgets indépendants J3 et J4 ont des portées distinctes : le premier possède un domaine et des constantes explicites ; le second garde le nouveau seuil BV qualitatif non évalué.

La substance manquante reste une estimation signée arithmétique de P^{a9,>=2}-M^{a9,>=2} avec le 2max(e,0) requis par le cadre. Introduire cette petite taille comme hypothèse, compiler seulement J1 ou invoquer BV après disparition de mu(r) ne serait pas un mécanisme gagnant. Aucun fichier Lean de ce type n'est demandé.

Le transport conjoint apporte une représentation plus proche de la frontière critique avec un modèle honnêtement raccordé, et paie un nouveau défaut indépendant. Il ne casse pas encore la parité. La victoire reste fausse, et aucune impossibilité générale n'est alléguée.
