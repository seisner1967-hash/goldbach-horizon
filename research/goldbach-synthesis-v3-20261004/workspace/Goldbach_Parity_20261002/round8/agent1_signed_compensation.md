# Agent 1 — bascule physique et compensation signée, boucle 8

**Statut : gain indépendant sur une tête physique, compensation complète non prouvée.** La piste retire globalement le Type-I acquis, puis estime une tête du physique par son coefficient carré-libre positif, un vrai préfixe de primes en progression et une déformation eulérienne de Möbius. Le secteur long et son raccord au modèle harmonique restent ouverts. Ce rapport ne soumet aucun fichier Lean standard de substitution et ne prétend pas à une victoire.

Les audits finaux `round7/agent3_contract_audit.md` et `agent4_contract_audit.md`, les contraintes Arbor et les §§6, 12.1, 12.7–12.10 de la monographie ont été relus. Les sources, la boucle 7 et les acquis sont conservés.

## 1. Première analyse de principes

La variable qui oscille réellement dans le physique, après multiplication par le Möbius du second axe, est le cofacteur r : son coefficient est mu(r). Le facteur court k est alors carré-libre avec coefficient mu(k)^2, donc positif. Le poids de primes Lambda(N-kr) dépend encore de r ; le caractère natif sur une fibre k|m ne crée aucune oscillation supplémentaire, puisque n=N-kr est congru à N modulo chaque conducteur divisant k.

La masse Nu du secteur l=1 trouvée à la boucle 7 vient principalement du terme -log(N-m) dans le profil raw. Elle ne peut être payée séparément en valeur absolue. Le Type-I complet I, qui contient exactement ce terme et les mêmes noyaux, est toutefois un acquis payé globalement sous ses prémisses. Ce paiement peut être utilisé avant les normes, sans modifier F_N ni supprimer un secteur. Il ne paie pas une nouvelle somme de Möbius pondérée par Lambda.

Le nouveau mécanisme examine donc les cofacteurs alpha<r<=H dans le physique Lambda, et non une coupe de F_N présentée comme le profil entier. La bascule y expose les moduli r*d^2*t. Elle permet une vraie estimation de primes en progression lorsque ces moduli sont sous le niveau de distribution. Elle ne remplace pas le module CRT d'une composante HH par un conducteur de signes ; ici le calcul porte directement sur le scalaire raw complet et son noyau littéral.

Le mécanisme doit dépasser les témoins précédents : m=311 ne peut être effacé ; m=303 et le bloc 101,303,707,2121 ne deviennent pas positifs par une simple identité de transport ; la ligne native k=7 de la boucle 7 ne peut être remplacée par un twist de Jacobi. La piste proposée n'utilise aucun de ces raccourcis. Elle conserve les fibres incomplètes, et son gain vient d'une distribution indépendante des primes sur de vrais moduli, puis de Mertens sur un coefficient multiplicatif précis.

## 2. Quatre lignes pour l'arbre

Mechanism: Retrait global du Type-I acquis puis bascule hyperbolique du physique, avec carré-liberté positive du facteur k et modèle harmonique conservé avant les normes.

Hypothesis: Dans alpha<r<=N^(3/8), une coupe sur le square-part b expose des AP sous le niveau BV ; leur principal est un tilt eulérien de Möbius contrôlé par Mertens, tandis que le secteur long reste à compenser.

Observable: Identités littérales à N=10^8, modules réels b^2*c=r*d^2*t, queues physiques et principales payées, puis audit indépendant du budget signé r>N^(3/8) contre le modèle entier.

Conflicts: La bascule et le type de fibre répétée sont acquis pour I/EJ ; leur extension à Lambda n'est pas seule un gain. BV ne contrôle pas mu(r)Lambda(N-kr) dans le secteur long ; k=1 s'annule dans les deux branches, et le paiement global de I a l'onset 10^24.

## 3. Raccord exact au profil original

On conserve N pair, alpha=ceil(N^(1/4)), Q=floor((N-1)/alpha), n=N-m et les noyaux D et W littéraux. En particulier alpha*k<m, k<=Q, k|m dans D et gcd(k,nN)=1 dans W ne sont jamais remplacés par une face réelle.

Posons

```
Lambda_N(n)=Lambda(n)1_(n>1)1_(gcd(n,N)=1),
S_Lambda=sum_(1<=m<N) Lambda_N(N-m)mu(m)[D(m)-W(N-m,m)],
I=sum_(1<=m<N) log(N-m)1_(N-m>1)1_(gcd(N-m,N)=1)
                         mu(m)[D(m)-W(N-m,m)].
```

La définition de I est exactement celle du §6 : h1(n)=log n, même masque unitaire et même D-W. Le n=1 supplémentaire affiché ici n'ajoute aucune perte, puisque log 1=Lambda(1)=0. Aucun facteur mu(n)^2 n'est introduit, et Lambda_N conserve les puissances premières propres sur le premier axe.

Le raccord est une identité point par point,

```
S_full = S_Lambda-I,
D_N = -S_Lambda+I+2max(e,0).                            (R1)
```

Le e est celui du pont complet d'origine, sans correction de translation ni changement de couverture. On ne le renomme pas en un nouveau reste favorable.

Le paiement global acquis de I provient du §12.7, après (70), avec les prémisses de contour/completion qui y sont spécifiées. Il donne |I|<3*10^(-6)N/(u ell) à l'onset adaptatif **u>=10^24**, et non u>=1024. Le PDF original, p.32 (66), p.33 (u0<2^80, 54<ell0<56) et p.36 (72), confirme l'exposant 24 perdu dans certaines extractions textuelles. Les rendus de source ajoutés par root dans `round8/source_onset_page32.png`, `page33.png`, `page36.png` ne modifient pas cet acquis ; ils permettent de l'identifier correctement. Ce rapport ne transporte pas ce paiement vers N=10^8.

L'usage du paiement de I compense globalement le gros terme logarithmique de la boucle 7. Il ne justifie ni une estimation absolue de son secteur l=1, ni l'oubli des autres l. Le résultat de la boucle 7 reste valable dans sa portée.

## 4. Bascule et ligne k=1

Pour k<=Q, gcd(k,N)=1, définissons

```
P_k=sum_(r>alpha, kr<=N-2, gcd(r,kN)=1)
                      mu(r)Lambda(N-kr)log r,
M_k=sum_(alpha*k<m<=N-2, gcd(m,N)=1, gcd(N-m,k)=1)
                      mu(m)Lambda(N-m)log(m/k).
```

La bascule réelle est

```
mu(k)mu(kr)=mu(k)^2mu(r)1_(gcd(k,r)=1),
S_Lambda=-sum_k mu(k)^2P_k+sum_k mu(k)M_k/phi(k).         (R2)
```

Les facteurs répétés sont conservés : si k n'est pas carré-libre, les deux membres de la première identité sont zéro ; si k est carré-libre mais partage un premier avec r, mu(kr)=0. Cette identité est déjà employée pour I_D au §12.7. La présente application à Lambda, avec tous les masques et fronts, est un raccord à vérifier ; l'identité seule n'est pas l'information nouvelle.

Pour k=1, P_1=M_1 exactement : domaine r=m>alpha, n>1, unités et log r=log m sont identiques. La ligne k=1 du scalaire **centré** est donc zéro avant toute valeur absolue. Cette annulation n'est pas la suppression du secteur l=1 de la boucle 7 ; les deux indices désignent des regroupements différents.

Après cette annulation, écrivons

```
P^{>=2}=sum_(2<=k<=Q, gcd(k,N)=1)mu(k)^2P_k,
M^{>=2}=sum_(2<=k<=Q, gcd(k,N)=1)mu(k)M_k/phi(k).
D_N=P^{>=2}-M^{>=2}+I+2max(e,0).                       (R3)
```

La composante M^{>=2} n'est pas automatiquement payée par l'acquis sur le Z_ref complet : celui-ci contient la ligne k=1 également. La retirer du physique exige de la retirer du modèle, comme dans R3.

## 5. Tête physique et préfixe exact

Fixons H=floor(N^(3/8)), et supposons la condition de cap acquise Q(alpha+1)>N-1. Pour tout entier r>alpha, K_r=min(Q,floor((N-2)/r)) se réduit alors exactement à floor((N-2)/r). On ne remplace pas ce plancher par N/r dans l'identité.

La tête avec k=1 encore visible est

```
P_head_all=sum_(alpha<r<=H, gcd(r,N)=1)mu(r)log r
           *sum_(1<=k<=K_r, gcd(k,r)=1)
                              mu(k)^2Lambda_N(N-rk).    (R4)
```

Le masque Lambda_N rend gcd(k,N)=1 redondant dans cette écriture : si k partage un premier avec N, Lambda_N(N-rk)=0. Il ne supprime pas les proper powers unitaires du premier axe.

Le carré-libre positif admet l'expansion mu(k)^2=sum_(d^2|k)mu(d). Les d partageant r sont exclus par gcd(k,r)=1 ; ceux partageant N n'apportent que des Lambda_N nulles. Pour les autres d, l'expansion exacte de gcd(k/d^2,r)=1 donne t|rad(r). On obtient

```
P_head_all=sum_r mu(r)log r
             sum_(d>=1, gcd(d,rN)=1)mu(d)
             sum_(t|rad(r))mu(t)
             sum_(1<=v<=floor(K_r/(d^2*t)))
                                  Lambda_N(N-r*d^2*t*v). (R5)
```

Tous les termes sont finis, les bornes v<=floor(...) donnant zéro au-delà de leur domaine. Le modulus arithmétique de chaque AP est réellement q=r*d^2*t, premier à N.

Posons X=N-1 et

```
psi_N(X;q,N)=sum_(1<=n<=X, n congruent N mod q)Lambda_N(n).
```

Le dernier préfixe de R5 est exactement psi_N(X;q,N) : les termes n>1 dans cette classe sont n=N-qv avec v>=1 et qv<=N-2. Il n'y a pas de lower-prefix dépendant de r à ajouter ; K_r est justement la limite entière complète. Le point n=N est hors de X, et n=1 a Mangoldt zéro.

Cette identification **contient le point k=1** lorsque d=t=1. Pour estimer la tête de R3, il faudra donc soustraire

```
P_head_1=sum_(alpha<r<=H, gcd(r,N)=1)
                              mu(r)Lambda(N-r)log r,
|P_head_1|<=H*u^2.                                     (R6)
```

La charge R6 est une majoration réelle de cette petite tête, pas l'oubli de la ligne k=1 globale. Sa cancellation globale a déjà été faite dans R3.

## 6. Regroupement réel des moduli répétés

Les coefficients non nuls de R5 ont r,d,t carrés-libres, d premier à r, et t|r. Écrivons de manière unique

```
b=d*t, c=r/t, g=t,
q=b^2*c, r=c*g, d=b/g, g|b,
b,c squarefree, gcd(b,c)=1.
```

Alors mu(r)mu(d)mu(t)=mu(b)mu(c)mu(g), et le coefficient réel est

```
w_{alpha,H}(b^2*c)=mu(b)mu(c)
                      sum_(g|b, alpha<c*g<=H)mu(g)log(c*g).
P_head_all=sum_(b,c squarefree, gcd(b,c)=1, gcd(bc,N)=1)
                      w_{alpha,H}(b^2*c)psi_N(X;b^2*c,N). (R7)
```

Les fronts alpha<c*g<=H sont littéraux. Cette fibre est du même type que celle du §12.1, (46)–(47). La découverte n'est pas une nouvelle identité de fibre autonome ; c'est son application au porteur physique Lambda de R4, et les coûts indépendants que ce raccord expose.

Si c>alpha et c*b<=H, la fibre est complète. Dans ce cas la somme intérieure vaut log c pour b=1 et -Lambda(b) pour b>1. Pour b carré-libre composé elle vaut zéro. **Les fibres coupées ne sont pas remplacées par cette formule.** En particulier c<=alpha ou c*b>H ne sont pas des erreurs nulles.

Prenons B_cut=floor(N^(1/32)) et conservons seulement b<=B_cut dans R7. Cette coupe auxiliaire est distincte du B=ceil(L^20) fixé au §12.1 et ne modifie pas ce paramètre acquis. Tous les moduli retenus vérifient q<=B_cut^2*H<=N^(7/16). La queue b>B_cut est conservée séparément. Une troncature peut avoir une contribution non nulle sur un m non carré-libre ; sa queue la cancelle dans l'identité complète. On n'ajoute donc aucun masque mu(m)^2 à la troncature pour la rendre artificiellement favorable.

## 7. Deux paiements de queue indépendants et explicites

On a |w_{alpha,H}(b^2*c)|<=u*tau(b). Pour ce préfixe spécial X=N-1 et cette classe N modulo q, le nombre des m=qv est exactement au plus floor((N-2)/q)<=N/q. Ainsi

```
psi_N(X;q,N)<=N*u/q.
```

L'absence de +1 vient de ces **multiples positifs originaux** ; elle ne serait pas justifiée pour un intervalle arbitraire d'une AP. C'est le même principe de comptage que celui explicité au §12.7 pour une autre queue positive.

La borne sum_(b<=z)tau(b)<=z(1+log z) et Abel donnent

```
sum_(b>B_cut)tau(b)/b^2<=2(2+log B_cut)/B_cut.
```

En conservant toutes les sélections puis en les élargissant pour un majorant, la queue physique de R7 paie

```
E_phys(B_cut)<=2*N*u^2*(1+u)*(2+u)/B_cut.                      (R8)
```

Pour le principal AP X/phi(q), la même queue paie

```
E_main(B_cut)<=9*N*u*(1+u)*(2*u^2+7*u+8)/B_cut.                (R9)
```

En effet, phi(b^2*c)=b*phi(b)*phi(c), sum_(c<=H)1/phi(c)<=3(1+u), b/phi(b)<=3(1+log b), et Abel fournit

```
sum_(b>B_cut)tau(b)(1+log b)/b^2
 <=[2(log B_cut)^2+7log B_cut+8]/B_cut.
```

R8 concerne la vraie queue physique ; R9 concerne la queue du principal AP lors du passage vers le produit eulérien complet. Elles sont distinctes et ne sont pas échangées. Les constantes affichées sont conservatrices. Avec B_cut de taille N^(1/32), ces deux pertes sont des puissances de N gagnées, accompagnées de facteurs polynomiaux explicites en u.

## 8. Principal : tilt eulérien réellement estimable

La somme principale complète, avant la coupe b<=B_cut, est absolument convergente dans d. Pour chaque r,

```
sum_(d, gcd(d,rN)=1)mu(d)/phi(d^2)
          sum_(t|rad(r))mu(t)/phi(r*t)
= C_sf(rN)/r,
C_sf(K)=product_(p prime, p∤K)[1-1/(p(p-1))].
```

La séparation utilise phi(r*t)=t*phi(r), phi(d^2)=d*phi(d) sur le support carré-libre et sum_(t|rad(r))mu(t)/t=phi(r)/r. N pair retire le facteur p=2, donc C_sf est positif et au plus 1. Le principal complet de la tête vaut

```
J_head=X*sum_(alpha<r<=H) a_N(r)log r/r,
a_N(r)=mu(r)1_(gcd(r,N)=1)C_sf(rN).                    (R10)
```

Ce poids est multiplicatif, à une constante près. Si beta_p=[1-1/(p(p-1))]^(-1), alors

```
a_N=C_sf(N)*(h_N * mu_N),
mu_N(r)=mu(r)1_(gcd(r,N)=1),
h_N(p^j)=1-beta_p=-1/[p(p-1)-1]  (p∤N, j>=1),
h_N(p^j)=0                           (p|N, j>=1).
```

Ce tilt est quadratiquement petit ; les deux moments nécessaires sont uniformes :

```
sum_d |h_N(d)|/d <2,
sum_d |h_N(d)|/sqrt(d) <4.                            (R11)
```

Pour le premier, le log du produit est au plus sum_(j>=2)j^(-3)<=1/4. Pour le second, on majore les termes locaux par 3/(sqrt(p)*(p-1)^2) et la somme entière correspondante par 3[2^(-5/2)+(2/3)2^(-3/2)]<1.24, dont l'exponentielle est <4. Ces estimations ne créent pas une hypothèse de gain sur D_N.

Le préfixe principal masqué acquis au §12.7, calibré pour x>=N^(1/8), est

```
|M_N(x)|/x<=13u^2 exp(-sqrt(u)/96)+exp(-u/64).
```

Pour t>=alpha>=N^(1/4), la convolution R11 se sépare à sqrt(t). Son petit argument reste >=N^(1/8) et son reste utilise la borne triviale |M_N(x)|<=x. Cela donne

```
|sum_(r<=t)a_N(r)|/t <= eps_M(u),
eps_M(u)=26u^2 exp(-sqrt(u)/96)
          +2exp(-u/64)+4exp(-u/16).
```

Abel avec les deux endpoints alpha et H, et le poids log t/t, donne la marge sûre

```
|J_head|<=2*N*u^2*eps_M(u).                            (R12)
```

Il s'agit d'une estimation indépendante d'un coefficient arithmétique réel, pas du postulat que le principal serait petit. Les prémisses et le domaine des préfixes masqués acquis doivent être conservés. R12 ne paie pas le secteur r>H.

## 9. Erreur AP, BV pondéré et effectivité

Dans la coupe b<=B_cut, Q0=B_cut^2*H<=N^(7/16). Posons

```
E(q)=max_(x<=N,a unit mod q)|psi(x;q,a)-x/phi(q)|,
Delta_BV(N,Q0)=sum_(q<=Q0)E(q).
```

Il s'agit du vrai psi avec toutes ses puissances premières. Le masque Lambda_N retire au plus

```
sum_(p|N, p^j<=N)log p<=omega(N)*u<=u^2/log2
```

sur chaque modulus. Ce retrait unitaire est donc payé séparément ; les puissances propres à base première à N restent dans psi_N.

Comme q=b^2*c détermine b,c de manière unique sur les moduli cube-free, |w(q)|<=u*tau(q). La perte de la coupe sous AP vaut au plus

```
E_AP <= u*sum_(q<=Q0)tau(q)E(q)
        +(u^3/log2)*Q0*(1+u).                        (R13)
```

Cette pondération ne réclame pas une estimation inconnue pour des coefficients libres. Pour rendre son coût visible, choisissons L>0 et partageons tau(q)<=u^L ou >u^L. La borne AP élémentaire conserve son +1 ; avec q<=sqrt N et u>=1, elle donne E(q)<=8Nu/q. L'inégalité tau(q)^2<=d_4(q) fournit sum_(q<=Q0)tau(q)^2/q<=(1+log Q0)^4. Par conséquent

```
E_AP <= u^(L+1)*Delta_BV(N,Q0)
        +8*N*u^(2-L)*(1+u)^4
        +(u^3/log2)*Q0*(1+u).                        (R14)
```

La borne unweighted all-prefix BV utilisée dans le cadre au §8, autour de (36), est indépendante du moment de parité restant. Pour chaque A fixé, elle donne un C_A et un seuil N_A quand Q0<=sqrt N/(log N)^(B_A). Notre Q0 de taille N^(7/16) satisfait cette condition pour N assez grand. Avec L=A+8 et un exposant BV A+L+3=2A+11, R14 a alors une partie BV <=[C_(2A+11)+2^7]N/u^(A+2), plus son coût unitaire de puissance N^(7/16).

Le symbole C_(2A+11) désigne ici la constante du théorème classique indépendant ; elle n'a pas été évaluée pour ce nouveau raccord. Le seuil N_A non plus. **Il serait incorrect d'affirmer ce nouveau paiement de tête dès u=10^24 en réutilisant le seul onset de I**, ou d'importer le certificat primitif spécifique des poids w_B du §12.1 sans refaire ses substitutions. R14 reste un budget explicite en termes de l'observable indépendant Delta_BV ; la conséquence qualitative est justifiée par BV classique, mais sa calibration effective commune au ledger n'est pas obtenue dans ce rapport.

## 10. Gain de tête obtenu et obligation globale conservée

La combinaison précédente donne une estimation indépendante

```
|P_head_all|<=E_H,
E_H=2Nu^2 eps_M(u)+E_phys(B_cut)+E_main(B_cut)+E_AP.
|P_head^{>=2}|<=E_H+H*u^2.                            (R15)
```

Les frais de R8/R9 et la perte unitaire R13 sont des puissances de N ; R12 exploite le Mertens masqué réellement acquis ; R14 exploite un vrai BV indépendant. Pour chaque A fixé, on obtient qualitativement P_head_all=O_A(N/u^A), avec un seuil non évalué pour cette application. C'est un gain réel sur la tête physique alpha<r<=H, avec les vrais coefficients, plutôt que la compilation d'une identité standard présentée comme victoire.

Définissons le complément physique P_tail^{>=2} par r>H, avec les mêmes k, unités, faces et coefficients que R3. L'identité complète reste

```
D_N=P_head^{>=2}
       +[P_tail^{>=2}-M^{>=2}]
       +I+2max(e,0).                                (R16)
```

Le bracket de R16 n'est ni nul, ni payé par R15. Pour k=3 et 3∤N, par exemple, le physique long contient

```
sum_(r>H, 3r<=N-2, gcd(r,3N)=1)
                       mu(r)Lambda(N-3r)log r.
```

BV donne la distribution de Lambda dans des classes, pas sa distribution après multiplication par mu(r). Le préfixe acquis de mu(r)chi(r) à petit conducteur ne contient pas Lambda(N-3r). Sur la branche physique, le facteur natif chi(N-3r)conj(chi(N)) modulo 3 vaut constamment 1 ; il ne crée aucune oscillation supplémentaire. La racine d'un secteur HH développé ne peut pas non plus être estimée comme un coefficient libre puis rapportée au raw sans ses autres raccords.

La fermeture exige encore un budget signé indépendant de P_tail^{>=2}-M^{>=2} et de 2max(e,0), plus une calibration effective des frais de tête sur le domaine choisi. Les paiements globaux acquis de I, EJ ou Z_ref ne sont pas ajoutés plusieurs fois. Aucun poids de Chen ni une projection de parité déjà compilée n'est annoncé comme information nouvelle pour ce bracket.

## 11. Contrat numérique et décision Lean

À N=10^8, alpha=100, Q=999999 et H=1000. La valeur B_cut=floor(N^(1/32)) vaut 1 ; le paiement asymptotique de cette coupe n'est donc pas un petit budget numérique à cette échelle. Le banc de l'Agent 6 doit tester les identités, leurs faces et les cancellations, pas certifier R15 par quelques valeurs.

Le contrat transmis conserve : R1/R2 sur des têtes et des arguments isolés ; les facteurs répétés de la bascule ; la ligne P_1=M_1 ; R5 avec ses planchers et unités ; R7 point par point sur des m sélectionnés ; des fibres complètes et coupées ; la queue de la coupe b<=B_cut ; et le comptage positif n=N-qv. Les puissances premières du premier axe sont testées sans les filtrer par mu(n)^2. Le reçu indépendant devra indiquer sa portée et ne sera pas assimilé à une somme complète ni à un paiement analytique.

Le banc de l'Agent 6 signalé à root confirme notamment le témoin m=112211=11*101^2, n=99887789 premier. La tête complète au point m est zéro : le seul r carré-libre dans (100,1000] est 101, et son quotient k=1111 partage 101 avec r. La coupe B_cut=1 conserve pourtant le coefficient -log101, tandis que le terme de queue q=101^2 apporte +log101. Après multiplication par Lambda_N(n), ces deux poids non nuls se cancèlent. Ce témoin interdit de supprimer la queue au motif que le second axe complet est carré-libre. Le diagnostic r=303,k=63 montre également que l'exclusion gcd(d,r)=1 de R5 est indispensable. Ces résultats appartiennent au reçu numérique du rôle 6 ; leur rejeu indépendant demeure celui du Juge.

R7 et les identités de bascule sont falsifiables et doivent être rejetées avant Lean si leur raccord numérique est faux. Si elles passent, cela ne donne toujours pas une candidature gagnante : R16 conserve une contribution signée non estimée. Une formalisation de R1/R2 seule, une hypothèse de petite corrélation placée dans R16 ou un nouvel axiome analytique portant le gain souhaité serait une substitution au travail demandé.

La piste apporte un secteur estimable et clarifie le reste qui doit réellement compenser le physique et le modèle. Elle ne prouve pas la cible conditionnelle complète. La victoire reste fausse.
