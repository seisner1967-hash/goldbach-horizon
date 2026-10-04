# Boucle 6 — deux axes carrés-libres, vraies progressions HH

Agent 2, nœud Arbor 10, 2 octobre 2026. Sources anciennes et reçus conservés. Aucun fichier Lean écrit dans ce rôle.

**Résultat.** L'expansion à deux diviseurs carrés et le CRT sont exacts. Le twist isolé d'un caractère nonprincipal reste nonprincipal dans les cellules admissibles. Cependant la longueur pertinente est celle de la progression imposée par le premier H, et non la longueur brute de zeta. Dans la boîte équilibrée revue, PV ne donne pas de gain uniforme aux grands conducteurs. Un second twist sur le complément peut même rendre le caractère principal. Ce diagnostic ne constitue pas une impossibilité globale ni une victoire.

## 1. Contrat, paramètres et liberté réelle de y

Le nœud 10 exige tous les sélecteurs, les deux axes carrés-libres, les masques unitaires, les fronts stricts, la rugosité et les coefficients réels. L'identité ne doit pas supprimer le secteur zeta=1 ni remplacer le contrôle demandé par une hypothèse de corrélation. CONTRACT.md et l'arbre courant ont été relus.

La continuation fournie §1 fixe a=u v x, r=s t zeta, n=a b, m=r k=N-n, u,v,s,t>y. Elle autorise une sélection de termes développés, pas une annulation de H_y(a) après suppression de termes. Elle impose I_W(n), gcd(n,N)=1 et les détecteurs carrés-libres originaux.

Le seuil y n'est pas nécessairement alpha=N^(1/4). Les sources revues `sprint15/agents/weighted_hh_root_main_raw_prefixes.txt`, §1, utilisent y=N^z, z>0 fixé, indépendant du W presque-puissance. `hh_partition_orientation_sign_audit.txt`, §3, donne une famille y=N^(1/16), a,r~N^(3/4), b,k~N^(1/4). `rosser_almost_power_rough_reduction.txt`, §5, impose les écarts positifs

rho_m=1-max((1+t)/2+z,3/2-t+3z)>0,
rho_g=1-(39/20)(1-t+2z)>0.

La famille t=3/4,z=1/16 satisfait ces écarts. Aucun changement du profil quart alpha/Q n'est effectué ici.

Pour st~N^nu dans cette boîte, zeta~N^(.75-nu), nu>2z. Une longueur BRUTE supérieure à sqrt(N) n'existe que si nu<.25, donc si z<.125. Si y=N^(1/4), cette sous-zone est vide. La famille revue y=N^(1/16) permet une sous-zone brute longue, mais cela ne suffit pas à une longue progression vraie.

## 2. Gelage fidèle des deux H et fronts

Fixons b,u,v,k,s,t, conservons le signe mu(u)mu(v)mu(s)mu(t), et posons

A=b u v, C=k s t, x=(N-C zeta)/A.

La fibre exacte est A x+C zeta=N, x,zeta>0. On conserve également a=u v x, r=s t zeta, k<=Q, r>alpha, n,m carrés-libres, I_W(n), gcd(n,N)=1 et toutes les faces originales. Dès qu'une fibre originale est non nulle, A,C sont carrés-libres et gcd(A,C N)=1. En effet A|n, C|m, gcd(n,m)=gcd(n,N)=1. Si A ou C n'est pas carré-libre, la fibre sélectionnée est nulle.

Les fronts suivants sont exacts pour des caps entiers :

* r>alpha équivaut à zeta>=floor(alpha/(s t))+1 ;
* x>=1 impose zeta<=floor((N-A)/C) ;
* a<=m impose zeta>=ceil(N/[C(b+1)]) ;
* b<=m impose zeta>=ceil(b/C) ;
* a>U impose zeta<=floor((N-b(U+1))/C).

Une fenêtre dyadique, une autre face ou un cap est gardé littéralement dans theta(zeta). Les deux logarithmes valent log(b) log(s t zeta) sur le support W>=V_original. Le poids F(zeta) inclut ces logarithmes, theta, et toute donnée réelle restante. L'identité ci-dessous vaut pour un poids arbitraire ; une estimation par Abel exige de payer sa variation, qui n'est pas contrôlée par la seule condition |theta|<=1.

Le gelage alternatif a,s,t,k conserve H_y(a) complet. Sa congruence a|N-C zeta a pas a. Dans a~N^.75 et zeta de longueur X~N^(.75-nu), il contient au plus un zeta lorsque X<a. Aucune périodicité ne crée de cancellation dans une fibre à un point.

## 3. Identité exacte à deux carrés et CRT

Soit chi un caractère primitif nonprincipal de conducteur q|N, prolongé par zéro hors unités. Le symbole q désigne ici le conducteur, et ne remplace ni N ni le module CRT original a r. Définissons K=C N, P_W=produit des premiers <=W. Pour un intervalle fini J de zeta positifs tel que 0<N-C zeta, considérons la vraie composante tordue

T_chi = mu(C)^2 sum_(zeta in J, A|N-C zeta)
 F(zeta) chi(zeta) mu(zeta)^2 mu(N-C zeta)^2
 1_(gcd(zeta,K)=1) I_W(N-C zeta).                 (S1)

Le masque K provient exactement de mu(C zeta)^2=mu(C)^2 mu(zeta)^2 1_(zeta,C)=1 et de gcd(N-C zeta,N)=1 iff gcd(zeta,N)=1. Dans une fibre positive C<N, donc K<N^2 : il respecte le seuil de masque log K<=2 log N. Les acquis de la monographie §12.6 pour mu(n)chi(n) avec ce masque restent acquis ; S1 contient mu^2 et un complément mobile, donc n'est pas ce préfixe.

Développons simultanément

mu(zeta)^2=sum_(d^2|zeta)mu(d),
mu(n)^2=sum_(e^2|n)mu(e),
1_(zeta,K)=1=sum_(f|rad K,f|zeta)mu(f),
I_W(n)=sum_(ell|P_W,ell|n)mu(ell).                 (S2)

La somme est finie, avec d<=sqrt(max J), e<=sqrt(N), f|rad K et ell|P_W, ell<=N lorsque son terme est non nul. Pour les cellules non nulles, on peut conserver les conditions

gcd(d,A e K)=1, gcd(e,C N)=1,
gcd(ell,C N)=1, gcd(f,q)=1.                       (S3)

Pour supprimer d non premier à K, on conserve d'abord le masque exact de zeta puis on développe celui-ci. Pour supprimer e ou ell rencontrant N, la relation n=N-C zeta avec le twist et le masque exact impose n unité aux premiers de N. Les suppressions se justifient après regroupement de ces cellules, jamais en prenant les valeurs absolues avant les cancellations d'inclusion-exclusion. Une version sans ces suppressions est toujours donnée par S2 avec ses congruences générales ; les termes incompatibles y sont nuls ou se compensent exactement.

Dans les cellules admissibles S3, f et d sont premiers entre eux. Posons

M=lcm(A,e^2,ell), B=f d^2,
v0 ≡ N (C B)^(-1) mod M.

On a gcd(C B,M)=1 et gcd(M,q)=1. Les quatre conditions de divisibilité sont exactement

zeta=B(v0+M j), j entier,
zeta in J.                                            (S4)

Par conséquent S1 est la somme des coefficients mu(d)mu(e)mu(f)mu(ell), multipliés par mu(C)^2 chi(B), de

sum_(j: B(v0+M j) in J) F(B(v0+M j)) chi(v0+M j).       (S5)

IMPORTANT : e peut rencontrer A. Le module est lcm(A,e^2,ell), pas A e^2 ell. Les congruences n=0 mod A,e^2,ell ont le même second membre N pour C zeta et sont compatibles ; aucune coprimalité artificielle entre ces trois modules n'est ajoutée. La période en zeta est B M.

Pour gcd(M,q)=1, chi(v0+M j)=chi(M)chi(j+c), c ≡ v0 M^(-1) mod q. Sur q valeurs consécutives de j, sa somme est zéro. Le twist isolé reste donc nonprincipal. Si q ne divise pas N, ou si des unités sont supprimées, cette conclusion exige un nouvel audit : un M divisible par q peut rendre le twist constant. Ce cas est hors des hypothèses S1, et n'est pas silently compté comme nonprincipal.

## 4. Caractère réellement principal dans un produit de deux axes

S1 est une composante avec un twist ISOLÉ. Il faut identifier exactement le twist de toute projection spectrale avant d'y importer son estimation. Pour q|N et zeta unité, on a

chi(N-C zeta)=chi(-C)chi(zeta).

Donc

chi(N-C zeta) conj(chi(zeta))=chi(-C).                  (S6)

Le membre droit est constant, non nul sur les cellules admissibles. Deux twists compensateurs sur les deux axes peuvent donc annuler toute oscillation. Pour un caractère quadratique, chi(N-C zeta)chi(zeta) est également constant. L'affirmation « chacun des deux caractères est nonprincipal, donc leur produit l'est » est fausse dans l'objet additif à q|N. S6 est un falsificateur exact distinct d'un test de signe global HH.

Avec TOUS les facteurs du développé, la même identité prend la forme

chi(A)chi(x) conj(chi(C))conj(chi(zeta))
 =chi(n)conj(chi(m))=chi(-1).                          (S6b)

Il n'est pas permis de geler x, de le supprimer du caractère ou de traiter ce produit comme un twist isolé de zeta. S6b certifie le secteur compensateur précis ; déterminer si une expression spectrale donnée contient ce produit requiert encore l'audit de cette expression. Une autre projection ne lui est pas assimilée par défaut.

S1-S5 ne remplacent jamais automatiquement le moment spectral complet par chi(zeta). Il faut garder ses facteurs de caractères sur u,v,b,k,s,t,x et vérifier qu'aucun facteur dépendant de x n'annule l'oscillation restante. Les diagonales et le secteur principal résultant restent à payer.

## 5. Coût de la tête, de la rugosité et des poids

La périodicité donne B(q)<=q pour une somme non pondérée. La borne PV pour un caractère nonprincipal modulo q donne B(q)<<sqrt(q) log q, y compris composite ; après le changement affine unité, elle s'applique à S5. Source primaire : Montgomery–Vaughan, *Multiplicative Number Theory I*, théorème 9.18, p.307 du livre ; l'exercice 9.4.1 explicite le changement affine.

Pour le poids, écrire V_J(F)=sup_J|F|+variation_J(F), et payer le nombre réel de morceaux de J. Les logarithmes seuls coûtent O((1+log N)^2), puisque log zeta est monotone. Une sélection theta arbitraire peut coûter sa variation entière ; elle n'est pas gratuitement polylogarithmique.

Avec d<=D,e<=E et l'inclusion-exclusion EXACTE de la rugosité, la majoration de tête obtenue en sommant les cellules en valeur absolue est

|head| << V_J(F) B(q) D E 2^omega(K) 2^pi(W).          (S7)

On peut supprimer les termes incompatibles ou ceux contenant un premier de q, mais on ne peut pas ignorer ce coût. W est plus grand que toute puissance fixée de log N dans les profils presque-puissance revus. Le primorial ne constitue donc pas un masque de variation négligeable.

Une alternative légitime utilise deux poids de Rosser lambda^-<=I_W<=lambda^+, supports ell<L_sieve, |lambda_ell|<=1. Leur existence, leur ordre pointwise et l'erreur de densité epsilon(h)=exp[-h log h/2], h=log L_sieve/log(W+1), découlent des deux parités du lemme 8 et du théorème 7 de Motohashi. Cela remplace 2^pi(W) dans la tête par L_sieve, MAIS conserve un reste signé réellement contrôlé par un encadrement positif :

0<=lambda^+(n)-I_W(n)<=lambda^+(n)-lambda^-(n).

Sur n=N-C zeta, zeta dans un intervalle de longueur X, après suppression POSITIVE des autres sélecteurs, chaque ell admissible a au plus une classe ; les premiers p|C sont inactifs car gcd(C,N)=1. La masse de cet écart est

O(X V_C(W) epsilon(h)+L_sieve),
V_C(W)=prod_(p<=W,p∤C)(1-1/p).                         (S8)

Le terme L_sieve paie les erreurs de plancher ; il n'est pas absorbé dans la densité. Un poids borné multiplie S8 par sa norme, et un enveloppement divisoriel doit encore payer son moment. S8 ne prétend pas que la seule densité d'un crible supérieur contrôle un reste tordu. Les deux poids sont nécessaires. Source primaire : Motohashi, *Lectures on Sieve Methods and Prime Number Theory*, lemme 8 p.44, théorème 7 et sa preuve pp.46–48, (2.2.4)–(2.2.5).

L'identité S2 reste l'objet exact, S7 la majoration brute, S8 une substitution possible avec sa charge. Aucun résultat analytique déjà acquis sur les masques petits conducteurs n'est recompté comme nouveau théorème.

## 6. Queues carrées et tous les +1

Posons Z=max J, X=longueur de J, L0=1+X/A, et T_N=max_(n<=N)tau(n). Le support A et C carrés-libres est celui de la fibre originale. Pour a_D(zeta)=sum_(d<=D,d^2|zeta)mu(d), b_E(n)=sum_(e<=E,e^2|n)mu(e),

mu^2(zeta)mu^2(n)-a_D(zeta)b_E(n)
 =(mu^2(zeta)-a_D(zeta))mu^2(n)
    +a_D(zeta)(mu^2(n)-b_E(n)).                        (S9)

Ainsi une queue n'est pas seulement un indicateur de grand carré : le second terme paie |a_D|<=tau(zeta)<=T_N. Sur la progression vraie, d est premier à A, et le comptage d^2|zeta donne

T_d <= c X/(A D)+floor(sqrt Z).                        (S10)

Le +1 de chaque progression a bien produit floor(sqrt Z). Pour e carré-libre, h=gcd(e,A), e^2|A x impose e^2/h|x. La congruence en x a pas C, premier à e. Le nombre est au plus c L0 h/e^2+1. L'identité gcd(e,A)=sum_(h|e,h|A)phi(h), suivie de la queue de sum j^-2, donne

T_e <= c L0 tau(A)/E+floor(sqrt N).                    (S11)

Chaque +1 a encore été payé. Le regroupement des diviseurs de A, plutôt qu'une coprimalité fausse de A,e, explique tau(A). On peut utiliser à la place les bornes sûres plus faibles c X/D+sqrt Z et c X/E+sqrt N si l'on abandonne positivement A.

La différence entre S1 et sa tête deux carrés, sur les autres sélecteurs encore exacts, est donc au plus

sup|F| [T_d+T_N T_e].                                 (S12)

Les maillages d'une substitution de Rosser augmentent ses enveloppes ; les queues originales doivent être payées avant cette inflation ou avec les nouveaux moments. Une queue globale de la campagne antérieure ne peut pas être copiée comme borne par fibre.

La formule optimiste B D E+X/D+X/E+sqrt N donne D=E~(X/B)^(1/3) et B^(1/3)X^(2/3)+sqrt N seulement si X/B>=1, et avant les masques et multiplicité. Pour une vraie progression, substituer L0 à X dans ses termes principaux ne supprime ni sqrt Z, ni sqrt N, ni tau(A), ni T_N. Le critère de gain uniforme est une longueur EFFECTIVE supérieure à B, pas une longueur brute supérieure à sqrt N.

## 7. Audit quantitatif complet de la boîte équilibrée

Développons aussi le premier H. Dans b,k~N^.25, uv~N^sigma, st~N^nu, sigma,nu>2z,

A~N^(.25+sigma), C~N^(.25+nu),
X_zeta~N^(.75-nu),
L_fibre~N/(A C)=N^(.5-sigma-nu).                       (S13)

Une fenêtre plus courte diminue L_fibre. Le nombre brut des sextuples b,u,v,k,s,t de cette boîte est N^(.5+sigma+nu) à facteurs logarithmiques près. Nombre de fibres fois longueur effective est donc de l'ordre N. La conservation des quatre vrais signes est exactement ce qui impose A et cette longueur.

Pour q~N, PV coûte N^.5 log N, supérieur à L_fibre. L'optimum hypothétique D=E~(L_fibre/B)^(1/3) serait une puissance N NEGATIVE ; il n'est pas un choix permis de coupure. Le minimum trivial/périodique donne seulement L_fibre avant poids. Après somme extérieure absolue, on retrouve N avec ses logarithmes, sans réserve N/(256 log N loglog N).

Même en ignorant frauduleusement la progression A mais en payant ensuite tous les paramètres, le calcul optimiste avec X_zeta et B=N^.5 donne

N^(.5+sigma+nu) * N^(1/6+(2/3)(.75-nu))
 =N^(7/6+sigma+nu/3),                                (S14)

déjà supérieur à N, avant masques, poids et termes sqrt N. Ceux-ci coûtent à eux seuls N^(1+sigma+nu) dans ce gelage absolu. S14 est le coût d'une majoration, pas une borne inférieure sur le vrai signé.

Le théorème de Burgess lu dans la même source primaire (Montgomery–Vaughan, th.9.27, p.315) concerne un conducteur premier p. Il donne, pour l'entier j>=1, une taille L^(1-1/j) p^((j+1)/(4j^2)) fois logarithmes. Dans la boîte revue y=N^(1/16), sigma,nu>1/8, donc L_fibre<N^.25. Aux conducteurs p~N, aucun j ne donne un gain relatif par ce théorème. Il ne faut pas importer son énoncé premier à tous les conducteurs composites. Pour y bien plus petit, certaines sous-boîtes ont L_fibre>N^.25 et pourraient relever d'une borne de caractère court après paiement des masques ; cela ne prouve ni le support complet, ni le gain global, ni le secteur principal S6. Aucune impossibilité universelle à ces paramètres n'est revendiquée.

Les petits q, avec log K<=2 log N, sont distincts : S5 peut effectivement bénéficier de la périodicité ou PV quand sa vraie longueur est polynomiale. Mais les phases compensatrices, les queues et le regroupement extérieur restent à payer. Le contrôle de petits conducteurs déjà acquis pour mu chi n'est pas déclaré à nouveau prouvé. Le reste des grands conducteurs n'est pas couvert par ce seul secteur.

Un traitement conjoint x,zeta ne crée pas une seconde dimension libre : Ax+C zeta=N fixe une droite et une unique progression. Changer le paramètre ne change pas son nombre de points. Sommer plusieurs A,C avant les valeurs absolues pourrait produire une information différente, mais réclame une estimation signée avec mu(u)mu(v)mu(s)mu(t) et les classes CRT réelles. Aucun théorème indépendant couvrant ces coefficients et toutes ces cellules n'a été dérivé ici. Le poser comme nouvelle hypothèse serait réintroduire le moment manquant.

## 8. Secteur zeta=1, filtre transmis et verdict

Zeta=1 satisfait les deux expansions avec d=1 et conserve toute la condition mu(N-C)^2, I_W(N-C), A|N-C, k<=Q, st>alpha et les faces originales. L'identité ne le retire pas. La continuation fournit pour zeta<=Z une amplitude O(N L^(3+o(1))) à Z polylogarithmique ; elle indique expressément que la somme signée agrégée et le budget terminal restent ouverts. Cette amplitude ne fournit pas la marge demandée. Les secteurs courts et les grands conducteurs restent donc de vraies obligations.

Formules S1–S6 et fronts transmis à l'Agent 6 avant toute formalisation. Banc imposé N=100000000, chi5 induite (période unité effective 10), avec tous les masques :

1. Comparer directement les coefficients du double carré à l'expansion CRT, y compris e partageant A.
2. Garder le développé A=buv, C=kst et ses quatre signes, les unités et les caps stricts.
3. Vérifier que la progression conserve son pas A avant les carrés, et que sa longueur est X/A, pas X.
4. Vérifier la somme périodique nulle du twist isolé dans une cellule M premier à 5.
5. Vérifier le produit principal exact S6, sans le créditer comme oscillation.
6. Retenir zeta=1 et les cellules incompatibles avec les unités ; ne pas transformer l'exemple numérique y=2 en une famille asymptotique de secteurs longs.

Statut : identité arithmétique exacte et obstruction quantitative au transfert PV sur la longueur brute. Aucun contrôle du signé HH complet ni de D_N, aucune victoire. Le candidat de gain uniforme par cette longueur est rejeté avant Lean. Une formalisation éventuelle de S4/S6 certifierait seulement ces faits partiels.

Liens primaires :

* [Montgomery–Vaughan, caractères et sommes de Gauss, th.9.18 et 9.27](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/13.0_pp_282_325_Primitive_characters_and_Gauss_sums.pdf)
* [Motohashi, lemme de Rosser et lemme fondamental](https://www.math.utoledo.edu/~codenth/Spring_13/3200/NT-books/Lectures_on_Sieve_Methods_and_Prime_Number_Theory-Motohashi.pdf)
