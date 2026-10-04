# FINAL2 — switch hyperbolique conjoint de toute la famille non-SS

La contribution nouvelle est une **réduction arithmétique couvrant tous les rangs** des deux ressources composites, avec un choix canonique entre leurs facteurs terminaux et leurs cofacteurs. Elle donne deux sommes à coefficients réels et un conducteur équilibré ; elle conserve exactement la partie au-delà de sqrt(N). Une borne écrite supplémentaire traite la couche nouvelle de ressources de rang 3 à conducteur court. La réduction et cette borne locale ne paient ni le reste long, ni T_A, ni Gamma entière. `score = 0`, `victory = false` ; aucun Lean ni producteur numérique n'a été exécuté par ce rôle.

Ownership : ce rapport et `round19/role2/**`. Les 1361 archives, les huit modules18, leurs oleans et l'arbre sont readonly. Les lectures effectuées sont PROBE19, feedback18, FINAL2/4_18, contenu/Juge18, FINAL2_15 et FINAL2_17, puis une vue fraîche des contraintes (33 findings, 5 directions pruned, maxdepth2). Le premier affichage constraints a échoué à l'encodage cp1252 ; le même appel readonly avec `-B -X utf8` a ensuite réellement affiché les contraintes, exit0. Ce n'est pas un échec Lean ou mathématique. Deux recherches de noms historiques de rapports inexistants ont été corrigées par `rg --files`, sans exécuter de programme historique.

## Probe et choix du mécanisme

Q1 First principles : **mauvaise représentation du reste et mauvais crédit de capacité**. La clôture18 laisse 634 demandes S hors SS, alors que les 40 SS ne sont qu'une sélection ; FINAL4_18 conserve 54 kernels actifs, 14 axes m0 exactement nuls et seulement 2 ancres déjà existantes. Le retour15 distinguait 400 labels premiers de 360 vertices physiques. Ces deux éléments empêchent de remplacer le reste par une famille de quatre formes avec quotient arbitrairement premier, ou de compter un réciproque pour chaque e.

Q2 Hidden assumption : « le petit témoin est la seule variable dans laquelle un changement de coordonnées est utile ». En la retirant, chaque ressource peut être écrite **cofacteur entier × plus grand premier effectif**, quelle que soit sa multiplicité. Le couple de ressources possède alors deux orientations possibles ; la primalité se déplace avec les facteurs, elle ne disparaît pas.

Q3 Elephant : l'orientation la plus courte a encore un conducteur pouvant dépasser sqrt(N). Dans le canal retourné, les deux formes divisées valent des cofacteurs composites ; les deux primalités terminales sont des poids sur les paramètres. Un +1 par toutes les cellules possibles, ou un BV de Lambda seule, ne paie pas cette famille. Les signes du réciproque de rang 3 sont même défavorables au principal source.

Q4 Hamming : **oui pour une réduction quantitative exploitable, non pour une victoire actuelle**. Elle couvre S privé de SS sans supposer une disponibilité et sépare une nouvelle couche à rang 3 dont le coût total peut être calculé. L'estimation bilinéaire signée des canaux medium/long et la consommation physique restent réellement ouvertes.

Les quatre mouvements sont appliqués. Inversion : abandonner le témoin minimal comme unique variable, garder le facteur terminal et le cofacteur complet. Raisonnement depuis la réussite : exiger une partition sur toutes les ressources, le vrai conducteur et les prix avant de demander une estimation. Transfert analogique : décomposition hyperbolique à deux canaux, avec coordonnées diophantiennes et rang multiset plutôt qu'une capacité de graphe. Rétro-ingénierie : les 634 axes hors SS imposent de garder les rangs >=3 ; les 14 m0 nuls imposent de suivre les axes raw ; les labels15 imposent une bijection sur les vertices.

Rejets conceptuels, sans faux logs de compilateur :

- Retirer deux petits facteurs et déclarer le quotient premier partout : faux pour le rang >=4 ; ce n'est pas une extension admissible de SS.
- Fixer tous les cofacteurs et oublier le +1 : leur produit peut dépasser N ; le nombre de cellules remplace alors abusivement le nombre d'incidences.
- Utiliser un poids Richert négatif sur les hauts rangs pour majorer la demande positive : une demande positive indépendante du rang de la ressource ne devient pas <= un poids négatif. Il faudrait garder un prix de correction, actuellement non payé.
- Annoncer que `min(h1*h0,r1*r0)<N` donne le niveau BV : faux ; la partie entre sqrt(N) et N est explicitement retenue ci-dessous.

Déclaration du survivant : hypothèse attaquée = représentation irréversible par le petit témoin ; classe = switch arithmétique conjoint et partition hyperbolique ; chaîne = déplacer les véritables primalités avec le facteur choisi évite de perdre les ressources à quotient composite, observable par une bijection complète et un coût de couche de rang 3 ; orthogonalité = aucun nouveau mode chi ou nouveau Gram/calibrage du rôle1, aucune nouvelle optimisation SS ; conflits = aucune couverture par log supposée gagner 1/u, aucun transport positif/Hall, aucune substitution theta/raw ou disparition du prix long. Le candidat n'est pas un réglage d'un seul nombre : le changement essentiel est le second canal et son support réel.

Mechanism: Switch hyperbolique conjoint sur le plus grand facteur premier réel de chaque ressource, avec deux canaux de conducteur équilibré, rang multiset et union physique exacte.
Hypothesis: Le canal retourné garde la primalité sur ses paramètres et couvre les ressources à quotient composite ; une couche nouvelle de rang3 à conducteur court possède un coût indépendant, tandis que les canaux au-delà de sqrt(N), leurs prix et le déficit global restent à estimer.
Observable: Sur la nouvelle fenêtre entière q1600100..1601100 à N=10^8, vérifier la bijection tagged(a,b,t), tous les rangs et facteurs répétés, les conducteurs courts/medium/long, le vrai bracket et les réciproques physiques uniques ; aucune densité ni signe n'est fixé avant calcul.
Conflicts: Les identités/log-coverage, racines et poids18 ne sont pas redérivés comme gain ; gcd, primalités déplacées, CRT+1, rawproperpowers, prix longs et signes de rang sont conservés, sans disponibilité ni borne cible ajoutée en prémisse.

## Domaine, vrais objets et coefficient conservé

Conserver N pair positif, u=logN, ell=logu, alpha=ceil(N^(1/4)), Q=floor((N-1)/alpha), a=ceil(N^(7/16)), M=ceil(N^(3/4)), Z=floor(N^(1/4)), et p0 canonique, premier impair minimal ne divisant pas N. Le source reste u>=10^24. A7, le vrai S(N), U4, whole U_a et le ledger acquis ne sont pas remis en cause.

Le support des demandes étudiées est celui de17/18 : q premier unitaire, q>=M ; e carré libre unitaire, p0<e, eq<=N-Q-1 ; n_e=N-eq premier. e<=E=floor((N-Q-1)/M)<=N^(1/4)<a, q>a et q>e. Le coefficient réel acquis est

    C(eq) = Lambda(e) - mu(e) W_a(n_e,eq),
    b(e,q) = log(n_e) C(eq),
    t(e,q) = max(b(e,q),0).

Dans les identités avant masque premier, employer plutôt la définition universelle `-mu(eq)*(D_a(n_e,eq)-W_a(n_e,eq))`, qui est réelle même si q n'est pas premier. Les termes de F1 ne sont substitués que lorsque l'indicatrice de q vaut 1. Les unités `(k,n_e*N)=1`, original Q, k1, `a*k<eq` et tous les diviseurs restent dans les kernels. Le mask raw sur n_e conserve les puissances propres, sans mu(n_e)^2.

Les ressources sont n1=N-q et n0=N-p0*q. Dans les cellules sans incidence e1/p0, elles sont composites >=2. S impose qu'au moins une a un facteur premier <=Z ; SS18 sélectionne les deux ressources semipremières avec leur témoin <=Z et un quotient effectivement premier plus grand. Le nouveau domaine est **exactement S privé de SS**, et non une nouvelle définition de S. Pour construire les coordonnées indépendamment des deux incidences premières, on peut parcourir tous les q unitaires satisfaisant les fronts et appliquer I(q) et theta/raw(n_e) uniquement dans la mesure finale. On nomme alors « cellule structurelle non-SS » la condition sur les ressources avant le masque de n_e ; après ce masque, elle restitue exactement les demandes non-SS initiales. Les conditions de factorisation des ressources sont arithmétiques et gardent leur complément.

## Extraction terminale complète, multiplicité et gcd

Pour chaque entier n>=2, définir r(n) comme le maximum du véritable multiset de ses facteurs premiers, puis h(n)=n/r(n). Alors

    r(n) est premier, n=h(n)*r(n), P+(h(n))<=r(n),
    Omega(n)=Omega(h(n))+1,
    n composite <=> h(n)>=2.

P+(1)=1 et Omega(1)=0. Les facteurs répétés sont comptés avec multiplicité. Il est **interdit** d'ajouter gcd(h(n),r(n))=1 : pour p^3, h=p^2 et r=p. Le couple (h,r) est néanmoins unique, car r est une valeur maximale déterminée, même si elle apparaît plusieurs fois. C'est une extraction terminale sur tous les rangs, pas la sélection semipremière minFac18.

Poser h1=h(n1), r1=r(n1), h0=h(n0), r0=r(n0). Les deux relations sont

    h1*r1+q=N, h0*r0+p0*q=N,
    p0*h1*r1-h0*r0=(p0-1)*N.                     (H1)

La coprimalité p0 avec n0 est dérivée de n0 congru à N modulo p0 et `(p0,N)=1` ; elle donne `(p0,h0*r0)=1`, et donc la coprimalité avec h0 et r0 séparément. Elle ne donne pas `(p0,h1)=1`.

Avec un anchor impair libre, `(n1,n0)` peut être non trivial : il divise p0-1, car `(q,N)=1` donne `(q,n1)=1` et `n0-p0*n1=-(p0-1)N`, ou encore `n1-n0=(p0-1)q`. Cette possibilité n'est pas effacée dans la preuve générale. **Pour le p0 canonique fixé**, tout premier divisant ce gcd est <p0. Le premier 2 divise N ; tout premier impair <p0 divise N par minimalité. Mais n1,n0 sont unitaires à N. Le gcd est donc 1. La conclusion `(n1,n0)=1` ne requiert pas que les quotients soient premiers : elle vaut avant la sélection SS et est un raccord à généraliser explicitement depuis le noyau18.

Il s'ensuit que tous les gcd croisés entre un facteur de n1 et un facteur de n0 valent 1. Cela ne force jamais la coprimalité des deux facteurs **dans la même ressource**. Les versions générales avec anchor non canonique doivent garder g=gcd(a,b), g|p0-1 et le conducteur réduit a*b/g ; elles ne sont pas remplacées par la version g=1 sans la preuve précédente.

## Deux canaux et vraie bijection diophantienne

Choisir une seule orientation :

    D : h1*h0 <= r1*r0 ; (a1,b0,x,y)=(h1,h0,r1,r0).
    P : h1*h0 >  r1*r0 ; (a1,b0,x,y)=(r1,r0,h1,h0).

Le symbole a1 est un nouveau paramètre entier ; il ne remplace pas le front a fixé. L'égalité va uniquement dans D. Dans les deux canaux

    p0*a1*x-b0*y=(p0-1)*N, q=N-a1*x,
    C_bal=a1*b0=min(h1*h0,r1*r0),
    C_bal^2 <= n1*n0 < N^2, donc C_bal<N.          (H2)

`C_bal<N` est une borne de conducteur, **pas** un gain analytique et **pas** `C_bal<=sqrt(N)`. a1,b0 ne sont pas présumés premiers dans D. Dans P ils sont les deux premiers terminaux réels, mais x,y sont des cofacteurs entiers arbitraires >=2.

Sous le p0 canonique, `(p0*a1,b0)=1`. Soit x0 le représentant 0<=x0<b0 de

    p0*a1*x0 congru à (p0-1)*N modulo b0.

Définir l'entier signé y0=(p0*a1*x0-(p0-1)*N)/b0. Alors toutes les solutions sont, avec t entier,

    x=x0+b0*t, y=y0+p0*a1*t,
    q=N-a1*x0-a1*b0*t.                            (H3)

y0 peut être négatif ; une soustraction naturelle tronquée serait incorrecte. Les conditions x,y>=1, q>=M, eq<=N-Q-1 et les conditions d'extraction déterminent l'intervalle entier de t et ses sous-sélecteurs. Sa longueur avant les conditions de facteurs est au plus N/(e*C_bal)+1, avec le +1 conservé. Les fronts peuvent rendre l'intervalle vide.

Dans D, le sélecteur exige x,y premiers, P+(a1)<=x, P+(b0)<=y, a1,b0>=2, et a1*b0<=x*y. Dans P, il exige a1,b0 premiers, P+(x)<=a1, P+(y)<=b0, x,y>=2, et x*y>a1*b0. Dans les deux cas on reconstruit n1=a1*x, n0=b0*y, puis le vrai q par H3 et le vrai e par le label du cœur. Les conditions S privé de SS, les unités et tous les fronts sont reportés exactement. Il ne suffit pas de vérifier la seule équation H1.

Ces constructions sont inverses : le facteur terminal maximal restitue le couple unique ; H2 restitue le tag unique ; x modulo b0 restitue x0 et t. Pour une somme sur les m=eq où q>=M est premier, q est l'unique facteur >=M puisque M^2>N, donc (e,q) restitue également le vertex physique. Cette unicité est le mécanisme anti-double-comptage ; elle ne constitue pas une assignation de capacités.

Ainsi la somme réelle non-SS, avec son masque theta, est exactement

    B_nonSS = sum_D K_D(e,a1,b0,t) I(q) theta_N(n_e)
            + sum_P K_P(e,a1,b0,t) I(q) theta_N(n_e),       (H4)

où K_D/K_P sont la définition universelle réelle C(eq) multipliée par le sélecteur arithmétique décrit ci-dessus. Ce ne sont ni des coefficients adversariaux libres, ni des capacités. La version raw remplace uniquement theta_N(n_e) par rawLambda_N(n_e). Leur différence est un poste properpower sélectionné, conservé dans B_pp^a et jamais ajouté deux fois au ledger.

Dans D, les deux primalités x,y sont des contraintes de la variable ; dans P, les primalités a1,b0 sont sur les paramètres. Une présentation avec quatre formes divisées toutes premières dans P serait fausse. La somme P garde littéralement ces deux masques sur les paramètres et les gardes P+(x),P+(y). Il n'y a aucune division par une densité ni aucun transfert gratuit des poids18.

## Prix des conducteurs medium et long

Prendre B=floor(N^(1/8)) comme seuil analytique auxiliaire ; il ne modifie ni alpha, a, Q, Z ou M. La partition disjointe de H4 est

    C_bal<=B ; B<C_bal<=sqrt(N) ; sqrt(N)<C_bal<N.   (H5)

La troisième famille existe arithmétiquement et n'est pas supprimée par H2. La longueur N/(e*C_bal)+1 reste la vraie longueur de chaque cellule ; lorsque C_bal>N/e, une cellule peut porter au plus un entier, sans que la somme des +1 sur tous les paramètres soit petite. Les tuples actifs sont certes en bijection avec les q, ce qui interdit une surmultiplicité artificielle, mais borner leur nombre par tous les q perd les primalités et reste trop cher.

Le **prix long littéral** est la dernière somme de H4 restreinte à `C_bal^2>N`. Son vrai W, ses deux signes mu(e), Lambda(e), les deux incidences, facteurs répétés, P+(cofacteur), paramètres premiers du canal P et le +1 sont conservés. Le prix medium est défini de la même façon. Ce sont des sommes à estimer, et non des hypothèses « prix petit » utilisées dans un Lean. Même le domaine medium ne relève pas automatiquement de BV : le q premier pondère l'incidence N-eq première, et les quotients/paramètres restent couplés.

Le fallback acquis C7, obtenu en oubliant toutes les ressources dans un upper sieve des deux formes, reste de type `98304 N ell^2 + N^(3/4)u^7` sur S entier. Il ne paie pas ces prix. Une borne encore plus grossière en sommant l'enveloppe `u[Lambda(e)+4ell]` sur tous les q est `3 N u^2 ell` ; ce constat montre précisément pourquoi une couverture entière n'est pas un gain.

L'estimation indépendante à rechercher est une **dispersion bilinéaire avec les poids fixes du canal retourné**, sur l'équation `p0*a1*x-b0*y=(p0-1)N`, les domaines dyadiques de a1,b0 et les restrictions P+(x)<=a1/P+(y)<=b0, sous les deux incidences q et N-eq et le coefficient réel C(eq). Elle doit être obtenue sur les sommes pondérées en x,y/paramètres, y compris `a1*b0>sqrt(N)`, et conserver les modèles locaux, non-unités et prix de calibration avant la somme en e. Un niveau sur Lambda(q) seul, un caractère fixé, ou une borne « H4<=cible » ne serait pas cette information. Aucun théorème disponible applicable à ces coefficients et à l'onset fixé n'est établi ici. C'est une obligation analytique identifiée, pas une prémisse de victoire.

## Une couche nouvelle réellement quantitative : rang 3 et conducteur court

La sous-famille T_3short impose aux deux ressources 2<=Omega(n_j)<=3, au moins une Omega=3, et h1*h0<=B. Elle est dans S privé de SS : les ressources sont composites, les facteurs des h_j sont <=B<Z, et au moins une n'est pas semipremière. Toutes les multiplicités, en particulier h_j=p^2, restent. Au source n_j>=M et h_j<=B donnent r_j>=M/B>=N^(5/8). Par ailleurs h1*h0<=N^(1/8)<r1*r0, donc cette couche est uniquement dans D. Les quatre entiers q,n_e,r1,r0 sont réellement premiers et dépassent le niveau T=floor(N^(1/8)).

Fixer h1,h0 entiers copremiers, et L=h1*h0. La progression réelle q=A+L*v satisfait q congru à N modulo h1 et p0*q congru à N modulo h0. Les quatre valeurs sont q, N-eq, (N-q)/h1, (N-p0*q)/h0. Les divisions sont entières ; les constantes sont prises dans Z avant les calculs modulaires. Le produit des pentes et déterminants a l'absolu

    Delta_h=N^6*e*p0*L^6*(e-1)*(e-p0)*(p0-1).      (H6)

Ce polynôme est distinct de celui18 aux témoins premiers ; il ne lui hérite pas gratuitement de rho. La preuve écrite de primitivité conserve pour tout p|h1 l'exclusion e!=1 mod p, et pour tout p|h0 l'exclusion e!=p0 mod p, dérivées de n_e premier plus grand que p. Au premier p|L, une seule des deux formes quotient a une pente unitaire ; l'autre quotient est une constante non nulle, parce que p>=p0, p ne divise pas p0-1 et `(p0,h0)=1`. q et n_e sont constants non nuls. Ainsi rho(p)=1 pour p|L même si p^2|L. Hors Delta_h, les déterminants donnent quatre racines distinctes ; ailleurs 1<=rho<=min(4,p), sauf saturation/cellule vide. C'est un raccord conditionnel à vérifier, **pas** un nouveau acquis Lean prétendu. L'identité H4 n'a pas besoin de ce raccord pour couvrir la couche longue.

Au source les mêmes inputs analytiques indépendants que18, les gardes de non-saturation et le calcul du nouveau polynôme donneraient, par l'argument Selberg déjà acquis,

    G_h(T)>=u^4/(K_3*ell^3), K_3=54*1024^4=59373627899904.

En effet logT>=u/16, Y=floor(T^(1/32)) donne logY>=u/1024, et le prix en totient est <=3ell. L'ancien bound écrit p0<u^3, e<=N^(1/4), L<=N^(1/8) donne Delta_h<=N^8 au source ; Mertens/totient, les floors et prime-log restent des inputs à formaliser comme18. Le cardinal par cellule garde

    K_3*ell^3*N/(e*h1*h0*u^4) + 1 + N^(1/4)*u^11.  (H7)

Le 1 est extérieur ; les autres CRT+1 sont dans le reste Selberg entier. Aucune capacité ne sert à H7.

Le **nouveau budget de rang multiset** est explicite. Sur les premiers P<=B, poser S_1=sum(1/p) et S_2=sum(1/p^2). La somme sur tous les cofacteurs ayant Omega=1 ou 2 et ces facteurs est exactement

    H_2=S_1+(S_1^2+S_2)/2.                         (H8)

Les produits de deux premiers distincts sont comptés une seule fois et les p^2 sont gardés avec coefficient 1/p^2. Remplacer H8 par `S_1+S_1^2/2` effacerait les puissances. Les restrictions h<=B et h1*h0<=B diminuent cette somme positive. La borne écrite D9_18 donne S_1<=2ell ; S_2<=sum_(n>=2)1/n^2<1, donc H_2<=3ell^2 pour ell>=3. L'enveloppe pondérée des e garde `sum_e u[Lambda(e)+4ell]/e<=3u^2 ell`.

Le premier terme de H7, sommé sur tous les e et cofacteurs, est donc au plus `27 K_3 N ell^8/u^2`. Pour les deux restes, le nombre entier de paires (h1,h0) avec produit <=B est <=B(1+logB). Avec E<=N^(1/4), poids <=u^2 et le +1 conservé, leur coût entier est <=`2 N^(5/8)u^14`. Par écrit,

    T_3short <= 27 K_3 N ell^8/u^2 + 2 N^(5/8)u^14. (H9)

C'est une borne nouvelle sur une couche non-SS à rang 3, avec tous paramètres et facteurs répétés. Elle n'est pas seulement SS avec un nouveau niveau. Elle reste conditionnelle aux raccords analytiques identifiés et ne paie pas les autres rangs/conducteurs.

Pour illustrer honnêtement son onset conservateur, au point initial u0=10^40 on a ell0<93, puis ell^9/u décroît pour u>=u0. L'inégalité entière `8192*27*K_3*93^9 < 10^40/4` et le coût exponentiel `16384*exp(-3u/8)*u^15*ell<1/4` donnent T_3short<=N/(8192u ell) après ces raccords. Le second coût peut être borné avec le terme d'ordre64 de l'exponentielle et `64!<=64^64`, sans flottant. **Cette borne ne remplace pas le source u>=10^24** : le segment intermédiaire et la somme longue restent impayés. H9 n'est pas proclamée Lean ni Win.

## Signes des réciproques : la couche triprime n'est pas une capacité

Le seul réciproque ayant un premier axe réel est m1=N-q, dont le complément est q. m0=N-p0*q a pour complément p0*q ; theta et raw Lambda y sont exactement nuls, quel que soit le rang de m0. Il reçoit zéro capacité.

Sur la couche courte, h1<a<r1 et le préfixe court entier de m1 est Div(h1). Le coefficient réel de m1 est donc `Lambda(h1)-mu(h1)*W_a(q,m1)` lorsque la factorisation est squarefree, avec l'annulation source générale si m1 n'est pas squarefree. Pour un h1=p*s à deux premiers distincts, Lambda(h1)=0 et mu(h1)=+1 : C(m1)=-W, donc son principal U4 est **+S(N)**. Un réciproque triprime n'est pas une nouvelle capacité favorable. Pour h1=p^2, mu(m1)=0 et le coefficient est exactement zéro. Le cas h1 premier garde log(h1)+W comme18, et une ancre p0 déjà existante reste consommée une seule fois.

Tous les e d'un q partagent m1 ; un m1 qui est aussi une demande dans une autre fibre doit être fusionné avant tout paiement. H4 et H9 n'en soustraient aucun crédit. Les vertices des deux canaux sont des coordonnées, pas deux ressources distinctes. Il reste à contrôler le déficit des incidences présentes T_A et la totalité de la comparaison pondérée.

## Théorèmes Lean concrets proposés, aucun fichier Lean lancé

La première cible de formalisation est **la bijection arithmétique nouvelle H1–H4**, pas un nouveau calcul de racines18 :

1. `largestPrimeExtraction_unique` : pour n>=2, le maximum effectif de `Nat.primeFactorsList n` est premier, divise n, restitue n=h*r et Omega(n)=Omega(h)+1 ; unicité sous r premier, n=h*r et tout facteur de h<=r. Les multiset et p^k restent effectifs.
2. `resource_common_divisor_dvd_anchor_sub_one` puis `canonical_resources_coprime` : garder d|p0-1 dans le cas général et dériver gcd1 uniquement avec le premier manquant canonique et les unités, sans utiliser la primalité des quotients SS. `anchor_coprime_resource0` est séparé.
3. `balancedResourceEquiv` : construire une équivalence entre le subtype des vrais points S privé de SS et le subtype **taggé** des tuples entiers (e,a1,b0,t) H3 portant les deux sélecteurs complets D/P. Les fonctions inverses reconstructives et tous les caps font partie du théorème, pas d'un axiome de cardinal.
4. `nonSS_actual_bracket_switch` et `nonSS_actual_raw_switch` : sommer l'équivalence avec `GoldbachRound11.sourceBracket`/coefficient physique réel, theta et raw distincts. D_a/W_a doivent être les définitions importées, sans profile libre ni disparition de prix.
5. `balanced_conductor_stratification` : C_bal<N, avec une partition explicite C_bal<=B / medium / C_bal^2>N ; aucune assertion C_bal<=sqrt(N). Conserver les branches vides et les égalités de fronts.
6. `rankTwoCofactorHarmonicIdentity` : prouver le H8 fini sur les vrais produits p et p*q avec p<=q, y compris le diagonal p=q ; puis la borne de paramètres `sum_(h1<=B) floor(B/h1)<=B*(1+logB)` dans une couche séparée si la preuve analytique est sélectionnée.

Ces énoncés sont auxiliaires. Même compilés sans sorry, ils ne démontrent pas une distribution du canal long, H9 sous toutes les conversions analytiques, ni une borne de D_N. Ne pas faire de H9, d'une petite Gamma, d'une capacité suffisante ou d'une disponibilité une prémisse de la prétendue victoire.

## Contrat du nouveau test strict N=10^8, non exécuté

Fenêtre déclarée **[1600100,1601100]**, tous les 1001 entiers ; elle est distincte des banques17/18 et ne dépend d'aucun signe ou incidence observé. Paramètres originaux alpha100,a3163,Q999999,M1000000,p0=3,Z100. Pour chaque entier q, primalité exhaustive correcte et unités ; pour chaque q premier, tous les e SF/unitaires 1<=e<=floor((N-Q-1)/q), sans choix parmi les compléments premiers. Le cap réel est calculé pour chaque q, pas supposé constant.

Enregistrer les factorisations complètes de n1,n0, leurs rangs Omega avec multiplicité, r1,r0 maximaux et h1,h0 ; classer A/R/S/SS/complement par les définitions18. Pour **tous les points non-SS** et pas seulement ceux où n_e est premier, enregistrer tag D/P, a1,b0,x0,y0 signé,t, les deux inverses, C_bal, toutes les coprimalités justifiées et l'égalité H1. Garder les cas h_j ayant un facteur commun avec r_j. Le contrôle de `C_bal^2>N` ne présuppose pas l'existence de cette strate ; une strate vide est un résultat fini.

SourceB=floor(N^(1/8))=10 et T=10 sont dérivés par racines entières, jamais par flottants. Comme tout h1>=3 et h0>=7, h1*h0>=21 ; **la couche D courte source est vide à ce N**, ce qui doit être enregistré comme garde entière, pas contourné en changeant le front. Pour vérifier le H8 et les routages de rang3 hors de l'onset analytique, une échelle auxiliaire distincte B_test=2048 est déclarée avant calcul. Elle sert uniquement aux identités finies et à la partition des mêmes points ; elle ne reçoit ni H9 source ni un paiement global. Tous les cofacteurs h<=2048 de rang1/2 sont énumérés, avec leurs p^2 ; séparément, tous les produits non coupés de un ou deux premiers <=2048 vérifient l'égalité rationnelle H8. La somme coupée h<=2048 est seulement <=H8. Les restrictions h1*h0<=B_test restent explicites.

Les kernels réels sont nouveaux sur ces seuls vertices, après gate root. Évaluer D/W pour tous les axes theta/raw actifs nécessaires à H4 et aux réciproques m1 physiques uniques ; les axes nuls gardent leur formule littérale et terme zéro, sans kernel libre. Les m1 non-squarefree ont C=0 par mu(m1)=0 ; leur annulation n'exige pas de fabriquer un W. m0 garde raw=theta=0. Les tableaux q/e sont fusionnés par m et premier axe avant toute somme. Conserver les sommes D/P et courts/medium/long, theta/raw/pp, les rangs, les deux signes mu(e), les vrais C et la partie positive certifiée séparément. Les intervalles de log sont rationnels stricts et les résultats ne sont jamais des nombres flottants.

Falsifiers propres à ce mécanisme : (i) `gcd(h_j,r_j)=1` pour toute ressource (facteurs répétés) ; (ii) quatre formes divisées premières dans P (cofacteurs composites) ; (iii) conducteur équilibré <=sqrt(N) toujours ; (iv) réciproque triprime fournit un poids favorable ou p^2 fournit une capacité ; (v) chaque e/tag fournit un nouveau m1. Ne pas imposer qu'un falsifier fini existe : en son absence écrire `NO_COUNTEREXAMPLE_IN_WINDOW`. Les identités de sélection et H4 doivent, elles, être exactes sur tout le support. Une assertion réellement fausse tue l'itération et garde source, snapshot, log et exit avant correctif.

Le premier essai canonique est unique. Aucun replay/PASS ancien, ancienne banque W/D/prix/log/signe, PDF ou Lean n'est lancé. Un test réussi à N=10^8 ne vérifie ni u>=10^24 ni u>=10^40 ; les gardes analytiques fausses y restent fausses.

## Sources primaires et obligations finales

Le parallèle avec Chen est **une analogie de mécanisme**, pas un théorème transféré. [Matomäki–Zúñiga-Alterman, Weighted sieves with switching, version 14 mars 2025](https://arxiv.org/pdf/2405.19063), §§3–5, impose une information de distribution sur les problèmes original et retourné ; ses poids peuvent éliminer certains hauts rangs dans son propre problème. Cela ne prouve aucune information correspondante pour H4, et ses asymptotiques à constantes implicites ne donnent pas notre onset. Le présent choix canonique D/P et le budget multiset sont dérivés ici, sans attribuer une nouveauté bibliographique générale à la décomposition hyperbolique.

Les bornes indépendantes écrites S_1, prime-log, Mertens/totient et leurs domaines sont ceux vérifiés dans [Rosser–Schoenfeld 1962](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf), avec D9_18 dérivé par sommation partielle et ses fronts, et les ingrédients finis [Ford, §4](https://ford126.web.illinois.edu/sieve2023.pdf). Aucun de ces résultats n'est recompilé ou réexpérimenté ; leur raccord au nouveau cofacteur composite H6 reste une obligation séparée.

Obligations ouvertes : distribution quantitative signée des canaux medium/long sous leurs poids effectifs et toutes erreurs ; raccord Selberg/rho composite pour H7 ; conversions analytiques, troncatures et somme entière pour H9 ; segment source10^24..10^40 ; rang>=4 ou h1*h0>B ; T_A, union de capacités à travers les fibres, Gamma agrégée et tous les autres postes du ledger. La couche rank3short et H4 ne sont jamais ajoutées comme paiement à P5 sur le même support.

Le ledger fixé reste `D_N=Bprime^a+Bpp^a+Pband>=2+Zface>=2+Ialpha+2max(e,0)`. Original alpha/Q/k1/whole U_a, rawLambda_N sans mu(n)^2, principal -S(N)N, vrais S(bN), c1/b1/e1, longs/faces/nonbulk, I acquis, P5K2/J2 sur bloc entier avant retrait et alternative U4/variation gardent leur place. Aucun nouveau crédit ou erreur n'est soustrait deux fois. **FINAL conceptuel gelé : réduction entière réelle et couche quantitative conditionnelle, prix long explicite, aucune victoire et aucun NoGo global.**
