# Boucle 17 — demande sans capacité et partition par petits facteurs

FINAL conceptuel du rôle 2, idéation indépendante. Résultat écrit sélectionné par le root : une estimation quantitative après union physique de la sous-famille où les deux ressources absentes sont aussi rugueuses. La branche des petits facteurs et le déficit global restent ouverts. Aucun ancien fichier, banc ou module Lean n'est modifié ou exécuté. Score 0 ; aucune victoire.

## 1. Probe, quatre mouvements et sélection

Q1 First principles : **mauvais crédit du signe et mauvaise représentation du complément d'incidence**. A7 est acquis sous Lean sur le vrai S(N), mais ne minore aucune incidence. Le banc complet 16 a 95 incidences sur 612 vertices, zéro ressource e1 et trois ressources e3 ; son déficit entier et sa somme réelle sont positifs. Le retour 15 conservait en outre 400 labels premiers pour seulement 360 vertices physiques. Ces deux preuves interdisent de transformer signe ou labels en capacité.

Q2 Hidden assumption : « une ressource non première est sans petit facteur ». C'est faux : le complément de l'incidence première comprend les nombres avec un petit facteur et les composites rugueux. Si cette implication est retirée, la demande conditionnée se sépare en deux problèmes de crible différents, sans supposer de partenaire.

Q3 Elephant : il faut contrôler **la masse des deux branches** après union de tous les e, et le déficit lorsque des ressources existent mais ne suffisent pas. Une borne dimension 4 sur les seules ressources rugueuses ne paie pas automatiquement la branche avec petit facteur, dont le terme principal peut rester de taille N.

Q4 Hamming : **oui, résultat partiel avec lacune quantifiée**. Le nouveau calcul majore une demande réelle sans utiliser une minoration de couples premiers. Il fournit un budget effectif pour une partie du complément conditionné, et exhibe séparément la branche qui empêche encore le contournement global.

Les quatre mouvements sont examinés : inversion de l'hypothèse d'incidence en une partition par facteurs ; raisonnement depuis la réussite imposant une consommation unique avant les majorations ; transfert du crible supérieur à quatre formes sur la vraie variable q ; rétro-ingénierie des déficits 16, qui oblige à conserver e1, Λ(e) et les demandes même lorsque trois ressources e3 sont présentes.

Auto-filtre :

* **A — absence implique rugosité** : rejeté avant soumission ; la branche des petits facteurs peut contenir presque tout le complément et aucune implication ne l'enlève.
* **B — trois formes avec une seule ressource rugueuse** : estimation possible, mais après la somme sur les cœurs son majorant est de type N·poly(log u)/u ; aucune marge au budget annoncé n'est obtenue avec cette seule information. Elle est absorbée dans la partition plus forte, sans être ajoutée comme crédit.
* **C — deux ressources rugueuses, union canonique, quatre formes** : retenu. L'estimation de cette sous-famille est démontrée ci-dessous ; l'absence de disponibilité n'est jamais remplacée par une hypothèse première.

Déclaration du survivant : l'hypothèse attaquée est l'identification absence/rugosité ; la classe de mécanisme est une partition arithmétique suivie d'un crible supérieur effectif ; la causalité est la quatrième exclusion réelle, qui ajoute deux facteurs logarithmiques aux deux formes premières ; l'axe diffère du Type II calibré du rôle 1, car q est directement la variable criblée et aucune moyenne BV de μΛ n'est utilisée ; le conflit avec les transports antérieurs est résolu en ne construisant aucun partenaire et en ne consommant aucune capacité dans la borne rugueuse.

Mechanism: Partition canonique de la demande sans incidences e1/p0 selon les premiers facteurs des deux complémentaires, puis crible supérieur des quatre formes réelles après union de tous les petits cœurs.
Hypothesis: La branche où les deux complémentaires sont z-rugueux possède une majoration indépendante au budget source ; la branche avec petit facteur et le déficit des incidences présentes demeurent des obligations quantitatives séparées, sans partenaire ni densité supposés.
Observable: Sur une fenêtre neuve complète à N = 10^8, partitions A/R/S, racines locales, G et carré Selberg rationnels, vrais D/W/Λ, capacités uniques et témoin réfutant absence implique rugosité ; aucune extrapolation de cette fenêtre au source.
Conflicts: A7 n'est pas reprouvé ; les labels et capacités ne sont pas multipliés, Λ(e) et rawproperpowers restent, les collisions locales et CRT +1 sont explicites, ni OR petit ni déficit global payé n'est adopté comme hypothèse.

## 2. Domaine physique et coefficient acquis

Écrire u = log N, ell = log u. N est pair strictement positif, et au source u ≥ 10^24. Les paramètres restent alpha = ceil(N^(1/4)), Q = floor((N−1)/alpha), a = ceil(N^(7/16)), M = ceil(N^(3/4)). p0 est le vrai premier impair minimal ne divisant pas N ; en particulier **(p0,N)=1**. A7 acquis donne S(N)−log p0 ≥ 1/144, sur le vrai `GoldbachRound11.singularSeries`. Le raccord écrit A9 et U4 sont des inputs source, pas une nouvelle compilation de ce rôle.

Le support étudié est l'union de TOUS les points

    q premier, (q,N)=1, q ≥ M,
    e carré libre, (e,N)=1, p0 < e,
    e q ≤ N−Q−1, n_e = N−e q premier.

Le petit cœur satisfait e ≤ E_N := floor((N−Q−1)/M) ≤ N^(1/4) < a. Il n'est pas choisi selon une incidence observée. q > a et q > e ; les diviseurs courts de e q sont tous les diviseurs de e, y compris ceux ≤ alpha. Le raccord F1 acquis est

    U_a(e q) = −Λ(e),  μ(e q) = −μ(e),  Λ(e q) = 0,
    C_(e q) = Λ(e) − μ(e) W_a(n_e,e q).

Le vrai kernel garde Q, a k < e q, μ(k)/φ(k), les unités (k,n_e N)=1 et k1 conjoint. Pour un cœur premier Λ(e)=log e ; pour un cœur composite carré libre Λ(e)=0. e1 est hors de cette formule et garde C_q = −log q − W_a(N−q,q). e = p0 garde C_(p0 q) = log p0 + W_a(N−p0 q,p0 q).

Sur ce support les deux ressources potentielles sont physiquement éligibles : q ≥ M, p0 q ≥ M et n1 := N−q > n_e > Q, n0 := N−p0 q > n_e > Q. Elles sont unitaires si q l'est. Leur incidence vaut donc I1 = 1_(n1 premier) et I0 = 1_(n0 premier), sans existence supposée. Sous U4, e1 a C_q ≤ −u/2 et p0 a C_(p0 q) ≤ −1/288 lorsque son premier complément existe. Une ressource absente vaut zéro.

La représentation physique est unique : q est l'unique facteur premier ≥ M, puisque deux facteurs ≥ M auraient produit > N ; e = m/q est ensuite déterminé. Tous les labels historiques donnant ce même m sont fusionnés. Deux q distincts ne partagent ni demande m=e q, ni capacité q ou p0 q. Les capacités e1 et p0 ne sont pas de nouveaux vertices à ajouter une seconde fois au ledger.

Définir b_(e,q) = log(n_e) C_(e q) sur les incidences premières, et t_(e,q) = max(b_(e,q),0). Au source, U4 donne W = −S(N)+δ, |δ|≤epsilon_W≤1, et S(N)<3 ell. Donc

    t_(e,q) ≤ u [Λ(e)+S(N)+epsilon_W] ≤ u [Λ(e)+4 ell].       (C1)

C1 conserve Λ(e) ; il majore aussi les cœurs dont le coefficient réel est négatif par une enveloppe positive, sans déclarer ces points nuisibles. Aucun μ(n)^2 n'est introduit sur le premier axe. Les n properpowers restent dans B_pp^a et ne sont pas évalués par le masque commun premier de U4.

## 3. Partition exacte de la demande, aucune implication de disponibilité

Fixer z = N^(1/4). Sur le domaine source, q,n_e,n1,n0 > z. Soit P(z) le produit des premiers ≤ z. Pour chaque demande réelle, poser :

* A : I1+I0 ≥ 1, ressources présentes ; elles restent comptées une fois.
* R : I1=I0=0 ET (n1 n0,P(z))=1.
* S : I1=I0=0 ET (n1 n0,P(z))>1.

Ainsi T = T_A+T_R+T_S exactement, avec T_X = somme des t_(e,q) sur la cellule X. R n'est pas tout le complément de A. Cette partition ne retire aucune demande et ne déclare aucun déficit payé. Pour borner T_R, on peut oublier I1=I0=0 dans un **majorant** ; on ne modifie pas la définition de R.

La capacité réelle de la comparaison est, une seule fois par q,

    R_unique = sum_q [ max(−b_(1,q),0) + max(−b_(p0,q),0) ],

avec ses propres incidences premières. Le signe ou la taille de T_A+T_S−R_unique est inconnu. Aucun parent n'est affecté à chacun des e séparément. La borne sur T_R ne consomme pas R_unique.

## 4. Quatre formes, collisions et crible fini effectif

Pour e > p0, prendre la vraie variable entière q et

    F_e(q) = q (N−e q)(N−q)(N−p0 q),
    rho_e(l) = #{x mod l : F_e(x)=0 mod l}, l premier,
    Delta_e = N e p0 (e−1)(e−p0)(p0−1).

Les racines sont l'union des quatre formes, jamais quatre racines postulées. **(e,N)=1 et (p0,N)=1** assurent qu'aucune forme ne s'annule identiquement modulo l : une pente nulle de N−e q ou N−p0 q a une constante N non nulle ; q et N−q ont toujours une pente non nulle. Chaque forme fournit au plus une racine. Donc 1≤rho_e(l)≤min(4,l) ; pour l ne divisant pas Delta_e, les quatre racines sont distinctes et rho_e(l)=4. Les facteurs N, e, p0 et toutes les différences entre pentes figurent dans Delta_e. 2 et 3 divisent Delta_e : N est pair ; si p0>3, alors 3|N, tandis que p0=3 fournit ce facteur lui-même.

Si rho_e(l)=l pour un l≤z, la cellule rugueuse est vide : tout entier q est interdit. Aucun g négatif ou dénominateur nul n'est introduit.

À N=10^8, p0=3 et N≡1 mod3. Pour e≡2 mod3, les formes q,N−q,N−e q occupent les trois classes, donc rho_e(3)=3 et R est vide ; N−3q est une constante non nulle modulo3. Pour e≡0 ou1 mod3, rho_e(3)=2. Lorsque p0>3, 3|N et les gardes d'unité font au contraire rho_e(3)=1. Ces collisions sont gardées dans le crible, avec leurs capacités éventuellement absentes.

Pour un e sans saturation locale, poser

    h_e(d) = product_(l|d) rho_e(l)/(l−rho_e(l))   pour d carré libre,
    G_e(z) = sum_(d≤z, d carré libre) h_e(d),
    G_(e,d)(y) = sum_(r≤y, r carré libre, (r,d)=1) h_e(r),
    lambda_e(d) = μ(d) product_(l|d) (1−rho_e(l)/l)^(-1)
                  * G_(e,d)(z/d) / G_e(z), d≤z,
    lambda_e(d) = 0 autrement.

Alors lambda_e(1)=1 et |lambda_e(d)|≤1. Le crible supérieur utilisé est le théorème 4.1, avec ses poids (4.4) et son reste (4.5), dans les [notes primaires de Kevin Ford, §4, pages imprimées 43–45, indices PDF 42–44](https://ford126.web.illinois.edu/sieve2023.pdf). En comptage PDF à partir de 1, ce sont les pages 43–45 ; le théorème est page 45 et les poids/norme page 44. Il porte sur des entiers q, pas une AP appliquée arbitrairement à μΛ ; ici la distribution nécessaire est fournie directement par CRT.

Pour contrôler les poids sans poser leur résultat, fixer g(d)=rho_e(d)/d, G=G_e(z), h=h_e. Le regroupement des d selon l=gcd(d,t), pour t carré libre ≤z, donne

    G = sum_(l|t) h(l) G_(e,t)(z/l)
      ≥ G_(e,t)(z/t) product_(l|t)(1+h(l)).

Or product(1+h(l))=h(t)/g(t)=product(1−rho_e(l)/l)^(-1). La formule explicite lambda(t) donne donc |lambda(t)|≤1 et lambda(1)=1. Pour le terme principal, la diagonalisation finie est

    sum_(d,t≤z) lambda(d)lambda(t)g(lcm(d,t))
      = sum_(r≤z,SF) [sum_(r|d,d≤z)lambda(d)g(d)]²/h(r).

L'inversion de Möbius dans la formule donnée de lambda fournit sum_(r|d)lambda(d)g(d)=μ(r)h(r)/G. Le membre droit vaut sum_r h(r)/G²=1/G. Tous ces ensembles et sommes sont finis.

Pour l'intervalle entier J_e=[M,floor((N−Q−1)/e)], de cardinal X_e≤N/e, CRT donne rho_e(d)=product_(l|d)rho_e(l) pour d carré libre, et

    #{q in J_e : d|F_e(q)} = X_e rho_e(d)/d + r_e(d),
    |r_e(d)| ≤ rho_e(d).                                      (C2)

Le +1 par classe est conservé avant toute somme. Le carré Selberg majore point par point le masque (F_e(q),P(z))=1. Son terme principal est exactement X_e/G_e(z), et son reste absolu satisfait

    error_e ≤ sum_(d≤z²,SF) 3^omega(d) rho_e(d)
            ≤ sum_(d≤z²) tau_12(d)
            ≤ z² (1+2 log z)^11.

La première multiplicité est celle des deux diviseurs dont le lcm est d, la seconde utilise rho_e(d)≤4^omega(d). La dernière inégalité vient de la convolution à 12 facteurs : fixer les 11 premiers facteurs, compter le dernier par X/(produit), puis majorer par H_floor(X)^11. Aucun conducteur ni reste BV n'est importé.

L'identité finie exacte à vérifier dans le contrat est sum_(q in J_e)(sum_(d|F_e(q),d≤z)lambda(d))² = X_e/G_e(z)+sum_(d,t≤z)lambda(d)lambda(t)r_e(lcm(d,t)). Le majorant utilise ensuite la valeur absolue de chaque reste, jamais un signe de reste désiré.

Par conséquent, sans hypothèse de densité première,

    #{q in J_e : q,n_e premiers ; (n1 n0,P(z))=1}
      ≤ X_e/G_e(z) + z²(1+2log z)^11.                         (C3)

q,n_e>z rendent la condition de crible nécessaire. Les conditions d'unité et les deux absences peuvent être rétablies par restriction, pas par égalité.

## 5. Minoration uniforme explicite de G, puis somme sur tous les e

Les deux seuls inputs externes effectifs supplémentaires sont theta(x)<1.01624 x<2x **pour tout x>0**, et

    d/φ(d) < exp(gamma) loglog d + 2.50637/loglog d, d≥3.

Ce sont respectivement (3.32), théorème 9, et (3.42), théorème 16 de l'article primaire [Rosser–Schoenfeld, 1962, pages imprimées 71–72, indices PDF 7–8](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf), [notice DOI originale](https://doi.org/10.1215/ijm/1255631807). En comptage PDF à partir de 1, (3.32) est page 8 et (3.42) page 9. (3.42) vaut pour d≥3 et évite l'exception de (3.41). Les bornes des tableaux limitées à 10^8 ne sont pas utilisées au source. Les raccords ci-dessous sont dérivés pour nos formes ; aucune asymptotique avec constante cachée n'est employée.

**Troncature.** Poser w=z^(1/32). Le produit fini Z_e(w)=product_(l≤w)(1−rho_e(l)/l)^(-1) est la somme de h_e(d) sur les diviseurs du primorial de w. Sous la mesure h_e(d)/Z_e(w),

    E(log d) = sum_(l≤w) rho_e(l) log l/l
             ≤ 4 sum_(l≤w) log l/l ≤ 8+8log w.

La dernière inégalité suit de theta(t)<2t et d'une intégration partielle. Pour log z≥32, le membre droit est ≤(log z)/2. Markov laisse donc au moins la moitié de Z_e(w) sur d≤z : G_e(z)≥Z_e(w)/2. Cela prouve la troncature réelle ; prendre le produit complet comme s'il était déjà contenu dans G serait faux.

**Collisions.** Pour les premiers hors Delta_e, (1−4/l)^(-1)≥(1−1/l)^(-4). Pour les premiers divisant Delta_e, rho≥1 permet le minorant (1−1/l)^(-1). Donc

    Z_e(w) ≥ [ product_(l≤w)(1−1/l)^(-1) ]^4 [φ(Delta_e)/Delta_e]^3.

Le produit géométrique fini contient tous les entiers ≤floor w, d'où product≥H_floor(w)≥log w. C'est l'usage du développement eulérien positif acquis, pas une nouvelle preuve de A7 ni une marge supposée pour S.

**Prix uniforme.** e≤N^(1/4), p0<u³ et 6 log u≤u/4 donnent

    N ≤ Delta_e ≤ N e³ p0² ≤ N^(7/4)u^6 ≤ N².

Avec exp(gamma)<2, ell≤loglog Delta_e≤ell+log 2 et (3.42), on a Delta_e/φ(Delta_e)<3ell au seuil source. Ainsi

    G_e(z) ≥ (log w)^4/[2(3ell)^3]
           = u^4/[14495514624 ell³],
    z=N^(1/4), w=N^(1/128).                                  (C4)

La constante est 2*128^4*27. La perte des facteurs locaux est donc payée, y compris les premiers divisant N ou e−p0. Il n'est pas demandé que Delta_e soit petit par rapport à z.

**Union et poids réels.** Après (C1)/(C3), sommer sur TOUS les e≤E_N, puis élargir seulement le majorant aux entiers et aux premiers :

    sum_e Λ(e)/e ≤ sum_(p≤E_N) log p/p ≤2+2log E_N≤u,
    sum_e 1/e ≤1+log E_N≤u/2,
    sum_e [Λ(e)+4ell]/e ≤4u ell.

Le prix principal pondéré est donc ≤4N u²ell/min G_e. Le reste comporte au plus N^(1/4) cœurs physiques, avec u[Λ(e)+4ell]≤u². Puisque z²=N^(1/2),

    T_R ≤ 57982058496 N ell^4/u² + N^(3/4)u^13.              (C5)

Les cœurs ayant une obstruction locale sont simplement vides. Cette majoration n'a ni nombre de labels ni constante de capacité cachée.

**Onset effectif.** À u0=10^24, ell<56 et

    57982058496*16384*56^5
      =523183096654036482392064 <10^24.

La fonction (log u)^5/u décroît pour u>exp(5), donc le premier terme de (C5) est ≤N/(16384u ell) sur tout le source. Pour le reste, le logarithme du ratio à N/(16384u ell) est log16384+14logu+logell−u/4 ; il est négatif à u0 et sa dérivée 14/u+1/(u ell)−1/4 reste négative. D'où l'estimation indépendante écrite

    T_R ≤ N/(8192u ell), u≥10^24.                            (C6)

C6 majore une sous-famille réelle avec les vrais coefficients via U4. Il ne minore aucun couple premier et ne paie pas T_S ou T_A. A9 n'est pas une prémisse sur la quantité des ressources. La preuve de ce rôle est écrite, avec les inputs analytiques source identifiés ; aucune compilation n'a été lancée.

## 6. Branche des petits facteurs : coût distinct et obstruction restante

La partition de S est canonique : si n1 a un facteur premier ≤z, choisir j=1 et l=P^−(n1) ; sinon choisir j=p0 et l=P^−(n0). La deuxième face impose n1 rugueux. Chaque demande a un seul témoin. Alors n_j=l v, tous les facteurs de v sont ≥l, et l ne divise ni N ni j. Pour un cœur e≡j mod l,

    n_e = N−e q ≡ N−j q = n_j ≡0 mod l.

Puisque n_e>Q>z≥l, son incidence première est exactement nulle. Son raw peut néanmoins être celui d'une puissance propre de l, qui reste dans B_pp^a. Cette exclusion véritable ne dit rien sur les autres classes de e.

Une borne indépendante explicite de la masse S s'obtient en oubliant le témoin et en criblant les deux formes q,N−e q. Ici rho_2(l)=2 hors N e, et au moins1 sur les collisions. Le même argument, avec w_2=z^(1/16), donne

    G_(2,e)(z) ≥ u²/(24576ell),
    count_2 ≤ X_e/G_(2,e)(z)+z²(1+2logz)^5,
    T_S ≤ 98304 N ell²+N^(3/4)u^7.                           (C7)

Le lcm a maintenant le poids 3^omega(d)*2^omega(d), majoré par tau_6 ; les paramètres, CRT +1 et poids (C1) restent les mêmes. C7 est un coût distinct, très supérieur à N/(256u ell). Il ne constitue ni un paiement ni une minoration de la branche S. Cette branche peut encore porter toute la demande ; on ne prétend pas qu'elle est négligeable ou qu'elle porte effectivement une masse source donnée.

Le problème qui reste est précis. Dans chaque face du témoin, la vraie variable produit est l v :

    j=1  : q=N−l v,        n_e=e l v−(e−1)N ;
    j=p0 : q=(N−l v)/p0,   n_e=[(p0−e)N+e l v]/p0,
                            l v≡N mod p0.

Les contraintes de premier facteur, les deux incidences q,n_e, les unités, Λ(e), μ(e) et la priorité entre faces sont conservées. Le terme principal positif des classes restantes n'est pas retiré par l'identité. Fermer S demanderait une information signée ou une comparaison quantitative avec les ressources, raccordée à ces produits et conducteurs réels. Aucun tel mécanisme supplémentaire n'est démontré ici. Un BV pour Λ seule, ou un petit défaut OR posé comme hypothèse, ne le fournirait pas. Pour A, même une ressource présente peut ne pas payer tous les e : le déficit entier après R_unique reste inconnu.

## 7. Contrat numérique neuf, complet et séparé du source

Soumis au root avant lancement. N=10^8, alpha=100, a=3163, Q=999999, M=1000000, p0=3. Fenêtre fermée **[1200100,1200300]**, soit 201 entiers : tester chacun pour obtenir les q premiers unitaires. Pour chaque q, TOUS les e SF/unitaires 1≤e≤min(a,floor((N−Q−1)/q)) ; le cap commun est 82. z=100. e1, e3, autres cœurs premiers et rangs pairs restent dans l'union ; les rangs impairs composites sont finis vides car leur minimum unitaire 231>82, sans conclusion source.

Le contrat conserve pour chaque candidat e,q les facteurs de e,q,n_e,n1,n3, toutes les incidences theta et raw séparées, les fronts, le préfixe complet U_a, μ/Λ et D/W sur tous axes theta/raw actifs ; les axes exactement nuls gardent leur kernel littéral et leur terme zéro. Les puissances propres de n_e,n1,n3 ne sont pas filtrées par μ². Les deux ressources q/3q sont évaluées une fois par q et demeurent présentes dans la comparaison entière, même lorsqu'une classe de demandes est interdite modulo3.

Partitions à mesurer, sans signe de résultat fixé :

1. A/R/S sur les demandes e>3 réellement premières ; facteur témoin minimal et exclusion e≡j mod l ; liste entière des vertices, sommes signées, parties positives certifiées et capacités uniques.
2. Pour chaque e>3, rho_e(l) réel pour TOUS les premiers l≤100. Si rho=l, certificat d'obstruction et R vide, sans G. Sinon G_e(100), tous les lambda(d) rationnels d≤100, lambda1=1, |lambda|≤1 et identité principale quadratique1/G.
3. CRT exact et +1 pour tous les lcm de supports lambda, sur l'intervalle des 201 entiers ; comptage réel du masque rugueux et son majorant par carré. La borne numérique avec reste absolu peut être très faible et doit être publiée ainsi, sans la remplacer par un petit résultat postulé.
4. Les coefficients principaux Λ(e)+μ(e)S_N restent affines sur l'enclosure acquise 847/512≤S_N≤11011/6144 ; les signes des vrais W sont mesurés indépendamment. Les sommes R/S/A et les déficits peuvent avoir tout signe. C6/C7 ne sont pas appliquées à u=log(10^8), hors onset. Le certificat fini vérifie la partition et le crible, pas l'input source U4.

Falsifiers stricts nouveaux : (i) « I1=I3=0 implique n1,n3 rugueux » ; chercher dans la fenêtre complète une demande première en S, sans exiger son existence ; (ii) rho=4 sur tous les premiers, ce qui omet N/e/p0/différences et les obstructions modulo3 ; (iii) transfert de C6 à la demande entière sans S/A ; celui-ci est comparé aux masses mesurées, sans prétendre réfuter l'onset source. Toute assertion réellement ratée garde source/snapshot/log avant correction ; l'absence de contre-exemple reste finie. Les anciennes assertions déjà réfutées ne sont pas rejouées comme résultats neufs.

Pour factoriser n≤10^8, une liste de premiers jusqu'à10000 suffit ; elle ne sert pas à limiter l'énumération des q>10^6. Les 201 entiers sont effectivement testés. Le modèle bilatéral S(bN), b=m/l à la suppression réelle, reste distinct de S(N), avec b1/e1/c1 et cofacteurs longs ; le crible unilatéral ci-dessus ne lui transfère aucun poids.

## 8. Obligations, ledger et état de clôture conceptuelle

Obligations formelles pertinentes : union physique injective ; partition A/R/S avec priorité des deux faces ; root count et collisions sur les quatre formes ; CRT avec +1 ; poids Selberg finis et majorant quadratique ; minoration G par la vraie troncature Markov et le prix Delta/φDelta ; convolution tau_12 et somme pondérée avec Λ(e) ; raccord C1/U4 puis constantes C5/C6 au domaine source. Les références primaires et leurs ranges doivent être raccordées, non ajoutées comme une hypothèse égale à C6. Un Lean de CRT seul serait auxiliaire et ne remplacerait pas la preuve quantitative manquante de S/A.

Inputs immuables : A7 certifié dans les deux nouveaux modules 16 ; source W/U4 dans round10/agent1_prime_signed.md ; coefficient F1 et domaines e1/prime/composites dans round15/agent2_signed_cofactors.md ; sourceBracket/harmonicKernel/singularSeries dans round11/lean/ThreeAdicPrimePairing.lean. Controller16 SHA256 `10d9f68fc649d965aa5eecac96fecf5fd20f705527d42f52b855662acec02332` ; 799 protections. PROBE17 SHA256 `cbe1d2a7b02f96ce3743b0b5108c035666be756b4fbe8a83069e4995513e2388` ; feedback16 SHA256 `fffa09da54f932460a21252c18066a02857f3972aaf493c84c8f5dec882d041c`. Vue constraints fraîche lue avec le helper Python -B -X utf8 ; aucune ancienne banque/PASS/preuve/rendu exécuté.

Le budget C6 porte seulement sur la branche R de J1, q≥M, e≤N^(1/4). Il remplace le coût de cette branche et n'est pas ajouté à une charge U4/NG54 sur le même support : epsilon_W est déjà dans (C1), sans nouvelle allowance N*epsilon_W. Les autres choix U4/variation restent alternatifs. q∈(a,M), J1 à cœur incomplet, J0, J2 et toutes les autres couches demeurent hors de cette estimation. P5 reste sur K2/J2bulk ENTIER avant les retraits exacts, et aucun crédit rough −R_pair ou capacité e1/p0 n'est payé deux fois.

Le ledger entier reste `D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0)`. Whole U_a, originalalpha/Q, k1 conjoint, rawproperpowers, principal −S(N)N, S(bN), b1/c1/e1, longs, célibataires/faces/nonbulk, terme couvert, onset BV effectif supplémentaire et source u≥10^24 sont conservés. La demande avec petit facteur et la demande lorsque des incidences existent n'ont aucune compensation globale prouvée.

Statut FINAL conceptuel : `INDEPENDENT_EFFECTIVE_FOUR_FORM_ROUGH_ABSENCE_DEMAND_BOUND`, `SMALL_FACTOR_BRANCH_MAIN_COST_EXPLICIT_UNPAID`, `PRESENT_INCIDENCE_GLOBAL_DEFICIT_UNESTIMATED`, `NO_NEW_LEAN_OR_BANK_BY_ROLE2`, `SCORE_ZERO`, `VICTORY_FALSE`. C6 est un résultat écrit nouveau et partiel sélectionné par le root ; l'objectif global reste ouvert. Le contrat est complet et figé avant autorisation du producteur. Le reçu et les résultats numériques éventuels forment une annexe distincte, sans modification de ce FINAL ni transfert de la fenêtre au domaine source.
