# Boucle 18 — double extraction des témoins semipremiers

FINAL conceptuel du rôle 2. Une nouvelle majoration quantitative porte sur une vraie couche **non rugueuse** de T_S : les deux ressources absentes sont des produits d’un petit premier canonique et d’un grand premier. La majoration conserve tous les e et témoins, les deux étages de CRT +1 et le prix de l’union. Elle n’est ni une estimation de T_S entier, ni une disponibilité supposée. Aucun banc ni Lean n’a été lancé. `score = 0`, `victory = false`.

La borne obtenue est valable au seuil source u = log N ≥ 10^24, mais son paiement au budget N/(8192 u log u), avec les constantes conservatrices retenues ici, n’est établi qu’à u ≥ 10^36. L’intervalle 10^24 ≤ u < 10^36 et le résidu à quotient composite restent ouverts. Les 997 archives et les FINAL 17 sont immuables.

## Probe et filtrage

Q1 First principles : **mauvais espace d’action et mauvais crédit de capacité**. Le banc rough 17 avait A = 11, R = 0, S = 18 et un déficit entier positif ; ses quatre formes originales n’ont donc payé aucune demande R dans cette fenêtre. Le banc complet 16 avait 95 incidences, zéro e1 et trois e3, avec déficit et somme réelle positifs. Ces deux constats ne sont pas des NoGo source, mais interdisent de confondre rugosité, signe source et capacité disponible. La fusion 15 distinguait en outre 400 labels premiers de 360 vertices physiques.

Q2 Hidden assumption : « une ressource composite ayant un petit facteur ne fournit plus de quatrième exclusion première ». Lorsqu’elle est effectivement semipremière, son **quotient** est premier ; une division arithmétique réelle, dans une progression CRT, restaure l’exclusion. La primalité du quotient est une condition de sélection vérifiée, jamais une densité ni une existence postulée.

Q3 Elephant : les ressources à au moins trois facteurs peuvent porter le résidu principal. Le changement de variable ajoute aussi des paramètres témoins ; leur somme harmonique et tous les +1 peuvent annuler le gain. Une réciprocité virtuelle sur N − p0 q a un premier axe p0 q composite et ne donne aucune capacité.

Q4 Hamming : **oui, acquis quantitatif partiel possible**. Le mécanisme atteint une couche de S qui était exclue de R par définition, avec un prix global calculé. Il ne franchit pas seul la frontière globale : le résidu signé, T_A et les capacités consommées une fois restent non estimés au budget.

Les quatre mouvements sont utilisés. L’inversion d’hypothèse remplace le masque composite original par ses vrais quotients. Le raisonnement depuis la réussite impose de payer la somme sur e et les deux témoins avant de choisir le niveau du crible. Le transfert analogique est un switching de variables de facteur, avec deux divisions simultanées et des déterminants entiers conservés. La rétro-ingénierie des déficits 16/17 impose la couche à quotient composite et le masque raw, au lieu d’ajouter des ressources fictives.

Auto-filtre :

- Remplacer z ou p0 dans le rough 17 est rejeté : ce serait un changement de niveau sans nouvelle information arithmétique.
- Compter chaque e avec une nouvelle capacité réciproque est rejeté : cette capacité dépend seulement de q et doit être fusionnée ; pour j = p0 son premier axe raw est même nul.
- Retirer **tous** les facteurs petits d’une ressource et annoncer quatre formes partout est rejeté sans estimation : le cofacteur lisse peut être très grand, le quotient peut être 1 ou inférieur au seuil, et la somme des cofacteurs n’est plus la somme harmonique de deux premiers. Aucun crédit n’est pris sur cette extension.
- La double extraction semipremière est retenue : elle est une sélection réelle, son conducteur reste ≤ N^(1/2), tous ses quotients sont grands, et la somme des paramètres conserve un gain de deux puissances de u, avec un onset supplémentaire explicite.

Déclaration du survivant : l’hypothèse attaquée est la perte irréversible d’exclusions sur une ressource non rugueuse ; la classe de mécanisme est un switching arithmétique conditionné par factorisation canonique. La causalité est la primalité effective des deux quotients, qui fournit quatre formes après division. L’axe est distinct du rôle 1 : aucun mode χ, aucun BV avec coefficient κ arbitraire ni dispersion d’une équation à conducteur fixé n’est transféré. Les conflits antérieurs sont évités en conservant les vrais coefficients, l’union physique et la queue non sélectionnée.

Mechanism: Double extraction canonique des petits témoins semipremiers des ressources absentes, puis crible des quatre formes divisées dans leur vraie progression CRT et somme sur tous les cœurs et témoins.
Hypothesis: La primalité effective des deux quotients permet une majoration indépendante de cette couche non rugueuse, avec tous les paramètres et CRT +1 payés ; ni le reste à quotient composite, ni T_A, ni une capacité suffisante ne sont posés comme hypothèse.
Observable: Sur une fenêtre neuve complète à N = 10^8, factorisations canoniques, partition entière, polynômes divisés et déterminants, racines locales, masques theta/raw et fusion des vertices réciproques ; la somme totale et les signes restent mesurés.
Conflicts: Les racines et poids 17 ne sont pas redérivés ni transférés gratuitement à un polynôme différent ; le nouveau raccord local est une obligation réelle, Λ(e), les deux signes μ et rawproperpowers restent, et aucune couche partielle ni onset supplémentaire n’est appelé Win.

## Domaine réel et sélection canonique

N est pair positif. Conserver u = log N, ell = log u, alpha = ceil(N^(1/4)), a = ceil(N^(7/16)), M = ceil(N^(3/4)), Q = floor((N − 1)/alpha) et p0, premier impair minimal ne divisant pas N. A7, le vrai S(N), U4 et le raccord des cœurs complets restent les acquis 16/17 ; ils ne sont pas reprouvés.

Le support des demandes est l’union physique de tous les points

    q premier, (q,N) = 1, q ≥ M,
    e carré libre, (e,N) = 1, p0 < e ≤ E = floor((N − Q − 1)/M),
    e q ≤ N − Q − 1, n_e = N − e q premier.

E ≤ N^(1/4). e < q ; q est l’unique facteur premier ≥ M de m = e q. Les labels donnent donc un unique m et un unique couple (e,q). Les ressources sont n1 = N − q et n0 = N − p0 q. Comme q < N/e et e ≥ p0 + 1, n0 > N/e ≥ M ; n1 ≥ 3N/4. Elles sont unitaires à N et dépassent Q.

Le coefficient littéral demeure

    C_(e q) = Λ(e) − μ(e) W_a(n_e,e q),
    U_a(e q) = −Λ(e), μ(e q) = −μ(e), Λ(e q) = 0.

Au source, U4 donne W = −S(N) + δ avec |δ| ≤ epsilon_W ≤ 1 et S(N) < 3 ell. Pour la dette positive t_(e,q) = max(log(n_e) C_(e q),0), l’enveloppe acquise est

    t_(e,q) ≤ u [Λ(e) + 4 ell].                         (D1)

Λ(e) vaut log e pour les cœurs premiers ; il n’est pas supprimé. D1 majore les deux signes sans déclarer favorable toute une classe finie.

Poser Z = floor(N^(1/4)). La couche SS étudiée impose les **factorisations réelles**

    n1 = ℓ1 r1, n0 = ℓ0 r0,
    ℓj = le plus petit facteur premier de n_j, ℓj ≤ Z,
    r1 et r0 premiers.

Elle est une sous-famille de S : les deux ressources sont composites, absentes comme incidences premières, et possèdent un petit facteur. Les facteurs sont distincts dans chaque ressource : n_j ≥ M > Z², donc r_j > ℓ_j. Les unités et la définition canonique de p0 donnent ℓ1,ℓ0 ≥ p0. En outre ℓ0 ≠ p0, puisque p0 ∤ N − p0 q. Les témoins sont différents : si ℓ1 = ℓ0 = ℓ, alors ℓ | (p0 − 1) q ; comme q > Z ≥ ℓ et ℓ ≥ p0, c’est impossible.

Chaque q a un seul couple (ℓ1,ℓ0), indépendant de e. Le choix du plus petit facteur ne crée aucune multiplicité. Dans un majorant, la somme sur tous les premiers admissibles ℓ1,ℓ0 est permise ; elle ne crée pas plusieurs occurrences d’une même demande physique sélectionnée.

Le complément est exactement S privé de SS, notamment les cas où le quotient canonique de l’une des ressources est composite, ou où une seule ressource possède un petit facteur ≤ Z. Les ressources à au moins trois facteurs ne sont pas converties en quotients premiers. Elles restent au résidu, y compris les puissances propres et facteurs répétés.

## Vraies formes divisées et déterminants

Fixer un couple de témoins, poser L = ℓ1 ℓ0, et choisir le représentant CRT entier 0 ≤ A < L satisfaisant

    A ≡ N (mod ℓ1), p0 A ≡ N (mod ℓ0).

L’inverse de p0 modulo ℓ0 existe. Les q admissibles sont q = A + L x, pour x dans un intervalle entier consécutif J_(e,L,A). Cet intervalle a cardinal

    X_(e,L,A) ≤ N/(e L) + 1.                            (D2)

Le +1 extérieur est conservé. Les quatre formes, dans l’ordre (q,n_e,r1,r0), ont les couples (pente, constante)

    (L, A),
    (−eL, N − eA),
    (−ℓ0, (N − A)/ℓ1),
    (−p0ℓ1, (N − p0 A)/ℓ0).

Les deux quotients de constantes sont entiers par CRT ; aucune division modulaire libre ne les remplace. Pour Δ_ij = pente_i constante_j − pente_j constante_i, les six déterminants signés sont

    Δ12 = NL, Δ13 = Nℓ0, Δ14 = Nℓ1,
    Δ23 = Nℓ0(1 − e), Δ24 = Nℓ1(p0 − e),
    Δ34 = N(p0 − 1).                                    (D3)

Le produit des quatre pentes est −e p0 L³. La valeur absolue du produit de ces pentes et des six déterminants est donc

    Delta_switch = N^6 e p0 L^6 (e − 1)(e − p0)(p0 − 1).  (D4)

Elle est strictement positive et ≤ N^(41/4) ≤ N^11. Son radical est exactement le radical de Delta_e L, où Delta_e est le vrai produit de collisions 17. Il ne dépend pas du représentant A. L’orientation de D3 et le signe du produit des pentes restent explicites.

Les classes e ≡ 1 modulo ℓ1 et e ≡ p0 modulo ℓ0 forcent n_e divisible par leur témoin. Puisque n_e > Q > Z, leur theta vaut zéro. Ce retrait ne supprime pas rawLambda_N : une puissance propre du témoin peut rester et appartient au ledger B_pp.

Sur les autres classes, les quatre formes sont primitives. Pour q, A est unitaire modulo L. Pour n_e, une prime divisant e mais pas L laisse la constante N non nulle, par (e,N) = 1 ; les deux primes de L sont traitées par les exclusions précédentes. Pour r1, sa constante modulo ℓ0 est N(p0 − 1)/(p0ℓ1), non nulle. Pour r0, sa constante modulo ℓ1 est N(1 − p0)/ℓ0, non nulle, et modulo p0 elle vaut N/ℓ0, non nulle. Les témoins ≥ p0 et ℓ0 ≠ p0 justifient ces affirmations, sans oublier une prime divisant L.

À ℓ1, seules les racines de r1 subsistent ; à ℓ0, seules celles de r0 subsistent. Le vrai nombre de racines vaut donc **1** sur chaque témoin, sur les classes de cible non exclues. Pour une autre prime ne divisant pas L, la pente de q est inversible et fournit au moins une racine. Le polynôme produit a ainsi 1 ≤ rho ≤ min(4,p) ; hors Delta_switch, D3 donne exactement quatre racines distinctes. Une saturation locale rend la cellule vide et n’autorise aucun dénominateur nul.

Tous les quatre entiers premiers de SS dépassent le seuil de crible utilisé ci-dessous : q ≥ M, n_e > Q, et r_j = n_j/ℓj ≥ M/Z ≥ N^(1/2). La primalité des quotients est réelle. Elle n’est pas remplacée par une implication « quotient composite donc rugueux ».

## Estimation indépendante et paiement des paramètres

Prendre le **nouveau** niveau T = floor(N^(1/16)) sur la variable x, et Y = floor(T^(1/32)). Il est imposé ici par le nombre de paramètres e,ℓ1,ℓ0 ; il ne change ni le Z des témoins, ni alpha, a, Q ou le masque rough 17. Aucun estimateur source n’est appliqué à N = 10^8.

Les poids Selberg génériques acquis peuvent être construits sur les racines effectives de ces nouveaux polynômes. Ce raccord n’est pas déjà fourni par `FourFormRoots`, qui porte sur les formes originales : D3, la primitivité et rho effectif doivent être formalisés si le candidat est sélectionné. Il n’y a aucune borne de norme générique transférée au couplage.

Le moment, la troncature et le coût de collisions acquis, après ce raccord réel, donnent par écrit

    G_switch(T) ≥ u^4 / [K ell^3],
    K = 54 · 2048^4 = 949978046398464.                    (D5)

Les inputs indépendants conservés sont la somme première logarithmique, Mertens fini et le prix en totient du calcul source 17 ; leur conversion analytique n’est toujours pas Lean-certifiée. Les arrondis sont payés : log T ≥ u/32 et log Y ≥ log T/64 ≥ u/2048. log T ≥ 32 et 32 log Y ≤ log T. D4 donne log log Delta_switch ≤ ell + 3 ; Delta_switch ≥ N^6. Le théorème (3.42) de Rosser–Schoenfeld, pour Delta_switch ≥ 3, donne Delta_switch/φ(Delta_switch) ≤ 3 ell au source. Le prix de collisions est donc au plus (3 ell)^3. Ce n’est pas une hypothèse `G ≥ cible`.

CRT sur x donne pour chaque d carré libre une erreur au plus rho(d), avec le +1 par classe conservé. La multiplicité des paires de diviseurs ayant un même lcm est 3^omega(d). Comme rho(d) ≤ 4^omega(d), le reste Selberg est au plus

    T² (1 + 2 log T)^11 ≤ N^(1/8) u^11.                 (D6)

La convolution à 12 facteurs et tous les lcm sont conservés. En utilisant D2 et G ≥ 1, le nombre de q pour un triplet (e,ℓ1,ℓ0) est majoré par

    K ell³ N/(e ℓ1 ℓ0 u⁴) + 1 + N^(1/8)u^11.           (D7)

Le 1 central est le coût **extérieur** de la progression CRT, distinct des +1 intérieurs de D6. Les contraintes de plus petit facteur et de quotient premier peuvent être oubliées dans ce majorant, mais restent dans la définition physique de SS.

La somme sur tous les cœurs utilise

    Σ_(e≤E,SF,unit) [Λ(e)+4ell]/e ≤ 3 u ell.            (D8)

Λ(e) est non nul seulement sur les cœurs premiers ; la somme acquise Σ_(p≤E) log p/p ≤ 2 + 2 log E ≤ u et H_E ≤ 1 + log E ≤ u/2 donnent D8. Pour les témoins, on utilise

    Σ_(p≤Z) 1/p ≤ 2 ell.                               (D9)

D9 ne vient pas directement d’un théorème sur Σ1/p. La formule de sommation partielle, avec son front 2, est

    Σ_(p≤Z)1/p = π(Z)/Z + ∫_2^Z π(t)/t² dt.

Rosser–Schoenfeld (3.6), x > 1, donne π(t) < 1.25506 t/log t < (3/2)t/log t. Ainsi la somme est au plus `(3/2)[1/log Z + log log Z − log log 2]`. Au source, log Z ≥ 1, log log Z ≤ ell et −log log 2 < 1 ; cela donne au plus `(3/2)(ell+2) ≤ 2ell` pour ell ≥ 6. Aucun front à 2 n’est supprimé. Les restrictions d’unité, p ≥ p0 et les deux témoins distincts diminuent ce majorant.

La somme du premier terme de D7, pondérée par D1, est donc au plus `12 K N ell^6/u²`. Pour les deux restes, il y a au plus E Z² ≤ N^(3/4) triplets. Pour chacun, `u[Λ(e)+4ell] ≤ u²` au source. L’union entière donne finalement

    T_SS ≤ 12 K N ell^6/u² + 2 N^(7/8) u^13.            (D10)

Aucune capacité n’est consommée pour obtenir D10. Tous les cœurs et témoins sont sommés avant d’annoncer le gain ; la bound ne repose pas sur une fenêtre riche en semipremiers.

À u0 = 10^36, ell0 < 84 et `8192 · 12 K · 84^7 / 10^36 < 1/4`. Le rapport ell^7/u décroît ensuite, car sa dérivée logarithmique vaut `(7/ell − 1)/u < 0`. Le terme `2 exp(−u/8)u^13`, comparé à 1/(8192u ell), est inférieur à 1/4 au même seuil et décroît. D10 donne donc, en particulier,

    T_SS ≤ N/(8192 u ell) pour u ≥ 10^36.              (D11)

Ce grand onset est un coût réel du calcul conservateur. Il ne remplace pas l’onset initial 10^24 et ne paie pas automatiquement le segment intermédiaire. Améliorer seulement K ou T ne serait pas un contournement global.

## Réciprocité physique et reste non payé

Pour j = 1, le vertex réciproque m1 = N − q = ℓ1 r1 a réellement premier axe q. Il est bulk, unitaire, et q > Q. Ses diviseurs courts sont {1,ℓ1} puisque ℓ1 ≤ Z < a < r1. Son coefficient est `log ℓ1 + W_a(q,m1)`, avec vrai kernel. Le signe source est favorable si ℓ1 = p0, par A7 et U4 ; aucun tel signe n’est imposé à tous les autres témoins. Dans ce cas, r1 ≥ M et ce vertex est précisément une capacité p0 déjà présente dans l’union des ancres. Il ne peut être ajouté une seconde fois.

Pour j = p0, m0 = N − p0 q = ℓ0 r0 a pour complément **p0 q**, produit de deux premiers distincts. Sa theta et son rawLambda_N sont exactement nuls. Ce vertex ne fournit aucune capacité. Mon observation provisoire qui attribuait le premier axe q aux deux réciproques était incorrecte ; la distinction est corrigée avant ce FINAL et doit être testée dans le banc neuf.

Un m1 peut coïncider avec une demande existante de cœur ℓ1 > p0 dans un autre fibre. La fusion se fait par la valeur entière de m et son premier axe, avant toute charge. Tous les e du même q partagent le même m1 ; ils ne possèdent pas chacun une nouvelle ressource. D10 utilise uniquement une majoration de demande, donc ne retire aucun principal ni erreur du ledger.

Le reste `S\SS` conserve la majoration C7 source 17, trop grande, de type `98304 N ell² + N^(3/4)u^7`. Cette enveloppe ne constitue pas un paiement. Elle n’est pas redérivée ni améliorée artificiellement ici. Les ressources à au moins trois facteurs et leurs deux signes peuvent porter le terme dominant.

Une organisation exacte du reste consiste à choisir le premier j dans {1,p0} dont le témoin canonique ℓ ≤ Z a quotient composite, puis r = d v, où d est son plus petit facteur premier et P⁻(v) ≥ d. L’équation réelle est

    ℓ d v + j q = N,
    n_e = [(j − e)N + eℓ d v]/j,
    j | N − ℓ d v.

Les indicatrices premières de q et n_e, μ(e), Λ(e), le cutoff de plus petit facteur et le conducteur complet restent couplés. Une estimation de distribution d’un seul premier ou une moyenne de μ sur des classes e ne contrôle pas ce produit de deux incidences. L’obligation indépendante manquante est une estimation signée de ces formes bilinéaires **avec calibration locale complète et leurs prix**, pas une hypothèse `T_(S\SS)` petit ni une masse de partenaires favorable. Aucun théorème applicable avec un onset effectif n’est établi ici. L’identité de factorisation n’est pas présentée comme un gain. T_A après capacités uniques demeure également ouvert.

## Contrat numérique neuf proposé, sans lancement

N = 10^8, paramètres originaux alpha = 100, a = 3163, M = 1000000, Q = 999999, p0 = 3 et Z = 100. Fenêtre **fermée complète** `[1400100,1405100]` : 5001 entiers, sans choix selon une incidence. Tester chaque entier pour la primalité de q, puis tous les e SF/unit > 3 jusqu’au cap `floor((N − Q − 1)/q)` ; ce cap vaut 70 sur toute cette fenêtre. Aucun nombre de q, de SS ou de signes n’est présupposé.

Pour chaque q premier, conserver les factorisations entières complètes de n1 et n0, leurs plus petits facteurs, quotients et primalités. Classer A/R/S comme en 17, puis SS ou son complément pour chaque vraie demande n_e première. Conserver les axes raw, y compris ceux dont theta est nulle. Une absence de SS ou de contre-exemple reste un résultat fini, sans disponibilité universelle.

Pour chaque q satisfaisant SS et tous les e sous le cap, conserver A,L, l’intervalle entier en x, les quatre pentes et constantes entières et les six déterminants orientés D3. Tester les classes exclues, la primitivité sous garde, rho effectif pour chaque premier ≤ 100, rho = 1 aux témoins et rho = 4 seulement hors Delta_switch. Le niveau issu de la formule source vaut T = 3 et Y = 1 au N fini : aucune minoration logarithmique source ni D5/D10/D11 ne doit être appliquée. Un carré Selberg fini au niveau 3 peut vérifier le nouveau raccord exact ; il ne doit pas hériter des racines du polynôme original.

Évaluer les vrais D/W uniquement pour les vertices sélectionnés où theta ou raw est non nul, plus le réciproque m1. Les axes exactement nuls gardent le kernel littéral et un terme zéro, sans profil fictif. Conserver Q original, tous les diviseurs courts, les unités et le strict a k < m. Les profils de cœurs premiers et composites, μ des deux signes, Λ(e) et les propres puissances sont distincts.

Fusionner les demandes SS et les réciproques m1/m0 par leurs valeurs physiques, puis compter chaque vertex une fois. Ne pas soustraire une capacité pour chaque e. Mesurer les coefficients et sommes réels ; ne pas fixer leurs signes à l’avance. Les autres cellules et profils non évalués restent au complément exact, sans signe extrapolé.

Falsifiers neufs : promotion SS = S entier ; crédit raw non nul pour le réciproque j = p0 ; quatre racines supposées sur les primes divisant L ; primitivité de n_e proclamée sans ses deux exclusions. Les properpowers éventuellement présents dans une classe theta nulle sont conservés ; leur absence éventuelle ne devient pas un théorème. Le contrat ne rejoue aucun ancien q, W, signe ou PASS et attend la sélection root.

## Portée, sources et ledger

Le mécanisme est orthogonal au Type II calibré du rôle 1 et apporte une majoration nouvelle sur SS. Il n’est pas un bypass de parité établi. D10 est une démonstration écrite, sans Lean 18 ; le raccord des nouvelles racines, de la division CRT et de la réciprocité serait la première cible concrète de formalisation après sélection. Les acquis A7 et 17 restent intacts.

Référence primaire supplémentaire vérifiée : [Rosser–Schoenfeld 1962](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf), PDF page index 5, page imprimée 69, Corollary 1 (3.6), domaine x > 1 pour π ; son application à Σ1/p est explicitement dérivée en D9. Le même article, PDF indices 7–8, pages imprimées 71–72, conserve θ(x) < 1.01624x pour x > 0 et (3.42) pour n ≥ 3. Les fondations de crible et le moment sont les acquis 17, avec leur source primaire [Ford, §4](https://ford126.web.illinois.edu/sieve2023.pdf), PDF indices 42–44, pages imprimées 43–45 ; aucun de ces énoncés n’est recompilé ou réexpérimenté ici.

Le ledger demeure `D_N = Bprime^a + Bpp^a + Pband>=2 + Zface>=2 + Ialpha + 2max(e,0)`. Les branches e1/c1/b1, les cœurs premiers et Λ(e), original alpha/Q/k1/wholeU_a, rawLambda_N sans μ² sur le premier axe, vrais S(bN), principal −S(N)N, longs, faces/nonbulk et erreurs restent. P5 porte sur K2/J2 bulk entier avant retraits ; aucun second NG54, P5 ou crédit de capacité n’est créé. Le global et la cible N/(256u ell) restent ouverts.

**FINAL conceptuel terminé — score 0, aucune victoire ni NoGo global.**
