# FINAL20 ROLE2 — paiement absolu d'une couche friable réelle

Statut : FINAL d'idéation, preuve papier et contrat d'expérience, **aucune compilation ou exécution mathématique20**. Aucun PASS nouveau, aucun score, aucune victoire. La prospective dans `.coordinator/messages` demeure immuable. Ce paiement concerne un sous-domaine déclaré de19 ; le raccord à tout le support source et le ledger entier ne sont pas démontrés.

## Lecture fraîche et probe

Le skill `arbor-agent-ideate` est appliqué. Lecture effective intégrale des contraintes après clôture19 : helper readonly, chunk `1f98ed`, exit0, 35 findings, 5 pruned, maxdepth2, nodes13.11/14.4 done0. `PROBE_BLOCK.md`20 a été relu intégralement. Une invocation précédente de ce même helper a échoué avant affichage sur l'encodage cp1252 (`f84b3d`, exit1) ; `-X utf8` l'a corrigée. Un affichage groupé exit0 était tronqué, d'où la lecture séparée intégrale. Aucun de ces incidents n'est un échec numérique ou Lean. Le préflight20 a été déclaré réellement PASS par root ; je ne l'ai pas exécuté et ne sélectionne rien.

Q1 First principles : **mauvais crédit de capacité et coûts de réunion incomplets**. `NonSSBracketSwitch.lean`19, `physical_product_injective` et `nonSquarefree_reciprocal_bracket_zero`, exige une union physique ; la section FINAL4 du feedback19 conserve les trois strates et ne possède pas de paiement medium/long. Le feedback numérique19 constate le même m1 partagé entre e et le réciproque triprime défavorable. Les18 FAIL Lean techniques ont été corrigées : elles ne constituent aucune preuve d'obstacle analytique.

Q2 Hidden assumption : « les ressources composées de beaucoup de petits facteurs nécessitent le même contrôle conjoint des primalités que les ressources ordinaires ». On remplace cette exigence **sur une couche explicitement friable** par un paiement absolu, dérivé de grands diviseurs réels et non d'une covariance favorable.

Q3 Elephant : le complément avec au moins un grand facteur de chaque ressource, les m1 non friables attachés à F0 privé de F1, le bridge hors ResourceCell, e1/p0/singletons, Gamma, T_A, medium/long génériques et la capacité totale restent impayés.

Q4 Hamming : **oui pour une réduction quantitative nouvelle de tous rangs, non pour une victoire**. L'expérience doit atteindre la somme Euler et les vrais brackets, avec coût de chaque +1 et de chaque réciproque F1 unique ; un simple certificat de préfixe ne suffirait pas.

Les quatre mouvements : inversion de l'hypothèse de crible conjoint ; remontée depuis un retrait exceptionnel réellement payé ; transfert du certificat de préfixe multiset et de Rankin-Euler ; rétro-ingénierie des répétitions, des non-unités, des +1 et des ressources partagées du banc19. Sont écartés : nouveau Gram générique, calibrage19 déjà acquis, incidence libre et borne du reste prise en prémisse. Le survivant est à profondeur2 et forme une expérience de paiement friable, pas un réglage de constante.

Scratch : hypothèse attaquée = tout grand rang doit passer par le même switch D/P ; classe = majorant multiplicatif sur grands diviseurs réels ; chaîne = le cap fournit une grande ressource, sa friabilité fournit un grand diviseur, le tail Euler paie à la fois la masse et les fronts ; orthogonalité = aucune subtraction Selberg de quotient premier, ni racine/CRT/H8/calibration réexécutée ; conflit [1.2] = la couverture générique est1, ici seule la contrainte effective P+(n)<=Y ET n>=D reçoit un petit coût. Auto-filtre : ce mécanisme ne se réduit ni à un nombre, ni à « davantage de crible », ni à une hypothèse de disponibilité.

Mechanism: Retrait absolu de la couche de ressources entièrement friables par préfixe multiset à D=ceil(sqrt N), réunion des classes réelles et paiement Euler-Rankin des fronts et réciproques F1 physiques uniques.
Hypothesis: Le cap e*q+Q+1<=N et e>p0 forcent les ressources>=M>=D ; leurs grands diviseurs friables ont une masse et un cardinal assez petits, dérivés de véritables produits Euler, pour un paiement au source u>=10^24, sans hypothèse de petite demande ou de capacité.
Observable: N=10^8, tous les1001 q de1800100 à1801100 avant masks, Ysource=1 distinct de Ytest=4096, certificats/classes/+1/true theta et raw, Euler fini complet et union unique m1 ; la cible formelle est F1–F4 calculée sur les objets19 réels.
Conflicts: La couverture1 de[1.2] n'est pas promue en gain ; répétitions, non-unités, rawproperpowers, F0 privé de F1 réciproque, support source absent et autres coûts du ledger restent explicites, aucune disponibilité/Hall ni signe favorable ajouté.

## Objets importés et domaine couvert

Utiliser les fichiers **du Juge19**, en lecture seule, `NonSSBracketSwitch`, `BalancedResourceSwitch`, `SignedHyperbolicCRT`, `TerminalPrimeExtraction` et leurs dépendances auditées18/16/13. Ne pas reconstruire les anciennes preuves. Les définitions réelles sont :

    H = GoldbachRound19.NonSS.physicalDomain alpha N Z M
    resource1 N q = N-q
    resource0 N q = N-(anchor N)*q
    p0 = anchor N = leastMissingOddPrime N
    Q = (N-1)/alpha

`StructuralSupport` exige ResourceCell composite pour les deux ressources, q premier/unitaire, q>=M, e>p0, Squarefree e, e unitaire, e*q+Q+1<=N et le sélecteur nonSS. Rien ici ne transforme ce domaine déclaré en tout S privé de SS. Le bridge source reste un théorème distinct à construire ; son absence est un résultat de périmètre, pas une nouvelle prémisse silencieuse.

Les paramètres source demeurent alpha=ceil N^(1/4), a=ceil N^(7/16), M=ceil N^(3/4), Z=floor N^(1/4), u=log N, ell=log u et **u>=10^24**. Poser E=floor((N-Q-1)/M). Le cap implique e<=E<=N^(1/4), donc 1<e<=a, e<=Q, a<q et q>p0 au source. Les inégalités entières/floors doivent être prouvées à partir de ces paramètres ; un module générique peut d'abord les exposer comme gardes géométriques indépendantes.

Le vrai coefficient est celui de19 :

    C(e,q) = -mu(e*q) * [physicalDivisorKernel Q a (e*q) (N-e*q) N
                         - harmonicKernel Q a N (N-e*q) (e*q)].

Le raccord cofacteur donne C(e,q)=Lambda(e)-mu(e)*W, avec **W=harmonicKernel**, signe original log(k/m). Pour construire ce raccord sans nouvelle dépendance10 non auditée, utiliser `physical_short_divisor_complement_source`, déjà importé, et établir shortDivisorSum a(e*q)=-Lambda(e) : les diviseurs <=a sont exactement ceux de e lorsque e<=a<q ; e*q est SF composé, Lambda(e*q)=0 et mu(e*q)=-mu(e). Le point N-e*q est positif/unitaire parce que e*q est unitaire et <N ; sa primalité n'est pas requise. La même dérivation vaut pour le vrai rawBracket, y compris premier axe properpower.

Définir Smooth_Y(n) par n appartenant à `Nat.smoothNumbers (Y+1)` : la convention mathlib est **facteurs premiers strictement <Y+1**, donc <=Y, n>0. Ne pas utiliser une liste de facteurs distincts pour le préfixe. Définir F1(q)=Smooth_Y(N-q), F0(q)=Smooth_Y(N-p0*q), F(q)=F0(q) ou F1(q). Les filtrages F restent à l'intérieur de H ; un majorant positif pourra seulement agrandir le domaine.

## Garde de taille et certificat effectif

Le cap, e>=p0+1 et p0>=3 donnent exactement

    N-p0*q >= (e-p0)*q+Q+1 >= q+Q+1 >= M,
    N-q >= (e-1)*q+Q+1 >= 3*q+Q+1 >= M.

Ainsi les deux ressources dépassent D=ceil sqrt N. **Cconducteur<N ne fournit pas cette garde**. Toute extension sans le cap/e>p0 conserve explicitement ses ressources<D en complément.

Fixer

    T=u/(128*ell), Y=floor(exp T), sigma=1/log Y, D=ceil sqrt N.

Au source : ell>=6, log Y>=4, 0<sigma<=1/4, log Y<=u/(128ell), Y<=N^(1/128)<=Z et D<=2N^(1/2). Par exemple log u<=sqrt u pour u>=1 donne T>=sqrt u/128>8 ; floor(exp T)>=exp T/2 donne log Y>=T-log2>=T/2>=4. Toutes les constantes sont effectives au **seuil10^24**, sans nouvel onset10^40. Ces gardes ne sont pas utilisées à N=10^8.

Si n>=D est Y-friable, prendre le premier préfixe de `n.primeFactorsList` dont le produit atteint D. Son produit d divise n ; le précédent produit est<D et le dernier facteur<=Y, d'où

    d|n, D<=d<D*Y, Smooth_Y(d).

Facteurs répétés et gcd(d,n/d)>1 sont permis. Pour le majorant poser B_D={d : D<=d<=D*Y, Smooth_Y(d)}, ensemble fini d'entiers physiques. Le préfixe est canonique, mais l'union supérieure de tous les d possibles ne crée aucune nouvelle ressource par certificat.

## F1 : vraie somme Euler, sans petite somme prise en prémisse

Écrire P_Y={p premier : p<=Y} et

    Eplus = product_(p in P_Y) (1-p^(-(1-sigma)))^(-1),
    Eminus= product_(p in P_Y) (1-p^(-(1+sigma)))^(-1).

Les expansions géométriques donnent des **sommes réelles sur tous les entiers friables**, non des coefficients libres :

    sum_(n>=1, Smooth_Y(n)) n^(sigma-1) = Eplus,
    sum_(n>=1, Smooth_Y(n)) tau(n)*n^(sigma-1) = Eplus^2,
    sum_(n>=1, Smooth_Y(n)) n^(-1-sigma) = Eminus.

Pour Eplus le s=1-sigma est<1 : **ne jamais supposer la sommabilité sur tous les naturels**. Seule la sommabilité sur les entiers ayant leurs facteurs dans le fini P_Y est vraie. Pour chaque p, la série géométrique converge ; pour tau, tau(p^k)=k+1 et la série pondérée vaut (1-t)^(-2).

La nouvelle version élémentaire enlève l'ingrédient prime-harmonique écrit D9_18 de la prospective. Puisque p^sigma<=exp1<3 et 0<t<1 donne t<=-log(1-t),

    sum_(p in P_Y) 1/p <= 3 sum_(p in P_Y) p^(-1-sigma)
                          <= 3 log Eminus.

Or Eminus est une sous-série positive de sum_(n>=1)n^(-1-sigma). La comparaison intégrale élémentaire, sigma>0, donne

    sum_(n>=1) n^(-1-sigma) <= 1+integral_1^infinity x^(-1-sigma)dx
                            =1+1/sigma=1+log Y,
    sum_(p in P_Y)1/p <=3 log(1+log Y)<=3ell,

car 1+log Y<=u au source. Aucun PNT, Mertens, BV ou constante asymptotique n'intervient.

Pour t=p^(-(1-sigma)), sigma<=1/4 implique t<=2^(-3/4)<2/3 et -log(1-t)<=3t. Comme p^sigma<3,

    log Eplus <=9 sum_(p in P_Y)1/p <=27ell,
    Eplus<=u^27.

Le tail Rankin est D^(-sigma)<=exp[-u/(2log Y)]<=u^(-64). Par les vraies sommes ci-dessus,

    S_D=sum_(d in B_D)1/d <= D^(-sigma)*Eplus <=u^(-37),
    card B_D <=D*Y*S_D<=D*Y/u^37.                 (F1)

La petite somme S_D est **conclue**, jamais un champ libre. La variante plus forte de la prospective, S_D<=u^-46 et Eplus<=u^18, reste seulement la variante sous le D9_18 écrit sum1/p<=2ell ; elle n'est pas nécessaire au FINAL20. Les exposants de F2–F4 ci-dessous emploient uniquement la version3ell dérivée.

## Classes effectives, incompatibilités et deux +1

Pour chaque e>=1, garder l'intervalle réel J_e=Icc M floor((N-Q-1)/e). Il peut être vide. Sa différence d'endpoints est <=N/e.

Pour resource1, d|N-q est q≡N mod d ; cardinal dans J_e <=N/(e*d)+1. Pour resource0, d|N-p0*q est p0*q≡N mod d. La condition de solvabilité est gcd(p0,d)|N ; p0 premier absent de N impose zéro exact lorsque p0|d. Si p0 ne divise pas d, il existe une unique classe modulo d, même majorant **avec +1**.

Sur les q unitaires à N, les d non unitaires à N donnent zéro exact : dans une classe admissible, une prime commune à d et N diviserait q (p0 est unitaire à N). Ils peuvent rester dans la réunion supérieure positive B_D, mais ne portent aucune incidence active et ne donnent aucun crédit de densité. Aucun inverse modulaire d'un non-unitaire n'est introduit.

Préfixe puis union donne, j=0,1,

    card{q in J_e, gardesH : Fj(q)}
      <= sum_(d in B_D)[N/(e*d)+1]
      <=(N/e+D*Y)/u^37.

La réunion F0 ou F1 reçoit au plus deux fois ce majorant. L'intersection peut être surmajorée positivement ; elle n'est jamais deux capacités. La formule AP porte (L-1)/d+1 si L est le cardinal d'un intervalle non vide ; on ne remplace pas ce +1 par une longueur favorable. Toutes les strates et tous les rangs de H sont présents.

## Totients et vrai kernel : dérivation élémentaire à formaliser

La somme de totients écrite10 peut être reconstruite sous Lean sans hypothèse analytique. Pour n>=1, l'identité multiplicative finie donne

    n/phi(n)=sum_(d|n, Squarefree d)1/phi(d).

Elle suit de l'Euler exact de phi et du développement produit des facteurs premiers : localement 1+1/(p-1)=p/(p-1). La somme finie des termes SF <=X satisfait

    sum_(d<=X, SF d)1/(d*phi(d))
      <=product_(p<=X, prime)[1+1/(p*(p-1))]
      <=exp(sum_(p<=X, prime)1/(p*(p-1)))
      <=exp(sum_(j=2..X)1/(j*(j-1)))<=exp1<3.

La dernière somme télescope exactement en 1-1/X pour X>=2 ; X=1 séparé. Puis échange des deux sommes finies et H_floor(X/d)<=1+log X :

    sum_(n=1..X)1/phi(n)
      =sum_(d<=X, SF d)[1/(d*phi(d))]*H_floor(X/d)
      <=3(1+log X).                               (TK)

Ce sont des identités/bornes numériques indépendantes du support Goldbach, pas un coût cible pris en prémisse. La preuve formelle de TK reste à faire ; si l'exécuteur la laisse comme hypothèse explicitement indépendante, sa conclusion doit porter « conditionnelle sous TK non raccordé », sans crédit de paiement Lean au source.

Dans le vrai harmonicKernel, k>=1 et a*k<m<=N impliquent k<m, donc |log(k/m)|<=u. Avec |mu k|<=1, TK permet de retirer les masques uniquement dans le majorant absolu :

    |W|<=u sum_(k<=N)1/phi(k)<=3u(1+u)<=6u^2.

Le raccord physique donne |C(e,q)|<=Lambda(e)+|W|<=7u^2. La theta et la **rawLambda_N** véritables sur 1<=n<=N sont <=u, via `vonMangoldt_le_log`; l'indicatrice primeIncidence(q) est<=1. Ainsi

    |thetaBracket alpha a N e q|<=7u^3,
    |rawBracket alpha a N e q|<=7u^3.

Le masque mu(n)^2 n'est jamais introduit au premier axe raw. Une preuve obtenue seulement en remplaçant raw par theta n'est pas acceptée.

## F2 : paiement des demandes à tous les rangs

Noter T_F soit la somme des modules du thetaBracket réel sur H avec F, soit la somme des modules du rawBracket réel sur le même domaine. La variante theta majore aussi la demande positive et permet de payer le retrait absolu de l'union. Ce sont deux variantes alternatives d'une partition du ledger, pas deux paiements ajoutés. Agrandir positivement e en tous les entiers1..E donne

    T_F <=14u^3/u^37 * [N*H_E+E*D*Y]
        <=7N/u^33+28N^(97/128)/u^34.              (F2)

Ici H_E<=1+log E<=u/2, E<=N^(1/4), D<=2N^(1/2) et Y<=N^(1/128). Le second terme est précisément **la somme de tous les fronts +1**. Les strates courte/medium/longue sélectionnées, les e composites et les répétitions des ressources sont incluses ; il n'y a pas de restriction de rang implicite.

Employer F2theta avec Bpp original conservé, ou une partition raw qui retire la même sous-famille properpower de Bpp avant de la payer une fois. La somme de leurs deux bornes ne doit pas devenir un retrait double dans D_N.

## F3 : réciproques F1 physiques une fois ; complément F0\F1 conservé

Soit Q_F1 l'image en q de H filtré F1 : les e sont fusionnés avant consommation. Le q->m1=N-q est injectif et m1>=M. Sur le véritable sourceBracket(q,m1),

    |physicalDivisorKernel Q a m1 q N|<=u*tau(m1),
    |sourceBracket alpha a N q m1|
      <=u^2*tau(m1)+6u^3<=7u^3*tau(m1).

Le raw premier axe y coïncide avec theta parce que q est effectivement premier. Les m1 non SF ont un bracket exactement nul par19, mais demeurent dans le majorant positif de tau ; les m1 triprimes sont payés en module, aucun signe de capacité n'est revendiqué.

La vraie identité Euler de tau fournit

    sum_(M<=m<=N, Smooth_Y(m)) tau(m)
      <=N*M^(-sigma)*Eplus^2
      <=N*u^(-96)*u^54=N/u^42,
    U_F1=sum_(q in Q_F1) |sourceBracket(q,N-q)|<=7N/u^39.   (F3)

La première inégalité est terme à terme : tau(m)<=N*M^-sigma*tau(m)*m^(sigma-1), car m<=N et m>=M. Aucun profil tau libre n'est substitué à `m.divisors.card`. Le réciproque m0 a premier axe p0*q, produit de premiers distincts ; `reciprocal0_raw_zero`/`reciprocal0_theta_zero`19 le rendent nul.

**F0 privé de F1 :** F2 paie ses demandes seulement. Le m1=N-q non friable correspondant n'est pas couvert par F3 et reste dans la capacité/ledger original. Un poids tau(N-q) corrélé à la friabilité de N-p0q ne suit pas de l'Euler univarié ; aucune suppression de ces fibres entières n'est annoncée. Pour les intersections entre demande et réciproque, retirer l'union des vertices une fois ; T_F+U_F1 reste une surmajoration positive du coût absolu de cette union.

## F4 : budget source et absence de victoire

À partir des sommes effectives et des kernels précédents,

    T_F+U_F1<=7N/u^33+28N^(97/128)/u^34+7N/u^39
             <=9N/u^33<=N/(8192*u*ell), u>=10^24.       (F4)

En effet N^(-31/128)<=1 et u>=28 paient le deuxième terme par N/u^33 ; u^6>=7 paie le troisième de même. Enfin ell<=u et u^31>=9*8192 donnent le dernier pas. Aucun petit agrégat/S_D/Gamma/disponibilité n'est une hypothèse de F4 : les seules entrées sont les identités physiques et les inégalités élémentaires détaillées, à formaliser.

Le reste des demandes de H a r1>Y ET r0>Y, mais ceci **ne borne pas Omega** : un grand facteur peut coexister avec de nombreux petits. Le reste entier, les m1 non friables de F0\F1, le source hors H, e1/p0/singletons, autres faces/nonbulk, Gamma/T_A, medium/long génériques, BV/onsets et la capacité totale restent distincts et impayés.

Ledger inchangé : D_N=Bprime^a+Bpp^a+Pband>=2+Zface>=2+Ialpha+2max(e,0). Le paiement est une sous-majoration à insérer dans une partition exacte de ces objets ; il ne s'ajoute pas à Iglobal comme un nouveau bénéfice. P5 porte le bloc K2/J2 entier avant retrait exact, U4 reste une alternative sans double NG54, A7 et les vrais S(bN), -S(N)N, wholeU_a, Q/k1 sont conservés. **Même F4 compilé serait un ingrédient auxiliaire, pas le contournement complet de parité demandé.**

## Faisabilité Lean : nouvelles cibles substantielles et bibliothèques lues

Modules nouveaux proposés après gate numérique root :

1. `FriablePhysicalPrefix.lean` : `resource_ge_M_of_actual_cap`, `primeFactorsList_prefix_divisor`, `actual_nonSS_friable_cover` sur H19, d|n/D<=d<DY/friabilité ; classes affines exactes avec non-unités p0/N et fronts entiers conservés. Aucun nouveau CRT général19.
2. `FriableEulerRankin.lean` : vraie somme friable géométrique et tau, `prime_reciprocal_le_three_log_one_add_log`, `smooth_divisor_inverse_tail`, `smooth_tau_tail`. Les conclusions portent les Finset/séries réelles ; aucune prémisse « S_D petit ». La sommabilité géométrique n'est requise que sur le support fini de premiers pour Eplus. Construire la comparaison p-série de Eminus au lieu de supposer la borne harmonique D9_18.
3. `FriableKernelEnvelope.lean` : identité Euler de phi, `totient_inverse_sum_le_three_one_add_log` TK, puis absolu du harmonicKernel et des deux brackets réels ; le court cofacteur est dérivé des imports source en gardant toutes les unités et le raw propre.
4. `FriablePhysicalPayment.lean` : `actual_friable_demand_payment` F2, `unique_friable_reciprocal_payment` F3, puis `actual_friable_source_budget` F4 avec wrapper de paramètres source/floors/logs. Les ensembles de vertices sont des images finies, pas une capacité par e.

APIs **effectivement lues**, disponibles dans le cache mathlib9837ca9 :

* `Mathlib.NumberTheory.SmoothNumbers` : `Nat.equivProdNatFactoredNumbers`, `Nat.equivProdNatSmoothNumbers`, `Nat.mem_factoredNumbers_of_dvd`, `Nat.mem_smoothNumbers_of_dvd`, produit effectif de primeFactorsList.
* `EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum` et `..._geometric` : support fini et séries locales seulement. Le lemme `prod_filter_prime_geometric_eq_tsum_factoredNumbers` exige une sommabilité globale qui serait fausse pour sigma-1 ; **ne pas l'utiliser pour Eplus**.
* `ArithmeticFunction.sigma_zero_apply`, `sigma_zero_apply_prime_pow`, `isMultiplicative_sigma`, `Nat.Coprime.card_divisors_mul` et `hasSum_choose_mul_geometric_of_norm_lt_one` avec k=1 donnent les vrais poids tau(p^j)=j+1, sans hypothèse de poids libre.
* `Nat.totient_eq_mul_prod_factors`, `Nat.totient_prime_pow_succ`, `ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree`, `harmonic_le_one_add_log` permettent l'identité de TK et son majorant. L'Euler SF fini et le télescopage doivent être écrits : aucun lemme totient prêt à l'emploi n'a été trouvé/proclamé.
* `summable_nat_rpow`, `AntitoneOn.sum_le_integral_Ico` (utilisé par Harmonic/Bounds), `intervalIntegral.integral_rpow` permettent la p-série <=1+1/sigma. La constante de l'intégrale infinie peut aussi être conclue par les sommes partielles et limite, sans ζ analytique.
* `ArithmeticFunction.vonMangoldt_le_log`, `abs_moebius_le_one`, `Real.mul_rpow`, `Real.rpow_mul`, `Real.log_mul` assurent les majorations réelles et les produits.

La charge formelle est réelle : sommes sur sous-types, factorisations avec multiplicité, majorants des séries, casts Nat/Real, sommes finies phi et wrapper de seuil source. La proposition est mathématiquement élémentaire ; aucun de ces nouveaux théorèmes n'est prétendu compilé. Si un raccord analytique indépendant est exposé provisoirement comme champ, il doit être nommé littéralement (`TotientSumBound`, `PrimeReciprocalBound`, géométrie source) et son absence indiquée. La version principale demande de **dériver** les deux premiers ; remplacer F4 par une petite somme libre ne satisfait pas ce rôle.

## Contrat Python neuf strict

Le contrat complet, sans producteur exécuté, est dans `role2/numeric_contract.md`. La fenêtre est tous les1001 entiers q de1800100 à1801100, N=10^8, alpha100/Q999999/a3163/M1000000/Z100/p0=3/D10000. Ysource=1 et ses gardes fausses sont certifiés séparément de Ytest=4096. Les e SF/unité sous le cap sont énumérés sans filtre premier sur N-eq. Tous les q nonpremiers/nonunités, axes nuls et familles vides sont conservés avant le domaine H.

Le banc contrôle les préfixes de vrais multisets, les classes/gcd et les +1, les vrais D/W/theta/raw nouveaux sur les vertices actifs, les strates et l'union m1. Il ne réexécute pas les anciens PASS ni leurs kernels. Une annexe Euler petite mais exhaustive contrôle les exposants, leurs produits et tau, avec quatrième-racines certifiées rationnellement, puis le Rankin sur un ensemble complet d'entiers. Elle n'est pas vendue comme une énumération complète de B_D à Ytest4096 ni une preuve du budget asymptotique. Zérofloat et zéro décision par intervalle contenant0 ; logs en coefficients exacts avant intervalles rationnels.

FINAL rôle2 : paiement partiel concret au source initial sur le sous-domaine friable de H19, avec tous les fronts et réciproques F1 uniques. Complément et bridge source ouverts, aucune victoire ni sélection20.
