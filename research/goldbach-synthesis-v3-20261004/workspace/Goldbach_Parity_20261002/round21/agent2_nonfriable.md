# FINAL21 ROLE2 — réciproques non friables payées par moment global de diviseurs

Statut : proposition d'idéation et preuve papier, zéro compilation Lean, zéro calcul mathématique Python, zéro PASS nouveau et aucune victoire. Ce résultat proposé paie une dette précise de14.5. Il n'est ni une estimation du complément où les deux ressources ne sont pas friables, ni un raccord de H19 à la frontière source entière, ni une preuve du ledger de D_N.

## Lecture fraîche et choix de mécanisme

Les quatre documents demandés ont été lus intégralement : PROBE21, feedback20 root, FINAL5 réellement clos et retour logique20. Les sources Prefix/Payment/Demand/Aggregation/SourceBudget20 et NonSSBracketSwitch19 ont été lues intégralement ; SourceGeometry20 et deux fichiers mathlib sont lus aux plages déclarées dans le reçu. Le helper readonly `arbor_state.py view --cwd B --run-name parity --format constraints` a réellement terminé exit0, observation `e6bb4f`, sortie intégralement lue :37 findings,5 pruned,maxdepth2. Cette vue précède le présent IDEATE. Aucun noeud n'est créé ou sélectionné par ROLE2.

Q1 First principles : **mauvais raisonnement sur une rareté correcte et mauvaise unité de consommation**. FINAL5 et feedback20 section2 établissent que F0 privé de F1 laisse les réciproques `sourceBracket(q,N-q)` impayées ; F3 possède seulement l'image F1 unique. L'exemple enregistré `N-q=98199843=3*7*509*9187` est non friable dans cette couche. Les étiquettes e de H partagent un même q, ce qui impose de projeter avant toute inégalité. Ces deux faits sont les preuves du goulot ; les22 FAIL Lean techniques ne sont pas des erreurs analytiques.

Q2 Hidden assumption : « pour payer tau(N-q) sur F0, il faut établir sa corrélation favorable avec la friabilité de N-p0*q ». On abandonne cette exigence : une norme globale de tau indépendante de F0, combinée à la rareté effective de F0, suffit. Le moment global est dérivé arithmétiquement ; il n'est pas ajouté en prémisse.

Q3 Elephant : la réunion du complément non friable, ses vrais W, les parents, Gamma/T_A, medium/long, le support source absent et les six postes D_N restent ouverts. Le paiement proposé ne prétend pas fournir une capacité positive ou une disponibilité première.

Q4 Hamming : **oui pour une dette source nécessaire et précisément identifiée**. Le nouveau résultat visé porte sur les vrais réciproques non friables de F0 privé de F1, sous le seul onset fixé ; une identité générique de Cauchy ne suffirait pas sans la projection et les deux majorants dérivés.

Les quatre mouvements sont utilisés : inversion de l'exigence d'une corrélation conditionnelle ; remontée depuis un retrait F0 dont le réciproque manque ; transfert de la méthode petit support × moment global et de l'injection de paires de diviseurs dans quatre facteurs ; rétro-ingénierie de l'exemple non friable, des e répétés, et des fronts AP +1.

### Cinq candidats et auto-filtre

1. **Petit support physique × second moment global de tau — retenu.** Hypothèse attaquée : une borne conditionnelle de tau serait nécessaire. Classe : majorant de moment arithmétique indépendant sur une projection physique. Chaîne : les q de F0 privé de F1 sont peu nombreux par le certificat20 ; le second moment de tau sur tous1..N contrôle même les réciproques atypiques ; succès observable = somme réelle des ABS et borne source nouvelle sans corrélation libre. Orthogonalité :14.5 utilise un Euler sur m1 friable, ici m1 reste non friable ;14.4 réindexe de grands facteurs sans les payer, ici tous leurs rangs restent dans tau. Conflits :[1.2] couverture1 n'est pas promue ;[13.2] aucun flot/disponibilité n'est supposé. Survit : mécanisme concret, pas un réglage d'exposant.

2. **Double progression des diviseurs de m0 et m1 — écarté dans cette itération.** Hypothèse attaquée : les deux ressources seraient indépendantes. Classe : comptage corrélé CRT. Chaîne : `p0*m1-m0=(p0-1)*N` contraint le pgcd des diviseurs ; un comptage des vraies classes pourrait contrôler tau. Orthogonalité : remplacerait univarié14.5 par deux congruences. Conflits :les fronts sont impératifs. Le front brut de la somme d>=D jusqu'à D*Y et h<=sqrtN est de taille pouvant dépasser N par la perte Y ; aucun paiement effectif nouveau de ce front n'est démontré. Ne pas le cacher dans un reste libre.

3. **Annulation alternée pointwise dans U_a — écarté.** Hypothèse attaquée : toute somme tronquée de diviseurs serait uniformément petite. Classe : combinatoire signée de sous-ensembles. Chaîne : exploiter directement les mu(d) de la vraie coupure. Orthogonalité :éviterait tau, sans moment. Conflits :wholeU_a et la coupure doivent demeurer. Avec beaucoup de facteurs premiers proches et une coupure à un nombre fixé de facteurs, les sommes binomiales alternées peuvent être grandes ; aucune borne O(u^2) générale n'est fournie. Ce candidat replacerait la dette dans une prémisse pointwise injustifiée.

4. **Buchstab conjoint sur le plus grand facteur des deux ressources — écarté comme étape21 immédiate.** Hypothèse attaquée :P+>Y imposerait peu de facteurs. Classe : décomposition par grand premier. Chaîne : conserver l'ensemble des petits facteurs et toutes les répétitions, puis estimer les incidences terminales. Orthogonalité :complément au lieu de couche exceptionnelle. Conflits :14.4 possède déjà l'extraction et ses longs ; il manque une information première quantitative. Une nouvelle identité d'extraction seule redériverait14.4 et n'apporterait aucun paiement.

5. **Affectation d'un réciproque à un parent disponible — écarté.** Hypothèse attaquée :une ressource peut servir à chaque étiquette e. Classe : flot de capacité sur union de vertices. Chaîne :une affectation unique pourrait payer le complément si les parents et leurs W fournissaient réellement la capacité. Orthogonalité :contrôle combinatoire au lieu de moment. Conflits :[13.2] et les manques Hall/capacité des boucles14–19. Aucun parent favorable ou condition Hall n'est obtenu ; l'introduire en prémisse serait précisément le crédit manquant.

Le candidat1 attaque donc une classe distincte et concrète. Il ne change ni seuil, ni poids acquis, ni cutoffs ; il ajoute une information quantitative sur un objet explicitement impayé.

Mechanism: Projection des q physiques uniques de F0 privé de F1, puis paiement absolu du vrai réciproque non friable par Cauchy–Schwarz et second moment global de tau dérivé par injection de diviseurs dans quatre facteurs.
Hypothesis: La rareté F0 déjà obtenue avec ses fronts +1 donne card<=3*N*u^-37, tandis que la somme globale réelle de tau² est<=N*H_N³<=8*N*u³ ; leur combinaison paie les m1 non friables sans hypothèse de covariance, disponibilité ou borne Omega.
Observable: Nouvelle fenêtre entière q=2100100..2101100 à N=10^8, projection avant consommation, moment global entier exact, réciproques réels D/W/wholeUa/Q, sourceguardsFALSE et Ytest4096 distinct du source ; cible Lean source uniqueF0notF1Cost<=35*N*u^-14 puis coût friable étendu<=N/(8192*u*ell).
Conflicts: Les leçons[1.2]/[13.2] sont respectées par un paiement ABS dérivé sans couverture gagnante ni flot supposé ; les répétitions, non-unités, fronts, PP et intersections restent présentes, complément/sourcebridge/parents/Gamma/T_A/fullledger restent impayés et WIN=false.

## 1. Projection exacte avant le moment

Importer les oleans du Juge20 et les dépendances historiques en lecture seule. Les notations sont exactement celles19/20 :

    H = physicalDomain alpha N Z M
    F0(q) = Smooth Y (resource0 N q),  resource0 N q = N-anchor N*q
    F1(q) = Smooth Y (resource1 N q),  resource1 N q = N-q.

Définir les nouvelles étiquettes et leur image :

    L0minus1 = H.filter(fun v => F0(v.2) AND NOT F1(v.2))
    Q0minus1 = L0minus1.image Prod.snd
    Q01 = friableDemandDomain alpha N Z M Y |> image Prod.snd.

La projection fusionne tous les e. Pour tout q dans Q0minus1 il existe e avec StructuralSupport réel, F0 et nonF1. Il en résulte q premier/unitaire, M<=q<N, m1=N-q>=M>0 et m1<=N. L'application q->m1 est injective sur cet ensemble, par soustraction entière sous q<N. L'image Q0minus1 est disjointe de friableQ1 ; la partition exacte est `Q01=friableQ1 ∪ Q0minus1`. Ce sont des images physiques, pas une somme de cardinalités par rang.

La couche nonSquarefree de m1 conserve ses éléments dans Q0minus1 et dans le moment, même si son bracket réel est nul par l'acquis19. Aucun filtre Squarefree m1, triprime, signe de mu, Prime(N-eq) ou seuil de conducteur ne remplace le domaine déclaré.

## 2. Rareté unique avec les fronts déjà acquis

Le certificat20 `actual_friable_resource0_cover` fournit à chaque q un vrai d de `divisorBand D Y` divisant m0. Il garde primeFactorsList avec répétitions, D<=d<D*Y et les diviseurs nonSF. Le même q peut avoir plusieurs certificats, mais l'union est seulement une surmajoration positive du cardinal de l'image physique.

Pour chaque d, considérer **Q0minus1** filtré par d|m0. Les ressources de chaque q proviennent d'un témoin StructuralSupport, éventuellement avec un e différent. Les classes de m0 dépendent de q et d, pas de e : l'acquis `resource0_divisor_class` donne p0*q congru N mod d. Un témoin non vide fournit `(anchor N).Coprime d` via `anchor_resource0_coprime`, donc les q sont dans une seule classe modulo d. Les non-unités p0|d et (d,N)>1 gardent une classe vide exacte, sans inverse interdit. Utiliser l'intervalle agrandi `[M,N]` et le lemme acquis `finite_interval_congruence_card_le_real` :

    card{q in Q0minus1 : d|m0} <= N/d+1.

L'élargissement est positif et n'efface aucun front. Aucune somme sur e n'apparaît ; aucun crédit card(H)=card(image q) n'est pris. Ainsi, avec la vraie somme S_D,

    card Q0minus1 <= N*S_D + card(divisorBand D Y)
                   <= (N+D*Y)*S_D.

Au source, `actual_source_divisor_band_mass` déjà prouvé donne S_D<=u^-37. `sourceEupper>=1` et `source_rank_front_le_two_N` donnent D*Y<=Eupper*D*Y<=2N. D'où le **nouveau raccord de projection** :

    card Q0minus1 <= 3*N*u^-37.                         (R1)

On ne re-prouve ni Euler/Rankin, ni sourceGeometry, ni la borne20 ; ce sont des imports. La nouveauté est leur application à l'image q unique avec des témoins e variables et à un réciproque non friable.

## 3. Second moment global effectivement dérivé

Poser tau(n)=n.divisors.card comme20, sans restriction de facteurs. Poser d4(n) le nombre de quadruplets ordonnés strictement positifs `(a,b,c,d)` avec a*b*c*d=n. Cette fonction n'est pas un profil libre.

Pour chaque paire de diviseurs `(r,s)` de n>0, écrire

    g=gcd(r,s), x=r/g, y=s/g, z=n/lcm(r,s).

Le ppcm divise n ; g,x,y,z sont positifs et g*x*y*z=n. L'application est injective, car r=g*x et s=g*y sont reconstruits depuis ses trois premières coordonnées. Aucune coprimalité entre les facteurs de n, aucune squarefreeness et aucune limitation de Omega n'est imposée. On obtient

    tau(n)^2 <= d4(n).

Ensuite compter tous les quadruplets de produit<=N, en sommant les trois premières coordonnées :

    sum_(n=1..N) d4(n)
      = sum_(a=1..N) sum_(b=1..N) sum_(c=1..N) floor(N/(a*b*c))
      <= N * (sum_(a=1..N) 1/a)^3 = N*H_N^3.

Les tuples dont a*b*c>N contribuent0. Le floor des multiples est exact sur1..N ; ce comptage ne remplace pas les +1 de l'intervalle affine R1. L'inégalité floor<=quotient, les casts et les trois sommes finies suffisent. N=0 donne un ensemble vide ; on peut aussi déclarer 0<N pour la forme harmonique. D'où

    sum_(n=1..N) tau(n)^2 <= N*H_N^3.                  (R2)

Le lemme acquis mathlib `harmonic_le_one_add_log` donne H_N<=1+u ; pour u>=1, H_N³<=8u³. **R2 doit être prouvé dans un nouveau module**, et non transmis comme `MomentBound` libre. L'injection gcd/ppcm est une voie de preuve élémentaire ; la convolution ζ^4 et les facteurs locaux `(k+1)^2<=choose(k+3,3)` constituent une seconde voie possible si elle réduit la charge de formalisation.

La littérature du moment de diviseurs confirme la classe de résultat : le texte de recherche de Tao rapporte la croissance moyenne logarithmique cubique de d(n)². Aucun asymptotique ou constante de ce texte n'est utilisé ici ; R2 est dérivé ci-dessus avec une constante explicite. [Tao, What's New](https://terrytao.wordpress.com/wp-content/uploads/2009/01/whatsnew.pdf). Les définitions publiques de ζ et de la convolution sont documentées par [mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction/Zeta.html), mais les API réellement disponibles sont celles du cache4.15 lu localement.

## 4. Cauchy physique et vrai coût réciproque

L'injection q->N-q, m1 dans1..N, et la nonnégativité donnent

    sum_(q in Q0minus1) tau(N-q)^2
      <= sum_(n=1..N) tau(n)^2 <=8*N*u³.

La version finie de Cauchy dans le cache est `Finset.sum_mul_sq_le_sq_mul_sq`, avec f(q)=1 et g(q)=tau(N-q). Elle donne, après R1 et R2,

    (sum_(q in Q0minus1) tau(N-q))² <=24*N²*u^-34.

La somme est positive ; `(5*N*u^-17)²=25*N²*u^-34`. Une comparaison de carrés positifs, ou `nlinarith` avec les puissances réelles exposées, conclut

    sum_(q in Q0minus1) tau(N-q) <=5*N*u^-17.           (R3)

Le véritable `sourceBracket alpha a N q (N-q)` contient le signe mu, physicalDivisorKernel avec Q original et `a*k<m`, le vrai harmonicKernel W avec unité de k, et theta(q). L'acquis20 `actual_sourceBracket_abs_le_seven_tau` s'applique à q<=N, 0<m1<=N et a>=1 :

    |sourceBracket(q,N-q)|<=7*u³*tau(N-q).

On ne remplace pas W par un modèle ni U_a par un préfixe incomplet. Définir

    uniqueF0notF1Cost = sum_(q in Q0minus1) |sourceBracket(q,N-q)|.

La combinaison donne le paiement source réellement neuf à formaliser :

    uniqueF0notF1Cost <=35*N*u^-14.                     (R4)

q est effectivement premier/unitaire sur le support, donc le premier axe raw du réciproque coïncide avec theta(q). Les properpowers ne sont jamais annulées sur les demandes `N-eq` ; cette proposition prolonge le paiement **theta**20 et conserve le poste Bpp acquis payé une fois. Elle ne crée aucune nouvelle somme raw globale.

## 5. Coût étendu et union des vertices

Définir `sourceExtendedFriableCost = sourceFriableAbsoluteCost + uniqueF0notF1Cost`, avec les paramètres source20 exacts. La partition disjointe Q01 ci-dessus identifie le coût réciproque total F0∨F1 à la somme de F1 importée et du nouveau coût. Importer directement `actual_source_absolute_cost_le_nine`, sans refaire20 :

    sourceExtendedFriableCost <=9*N*u^-33+35*N*u^-14
                              <=44*N*u^-14.

Sous le seul onset **u>=10^24**, ell=logu<=u, u>=1 et u^12>=360448=44*8192. Donc 360448*ell<=u^13 et

    sourceExtendedFriableCost <=N/(8192*u*ell).         (R5)

Ce budget ne requiert pas un nouveau onset10^40. La grande marge du seuil fixé permet de garder le même plafond1/8192 après le paiement du réciproque manquant ; aucune optimisation du seuil n'est revendiquée.

La somme descriptive demande+réciproques peut rencontrer le même vertex source. Pour garantir la consommation unique, définir les vertices orientés par la paire physique `(n,m)` :

    DemandVertices = image_(v in friableDemandDomain) (N-v.1*v.2, v.1*v.2)
    ReciprocalVertices = image_(q in Q01) (q, N-q)
    RemovedVertices = DemandVertices UNION ReciprocalVertices.

Conserver un élément une fois dans cette union, avec poids `ABS(sourceBracket alpha a N n m)`. Pour les demandes q premier/unitaire, `thetaBracket` est exactement ce bracket multiplié par primeIncidence(q)=1. Le lemme positif sum_image<=sum_labels suffit ; l'injectivité produit19, si utilisée, est un acquis sous N<M² à instancier au source. Les réciproques sont injectifs en q. Enfin

    sum_(w in RemovedVertices) |sourceBracket(w.1,w.2)|
      <= friableThetaDemand + sum_(q in Q01)|sourceBracket(q,N-q)|
      = sourceExtendedFriableCost.

L'union garde les intersections au lieu de les transformer en deux capacités. Ce majorant ABS est un coût de retrait local sur H19, **pas une disponibilité positive**, pas la réunion globale des parents/W et pas une partition du ledger entier.

Restent ouverts : complément F0 faux ET F1 faux, bridge H19 vers tout support source, singletons/e1/p0/faces/nonbulk, medium/long génériques, incidence première/AP/SD, vrais M0/kappa, Gamma/T_A, parents et capacité totale, six postes de D_N. Les acquis Iglobal/A7/S(N), Q/k1/wholeUa/rawPP, P5 entier avant retrait et U4 alternatif sans double paiement sont inchangés. WIN=false même si R1–R5 et l'union compilent.

## Livrables de l'expérience proposée

Les signatures Lean et la liste d'imports readonly sont dans `role2/lean_contract.md`. Le contrat strict neuf N=10^8 est `role2/numeric_contract.md`. Les preuves papier ci-dessus sont des obligations de formalisation ; aucun fichier Lean compilable n'est prétendu fourni, aucun test exécuté. Root peut sélectionner ce sous-lemme source après la conservation3028 et sa lecture FULL. ROLE2 n'écrit aucun ancien fichier et ne touche pas l'Idea Tree.
