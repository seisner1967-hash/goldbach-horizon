# FINAL1 — boucle21 : erreur AP pondérée et fenêtres physiques exactes

Statut : proposition conceptuelle finale, prouvée sur papier ci-dessous, avant sélection par root. Aucun Lean, producteur numérique, ancien PASS, kernel, logarithme numérique, signe ou Juge n’a été exécuté par ROLE1. Les 3028 archives sont en lecture seule. Une formalisation de ce sous-lemme serait un nouvel ingrédient source nécessaire ; elle ne serait pas une victoire de parité.

L’apport recherché est précis : remplacer l’obligation B6 encore écrite sur papier par une borne uniforme des **vrais** restes AP20, avec leurs fenêtres, leurs deux fronts, la primalité de q et la suppression exacte de q|N. L’erreur de distribution est définie par une enveloppe finie des vraies sommes de premiers ; elle n’est jamais supposée petite. La borne proposée est

    |masse physique AP − intégrale/phi(nu)|
       <= (32/7) E_phys(N,t,nu,U) + (16/7) log N.

Elle est uniforme en nu, y compris nu>U. Le prix sur la totalité des coefficients signés est conservé. SD, BV effectif, principal−M0, slack/queue, kappa global et ledger restent ouverts.

## 1. Vue fraîche, probe et cinq candidats

ROLE1 a appelé réellement `arbor_state.py view --cwd B --run-name parity --format constraints`, exit0, puis lu FULL la sortie ; une seconde vue fraîche a été sauvegardée et lue FULL immédiatement avant IDEATE dans `role1/constraints_pre_ideate.txt`. Le hash de cette vue est lié au reçu de lecture ; aucun identifiant de chunk non observé n’est revendiqué. Elle contient37 findings,5 pruned,maxdepth2 et13.12/14.5 done0. Le skill `arbor-agent-ideate` a été lu FULL ; la séquence probe→quatre mouvements→cinq déclarations→auto-filtre est appliquée. Aucun node n’est créé ici.

PROBE BLOCK

Q1 First principles : **wrong credit assignment / conversion analytique manquante**. Dans FINAL5_20, la masse réelle moins le principal construit est seulement définie et majorée par son propre ABS ; B6/frame et distribution restent ouverts. Le feedback20, section3, conserve cinq Gamma theta/raw NEG tandis que les cinq principaux−M0 sont POS, gardes source FALSE. Ces deux pièces distinctes interdisent de créditer une identité ou un principal comme contrôle de l’erreur réelle.

Q2 Hidden assumption : la fenêtre `frameInterval` est déjà égale au support physique des q premiers unitaires, et l’erreur AP ordinaire se convertit gratuitement en erreur `log(N−tq)`. En supprimant cette hypothèse, il faut construire le bridge aux vrais `PhysicalWitness`, définir l’enveloppe AP avant le poids, et payer les deux endpoints ainsi que q|N.

Q3 Elephant : même après cette conversion, les modules hors niveau et l’agrégation des coefficients couplés restent chers. Une constante6 devant une erreur définie ne prouve pas que celle-ci est petite ; les cellules AP vides gardent leur principal et leur discrepancy.

Q4 Hamming : oui comme fermeture d’une obligation source nécessaire et falsifiable ; non comme victoire indépendante. Cette conversion permet de poser correctement l’estimation de distribution suivante sur un objet mesurable et uniformément défini.

Les quatre mouvements : inversion de l’équivalence supposée frame/AP ; raisonnement arrière depuis un estimateur numérique et Lean raccordé au vrai reste ; transfert de la représentation des fonctions en escalier à des cellules extrémales finies ; rétro-ingénierie des faux crédits principal/Gamma et des fronts+1 encore ouverts.

### Candidat A — retenu : cellules extrémales AP et variation physique

1. Hypothèse attaquée : conversion frame/AP et erreur pondérée déjà disponibles.
2. Classe : représentation de l’erreur par cellules finies, puis contrôle analytique par variation totale.
3. Chaîne : le bridge exact permet d’appliquer Abel à la vraie masse ; l’enveloppe finie fournit un majorant réel sur tout y, et la décroissance du vrai f limite son coût à deux valeurs au front gauche. Succès observable : vraie borne B6 sur `actualPrimeAP`/`actualCompositeAP`, sans un champ libre « petit reste ».
4. Orthogonalité :13.12 construit les poids et définit les restes ; A estime leur conversion aux erreurs ordinaires, sans redériver Bonferroni/Selberg/minFac/CRT.13.11 et13.8 portent les prix calibrés,13.9/13.10 les masques TypeII ; A ne change aucun prix ni masque.13.1/13.3–13.7 gardent les graphes physiques,13.2 est pruned ; aucun graphe/capacité n’est invoqué.14.5 paie la couche friable, ici aucune friabilité.
5. Conflits : root exige une information source et interdit le crédit d’identité ; A fournit un contrôle effectif mais laisse E et son prix littéraux. Les pruned4/6/13.2/1.2/9.2 ne sont pas réutilisés.

### Candidat B — éliminé : réciprocité Kloosterman du tableau signé

1. Hypothèse attaquée : les grands modules doivent être pris en ABS séparément.
2. Classe : analyse spectrale / changement de variables réciproque.
3. Chaîne : exploiter t=crs et le signe de xi après réciprocité pourrait économiser une puissance ; observable : véritable borne uniforme pour le shift N et les fenêtres p².
4. Orthogonalité : information de distribution au-delà de13.12, sans nouveau prix.
5. Conflits : aucun résultat uniforme correspondant n’est dérivé dans cette itération. Réécrire SD avec une nouvelle notation réintroduirait une prémisse gratuite. Éliminé avant formalisation ; aucune citation à shift fixe n’est promue à N croissant.

### Candidat C — éliminé : remplacement par un poids linéaire de Chen

1. Hypothèse attaquée : le minorant impair Bonferroni est l’unique retrait composite utilisable.
2. Classe : poids de crible avec switching.
3. Chaîne : une pondération par le nombre de petits facteurs pourrait rendre positif le principal composite sur davantage de p ; observable : minorant construit avec vrai principal favorable et coût de niveau démontré.
4. Orthogonalité : change la construction des poids13.12, pas le prix19.
5. Conflits : le domaine q<N^(9/16), la borne de niveau et le coût des grands p restent présents. Sans démonstration de l’agrégation nouvelle, ce serait un remplacement standard sans information neuve. Éliminé.

### Candidat D — éliminé : optimisation de la branche p0 seule

1. Hypothèse attaquée : le retrait p0 est perdu à cause d’un choix de z.
2. Classe : optimisation variationnelle locale.
3. Chaîne : adapter lambda par t pourrait accroître le retrait1/(p0−1) ; observable : gain net sur le principal entier après coût du poids.
4. Orthogonalité revendiquée : paramétrage local du poids.
5. Conflits : FINAL1_20 section10 établit déjà la compensation Euler de cette branche. Une variation de z ne contre pas cette compensation et constitue un shallow tweak. Éliminé.

### Candidat E — non retenu : bridge littéral M0/frame-référence

1. Hypothèse attaquée : M0 arbitraire représente déjà le prix acquis.
2. Classe : vérification des supports / partition exacte.
3. Chaîne : réindexer la référence entière en b=sq plus le complément produirait une expression littérale de M0 ; observable : aucun M0 libre dans le raccord.
4. Orthogonalité : prix réel et multiplicité des fibres, distincts du contrôle AP.
5. Conflits : le complément entier b non semipremier doit rester ; une identité de ce bridge seule ne fournit pas de gain analytique. Nécessaire plus tard, mais A ferme d’abord la conversion quantifiée d’un reste réellement présent. Non retenu dans cet essai borné.

Auto-filtre : A n’est ni un nombre/configuration, ni un nouvel énoncé de petitesse de SD/Gamma, ni une relecture d’un PASS20. Il change la représentation du reste réel et établit un théorème uniforme nouveau à partir de son objet arithmétique. Son résultat reste explicitement auxiliaire.

## 2. Hypothèse de node, quatre lignes seulement

Parent13, profondeur2. Le bloc est fourni à root, sans `TreeAddNode` ROLE1.

```text
Mechanism: Enveloppe finie des deux extrémités de chaque cellule AP réelle, bridge exact PhysicalWitness-frame et variation d’Abel du poids log(N−ty)/log y avec retrait q|N conservé.
Hypothesis: La conversion quantitativement manquante de13.12 donne |actualAP−main|<=32Ephys/7+16logN/7 uniformément pour les vrais fronts/caps et tous modules, sans supposer Ephys petit ni remplacer M0.
Observable: Nouveau théorème Lean sur actualPrimeAP et actualCompositeAP source, enveloppe non vide/finie et gardes dérivées ; nouveau producteur N1e8 exhaustif avant masks vérifie bridge, endpoints gauche/droite, intégrales et prix de tous coefficients signés.
Conflicts: Les principaux POS20 ne paient pas Gamma NEG ; Ephys et sa consommation globale restent explicites, grands modules/slack/queue/PP/M0/ledger conservés ; aucun mécanisme pruned ni PASS local déclaré WIN.
```

## 3. Bridge exact des axes physiques

On importe les objets20 gelés. F est le vrai `Parameters`18 et t=`switchedConductor F s`=c*r*s. Définir `StaticAxes F s` par c,r,s premiers, c<r<s<=a, cr<=a, cs<=a<rs, a<crs et (t,N)=1. Il s’agit de gardes arithmétiques sur un triple réel, pas d’une disponibilité d’incidence. Les triples invalides restent dans un catalogue de contrôle avec statut inactif ; on ne leur applique pas un principal valide.

Prendre 0<t, x<=N, x>=2 et le front dyadique entier j>x/2 au sens `x/2` Nat. Garder les définitions20 exactement :

    L=max(a+1,rs+1,ceil((N−x)/t),ceil(M/t)),
    U=min(floor((N−floor(x/2)−1)/t),floor((N−Q−1)/t)).

Les `ceil` sont les quotients Nat `(v+t−1)/t` ; les soustractions sont justifiées par les gardes explicites, jamais utilisées comme égalités réelles sans preuve. Sous `StaticAxes`, x<=N et `x/2+1>max(1,z)`, on démontre pour chaque q :

    q∈physicalQDomain F s z (frameInterval F s x)
       iff L<=q<=U, q prime et (q,N)=1.

Sens direct : le witness donne q premier, les bornes a<q et rs<q, le bulk et front original ; q appartient déjà à l’intervalle. L’unité de t*q donne celle de q. Sens inverse : les bornes de L produisent les strictes gardes a<q/rs<q et M<=tq ; celles de U donnent tq+Q<N et tq<=N−floor(x/2)−1. Le front inférieur en x donne tq>=N−x. Donc `floor(x/2)<N−tq<=x`, j>=2 et z<j, et l’on construit chaque champ du vrai witness avec b=s*q. La coprimalité de t*N avec les q est obtenue depuis (t,N)=1 et (q,N)=1 ; aucun `Prime(j)` n’apparaît.

Quand L>U, les deux ensembles sont vides. Quand p²>N, le composite window est vide. Sinon remplacer U par

    U_p=min(U,floor((N−p²)/t)),

avec le même L. Le théorème20 `physicalCompositeWindow_cap` raccorde exactement ce front, y compris p²=j. Pour p premier, p²>=4 garantit le positif de N−ty jusque U_p. Les candidats j=p² et p|j/p ne sont pas exclus.

Pour nu compatible, `nu|N−tq` devient la vraie classe `t*q=N mod nu`, puis l’unique classe b=N*t^(-1) mod nu. Son caractère réduit est dérivé de (nu,tN)=1. La classe nu=1 est présente, b=0, phi(1)=1. Pour nu non compatible, l’objet physique et son main20 sont nuls ; le théorème acquis20 est importé. On conserve néanmoins le catalogue de ces représentations nulles.

Le bridge porte sur cette extraction canonique, pas sur toute la frontière de D_N, H19, le nonSS ou toutes les capacités.

## 4. Enveloppe AP construite, finie et indépendante du poids

Pour N,t,nu entiers, nu>=1, définir les coefficients ordinaires

    c(q)=log q si q prime et t*q=N mod nu ; 0 sinon,
    Theta(m)=sum_{0<=q<=m} c(q),
    A(y)=Theta(floor(y)) pour y>=0,
    R(y)=A(y)−y/phi(nu).

Le masque q|N n’est pas supprimé dans A : il est retiré séparément en section6. La mesure c conserve seulement les premiers q ; le candidat j n’est jamais testé. Ce sont des AP de premiers ordinaires.

Pour un U entier>=0, soit la famille finie de valeurs

    V_U={ |Theta(m)−m/phi(nu)|,
           |Theta(m)−min(m+1,U)/phi(nu)| : 0<=m<=U }.
    E_phys(N,t,nu,U)=max V_U.

L’indice m=0 rend la famille non vide ; la valeur0 est présente, donc E>=0. Toutes les sommes/logarithmes sont finis et phi(nu)>0. L’enveloppe n’est pas un champ fourni par un oracle. Elle ne dépend ni de Gamma ni du poids f ni de son signe désiré.

Pour 0<=y<=U, poser m=floor(y). On a m<=y<=min(m+1,U), avec l’égalité m=U seulement au dernier endpoint. R(y) est affine en y sur la cellule de somme constante Theta(m). L’ABS d’une fonction affine est borné par le maximum aux deux bouts, donc

    |R(y)|<=E_phys(N,t,nu,U).

Le second bout est la **limite gauche** de l’erreur avant le saut premier suivant ; il ne devient pas `Theta(m+1)`. Cette différence est centrale. Au saut m+1, sa valeur après saut figure dans la première entrée de la cellule suivante. Aucune valeur gauche n’est effacée. Ainsi E_phys coïncide aussi avec le supremum réel de |R| sur[0,U] : chaque première valeur est atteinte, chaque seconde est atteinte ou est une limite par y↗m+1, et la borne précédente donne le sens réciproque. La formulation Lean initiale peut utiliser le max fini, en prouvant d’abord sa domination ; l’équivalence au sSup doit être explicitement prouvée si elle est annoncée.

E_phys utilise le front U réellement appliqué, pas automatiquement Y=N/t. Un objet `E_theta(Y,nu)` standard sur le supremum de toutes classes réduites et0<=y<=Y le domine si U<=Y ; cette domination ne le rend pas petit. Aucune application BV/SD n’est faite ici.

## 5. Vrai poids source : signes, dérivée et variation

Pour une fenêtre non vide L<=U, poser A=L−1 et

    f(y)=log(N−t*y)/log y,       A<=y<=U.

La preuve générique requiert A>1 et N−t*U>1. Ces gardes dérivent du frame précédent au source et du cap composite ; elles sont vérifiées littéralement dans le banc. N−ty>1, log y>0, donc f>=0 et f est C1 sur ce compact. Son dérivé est

    f'(y)=−t/((N−ty)*log y)
           −log(N−ty)/(y*(log y)^2) <=0.

Les deux termes ont le signe justifié par leurs dénominateurs positifs ; ni logarithme à zéro ni dérivée junk n’est utilisé. La dérivée est continue et intégrable sur le compact. Le théorème fondamental et ce signe donnent

    integral_A^U |f'(y)|dy = f(A)−f(U).

La source a=ceil(N^(7/16)) donne `log a >= (7/16)*u`. Comme A=L−1>=a, N−tA<=N et u>0,

    0<=f(y)<=f(A)<=16/7.

Le bound est valable pour tout t physique et tous nu ; il ne dépend pas d’un niveau de crible. Il traite aussi une fenêtre contenant un seul q, A=U−1, sans remplacer l’intervalle continu par un singleton.

Gardes source au seul onset fixé u>=10^24 : N>1 ; a>1 ; N/5<=x<=N/4 implique x/2>=N/10 ; pour le cutoff source z=ceil(N^(1/64)), z<=2N^(1/64)<=N/10, puis z<floor(x/2)+1. La seconde inégalité découle de `20<=exp(63u/64)`, immédiatement satisfaite au même onset ; le +1 du ceil est inclus. Aucun onset10^40 n’est requis et aucun estimateur asymptotique de premiers n’est invoqué. On peut aussi énoncer le résultat pour tout z sous la garde explicite z<floor(x/2)+1.

Les fonctions sourceU/sourceA et SourceOnset20 sont importées en lecture seule ; le nouveau lemme `source_a_log` est dérivé de `Nat.le_ceil` et `log_rpow`, pas pris comme prémisse.

## 6. Abel, retrait exact q|N et constante source

Le module cache `Mathlib.NumberTheory.AbelSummation` donne `sum_mul_eq_sub_sub_integral_mul` pour les endpoints réels A,U, avec les gardes de dérivée/intégrabilité ci-dessus. Appliqué aux coefficients c construits, il produit exactement

    sum_{L<=q<=U} f(q)c(q)
      = f(U)A(U)−f(A)A(A)−integral_A^U f'(y)A(y)dy.

Par intégration par parties du modèle linéaire y/phi(nu), soustraire `I/phi(nu)`, I=int_A^U f(y)dy. On obtient

    R_weight = f(U)R(U)−f(A)R(A)−integral_A^U f'(y)R(y)dy.

Il ne s’agit pas du renommage d’une masse−main : la formule exprime son erreur par l’AP ordinaire construite avant le poids. Puis

    |R_weight| <= [f(U)+f(A)+int|f'|] E_phys
                =2 f(A) E_phys <=(32/7)E_phys.

Pour q premier, f(q)c(q) vaut log(N−tq) dans la classe, car logq>0. Enlever le masque non unitaire q|N retire la masse positive exacte

    C_N=sum_{L<=q<=U, q prime, q|N, t*q=N mod nu} log(N−tq).

La liste est un sous-ensemble des vrais primeFactors de N, avec chaque premier une seule fois. `sum_{p|N} logp <= logN` découle de la factorisation avec multiplicité : `log_nat_eq_sum_factorization N` et les exposants>=1 ; les répétitions de N ne créent pas des retraits supplémentaires. Par f(q)<=f(A),

    0<=C_N<=f(A) sum_{p|N}logp <=(16/7)u.

Le reste **physique unitaire** est R_weight−C_N. Donc

    |actualAP−I/phi(nu)|
      <=2f(A)E_phys+C_N <=(32/7)E_phys+(16/7)u
      <=6(E_phys+u).

Même si C_N est nul sur une fenêtre finie, sa définition reste dans la preuve et dans les recettes. Le budget logN n’est pas supprimé au source. Les deux fronts exacts A=L−1,U sont nécessaires ; remplacer A par L change I et le reste.

Les nonunités nu sont la branche zéro déjà importée. Les fenêtres vides ont actualAP=I=0 et reste0 ; le max AP n’est pas artificiellement contraint à zéro. Les caps p² gardent le même A et leur U_p exact.

## 7. Raccord aux restes20 et prix entier des coefficients

Pour chaque vraie représentation Q `(d,e)` ou composite `(p,d,e,h)`, utiliser son nu20 et son endpoint U ou U_p. Le bridge et Abel donnent le bound précédent **sur actualPrimeAP20 et actualCompositeAP20**, puis leurs expansions PASS20 importées donnent une borne des `actualSelbergRemainder` et `actualCompositeRemainder`.

Définir explicitement, sans plafond de multiplicité réutilisé,

    PriceQ =sum_{d,e} |lambda_d lambda_e|
             [(32/7)E_phys(N,t,lcm(k,l),U)+(16/7)u],
    PriceC =sum_{p,d,e,h, card(h)<=2K+1}
               |lambda_d lambda_e mu(h)|
             [(32/7)E_phys(N,t,nu(p,k,l,h),U_p)+(16/7)u].

Les cases nonunitaires et fenêtres vides sont définies comme prix0 après leur preuve d’absence réelle. Tous les indices sont conservés, dont lambda=0, mu=0 et h ne divisant aucun quotient observé. Pour les autres cases, nu>U n’est aucun motif de prix0 : le main I/phi et E restent présents.

En conséquence,

    |actualSelbergRemainder|<=PriceQ,
    |actualCompositeRemainder|<=PriceC.

La borne entière pour un catalogue canonique réel conserve les facteurs `kappa_c=logc+S(N)` dans `sum |kappa_c b|`, ou additionne les bornes par fibre avec leur kappa réel. Il n’existe aucun nouveau32/40/64 de multiplicité gratis. Après regroupement par **nu et mêmes endpoints**, l’ABS d’un coefficient groupé peut réduire le prix ; la carte groupée doit être l’image exacte de toutes les représentations originales, et le prix dégroupé reste une certification sûre. Des fenêtres distinctes ne fusionnent pas par seul module.

L’estimateur20 remplace ses deux ABS par ces PriceQ/PriceC et garde Tail/Slack et M0. Aucun bound `PriceQ+PriceC<=N/(C*u*ell)` n’est annoncé : cette agrégation est la vraie obligation SD/BV à démontrer ensuite. Cette étape ne résout ni comparaison du principal complet, ni M0 littéral, ni capacité, ni Gamma totale, ni ledger.

## 8. Livrable Lean concret après sélection et gate numérique

Modules historiques importés sans rebuild : `SwitchedIncidenceEstimator`, ses six dépendances20 auditées, `SeparatedTypeII`18, `FriableSourceGeometry`20 seulement pour les fonctions/gardes source ; oleans readonly Juge20/historiques. Bibliothèque cache : `Mathlib.NumberTheory.AbelSummation`, `Mathlib.Analysis.SpecialFunctions.Log.Deriv`, intégrales/FTC et factorization existants. L’API de la source cache est l’autorité, pas la documentation latest.

Nouveaux modules bornés possibles :

1. `PhysicalFrameAP21`: `staticAxes`, `physicalQDomain_frame_exact`, `physicalCompositeWindow_frame_exact`, `actualPrimeAP_frame_reindex`, `actualCompositeAP_frame_reindex`. Les theorem statements doivent nommer les fonctions20, pas une somme générique représentant leur masse sans bridge.
2. `PhysicalAPEnvelope21`: coefficients c et Theta construits, max fini non vide, E>=0, `actual_ap_discrepancy_le_envelope` sur tous les réels du compact ; sSup équivalence seulement si prouvée. Une borne libre E ne remplace pas ce module.
3. `PhysicalLogVariation21`: vraie fonction f, dérivée/logguards/intégrabilité, antitone, `source_a_log`, source f<=16/7 et variation exacte ; guards depuis SourceOnset/sourceceil.
4. `PhysicalAPAbel21`: identité Abel avec le vrai c, retrait q|N, bound radical, `actualPrimeAP_B6` et `actualCompositeAP_B6`, puis PriceQ/PriceC sur les deux restes20 et raccord à l’estimateur20.

Tous les objets sont définis ; les hypothèses génériques sont seulement de positivité/fenêtre/coprimalité/static axes et sont dérivées dans le corollaire source. Aucune prémisse de petite erreur AP, somme cible, principal favorable, Gamma, disponibilité ou Hall. Chaque déclaration explicite reçoit un `#print axioms` qualifié. Aucun sorry/admit/axiom ajouté/native_decide/unsafe/trustMe, et une preuve interne ne remplace pas le PASS du module entier. Le Juge doit examiner le raccord final, pas seulement un lemme générique d’Abel.

## 9. Contrat numérique neuf STRICT N=100000000, non exécuté

Objet neuf : bridge physique/frame, AP ordinaire finie et conversion Abel/B6, comprenant les nouveaux endpoints et leur prix de tous coefficients. Ce producteur ne reprend aucun ancien résultat, bitmap, log, certificat ou PASS pour lui attribuer un crédit nouveau. Il peut employer une bibliothèque d’arithmétique à nouveau revue et liée ; un nouveau code autonome de représentation/bridge/enveloppe est nécessaire. Ce FINAL n’est aucune gate d’exécution.

Fenêtre principale : x=25000000 et **12500000<j<=25000000**, soit les12500000 entiers avant tout masque. C’est le vrai frame dyadique20 instancié avec N/5<=x<=N/4. Elle chevauche la banque19 sur `(12500000,24000000]` et la banque20 sur `(24000000,25000000]`. Aucune disjonction des historiques n’est prétendue. La nouveauté est l’objet/producer21 et ses vérifications de bridge/B6, pas l’absence d’anciens j. La sous-fenêtre20m<j<=25m peut être signalée séparément, jamais substituée au catalogue entier du frame.

Paramètres exacts : alpha100,Q999999,a3163,M1000000,p0 canonique calculé à neuf. Gardes : `u>=10^24` FALSE ; l’intervalle source en x TRUE ; les gardes génériques de f, frame et z sont vérifiées littéralement. Ne jamais publier « tous sourceguards TRUE » à partir de la seule fenêtre. Coupes nouvelles de contrôle z=13 et23, P=19, K=0 et1 ; coupe source z=ceil(N^(1/64)) séparée, Psource=floor(N^(1/64)), Ksource1, avec ses layers finis éventuellement vides. Ces paramètres test exercent les supports sans prétendre payer SD.

Catalogue exhaustif : tous c<r premiers unitaires à N avec cr<=a, tous s premiers r<s<=a avec cs<=a<rs, t=crs>a et (t,N)=1. Garder les triples aux intervalles physiques ou AP vides. Ici

    L=max(a+1,rs+1,ceil(75000000/t),ceil(M/t)),
    U=min(floor(87499999/t),floor((N−Q−1)/t)).

La borne sur q découle de t>=3*(a+1), donc q<87500000/(3*(a+1))<10000. Un crible neuf jusqu’à10000 suffit aux axes ; la factorisation de tous j<=25m est certifiée par les premiers<=5000, contenus dans ce même catalogue. Le bitmap j entier neuf conserve nonpremiers, nonunités, mu0, properpowers et entiers aux fronts. Aucun q n’est trouvé en filtrant d’abord `Prime(j)`.

Sorties et assertions nécessaires :

* Les deux constructions indépendantes de chaque domaine : witness physique champ par champ versus intervalle L/U puis q premier unitaire. Égalité exacte des cartes/ensembles, branche vide et endpoints L−1,L,U,U+1. Une requête composite garde p²=j et le cap U_p ; p²>N et U_p<L sont explicites.
* Tous les candidats j du bitmap et les facteurs répétés ; tous les q physiques avant prime(j), minFacj/properpower, p|j/p permis, nonminimal cells négatives et mu0. Ces diagnostics conservent les objets20 sans rejouer leurs anciennes banques.
* Catalogue de chaque k,l/h original, lambda rationnel réel, zéro lambda et zéro mu explicites ; xi et coefficients signés littéraux ; vrai nu=p*lcm(h,lcm(k,l)/gcd(lcm(k,l),p)). Les supports étendus nonSF sont des axes nuls documentés, jamais des capacités. Les coefficients originaux et la carte groupée par `(t,nu,L,U_p)` sont comparés exactement avant toute évaluation log.
* AP ordinaires de tous premiers q<=U, avant masque q|N ; classe réduite b par inverse entier seulement après compatibilité nu,tN. Les classes incompatibles/nulles et celles de nu>U restent au catalogue. Tous les indices d’enveloppe m=0..U sont présents avec la valeur après saut et la limite avant m+1, y compris m=U. Ce n’est pas un max observé seulement aux q physiques ou aux premiers.
* E_phys entouré par max d’intervalles rationnels extérieurs : si chaque valeur est dans[lo_i,hi_i], max est dans[max lo_i,max hi_i]. On n’identifie jamais la limite gauche Theta(m)−(m+1)/phi à la valeur après saut Theta(m+1). Les certificats d’enveloppe dominent tout le segment via l’argument affine, plus points rationnels internes de contrôle.
* f(A),f(U), dérivée signée, f<=16/7 et variation sont vérifiés par intervalles rationnels. Intégrale I enfermée par sommes de Darboux monotones sur subdivision rationnelle de chaque intervalle[ A,U ]; intégrer seulement entre L−1 et U. Le pas et la largeur sont publiés ; raffiner jusqu’aux décisions demandées ou conserver UNRESOLVED, sans transformer une indécision en identité fausse.
* Masse AP logj par cartes exactes des logarithmes d’entiers avec coefficients rationnels ; identité `physicalAP=unmaskedAP−C_N` par cartes avant log. Abel est vérifié en une version cellulaire : le terme integral f' A(y) se calcule exactement comme somme `Theta(m)*(f(m+1)−f(m))` avec endpoints partiels. Cette carte d’identités et les enclosures de I certifient le reste pondéré et son bound, sans quadrature flottante.
* Les coefficients c utilisent log(q) des premiers, le poids produit f(q)c(q) égale logj. Les properpowers de j utilisent logj dans la masse Selberg/AP et log(base première) uniquement dans le raccord raw acquis. Aucun masque mu(j)^2 sur raw. La correction PP reste séparée, aucun deuxième paiement Bpp.
* C_N construit sur q|N, avec sa carte, positif et au plus16u/7 ; au N fixé ses premiers2/5 sont sous les fronts, donc une possible masse0 n’annule pas la preuve générale. Ajouter un contrôle local strict déclaré **hors domaine physique N1e8**, Nlocal51051,t1,nu1,L3,U20, pour exercer le retrait de3,7,11,13,17. Il ne remplace aucun witness source et ne crée pas un crédit pour le N fixé.
* Tous les nouveaux restes et PriceQ/PriceC et leur agrégation sont certifiés, y compris nu>U, fronts+1 et classes vides. Kappa conserve la carte affine en S(N) avec la boîte C2 acquise ; aucune valeur de S libre. Ne pas prétendre estimer le M0 arbitraire ou les W/parents/D_N. Ces objets demeurent explicitement non évalués par ce contrat.

Arithmétique : entiers et `Fraction`, logarithmes par séries rationnelles entourées vers l’extérieur avec réduction d’argument exacte ; zéro float/log machine. Neuf producer avec hash fixe/PREEXEC/START/log/exits/receipt, gate root préalable et zéro ancien replay. Les signaux POS/NEG/ZERO/UNRESOLVED sont distincts ; aucun résultat n’est annoncé avant exécution.

Falsificateurs nouveaux : A=L au lieu deL−1 ; seulement une extrémité dans Abel ; E pris aux valeurs après saut seulement ; suppression du q|N ; classenu>U réputée erreur0 ; intervalle ayant un q mais intégrale déclarée0 ; produit phkl à la place du lcm ; cap p² strict ; q trouvé après Prime(j) ; masque mu0 supprimant un candidat raw ; garder seulement les coefficients groupés « favorables ». Chercher les contre-exemples dans le domaine exhaustif, sinon NONE_IN_DOMAIN et local boundary explicitement hors incidence physique. Un faux bridge ou une vraie inégalité réfutée tue sa promotion avant Lean ; une largeur d’enclosure non résolue est un statut de précision, pas un FAIL mathématique.

## 10. Sources primaires, portée et reste ouvert

La [documentation primaire mathlib de la sommation d’Abel](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/AbelSummation.html) confirme la famille de théorèmes de sommation partielle. Son état actuel possède des variantes supplémentaires ; nous utilisons uniquement le theorem effectivement lu dans la source cache au commit9837ca9d65d9de6fad1ef4381750ca688774e608. L’URL GitHub de ce commit a renvoyé cache miss dans l’outil web ; aucune lecture web de ce fichier précis n’est prétendue. La source locale entière AbelSummation a été lue FULL et reste l’autorité de signature. Log.Deriv a été consulté aux déclarations ciblées, Log.Basic aux lignes333–382 avec `log_nat_eq_sum_factorization`. Aucun théorème externe de distribution ou constante BV n’est importé.

Cette proposition établit sur papier une information nouvelle uniforme pour la conversion source du reste réel20 ; sa compilation est encore à réaliser par3/4 après sélection et PASS numérique. Elle n’affirme aucune estimation petite de E_phys, PriceQ/PriceC, SD ou Gamma. Le principal déterministe, son M0 littéral, les grands modules/slack/queue, agrégation kappa, PP/reference, capacités/sourcepartition et le ledger D_N entier restent à démontrer. Les acquis I/A7/C2 et la sourceu>=10^24 ne sont pas remis en cause. Score conceptuel0 ; WIN=false.

Les fichiers de lecture/manifeste/reçu ROLE1 sont gelés après préparation. Toute correction conceptuelle ultérieure devra être un fichier/version distinct conservant ce FINAL original. Aucun FAIL Lean/numeric n’est inventé : ROLE1 n’a exécuté aucun de ces moteurs.
