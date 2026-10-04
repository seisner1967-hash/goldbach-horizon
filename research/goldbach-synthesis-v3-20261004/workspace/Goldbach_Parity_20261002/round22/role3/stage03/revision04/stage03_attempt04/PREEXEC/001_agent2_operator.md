# ROLE2 — proposition opérateur / boucle22

Statut final proposé : **PAPER_ONLY / AUXILIARY_IDENTITY_PROPOSED / NO_D_N_GAIN**. Aucune compilation, invocation Lean, sonde Lean, évaluation mathématique Python ou vérification numérique22 n'a été exécutée. L'ancienne mission ROLE4/21 est arrêtée ; ses fichiers gelés n'ont pas été modifiés. Ce rapport ne sélectionne ni n'ajoute de nœud. Il présente un mécanisme géométrique concret pour sélection par le coordinateur.

Le candidat recommandé est le **mode constant d'une série d'Epstein non primitive sur la surface modulaire, suivi d'un télescope du coefficient de diffusion**. La surface et sa Laplacienne sont construites indépendamment de N et de la réponse recherchée. L'identité isole exactement une série arithmétique globale et possède une enveloppe explicite. Elle ne donne pas encore un gain sur D_N. Son premier banc réalisable porte sur le déroulement géométrique ; l'extraction complète du coefficient N a un contrat distinct et un coût très élevé.

## Porte IDEATE et probe

La séquence valide a été exécutée avec la vue fraîche complète des contraintes, commande helper `view --cwd B --run-name parity --format constraints`, capture f4cd25, exit0, puis lecture complète du skill ideate, capture66f6bf. La première lecture préalable du skill avait été corrigée par ce redémarrage. La vue, conservée dans role2/fresh_constraints.txt, contient37 enseignements et les branches13.13/14.6 interrompues par le pivot utilisateur. Une interruption utilisateur n'est pas une réfutation mathématique ni un FAIL Lean. Les lectures supplémentaires pendant la rédaction ne remplacent pas cette séquence.

Q1 First principles : classe de blocage = représentation et information quantitative absente. Preuve concrète1 : agent5_judge20, lu intégralement, conclut16modules/250théorèmes auxiliaires, bilan cumulé57/942 et NO_WIN ; ses contrôles source ne ferment pas D_N. Preuve concrète2 : PROBE22 identifie les propositions21 signée et non friable, avec charges globales/capacité encore ouvertes avant compilation. Aucun ancien PASS n'est rejoué.

Q2 Hidden assumption : des objets locaux de facteurs/AP procureraient la nouvelle information globale. Cette représentation est désormais interdite. La retirer ouvre la construction d'un producteur géométrique continu avec domaine, normalisation et erreurs explicites, plutôt qu'une nouvelle hypothèse de petit reste.

Q3 Elephant : un coefficient de diffusion et une série de chaleur ne paient pas automatiquement le couplage additif de deux premiers, les puissances premières ni la différence physique/modèle. De plus, le continuum interdit d'utiliser la trace thermique complète comme une trace ordinaire finie.

Q4 Hamming : oui pour chercher une source globale différente ; non pour déclarer la parité franchie à partir d'une réécriture analytique. L'identité et ses ponts ouverts doivent rester séparés.

## Les quatre mouvements utilisés

Assumption Inversion : abandonner la partition primitive et l'inversion de Möbius ; sommer tous les points entiers du réseau Epstein et calculer le mode cusp directement par recouvrement d'intervalles. C'est le candidatC1.

Backward From Success : une victoire quantitative requerrait un producteur global indépendant, une reconstruction uniforme sur un contour, une extraction à N avec tous les alias, puis un raccord aux coefficients physiques du bilan. C1 expose ces étapes et leurs queues ; C2 cherche un vrai déterminant Fredholm généré par la dynamique géodésique.

Analogical Transfer : comparer une trace régularisée adélique (C3), un système thermodynamique global avec fonction de partition (C4), et une paire réelle de diffusion à différence de résolvantes de rang fini (C5). Ces analogies vérifient le domaine de validité de «trace», «déterminant» et «résonance» avant leur emploi arithmétique.

Failure-Case Reverse Engineering : face aux deux blocages20/21, demander quel producteur pourrait établir une nouvelle information sans la postuler. Face à une trace complète non trace-class et à l'amplification du contour, le minimum vérifiable est un canal réel construit, sa normalisation, puis une erreur uniforme fermée. Une queue sur l'axe réel seule n'aurait pas détecté la dégradation près de l'axe imaginaire ; C1 garde δ=π/2−arctan(π/η).

## Cinq candidats distincts, cinq champs chacun

### C1 — Epstein complet / canal modulaire / télescope (recommandé)

1. Assumption challenged : l'identification géométrique devrait passer par une partition primitive et une formule divisorielle. On la remplace par le réseau entier non primitif et une normalisation analytique, sans développer1/ζ.
2. Mechanism class : géométrie globale et reconstruction analytique certifiée. Δ est la réalisation de Friedrichs de −y²(∂x²+∂y²) sur L²(PSL2Z\H,y^−2dxdy), avec son domaine de forme réel, et le canal cusp0 est de dimension1.
3. Mechanism + Hypothesis chain : le déroulement Epstein aide à produire un signal arithmétique global parce que le mode constant se calcule directement par intégration de tous les points du réseau ; on saura cette étape réussie si son identité et sa queue finie sont prouvées et si les certificats d'intégrales indépendants rencontrent leur enveloppe. Le succès local ne signifie pas D_N payé.
4. Orthogonality vs siblings : C2 utilise des opérateurs nucléaires de branches de fractions continues ; C3 une trace adélique régularisée ; C4 une trace thermique diagonale ; C5 des conditions au bord de Sturm–Liouville. Le sibling ROLE1/22 développe une autre reconstruction premiers/zéros ; C1 évite l'inventaire de zéros grâce à une droite absolument convergente.
5. Conflicts with prior insight : NO_WIN20 et charges ouvertes21 restent valables. Le contre consiste à changer le producteur et à rendre chaque queue réelle ; aucune charge globalement petite n'est mise en prémisse. Le théorème de diffusion complet et le lienD_N restent ouverts. La preuve historique de Cakoni–Chanillo utilisant Möbius/totient est exclue.

### C2 — opérateur de Mayer sur un espace holomorphe (écarté pour cette première exécution)

1. Assumption challenged : seul un opérateur auto-adjoint sur Hilbert produirait un déterminant spectral légitime.
2. Mechanism class : opérateur de transfert nucléaire sur le Banach A∞(D) des fonctions holomorphes sur un disque autour de1, continues sur sa fermeture. Les branches z↦1/(z+n) et leurs poids (z+n)^−2s génèrent L_s indépendamment du coefficient cible.
3. Mechanism + Hypothesis chain : le Fredholm nucléaire est une voie réelle parce que le déterminant de la dynamique encode la zêta de Selberg de la surface ; une première réussite serait une approximation à erreur en norme nucléaire, sans se satisfaire d'une erreur de norme opérateur. L'exactitude historique det(1−L_s)det(1+L_s)=Z_Selberg ne fournit pas un couplage additif ordinaire.
4. Orthogonality vs siblings : la variable est une branche dynamique et le domaine est Banach holomorphe, distinct du canal cusp deC1, des adèles deC3, du spectre diagonal deC4 et du bord deC5.
5. Conflicts with prior insight : «nuclear order0» n'est pas «auto-adjoint Hilbert trace-class». L'OCR de la source primaire ne suffit pas à fixer seul le rayon du disque ni les constantes d'une queue de branches ; ces deux vérifications et le pont géodésiques/premiers additifs sont ouverts. On ne prétend pas que les géodésiques primitives sont les nombres premiers ordinaires. Pas de contratN certifié actuellement.

Source primaire : [Mayer, MPI90-86, §II–III](https://archive.mpim-bonn.mpg.de/346/1/preprint_1990_86.pdf), lecture ciblée. Son résultat est utilisé comme orientation, pas comme axiome Lean.

### C3 — trace adélique régularisée de Connes (écarté)

1. Assumption challenged : une trace locale exacte et un terme de régularisation suffiraient à fournir automatiquement la formule globale à erreur finie.
2. Mechanism class : espace L² d'un corps local K, action U(λ)ξ(x)=ξ(λ^−1x), coupures spatiale et Fourier et produit R_Λ ; trace régularisée et intégrale en valeur principale.
3. Mechanism + Hypothesis chain : ce mécanisme traite réellement les divergences parce que le contreterme logarithmique fait partie de l'objet ; on saurait la couche locale contrôlée si le o(1) historique était remplacé par une enveloppe finie dérivée avec paramètres et fonctions tests explicites. Cette enveloppe n'est pas actuellement fournie pour le couplage global voulu.
4. Orthogonality vs siblings : représentation adélique et régularisation, sans branches de transfert ni source Epstein, distinctes deC1/C2/C4/C5.
5. Conflicts with prior insight : la source laisse la version globale reliée à RH ; il est interdit de la supposer prouvée. Une somme de restes locaux o(1) n'est ni une borne fermée ni une minoration deD_N. Aucun théorème global ou annulation libre ne sera importé.

Source primaire : [Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, introduction et théorème3](https://alainconnes.org/wp-content/uploads/selecta.ps-2.pdf), lecture ciblée. Pas d'usage de son équivalence globale comme prémisse.

### C4 — Hamiltonien de partition ζ (écarté)

1. Assumption challenged : le continuum géométrique serait nécessaire pour obtenir une trace définie indépendamment de la réponse.
2. Mechanism class : sur ℓ²(N≥1), H e_n=log(n)e_n, domaine Σ(log n)²|v_n|²<∞. Cet opérateur diagonal réel est auto-adjoint par construction ; e^−βH est trace-class pour β>1 et Tr(e^−βH)=Σn^−β=ζ(β).
3. Mechanism + Hypothesis chain : une vraie fonction de partition aiderait à certifier la trace parce que sa queue est Σn>Qn^−β≤Q^(1−β)/(β−1) ; on saurait la trace certifiée si cette queue et le domaine étaient prouvés. Son logarithme isole un signal multiplicatif global, mais le spectre logn n'ajoute aucune géométrie additive sur N.
4. Orthogonality vs siblings : spectre discret et thermodynamique ; aucune fausse trace sur le continuum deC1 ni trace adélique deC3, et aucune dynamique deC2 ou conditions de bord deC5.
5. Conflicts with prior insight : ζ comme fonction de partition n'est pas une information nouvelle surD_N. Ajouter directement une entrée contenant les paires cibles ferait recopier la réponse par l'opérateur et est interdit. Pas de candidat retenu.

Lecture de contexte primaire : [Marcolli, qBostConnes, passage Hamiltonien/partition](https://www.its.caltech.edu/~matilde/qBostConnes.pdf). Le calcul diagonal et son intégrale de queue ci-dessus sont une dérivation élémentaire propre ; le texte complet n'a pas été lu et aucune propriété KMS supplémentaire n'est invoquée.

### C5 — vraie paire de diffusion au bord sur la demi-droite (écarté)

1. Assumption challenged : écrire «Birman–Krein» serait suffisant sans paire auto-adjointe construite.
2. Mechanism class : L²(R+), réalisations de −d²/dx² sur H² avec f(0)=0 ou f'(0)=κf(0), κ réel. La différence de résolvantes est de rang1. La source traite de vraies extensions auto-adjointes avec indices de défaut finis et système de diffusion complet.
3. Mechanism + Hypothesis chain : ce modèle fournit une trace relative légitime parce que les hypothèses de la paire et le rang fini sont vérifiables ; pour q=0, le canal a S_κ(λ)=(κ+i√λ)/(κ−i√λ), λ>0. On saurait cette étape formelle réussie en construisant résolvantes, branche, trace relative et déterminant avec toutes les conditions au bord. Elle ne produit aucun premier ordinaire.
4. Orthogonality vs siblings : continuum avec conditions de bord et rang fini relatif ; ni trace thermique complète deC1 ni opérateur nucléaire BanachC2, adéliqueC3 ou diagonalC4.
5. Conflicts with prior insight : choisirκ ou un potentiel pour forcer la réponse encode l'objet cible et n'est pas une dérivation. Aucun producteur géométrique autorisé de ce couplage n'est connu ici ; ce candidat n'est pas sélectionnable pour le livrable arithmétique.

Source primaire : [Behrndt–Malamud–Neidhardt, Scattering matrices and Weyl functions, introduction, §2.2](https://arxiv.org/pdf/math-ph/0604013), lecture ciblée ; résolvantes communes et branches explicites sont des conditions, pas des axiomes gratuits.

## Identité retenue et dérivation

La note [uniform_formula.md](role2/uniform_formula.md) donne la dérivation complète sur papier. Pour Re(s)>1, y>0, le producteur est

E_full(x+iy,s)=½Σ_(m,n)≠(0,0) y^s |m(x+iy)+n|^(−2s).

Toutes les bases sont positives et les puissances utilisent leur logarithme réel. Le mode m=0 donne ζ(2s)y^s. Les intervalles de longueur |m| des m≠0 recouvrent R exactement |m| fois presque partout ; la substitution paie ce facteur. Les deux signes de m absorbent½. L'intégrale gamma donne alors

C0 E_full = ζ(2s)y^s + √π Γ(s−½)/Γ(s) ζ(2s−1)y^(1−s).

Après normalisation sans série de1/ζ, φ(s)=√π Γ(s−½)/Γ(s) ζ(2s−1)/ζ(2s). Son identification avec la diffusion de la Laplacienne nécessite encore l'unicité et la résolvante, avec contrôle L² de la différence de solutions. Définir ce quotient ne prouve pas à lui seul cette identification.

Pour L(w)=−ζ'/ζ(w), ψ=Γ'/Γ et Re(w)=2, le signal

D(w)=½[ψ(w/2)−ψ((w+1)/2)−φ'/φ((w+1)/2)]

satisfait exactement D(w)=L(w)−L(w+1), puis L(w)=Σ_(k<K)D(w+k)+L(w+K). D(w) est un signal analytique ; ce symbole ne désigne pas le résidu D_N du bilan.

La queue C(σ)=log2·2^−σ+2^(1−σ)[log2/(σ−1)+1/(σ−1)²] est dérivée de Λ≤log et de l'intégrale décroissante, pour σ≥2. Mellin reconstruit F(t)=ΣΛ(n)e^−nt sur Re(t)>0. Le télescope fini reconstruit P_K(t)=ΣΛ(n)(1−n^−K)e^−nt ; |F−P_K|≤C(K), K≥2. Ni inversion Möbius ni décomposition arithmétique locale ne sont introduites. La série standard de−ζ'/ζ nécessite une preuve globale analytique ou un résultat existant audité ; sa provenance mathlib est déclarée dans le contrat Lean.

Les autres sources primaires de cette dérivation sont [Lagarias–Suzuki, équations1–2 et10–11](https://arxiv.org/pdf/math/0412039), [Borthwick, domaine et diffusion](https://math.dartmouth.edu/~specgeom/Borthwick_slides.pdf), et [NIST DLMF27.4.12](https://dlmf.nist.gov/27.4.E12). La source historique de [Cakoni–Chanillo, proposition2.5](https://sites.math.rutgers.edu/~chanillo/te.pdf) a été lue aux lignes513–577 : sa preuve Möbius/totient est exclue, pas reprise comme formalisation.

## Enveloppe, bancs et coûts gardés

Les enveloppes complètes figurent dans uniform_formula et numeric_contract. Sur t=η−iθ, |θ|≤π, la décroissance gamma utilise δ=π/2−arctan(π/η), et non la valeur de l'axe réel. L'erreur uniforme de reconstruction est C(K)+alias_Mellin+queue_discrète+rayon_des_évaluations. Le schéma Poisson exige la preuve de toutes les dérivées Schwartz, pas seulement une borne sur la fonction. Les identités gamma proviennent de [DLMF5.4.3](https://dlmf.nist.gov/5.4.E3) et de la récurrence [5.5.1](https://dlmf.nist.gov/5.5.E1) ; le mécanisme de quadrature est comparé à [Trefethen–Weideman, §5](https://people.maths.ox.ac.uk/trefethen/publication/PDF/2014_149.pdf), sans prendre son argument «outline» pour un théorème de remplacement.

L'extraction de G_N=ΣΛ(n)Λ(N−n) par le cercle donne une erreur ≤e^(ηN)(2B_F ε_F+ε_F²)+alias_cercle+rayon_extérieur. À N=10^8, η=8logN/N implique l'amplification N^8=10^64. M=N+1 garde100000001 nœuds extérieurs ; le contrat uniforme proposé J=1280000000000,h=1/128 garde2560000000001 nœuds intérieurs par signal. Ce coût astronomique est déclaré, aucune exécution n'est proposée sans accélération prouvée ou décision explicite du coordinateur. Le rayon ε_eval reste à construire ; aucune bibliothèque certifiée complexe disponible n'est présumée.

Premier banc proposé : EPSTEIN_UNFOLDING_AUX,18cas bas et6cas à y=√N=10000, sans gamma ni zéros. Les indices, primitives et queues sont explicites et utilisent des intervalles rationnels pour les racines carrées. Il ne vérifie ni la résolvante ni le coefficient à N. Deuxième banc : HEAT_AUX, signal réel et pleine référence1..10^8 neuve, sans replay. Troisième : COEFFICIENT_N, contour complet, enveloppe et producteurs certifiés encore ouverts. Le rôle6 a audité sur papier les signes, facteurs, indices et queues de la note ; aucun PASS numérique n'est revendiqué.

Les puissances premières propres Q(n)=Λ(n)−log(n)1_Prime(n) produisent Q·prime, prime·Q et Q·Q ; les trois restent dans le ledger et ne sont pas traitées comme queues spectrales. Les modes constant/cuspidal/résiduel et le continuum restent des objets de l'opérateur complet ; seul le canal cusp0 entre dans l'identité choisie. Aucun mode retiré n'est silencieusement imputé àD_N.

Il reste à raccorder G_N au modèle physique et à payer B_prime^a, B_pp^a, P_band≥2, Z_face≥2, I_α et2max(e,0), avec Q, k=1, unités, wholeU_a et fronts réels. Le seuil source logN≥10^24 n'est pas satisfait par le test10^8 et n'est pas utilisé comme garde finie. Aucun gain de signe, RH, Hilbert–Pólya, simplicité de zéros ou annulation équivalente àD_N n'est supposé.

## Self-check et hypothèse à quatre lignes

C1 n'est ni une modification de seuil, ni une reformulation de prompt, ni «plus de calcul». Son mécanisme est un producteur Epstein et un déroulement global ; son observable local est une identité et une queue finie, avec falsification indépendante possible. C2–C5 ont des mécanismes distincts mais sont écartés pour leurs ponts ou erreurs finies non construits. Les trois axes demandés ont été examinés : dualitéL via le canal, géométrie modulaire exacte via Epstein, et opérateurs/résonances via Mayer, Connes, partition et extensions. Aucun ancien nœud local interdit n'est prolongé.

Mechanism: Mode cusp0 du réseau Epstein complet sur PSL2Z\H, normalisé analytiquement, puis télescope exact du coefficient scalaire de diffusion et reconstruction Mellin–Poisson à queues fermées.
Hypothesis: Ce producteur géométrique indépendant de la réponse change la représentation globale et isole L=−ζ'/ζ sans inversion Möbius ; l'identification opérateur et le paiement de D_N restent des obligations distinctes.
Observable: Identité de déroulement et enveloppe finie à prouver sans sorry ; banc géométrique neuf24cas, puis signal completN=10^8 et contour avec tous les alias/rayons si leurs producteurs sont certifiés ; aucune victoire sur AUX.
Conflicts: NO_WIN20 et ponts ouverts21 conservés ; trace thermique complète non trace-class, preuve historique Möbius exclue, aucune RH/positivité/cancellation libre, amplificationN^8 et chargesPP/fullledger payées séparément.

Le rapport et ses contrats sont destinés au gel par manifestes avant sélection, conservation et autorisation d'exécution nouvelles. Tous les résultats formels et numériques restent non exécutés.
