# Rôle 2 — boucle 13 : parité, poids physique et orientation de l’opérateur

**FINAL : deux promotions spectrales rejetées avant Lean ; aucune compensation quantitative obtenue.** Le premier probe porte sur une vraie variation de `Λ_N(N−m)` et non sur le commutateur harmonique ancien. Le second montre pourquoi une symétrisation bipartite efface précisément le coefficient orienté à estimer. Les objets sont raccordés au transfert12 avec son matching `S(cN)`. Aucun petit moment, aucune masse Goldbach favorable et aucune capacité ne sont supposés. Une identité matricielle ordinaire n’est pas envoyée à Lean comme gain de parité.

Le présent rapport est la seule production écrite de ce rôle. PROBE_BLOCK13, feedback12, agent2_bilateral12, agent5_12, REPORT.md et les définitions de `Λ_N`, B12/B13 dans agent2_bilateral_compensation11 ont été lus. Le gate d’idéation `arbor-agent-ideate/SKILL.md` a été appliqué après les contraintes fournies par le coordinateur. Les archives, sources et acquis ne sont pas modifiés.

## Probe et génération

Q1 First principles : **mauvais transfert de représentation et mauvais crédit**. D8/D9_12 conservent les deux incidences premières, quatre termes et trois formes sans estimation ; le cube sélectionné `{29,561}` a réfuté une stabilité héritée, et `n=8017²` a réfuté le remplacement raw par theta. Une symétrie de parité d’un opérateur doit donc être confrontée à son véritable coefficient orienté et à sa mesure physique.

Q2 Hidden assumption : une symétrie bipartite ou une conjugaison diagonale pourrait rendre le poids physique inoffensif. Si elle est abandonnée, il faut conserver les variations `Λ_N(N−m)−Λ_N(N−c)` et le modèle de ligne `S(cN)`, puis distinguer l’opérateur orienté de sa symétrisation.

Q3 Elephant : même une petite partie centrée laisserait le modèle signé, le secteur `c=1`, la référence `−S(N)N`, tous les `c>a` et le raccord à B13 sans comparaison quantitative. Les cubes locaux ne sont pas une partition de ces postes.

Q4 Hamming : **oui**. Le coefficient bilatéral réel est visé directement ; une symétrie qui le conserve pourrait être utile, tandis qu’une symétrie qui l’annule ne peut pas être créditée comme compensation.

Les quatre mouvements ont été utilisés. L’inversion garde la discontinuité prime/composite de la mesure, au lieu de la lisser. Le raisonnement depuis une réussite demande une propriété indépendante contrôlant le coefficient orienté, avec modèle et complément. Le transfert analogique examine le supercharge biparti et la normalisation de type Doob. L’analyse des échecs exige un cube entier avec unités, un point raw propre-puissance et des cofacteurs longs. Le Doob stationnaire a été auto-filtré : une chaîne réversible bipartite sans boucle impose déjà l’égalité des masses des deux classes dans chaque composante ; la demander serait déplacer la capacité de compensation dans l’hypothèse. Deux familles plus précises sont examinées ci-dessous.

## Objets physiques et transfert exact

Conserver `N` pair, `u=log N`, `ell=log u`, `alpha=ceil(N^(1/4))`, `Q=floor((N−1)/alpha)` et `a=ceil(N^(7/16))`. On utilise exactement

\[
\Lambda_N(n)=\Lambda(n)\mathbf1_{n>1}\mathbf1_{(n,N)=1},\qquad
G_N(m)=\mu(m)^2\Lambda(m)+S(N)\mu(m).
\]

Le premier axe garde les puissances premières propres. L’espace fini `X_N` comprend tous les `1≤m≤N−2` carré-libres, unitaires à N, y compris 1. Poser

\[
J_{m,m}=\mu(m),\quad V_{m,m}=\Lambda_N(N-m),\quad M_{c,c}=S(cN).
\]

La matrice de suppression orientée est

\[
T_{c,m}=\begin{cases}\log p/\log m,&m=pc,\ p\text{ premier},\ p\nmid c,\\0,&\text{sinon}.\end{cases}
\tag{A1}
\]

Toutes les gardes de `X_N` sont conservées. Chaque colonne `m>1` de T a somme 1 ; celle de 1 est vide. Cette conservation donne le coefficient réel de D5_12 et ne procure aucun gain absolu. Les matrices suivantes ne supposent pas que l’incidence `N−pc` soit indépendante de c :

\[
K_{\rm phys}=TV,\quad K_{\rm match}=MT,\quad
K_{\rm res}=TV-MT.
\tag{A2}
\]

Le matching est bien celui des deux formes `p,N−cp`, donc `S(cN)`, sous la garde `(c,N)=1`. Ce n’est pas `S(N)` constant. L’observable centrée entière est

\[
\mathcal E_N=\mathbf1^T J K_{\rm res}\mathbf1
=\sum_{(p,c)}\mu(c)\frac{\log p}{\log(pc)}
[\Lambda_N(N-pc)-S(cN)].
\tag{A3}
\]

Avec `R_N^(Λ)=sum_p Λ_N(N−p)log p` sur les vrais premiers unitaires et `mathcal M_N=1^T JMT1`, le transfert reste

\[
\mathcal B_N=R_N^{(\Lambda)}+S(N)\Lambda_N(N-1)
-S(N)(\mathcal E_N+\mathcal M_N)-S(N)N.
\tag{A4}
\]

Ce raccord fixe le paiement total : estimer `mathcal E_N` ne paie ni `mathcal M_N`, ni `R_N^(Λ)` face à la référence, ni le complément long. Il ne redéfinit pas le F_N source nonunitaire. Les différences nonunitaires gardent leur poste acquis dans le raccord source.

## Famille A : poids commutant et défaut réel

Mechanism: supercharge de suppression première, anticommutant avec la parité, confronté à son commutateur avec la mesure physique raw.
Hypothesis: une petite commutation quantitative indépendante du moment orienté permettrait de transférer une information spectrale ; la petitesse proposée est mise à l’épreuve, et n’est pas admise comme input.
Observable: sur un cube complet de diviseurs, tester `||[Q0,V]||₂≤||Q0||₂||V||₂/u` avec `Q0=T+T*`, les vrais poids, matching et toutes les orientations conservés.
Conflicts: le commutateur harmonique ancien était non nul et D8/D9 non estimés ; ici la variation de Λ_N est un nouvel objet, mais aucune norme nue n’est transférée au coefficient couplé.

Les deux symétrisations réelles sont

\[
Q_{\rm phys}=TV+VT^*,\qquad Q_{\rm match}=MT+T^*M.
\tag{A5}
\]

Comme `JT=−TJ` et J commute avec V et M, **les deux anticommutent exactement avec J**, pour n’importe quelles valeurs physiques. L’anticommutation seule ne discrimine donc pas les vrais premiers du modèle. Le défaut exact à payer est

\[
TV-MT=(TV-VT)+(V-M)T.
\tag{A6}
\]

Le premier terme garde les variations physiques ; le second garde les valeurs physiques à c et le matching `S(cN)`. Aucun des deux n’est supprimé.

Premier lemme vulnérable A : la borne de commutateur en `1/u` de l’Observable pour tout cube complet admissible. Elle est une hypothèse structurale indépendante d’une petite valeur de B13, assez forte pour rendre un transfert plausible, mais **fausse dans cette portée universelle**.

À `N=100000000`, prendre le cube complet

\[
E=\operatorname{Div}(561)=\{1,3,11,17,33,51,187,561\}.
\]

Il contient les douze arêtes de suppression et leurs douze orientations transposées. Tous les sommets sont unitaires, carré-libres et dans le front. Les seuls poids V actifs sont

\[
V_{11}=\log99999989,\qquad V_{561}=\log99999439.
\tag{A7}
\]

Les autres compléments ont plusieurs facteurs premiers distincts, notamment `N−187=99999813=3·271·123001`. Sur l’arête `561→187`, de facteur 3,

\[
|[Q_0,V]_{187,561}|=
\frac{\log3}{\log561}\log99999439.
\tag{A8}
\]

Le degré du cube est 3 et chaque poids est au plus 1, donc `||Q0||₂≤3`. Chaque poids raw est strictement inférieur à u, donc `||V||₂<u`. Le nouveau signe strict

\[
\Delta_A=\log3\,\log99999439-3\log561>0
\tag{A9}
\]

suffit à montrer une entrée supérieure à 3, alors que le membre droit proposé est strictement inférieur à 3. La réfutation n’utilise pas d’approximation flottante de spectre. Le rôle6 reçoit le contrat des huit sommets, des arêtes et du signe par intervalles rationnels. Le modèle constant `S(N)Id`, qui commute exactement, n’est qu’un faux contrôle : il n’est jamais substitué au matching.

Le vrai matching du cube garde, dans l’ordre des huit sommets, les rapports

\[
M_c/S(N)=(1,2,10/9,16/15,20/9,32/15,32/27,64/27).
\tag{A10}
\]

Un changement diagonal de jauge ne répare pas une commutation exacte : pour D diagonal inversible, `[D^{-1}Q0D,V]=D^{-1}[Q0,V]D`. Une réduction éventuelle de norme doit payer ses facteurs de conditionnement et le changement des vecteurs physiques. Aucune telle réduction n’est obtenue.

## Famille B : orientation conservée dans l’opérateur signé

Mechanism: distinguer le supercharge auto-adjoint biparti et sa partie orientée, puis porter la parité dans l’opérateur réellement associé au coefficient bilatéral.
Hypothesis: une propriété d’ordre de l’opérateur signé pourrait donner une information indépendante ; la symétrisation doit auparavant prouver qu’elle conserve le coefficient, ce qui est vérifié sur la vraie mesure.
Observable: comparer exactement `1^T J(TV+VT*)1` et `1^T JTV1`, puis tester la possibilité d’un minorant de Löwner universel du bon opérateur `J(TV−VT*)`.
Conflicts: le Gram générique ne contrôle pas ce coefficient ; le présent raccord prouve explicitement quelle partie porte la masse et interdit sa disparition par symétrisation.

Premier lemme vulnérable B : la symétrisation bipartite conserve ou contrôle par coercivité le coefficient orienté. Pour tout vecteur réel x,

\[
x^T J(K_{\rm phys}+K_{\rm phys}^*)x=0,
\qquad
x^T JK_{\rm phys}x=
\tfrac12x^T J(K_{\rm phys}-K_{\rm phys}^*)x.
\tag{B1}
\]

La première égalité vient du fait que `JQphys` est antisymétrique. Elle annule aussi le modèle avec ses valeurs `S(cN)` et le résidu. Elle n’exprime aucune annulation arithmétique du moment orienté.

Sur le cube entier E ci-dessus, les enfants des deux sommets actifs 11 et 561 ont tous μ égal à +1. La somme des poids de chaque colonne active vaut 1. Par conséquent,

\[
\mathbf1^T JQ_{\rm phys}\mathbf1=0,
\qquad
\mathbf1^T JTV\mathbf1=
\log99999989+\log99999439>0.
\tag{B2}
\]

C’est un nouveau contre-transfert exact sur un cube complet, pas le test de log-concavité sur `{29,561}`. Le bon opérateur est

\[
H_{\rm phys}=J(TV-VT^*),\quad
H_{\rm match}=J(MT-T^*M),\quad
H_{\rm res}=H_{\rm phys}-H_{\rm match}.
\tag{B3}
\]

Ces opérateurs sont auto-adjoints et anticommutent encore avec J ; `mathcal E_N=1^T H_res 1/2`. Une propriété spectrale de H_res devrait donc être prouvée avec ses vrais coefficients. Elle n’est pas déduite de celle de Q0, de Gauss ou d’un Gram générique.

Une positivité de Löwner universelle est auto-filtrée exactement : si H anticommute avec l’involution unitaire J, alors H et −H sont conjugués. `H≥0` impose aussi `−H≥0`, donc H=0. Ici B2 montre `Hphys≠0`. Comprimer vers un sous-espace favorable évite cette contradiction seulement en conservant le transfert des vecteurs, les blocs croisés et tout le complément. Aucune compression arithmétique utile n’est établie. Le candidat est donc rejeté avant estimation et avant Lean ; un calcul de spectre flottant n’est pas nécessaire.

Le banc conserve également une direction négative explicite, sans calcul d’eigenvaleur. Avec `x=e187−e561`,

\[
x^T H_{\rm phys}x=-2\frac{\log3}{\log561}\log99999439<0.
\tag{B4}
\]

Rester avec K orienté ne rend pas son spectre informatif gratuitement non plus : ordonnés par m, T, TV et MT sont strictement triangulaires puisque c<m. Ils sont donc nilpotents, pour n’importe quelle mesure physique et n’importe quel matching diagonal. Une petite valeur de rayon spectral ne borne pas A3 : B2 garde un coefficient orienté positif avec un rayon spectral nul. Il faudrait une information indépendante sur les vecteurs et les coefficients, ou sur une compression transférée entièrement, plutôt qu’une lecture des seules valeurs propres.

## Garde raw, complément et paiement total

Un second cube complet est proposé au rôle6 pour les nouveaux coefficients d’opérateur : `Div(35727711=3·43·419·661)`, seize sommets et trente-deux arêtes. Son sommet supérieur a `N−m=8017²`. Sur l’arête `m=35727711`, `c=54051`, `p=661`,

\[
(TV)_{54051,35727711}
=\frac{\log661}{\log35727711}\log8017>0,
\qquad (T\,\theta_N)_{54051,35727711}=0.
\tag{C1}
\]

Le cofacteur est strictement supérieur à `a=3163`. Ce test porte sur le **nouveau coefficient matriciel**, pas sur le rejeu du PASS12 de la même factorisation. Tous les autres sommets et les orientations sont conservés ; les imports historiques éventuels sont inertes et liés par SHA. Il certifie que la représentation reste raw et contient un secteur long, sans lui donner de paiement.

Les cubes complets sont fermés pour la suppression d’un sommet admis. Ils ne couvrent pas X_N : dans l’opérateur global, les arêtes provenant de colonnes extérieures, y compris celles arrivant sur un sommet du cube, restent dans le complément. Aucun empilement de cubes n’est autorisé sans compter les incidences. L1 reste égal à 1 sur chaque colonne squarefree supérieure à 1. Les `c=1` et toutes les unités sont présents ; A4 garde la référence `−S(N)N`. Le matching signé conserve A10 et, globalement, tous ses facteurs locaux. Aucun budget de face ou de properpower ne paie un commutateur d’opérateur.

Le coût total reste donc : moment physique orienté entier ; matching signé entier ; diagonal premier et raw propre-puissance ; unité ; complément `c>a` et extérieur des cubes ; principal de référence ; raccord source nonunitaire. Si un second moment était développé, il garderait DD−DM−MD+MM, les trois formes premières de sa branche première, collisions, diagonales, conducteurs et `+1`. Aucun de ces postes n’est estimé ici.

Le registre demeure

\[
D_N=B_{\rm prime}^a+B_{\rm pp}^a+
P_{\rm bande}^{\ge2}+Z_{\rm face}^{\ge2}+I_\alpha+2\max(e,0).
\]

Zéro crédit nouveau est affecté à ce registre. H2, célibataires, faces, J0/J1, B13 et son principal, le seuil effectif BV supplémentaire et le terme couvert restent ouverts. Les crédits rough/properpowers/harmonic face/corner/mobility ne sont pas doublés. Le bracket `D_a/W_a` n’est pas remplacé par T : les cubes testent B13 transféré, et tous les vrais noyaux D/W de la route source restent dans leurs postes.

## Portée et statut

Le contre-exemple A réfute la commutation en `1/u` **universelle sur les cubes admissibles**, à `N=10^8`. Il ne réfute pas un théorème quantitatif limité au domaine source `u≥10^24`, ni une propriété globale après sommation prouvée indépendamment. B1 et l’obstruction de Löwner sont des identités finies uniformes, mais elles n’estiment aucun moment. C1 garde le support raw ; il n’établit aucune asymptotique. Aucun seuil source ou BV n’est déduit du banc exploratoire.

L’information indépendante obtenue est négative et précise : la parité bipartite persiste avec toute mesure diagonale, la petite commutation proposée échoue sur le vrai poids, et la symétrisation supprime l’orientation requise. Aucun lemme positif nouveau susceptible de payer B13 n’a survécu. Les promotions sont rejetées mathématiquement avant Lean ; aucun message de compilateur ni échec Lean n’est fabriqué. Cumul conservé : 13 modules, 169 théorèmes auxiliaires ; aucun module13 soumis, victoire fausse.

Statuts : `PHYSICAL_PARITY_ANTICOMMUTATION_EXACT_ONLY` ; `UNIVERSAL_INVERSE_U_COMMUTATOR_TRANSFER_FALSIFIED` ; `SYMMETRIZATION_ORIENTED_MOMENT_TRANSFER_FALSIFIED` ; `UNIVERSAL_LOEWNER_POSITIVITY_SELF_FILTERED` ; `MATCHING_C1_REFERENCE_LONG_COMPLEMENT_UNPAID` ; `NO_QUANTITATIVE_CANDIDATE_SELECTED` ; `VICTORY_FALSE`.

## Reçu nouveau définitif et empreintes

Le rôle6 a confirmé le gel de `operator.json`, statut `PASS_NEW_ACTUAL_OPERATOR_IDENTITIES_ONLY`, et son rejeu intégral avec les deux nouvelles banques13 : tous champs JSON et tous octets identiques. Aucun ancien entrypoint PASS n’a été rejoué. Les cubes ont bien 8/12 puis 16/32 sommets/arêtes, et les quatre falsificateurs sont conservés avec des certificats de signe rationnels. La conservation des 514 anciens artefacts est contrôlée par le rôle6 ; l’idéateur ne relance pas son contrôle.

Les intervalles du reçu donnent notamment les enveloppes rationnelles strictes suivantes, vérifiées en lecture seule par comparaison exacte des fractions du JSON : `6/5<Delta_A<13/10`, `36<1^T JTV1<38`, `−41<` numérateur de B4 `<−40`, et `58<log661·log8017<59`. Les dénominateurs logarithmiques de B4 et C1 sont strictement positifs. Ce sont des signes finis à N=10^8, pas des estimations au seuil source.

| Artefact définitif | SHA-256 |
| --- | --- |
| `round13/operator_checks.py` | `64fcc468c5df6672ac123ee6103cef9ce0739052c3367be7593bac3aea78c9f2` |
| `round13/operator.json` | `d2c1cd93571533777de9c09bcc94c575098500ae59929fb3774ad1f940c9be8e` |
| `round13/shared.py` | `2eba4c18b1013677a168e99a7e896146a63bdcff4dee1180c1c4ba2e4323b43d` |
| `round13/numerical_replay.json` | `73b8b29449601032016218afa9a49873925426b9d32efe33393fe312a3163b3c` |

Les flags `global_D_N`, `asymptotic`, `payments`, `Lean_called` et `victory` restent faux. Le bon opérateur H est exposé pour une recherche ultérieure, mais aucune propriété quantitative indépendante qui paie son coefficient réel n’est sélectionnée. Le rapport est gelé après intégration de ces reçus ; aucun ajout futur n’est annoncé dans ce fichier.
