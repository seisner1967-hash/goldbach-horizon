# FINAL4 — changement D/P non-SS à tous les rangs

Les cinq nouveaux modules ont réellement compilé sous Lean 4.15.0, sans
erreur, warning, `sorry`, `admit`, axiome ajouté, `native_decide` ou `trustMe`
dans les sources finales. Les 160 commandes `#print axioms`, dont deux pour
des lemmes d'extension générés, impriment seulement `propext`,
`Classical.choice`, `Quot.sound`, ou aucune dépendance. Les sources contiennent
100 théorèmes explicites, 55 définitions et 3 structures. Il s'agit du résultat
du producteur ROLE4, à examiner par le Juge indépendant. Aucun cumul officiel
n'est augmenté ici. Score absolu 0, aucune victoire et aucune borne nouvelle
sur D_N.

La branche 14.4 est réellement sélectionnée. PROBE19, FINAL2, son contrat de
test, le prompt d'exécution 14.4 et feedback18 ont été intégralement lus.
Les skills Arbor executor et merge-eval sont appliqués dans l'ownership
`round19/role4/**` et ce rapport. Les dix dépendances historiques sont liées
dans `dependencies_readonly.json`, dont les oleans audités indépendamment
Judge18 et Judge16. Elles restent en lecture seule, sans recompilation ni
nouveau décompte de leurs théorèmes. Le cache mathlib est celui de Lean 4.15.0
et du commit `9837ca9d65d9de6fad1ef4381750ca688774e608` ; aucune installation
n'a été effectuée.

Le coordinateur a inspecté le nouveau PASS numérique canonique unique avant
d'accorder explicitement `ROOT19_FORMAL4_COMPILE`. Le gate effectif
`role4/root_compile_authorization.json`, SHA256
`6ccdfc20f4a95fc84733532b83cb3d0f773378ec11504b40a48c83d026026a5d`,
lie 26 fichiers numériques et leurs captures. Ce rôle ne lance aucun producteur
numérique, aucune évaluation du Juge et aucun replay. Ce gate autorise les
réparations techniques après un échec réel et interdit une nouvelle compilation
d'un module déjà PASS.

1. `TerminalPrimeExtraction.lean`, PASS à la tentative 02, définit le facteur
   maximal effectif par `Nat.primeFactors.sup id`, relie son appartenance à la
   véritable `primeFactorsList`, extrait `n=h*r`, prouve son ordre et son
   unicité, et conserve `Omega(n)=Omega(h)+1`. Les puissances répétées sont
   comptées ; le cas 3^3 donne h=3^2 et conserve la possibilité r|h. Le
   raccord P+(1)=1 est traité par `largestPrime`.
2. `BalancedResourceSwitch.lean`, PASS à la tentative 05, étend le raccord
   canonique de coprimalité aux ressources composites de tous rangs, sans
   quotient supposé premier. Pour un anchor libre, d|p-1 reste explicite.
   Les extractions réelles donnent les deux orientations D/P ; le sélecteur
   impose les primalités et les ordres de chaque canal. Dans P, les petits
   facteurs a et b sont premiers tandis que x et y sont les cofacteurs
   composites. L'égalité de produits est affectée à D. `encode_decode`
   prouve la suffisance du sélecteur factoriel complet. C=min(h1*h0,r1*r0),
   C^2<=n1*n0 et C<N sont des conclusions prouvées.
3. `SignedHyperbolicCRT.lean`, PASS à la tentative 07, construit x0 par
   Bezout et reste entier, y0 par division entière signée, et t dans Z.
   L'équation réelle donne x=x0+b*t, y=y0+p0*a*t et
   q=N-a*x0-a*b*t. `SignedGuard` contient les fronts de signe, le sélecteur
   factoriel complet et les contraintes de canal ; ses reconstructions
   sont réciproques. L'inverse est prouvé sur le sélecteur complet.
4. `NonSSBracketSwitch.lean`, PASS à la tentative 09, définit la famille
   physique S privé de SS avant le masque n_e premier. Le sélecteur SS
   reprend exactement le programme18 : minFac<=Z et quotient premier,
   pour les deux ressources. L'ordre strict du quotient n'est pas ajouté
   au sélecteur fini. Les unités, e squarefree, e>p0, q premier, M et le
   cap original Q=floor((N-1)/alpha) restent explicites. Les équivalences
   de subtypes, y compris coordonnées signées, reindexent le vrai
   `GoldbachRound11.sourceBracket`. Theta et raw Lambda sont distincts ;
   leur différence pour les puissances propres reste littérale, sans
   filtre mu(n)^2 ajouté à raw Lambda. D/P et les trois strates conservent
   intégralement les sommes medium et longues. Le produit physique e*q
   est injectif sur ce support sous le front indépendant M^2>N. Un m1
   non squarefree a bracket nul ; m0 a raw/theta nul sous q>p0 avec les
   vraies hypothèses de premiers distincts.
5. `RankTwoHarmonic.lean`, PASS à la tentative 12, somme les vrais entiers
   premiers et leurs produits ordonnés p<=q. L'unicité et la disjonction
   rang1/rang2 sont prouvées, p^2 est conservé, et la réciproque vient du
   multiset réel de longueur 1 ou 2. Le cut h<=B est exactement le filtre
   Omega de [2,B]. Le cofacteur terminal réel d'une ressource de rang2/3
   appartient à ce cut sous h<=B, par le théorème d'extraction. L'identité
   H8 est H2=S1+(S1^2+S2)/2 et conserve la correction diagonale S2/2.
   Aucun profil libre de représentation, input de densité ou cardinal
   supposé n'est utilisé.

Le seuil auxiliaire H9 est B_hyp=floor(N^(1/8)), distinct du B original fixé.
La couche rank3short, ses nouveaux rho/cofacteurs composites, ses conversions
Selberg/Mertens/totient/floors et son onset annoncé u>=10^40 ne sont pas prouvés
par ces fichiers. Le source u>=10^24 reste inchangé. Le segment intermédiaire,
les rangs>=4 et les conducteurs medium/longs ne sont pas payés. Aucune
disponibilité, petite Gamma, capacité suffisante, borne H9 ou cible D_N ne
sert de prémisse de victoire. H4 conserve la somme sans lui donner un signe
ni une estimation. H7 analytique, T_A, l'union physique des capacités et le
ledger complet restent ouverts. L'identité harmonique ne contrôle pas les
formes bilinéaires pondérées par les deux primalités effectives.

`build.py` conserve un PREEXEC exclusif avant chaque subprocess Lean : source
et lanceur capturés, commande/cwd/LEAN_PATH/compiler SHA, hashes du gate, du
nouveau numérique et des dix imports readonly, log intégral, exit et reçu.
Les modules PASS sont figés par source/olean SHA ; ils n'ont été ni modifiés
ni recompilés après leur premier PASS. Les 12 subprocess Lean se répartissent
en 5 PASS et 7 FAIL. Chaque FAIL est technique et distinct d'un échec
mathématique de parité :

| Tentative | Module | Résultat et cause réelle |
| --- | --- | --- |
| 01 | Terminal | FAIL : inférence de Finset.le_sup/id, positivité dans Nat.div_self, expansion de facteurs par simp/norm_num dépassant la récursion. |
| 02 | Terminal | PASS : 22 prints, aucun warning. |
| 03 | Balanced | FAIL : absence de Decidable pour le canal ; projections de ressources insuffisamment explicites pour les bornes naturelles. |
| 04 | Balanced | FAIL : borne Nat.sub_lt et simplification prématurée du minimum et du prédicat de branche. |
| 05 | Balanced | PASS : 41 prints, aucun warning. |
| 06 | Signed | FAIL : type attendu manquant avant trans ; unpack simplifié avant la réécriture de l'inverse. |
| 07 | Signed | PASS : 34 prints, aucun warning. |
| 08 | NonSS | FAIL : collision avec le conductor de mathlib ; alias/projections de produits non réduits ; division naturelle hors de portée d'omega ; lambda produit non réduite avant réécriture. |
| 09 | NonSS | PASS : 39 prints, aucun warning. |
| 10 | Harmonic | FAIL : produit cartésien explicite non reconnu par les réécritures en notation ×ˢ ; tactic ring après but déjà clos ; un binder inutilisé. |
| 11 | Harmonic | FAIL : commutativité des deux inverses dans la somme double. |
| 12 | Harmonic | PASS : 24 prints, aucun warning. |

Une invocation antérieure du lanceur Python a échoué à la lecture syntaxique,
avant tout subprocess Lean : `entry.update` mélangeait paramètres nommés et
paires de dictionnaire. Son source exact et son log ont été capturés après
l'échec sous `launcher_failed01_source_POSTEXEC.py.txt` et
`launcher_failed01.log`, avec reçu `launcher_failed01.json`. Ils ne sont pas
présentés comme PREEXEC. La réparation est limitée à l'appel entry.update.
Cet événement ajoute zéro compilation Lean et zéro échec mathématique.
Le lanceur corrigé a SHA256
`fd59294942a1bab559b929f2678a51808fb19c33717a0ee3775821bd8ef08641`.
Les `sorryAx` internes imprimés lors des FAIL sont conservés dans leurs logs ;
aucun ne subsiste dans les cinq logs PASS ni dans leurs fermetures d'axiomes.

`preparation.json` conserve l'état initial réel des sources à 00:15:25 UTC.
Avant le premier Lean, les améliorations statiques ont explicité les
quantifications d'ordre, les produits monotones Nat, puis le raccord direct
du cofacteur effectif au cut H8. Ces edits ne sont pas comptés comme échecs.
Le rapport DRAFT précédent est conservé avant son remplacement par ce FINAL.
Le manifeste final et son reçu lient les sources/oleans finales, tous les
PREEXEC, les logs/exit, le gate, le lanceur et les dépendances. Leur préparation
ne relance aucun calcul mathématique, compilateur ou Juge.

Résultat à transmettre au coordinateur : formalisation auxiliaire effective
réussie, score 0. Une décision du Juge indépendant et les estimations
analytiques manquantes sont encore requises ; la condition de victoire
Goldbach n'est pas satisfaite.
