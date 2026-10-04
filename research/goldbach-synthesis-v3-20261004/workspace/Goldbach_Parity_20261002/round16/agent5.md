# Boucle16 — Juge indépendant FINAL

**Audit unique terminé exit0 ; deux compilations indépendantes réussies. Résultat partiel pertinent, score0, victoryfalse.** Le vrai premier impair absent de N possède désormais une marge certifiée sur la vraie série singulière. Aucune estimation de sa première incidence, de la capacité après union ou du résidu entier D_N n'est obtenue ; la condition de victoire n'est pas satisfaite.

## Certificat mathématique réellement contrôlé

Le Juge a lu intégralement les cinq rapports FINAL1/2/3/4/6, les deux nouveaux modules Lean, les deux producteurs numériques et leur helper. Il a examiné les vrais journaux échoués du rôle3 et la définition source immuable de `GoldbachRound11.twinConstant` et `singularSeries`.

Le théorème principal compilé est `GoldbachRound16.Anchor.canonical_least_missing_prime_margin` :

```lean
{N : ℕ} (hN : N ≠ 0) (heven : Even N)
(hC2 : (2541 / 4096 : ℝ) ≤ GoldbachRound11.twinConstant) :
  (1 / 144 : ℝ) ≤ GoldbachRound11.singularSeries N -
    Real.log (GoldbachRound16.Anchor.leastMissingOddPrime N : ℝ)
```

`leastMissingOddPrime N` est sélectionné par `Nat.find` parmi les vrais premiers impairs qui ne divisent pas N. L'existence, la primalité, le caractère absent et la divisibilité de N par tous les premiers plus petits sont prouvés. Le cas N=0 est un sentinel explicite, exclu de l'énoncé.

Le terme C2 est le vrai tprod de la définition source. Sa convergence est dérivée par les produits finis antitones, la queue réelle est minorée via le télescopage entier, l'annulation des facteurs locaux est démontrée et la vraie somme harmonique est contenue dans le produit eulérien fini. Ces obligations ne sont pas des hypothèses substituées à la marge. L'input `2541/4096 ≤ twinConstant` est l'enclosure acquise explicite de la monographie ; il intervient dans les petits cas3/5/7/11. Le volet p≥13 ne l'utilise pas.

Le module4 apporte la marge harmonique et les logarithmes certifiés. Son import fresh est utilisé par le module3. Aucun réel S libre, aucune hypothèse égale à A7, aucun partenaire premier ou densité d'incidences n'est supposé. A7 est donc une nouvelle minoration arithmétique effective ; elle demeure un résultat auxiliaire. A9 et ses gardes U4 sont un raccord conceptuel écrit, **pas un nouveau théorème Lean compilé dans cette boucle**.

## Gel et exécution observée

Après réception de FINAL3, le gel a fixé78 fichiers et les cinq rapports FINAL. Le manifest `judge/input_sha256.json` vaut `7b0208501306518ad40dad01d254e26314755afedb4c0d93f8a1c62fbc984d58`. Le rôle3 avait terminé sa production avant ce gel ; aucune source gelée n'a été corrigée pendant l'audit.

Une seule invocation de `judge/launch-audit-once.py` a lancé le contrôle final, avec capture de stdout et du code de sortie à cette exécution. Le launcher refuse une seconde invocation de journalisation. La session34719 a fini exit0 le2026-10-02 à18:49:59UTC. Aucun producteur numérique, ancien banc, ancien module Lean, ancienne dépendance ou rendu PDF n'a été exécuté par le Juge.

Le contrôle a d'abord vérifié les inputs figés, les copies et les coefficients numériques stockés, puis compilé uniquement les deux nouveaux fichiers dans `judge/build`. La source4 fresh et son olean fresh ont été utilisés pour compiler3 ; les olean historiques de `round13/role3/dependencies` ont été lus sans reconstruction. Lean4.15.0 SHA `8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08` et le commit mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608` ont été vérifiés.

| Nouveau module | Théorèmes propres | Définitions propres | Résultat Juge |
|---|---:|---:|---|
| LeastMissingPrimeMargin |9|0|exit0, zéro erreur, zéro warning|
| EulerAnchor |27|8|exit0, zéro erreur, zéro warning|

Les36 sorties `#print axioms` sont exactement celles des36 déclarations nouvelles ; leurs axiomes sont seulement propext, Classical.choice et Quot.sound. Le scan des fichiers finaux trouve zéro token interdit sorry/admit/axiom/native_decide. Les théorèmes importés, anciennes définitions et certificats numériques ne sont pas recomptés. Le cumul est17 modules et244 conclusions auxiliaires ; les huit définitions nouvelles sont comptées séparément.

## Numérique en lecture seule

Le schema actuel du manifest numérique est vérifié :30 bindings, deux producteurs neufs, chacun un essai canonique exit0 et une copie isolée unique. Le Juge compare les octets complets et les champs complets de chaque gate et copie existante, sans les relancer. Sources, snapshots, vrais journaux, reçus canoniques/replay, imports historiques et rapports conceptuels sont liés par SHA.

Les1879 positions de certificats/signes ont des bornes rationnelles ordonnées et un signe strict compatible :654POSITIVE,95NEGATIVE,1130ZERO ; aucun flottant ni signe UNRESOLVED. Ce sont des positions de certificats, parfois répétées par la structure du fichier, et non1879 théorèmes indépendants. Les égalités des polynômes logarithmiques stockés, les fronts, unités, profils physiques, parties positives et sommes signées sont vérifiés séparément. Les kernels W stockés ne sont pas recalculés.

Banque1 : le support d77 est complet sur129870 entiers,51948 unités,216 incidences structurelles β réparties[0,106,110]. Le vrai défaut TypeI3 uniforme vaut38, le corrigé2, et la différence36 est gardée. Les vrais vecteurs vérifient Gamma=Gamma_star+L3 ; les trois signes sontNEGATIVE. Theta a[5067,5079,0] premiers ; les neuf properpowers raw sont conservés en classe0, sans filtrage μ(n)². La correction locale ne paie ni Gamma_star, ni TypeII, ni les vrais parents. Aucun kernel D/W n'est prétendu évalué dans ce banc.

Banque2 : tous201 entiers q sont testés ;18 q premiers donnent34 cœurs complets et612 vertices physiques distincts. Les128 profils D/W couvrent tous les axes actifs et les contrôles e1/e3 ; les484 autres termes sont exactement nuls, avec W littéral non estimé. Les branches e1, tous les cœurs premiers avec Λ(e) et les rangs2 sont gardés. Les95 incidences premières comprennent zéro e1 et trois e3 ; chaque ressource physique est consommée une fois. Les deux endpoints du déficit principal et la somme réelle entière sontPOSITIVE. Aucun signe source U4 n'est appliqué à N=10^8.

Quatre falsifications locales ont de vrais témoins : centrage TypeI3 uniforme exact, capacité e3 suffisante gratuitement pour tout le corps sélectionné, suppression de Λ(e), et réutilisation d'une capacité e3 pour plusieurs demandes. La promotion du signe A9 au fini a un seul statut NO_COUNTEREXAMPLE_IN_WINDOW, issu des trois points e3 observés ; elle ne devient pas une preuve source ou universelle. Zéro échec numérique réel a eu lieu.

Les champs false du préflight de conservation concernent uniquement l'action du préflight. Le manifest numérique FINAL précise leur portée statique ; les deux lancements réels sont prouvés par leurs reçus de lancement. Aucun ancien PASS ou reçu n'a été réécrit.

## Échecs Lean réels et diagnostic

Le rôle3 a exécuté13 invocations distinctes : un probe API et12 compilations du candidat. Neuf exit1 sont effectivement archivés, avec leurs snapshots et journaux ; quatre PASS intermédiaires4/9/11/13 correspondent à des sources étendues différentes. Le rôle4 a un essai producteur exit0. Les deux compilations supplémentaires du Juge réussissent ; aucune tentative n'est inventée ou relancée pour obtenir un autre journal.

| Échec rôle3 | Cause effectivement visible dans Lean |
|---|---|
|1|Noms API indisponibles dans le probe|
|2|Réduction bêta, coercitions, commutation et syntaxe d'induction|
|3|Normalisation du dénominateur du télescopage|
|5|Type du sup fini, focus d'un lambda et soustraction castée|
|6|Normalisation d'un numéral réel|
|7|Conditionnelle du facteur local et API d'un comparateur|
|8|Inférence du domaine d'indices|
|10|Évaluation des petits préfixes premiers finis|
|12|Réduction du if dépendant dans la sélection canonique|

Ces erreurs sont techniques. Les sorryAx imprimés dans certains journaux échoués décrivent leurs buts restants et ne figurent dans aucun certificat final. Lean n'a pas diagnostiqué une impossibilité analytique de parité dans ces essais. La disponibilité des premiers et la comparaison entière sont des obligations encore non prouvées, pas des messages du compilateur.

## Conservation et décision finale

L'inventaire exact des701 artefacts protégés, leurs ajouts/suppressions possibles et tous leurs SHA sont vérifiés avant et après. Le controller15 lie ses49 outputs, plus lui-même ; les deux documents originaux gardent leurs empreintes. Registry16 `5939d791139dbb3f9b26e5d1f372bbdf98d1927f9aaf2c5e9c22aa0a4e35d043`. Controller15 `7b2522fbeec0c17965b9bfba4df418552f0e31b2b4881c91edff00b79a81869f`.

Le ledger conserve D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0), les rawproperpowers, whole U_a, originalalpha/Q, modèles S(bN), c1/e1/b1, référence−S(N)N, cofacteurs longs, J0/J1/J2 restants, célibataires/faces/nonbulk, P5/K2 entier avant retrait et onset BV supplémentaire. Sourceu≥10^24 et N=10^8 restent distincts.

**Décision : garder A7 canonique et la correction TypeI locale comme acquis partiels. Ne pas déclarer de victoire.** Il manque une estimation indépendante de la masse des incidences q,N−p0q, de Gamma_star/TypeII et de la comparaison globale des capacités après union. A7 n'assure pas qu'une capacité favorable soit présente ; une famille vide contribue0. D_N≤N/(256logNloglogN) demeure non démontré.

| Pièce d'audit | SHA256 |
|---|---|
| judge_receipt.json |1bfca8e4e8e8a532f4f59aeb8e2299a5b67573e6f8c5c40811c886a317d4d30b|
| audit_launch_receipt.json |d5e5ae5599bcbbd37b5f974eabe349014d2796f66f27b83993bfa80bb5382b89|
| audit_launch.log |6cfde58ac4bc48fad73dbde2676c3ff457d0e22b170ce9269e2a5b9673928751|
| run-audit.py |1209dc2db0f04d3969ca304e687b818672d53b9f57bbb0b0b77437e599429bfa|
| LeastMissingPrimeMargin fresh log |91504945ea420cb4a870d7c98ae5d2d0ae9f3d80937a6a848ed8ceababc02199|
| EulerAnchor fresh log |294db524bf4fc766fdb10f3428cdea8eccaa32a7016e171e058252d973afa812|

**Score0. Result : CANONICAL_REAL_SINGULAR_MARGIN_COMPILED, GLOBAL_INCIDENCE_UNESTIMATED, VICTORY_FALSE.** Aucun input ou output gelé ne sera modifié après ce FINAL.
