# ROLE3 — sources G0, première étape de compilation proposée

Statut : PREPARED_SOURCE_ONLY, aucune invocation Lean/APIprobe/PythonMath parROLE3. Sélection effective16.1 et FINAL2 ont été lus intégralement. Les fichiers préparatoires précédents restent gelés.

EpsteinKernel22.lean définit un noyau réel indépendant du résultat recherché. Ses preuves source dérivent le raccord rpow, la primitive, la FTC sur tout intervalle orienté, les limites aux deux infinis et l’intégrabilité réelle, puis l’intégrale complète et l’inégalité de déficit continue. Aucun Integrable, HasDerivAt ou résultat cible n’est admis en prémisse générale pour ces conclusions.

EpsteinFinite22.lean est en préparation SOURCE, hors de cette étape de compilation. Il définit le noyau décalé original, la fenêtre Finset.Icc symétrique et l’intégrale effective de sa somme. La substitution conserve le jacobien signé. Les preuves source contiennent la bijection du signe négatif et le vrai télescopage entier, obtenu à partir de deux décompositions de sommes finies. Les deux bords ont les extrémités Q+1..Q+q et−Q..−Q+q−1. Il s’agit d’un découpage de coordonnées géométriques; aucune méthode arithmétique interdite n’est utilisée.

Ces preuves source sont **non compilées**. Les noms d’API, détails d’élaboration, conversions d’indices et tactiques seront jugés sur leurs sorties effectives, jamais présentés comme PASS au stade présent. Le déroulement infini, l’enveloppe de la fenêtre, le mode m=0 et l’assemblage cusp0 complet demeurent hors de cette première étape et en développement. La diffusion de Friedrichs, Mellin, chaleur, coefficientN et D_N restent ouverts. Cette étape n’est pas une victoire ni G0 complet.

run_stage_once.py propose UNE SEULE invocation de Kernel, avec outputneuf et sans retry. Finite n’est pas invoqué par ce launcher. Tous les inputs sont vérifiés puis capturésPREEXEC ; unSTART précède l’enfant Lean ; commande, log, exit, hasholean, POSTEXEC et reçu sont conservés. Le launcher exige un gate root explicite lié aux hashes du manifest, du launcher et des deux runtimes, avec le verdict numérique auxiliaire réel et no_win=true. Il ne compile rien lors de sa préparation.

Commande future, actuellement fermée :

`PythonCanonical -B -X utf8 round22/role3/run_stage_once.py --gate C/messages/round22_role3_stage01_authorization.json --attempt stage01_attempt01`

Le gate demandé a les champs role=ROLE3,node_id=16.1,attempt=stage01_attempt01,stage=G0_KERNEL_STAGE01,authorized=true,numeric_verdict=EPSTEIN_UNFOLDING_AUX_PASS,modules=[EpsteinKernel22],source_manifest_sha256,launcher_sha256,python_sha256,lean_sha256,no_win=true. Les chemins absolus effectivement proposés sont dans le manifest et le launcher. Ce document n’ouvre pas ce gate.

Les imports portent sur calcul différentiel réel, mesure/intégrales, racines/pouvoirs, intervalles entiers, opérations finies et tactiques. Aucune identité de LSeries, convolution de vonMangoldt, Möbius, crible ou estimation de progression n’est utilisée par cette étape.

Baseline historique57modules/942aux, score0. Modules nouveaux vérifiés parROLE3 :0. Toutes les déclarations explicites source ont un #print axioms qualifié pour la validation future et le Juge indépendant.
