# ψ auteur01 — échec réel conservé

La gate ROOT 24a5a041… a autorisé un seul launcher STOPFIRSTFAIL. Core a été
le seul enfant : START 2026-10-03T10:28:31.682668Z, FIN 10:29:02.682817Z,
exit 1, aucun olean. BetaLimit, Integral et Duplication n'ont pas été invoqués.
Le reçu réel 273774ecce0500c970ecac573a6a541be786dae1ea9d52e647aaad21ef048f20
et le log 1128364831728b06a269a279a56534a2d3c4144fa0da80d7c34c641f9e6a38ed
ont été lus FULL (09499e / 61387b). Le POST a été parsé pour son intégrité et
ses nombres de bindings seulement (a6c9ff) : 47 inputs et 6476 artefacts du
cache inchangés ; SHA fd644afe1383eb1a545e3d0b1fc21f6c22978cf2583a54911e6b924bda53d808.
Cette lecture du POST n'est pas une lecture humaine FULL de ses 1,64 Mo.

À la ligne 149, `rw zero_add` cherchait un motif sous une composition non
réduite. Le but affiché contient `((fun t => ...) ∘ betaStep) n`. La révision
réduit d'abord `Function.comp_apply`, puis simplifie `zero_add` et le cast de
zéro avec `simp only`, qui tolère l'absence d'un motif déjà simplifié. Ensuite
la vraie identité betaDifference_eq_ratio et R_z(0)=1 sont réécrites ; aucune
limite nouvelle n'est admise.

À la ligne 156, `0..1` a été lexé avec `0.` de type Float, dans une notation
d'intégrale sur un ensemble. Le compilateur attendait `Set ℝ`. La ligne 163
est une conséquence de ce domaine métavariable et non une dette Fubini.
La révision écrit la notation d'intervalle `0 .. 1` avec les deux espaces.
Les preuves d'intégrabilité des deux vraies intégrandes bêta restent intactes.

17 déclarations du Core ont produit des prints d'axiomes standards ; les deux
déclarations finales ont produit sorryAx par récupération après erreur.
Le module a échoué : ces lignes ne constituent ni un PASS ni des acquis nouveaux.
Aucun token de preuve incomplet n'était ajouté dans la source. La même notation 0 .. 1 est aussi corrigée dans BetaLimit et Integral ;
Duplication reste byte-identique à la première préparation. Il n'y a pas de
contre-exemple analytique établi, pas de diagnostic d'obstruction de parité,
pas de replay numérique et pas de retry implicite.

Le dossier revision02 est distinct ; source_final et psi_batch01_attempt01
originaux restent immuables. La nouvelle invocation exige sa propre gate ROOT.
