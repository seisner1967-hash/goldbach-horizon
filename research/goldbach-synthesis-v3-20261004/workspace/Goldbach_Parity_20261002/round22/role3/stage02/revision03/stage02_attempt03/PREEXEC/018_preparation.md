# ROLE3 — fenêtre finie G0, étape02

Statut : PREPARED_SOURCE_ONLY. Le Kernel revision02 a réellement compilé une fois, exit0, START07:14:47.195648UTC et FIN07:15:17.486606UTC. Son source b465bf53b124fa158eed1b5f01171d18ce7f8d7252bf27cf30db1ed7575a773c et son olean 9bf2da2b6cb3a5780868c51916afdf173e79a971d56fdf7a52c6b2abfa9def8d sont des dépendances immuables. Ses 33 audits ont exclusivement les axiomes standards ; log70182795d884a636bf5c89904a21ee83f4ce9c83fea2c718093a60cb2a275886, FULL41e1f7. Il ne sera pas recompilé par cette étape.

EpsteinFinite22 définit l’intégrande d’origine, la fenêtre entière symétrique, son intégrale et les deux sommes de bords. Il dérive le raccord rpow, l’intégrabilité de chaque cellule, la substitution affine avec jacobien signé, la bijection n→−n pour le signe négatif et le télescopage entier effectif. Les bords sont précisément Q+1..Q+q et−Q..−Q+q−1. Les sommes finies décrivent des translations géométriques ; aucune méthode arithmétique interdite n’est utilisée.

Les API Finset.sum_bij, Int.Icc_eq_finset_map, sum_range_add, intégrale affine et integral_finset_sum ont été inspectées en source mathlib4.15. Aucun sondage Lean n’a été ajouté. La preuve entière source demeure non compilée, avec 18 audits qualifiés prévus. L’étape suivante d’infini et la queue sont hors de ce gate.

run_stage02_once.py exige une nouvelle autorisation root : role=ROLE3, node_id=16.1, attempt=stage02_attempt01, stage=G0_FINITE_STAGE02, authorized=true, numeric_verdict=EPSTEIN_UNFOLDING_AUX_PASS, modules=[EpsteinFinite22], source_manifest_sha256, launcher_sha256, python_sha256, lean_sha256, dependency_olean_sha256=9bf2da2b6cb3a5780868c51916afdf173e79a971d56fdf7a52c6b2abfa9def8d, no_win=true. Il invoque exclusivement Finite UNE FOIS, avec l’olean Kernel réel sur LEAN_PATH, sortie neuve, PREEXEC, START, commande/log/exit, POSTEXEC et reçu. Aucun retry, autre module, Python math, version probe ou rejeu du banc numérique.

Commande future actuellement fermée :

`PythonCanonical -B -X utf8 role3/stage02/run_stage02_once.py --gate C/messages/round22_role3_stage02_authorization.json --attempt stage02_attempt01`

Les cinq FINAL2 et leurs lectures FULL restent liés au manifest. L’erreur réelle de la première tentative Kernel est conservée dans l’historique distinct ; son échec technique n’est pas une réfutation de la formule. Cette préparation est metadata seulement et ne compte aucune nouvelle compilation. Baseline officielle57modules/942aux inchangée avant le Juge indépendant. Aucune identité de diffusion, chaleur, coefficientN, majoration D_N ou victoire n’est créditée ici.
