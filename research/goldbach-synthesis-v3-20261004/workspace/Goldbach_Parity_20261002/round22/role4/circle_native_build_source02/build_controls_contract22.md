# BUILD_ONLY SOURCE02 — correction normative du CWD, aucune exécution

Le rapport SOURCE du Juge a identifié le désaccord entre le plan natif02 gelé
330ef397 (CWD=native02) et le parent build01 d19714a2 (CWD=ACTUAL).
Les deux anciens paquets, leurs handoffs et leurs reçus restent immuables.
Aucune gate ni compilation n'a précédé cette correction ; ce n'est aucun échec
arithmétique ou de parité. Le backend a4dcc246, les deux CPP, les arguments de
compilation, les quotas et les contrôles PREPOST ne changent pas.

Le nouveau plan effectif est `build_execution_plan22.json`. Il lie par SHA le
plan SOURCE natif02, mais remplace explicitement son CWD par le dossier neuf
`circle_native_build_source02/actual_build02_attempt01`. TEMP et TMP sont tous
deux son sous-dossier `tmp`. Le préflight exige ce CWD et ce TMP exactement,
les six variables de l'environnement propre du backend, aucun héritage de
environnement, le SHA du backend et les mêmes compiler/CPP/arguments. Le plan
effectif doit aussi correspondre au SHA dans la préparation et la gate futures.
Le backend reçoit exactement ACTUAL comme cwd : les fichiers temporaires
restent donc dans le répertoire surveillé. Aucun déplacement vers native02.

Le futur reçu porte deux références distinctes : `native_source_plan_sha256`
et `actual_build_plan_sha256`/path, plus CWD et TMP réellement sélectionnés.
Le champ historique `build_plan_sha256` reste le SHA du plan SOURCE natif02
pour le parent numérique gelé ; il ne certifie pas que son ancien CWD a été
appliqué. Avant une éventuelle gate numérique, le lecteur devra contrôler aussi
ce plan effectif et son lien avec le reçu. Aucune préparation numérique ne
résulte de cette compatibilité de format.

Autorités distinctes : nouveau gate ROOT
`round22_native_build02_authorization.json`, préparation locale future
`build_preparation22.json`, unique essai `actual_build02_attempt01`.
Toutes ces entrées sont absentes aujourd'hui. Deux drivers g++ au plus,
STOPFIRSTFAIL, zéro retry, aucune exécution des binaires produits. Backend
identique : active16/total32 observé, commitJob2GiB, RSS individuel2GiB,
RSS agrégée4GiB surveillée, wall partagé300s ; logs1MiB, copies32MiB,
metadata16MiB, binaries64MiB chacun, tmp64MiB, outputs256MiB surveillés.
Le RSS agrégé et les tailles de disque restent des moniteurs, pas des quotas
agrégées OS/NTFS. PREPOST originaux/copies/3089archives sont maintenus.

SOURCE_ONLY_NOT_PREPARED_NOT_COMPILED. Includes/imports effectifs, ABI,
ressources exercées et succès du build sont ouverts. Aucun --version/help,
préprocesseur, compiler, native runtime, Python candidate import/parser ou
calcul mathématique n'a été appelé. Au futur succès, le statut resterait
NATIVE_BUILD_EXIT0 ; coefficientN, H1, D_N et WIN demeurent ouverts.