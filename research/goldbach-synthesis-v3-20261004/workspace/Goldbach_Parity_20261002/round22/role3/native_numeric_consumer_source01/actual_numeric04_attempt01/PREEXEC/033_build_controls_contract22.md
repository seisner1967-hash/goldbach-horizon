# BUILD_ONLY03 — confiance Windows/GCC explicite, SOURCE uniquement

La version03 remplace le prérequis de fermeture universelle du loader par un
périmètre de confiance explicite pour deux compilations standard déjà définies.
Les sources native02, build01 et build02 sont conservées. Les CPP, le backend
Windows a4dcc246, les arguments g++ statiques, les quotas et STOPFIRSTFAIL
restent identiques. Le nouveau dossier d'essai est actual_build03_attempt01 ;
CWD est ce dossier, TEMP et TMP sont son sous-dossier tmp, avec les mêmes gardes.
Aucune exécution des .exe produits et aucune autorisation numérique implicite.

## Ce qui est établi par les métadonnées et ce qui est assumé

La pièce ROLE6 pe_static_import_observation22.json SHA36032c45 est liée readonly.
Elle décrit66images/825imports PE, dont119arêtes avec candidats locaux liés au
snapshot6332, et706arêtes Windows/API-set. Le parent vérifie les SHA/tailles des
images contre les bindings, l'égalité des descripteurs et des arêtes, les
candidats locaux et les deux classifications. Il n'appelle pas un parseur PE,
LoadLibrary, dumpbin ou outil similaire pour cela : il lit la pièce existante.
La méthode de cette pièce et ses bytes restent une dépendance métadata réelle,
pas une preuve Lean du chargeur. Sa lecture n'est jamais annoncée raw FULL.

La confiance opérationnelle est assumée explicitement dans Windows installé
(C:/Windows) et GCC installé (C:/msys64/ucrt64), y compris la sélection de ses
helpers, specs et plugins pour cette compilation standard. L'environnement
propre et les chemins de driver/source/arguments sont fixés. Les fichiers
sélectionnés sont liés par hash. Les chargements effectifs, la résolution DLL,
les forwarders, appels dynamiques et sélections réelles de sous-processus ne
sont pas observés ; leurs fermetures universelles restent OPEN. Le contrat ne
prétend ni connaître toutes ces sélections ni imposer leur fermeture par bytes.

Le nouveau compiler_trust_policy22.json est seulement une politique SOURCE.
Il ne constitue pas une revue indépendante du loader. Une future revue porte
le statut exact BUILD_ONLY_DECLARED_IMPORTS_REVIEWED_WITH_EXPLICIT_WINDOWS_GCC_TRUST,
le scope BUILD_ONLY, compilerSHA, policySHA et observationSHA. Elle doit conserver
effective_loads_observed=false, universal_loader_closure_verified=false,
numeric_authorization=false et produced_binary_invocations=0. Le parent refuse
all_non_OS_imports_bound=true. Il exige séparément l'acceptation explicite de
cette confiance par la future gate ROOT et la préparation ; aucune revue,
préparation ou gate n'est créée par l'auteur.

## Autorisation, ressources et reçu

Nouvelle gate prévue round22_native_build03_authorization.json, préparation
locale build_preparation22.json, essai exclusif actual_build03_attempt01.
Tous sont absents à ce stade. Deux drivers fixes au maximum ; wall partagé300s,
commitJob2GiB, active16, total32 observé, RSS individuel2GiB et agrégé4GiB
surveillé ; outputs256MiB, logs1MiB, captures32MiB, metadata16MiB, tmp64MiB,
binaries64MiB chacun. Les moniteurs de RSS agrégé et de disque ne deviennent
pas des quotas OS/NTFS. Le parent Python reste hors Job ; flags -I -S -B -Xutf8
seront fixés et observés extérieurement. Les mêmes gardes PREPOST, copies,
3089archives, job vide confirmé et absence de retry sont maintenues.

Le futur reçu NATIVE_BUILD_EXIT0 établirait seulement deux vrais exit0 et les
bytes des deux images produites. Il garde native_source_planSHA330ef397 et le
plan effectif03 distinct, ajoute policySHA, observationSHA et le périmètre de
confiance, et conserve effective_loads_observed/universal_loader_closure_verified
à false. Un tel reçu n'est pas une preuve de validité de l'arithmétique machine,
de loader natif après lien, de coefficientN ou de ressource total parent+child.
La FIN de driver et son hash binaire ultérieur restent deux observations.

SOURCE_ONLY_FROZEN_NOT_PREPARED_NOT_COMPILED sera le statut au handoff.
Aucun compiler, import candidat, probe, version/help, build, installation ou
programme numérique n'a été lancé. Une éventuelle autorisation BUILD_ONLY ne
modifierait pas la gate numérique distincte : coefficientN=1e8, raffinement
GMP/NTT/catalogue, H1, PP/frontière, D_N et WIN restent ouverts.
