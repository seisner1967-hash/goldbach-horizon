# Revue indépendante BUILD_ONLY01 : déficit de raccord plan/CWD

ROLE5 distinct de ROLE4, `SOURCE_REVIEW_COMPLETE_CWD_CONTRACT_DEFICIT`. Aucun compilateur/import/probe/API/backend exécuté, aucun .exe construit ou lancé. Baseline officielle78/1304 auxiliaires inchangée. Cette revue ne donne aucune autorisation de build ni de préparation numérique.

## Gel et lectures

Sous B/round22/role4/circle_native_build_source01, B=`D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002` :

| Fichier | SHA256 | Lecture indépendante |
|---|---|---|
| windows_build_job22.py | a4dcc246f5e491e63f6d9cff849ef2ae774dbf8b9a99a565bc251e94fd12dbed | FULLcdd748 |
| run_build_only_once22.py | d19714a2000c1167875789e144ac729b7f29e140a884286a2c4ffe9d995173b6 | FULL9be8ea |
| build_controls_contract22.md | 675d4b49438e50c415b12bd4a46fc6ce49949f315e114b020c5181ffbae5c707 | FULL52dbed |
| source_handoff22.json | 12a414e0b96d068f65f0130474683bd3db27223ad9fc76f4f2b09c5946d3b8d1 | FULL9be8ea,5bindings |
| read_receipts22.json | 27c8e82f0d8f983487eb51f7cfdcd1c63e3b2b537bcab7f39207f24c3385aa3e | FULL9be8ea |

Native02 handoff889d4e221911bdfe75104361d62f36accf3770a17f48f29d84a9ba8d1952da88/plan330ef3979d5ad467c03682f2d9f1c791b946c752e0cdc6c5456d0d7f04301e92 FULL52dbed. Métadonnées eb508e :snapshot6332/639196429B +12+5 handoff rows tous hashes/tailles intacts, zéro écart ; projection du header et bytes, pas rawFULL du grand snapshot. Ancienne lecture combinée tronquée exclue. Revue APIs propre TARGETED6ad735 et12b503, FULL petit jobapi.h12b503 ; aucune preuve d'ABI exercée.

## Défaut précis avant gate

`native02/build_plan22.json:19` fixe working_directory_future au dossier circle_native_revision02. `run_build_only_once22.py:22,225` fixe ACTUAL=buildSource01/actual_build01_attempt01 et transmet ACTUAL comme cwd à run_child. `windows_build_job22.py:186–187` dérive TEMP/TMP=cwd/tmp. Le préflight vérifie les deux vectors d'arguments/sourceSHA/compiler mais n'acquitte pas le champ cwd du plan. Il s'agit d'un mismatch normatif metadata/commande effective anticipée, pas d'un FAIL de compilation, d'une erreur GMP/NTT ou de parité.

Le cwd actuel du code est cohérent avec le moniteur :tmp64MiB, sous-arborescence d'essai+build-final256MiB. Déplacer simplement cwd vers le dossier SOURCE du plan étendrait la zone de fichiers relatifs hors ce moniteur. Correctif minimal recommandé : conserver cwd d'essai et TEMP/TMP d'essai/tmp ; créer un nouveau sibling SOURCE avec plan de build exact explicitement gated (cwd et temporary_prefix contrôlés par preflight). Distinguer la référence du plan SOURCE natif historique de celle du vrai plan de build ; ne pas prétendre qu'un hash de l'ancien plan garantit son cwd réellement appliqué. Toutes sources01/02 actuelles doivent rester gelées. ROLE4 a confirmé ce diagnostic, aucun correctif évalué dans cette revue.

## Ce qui est cohérent SOURCE

Au plus deux drivers g++ fixes, arguments absolutisés et statiques, aucun .exe produit invoqué/version/probe. Manifeste futur reconstruit depuis l'union exacte snapshot/nativehandoff/buildhandoff/revue SOURCE/revue loader ; tous bytes/captures requis. Contrôles/reviews/gate/manifest/copies rehashés PRE/POST,3089archives, no retries et dossier exclusif. La surinclusion toolchain/include/lib ferme les fichiers sélectionnés ; elle ne détermine ni includes effectifs ni loader transitif. La revue loader future doit réellement acquitter les imports non-OS sous base Windows explicitée. Le header MZ et SHA du fichier sorti attesteraient des bytes, aucune exécution ou correction mathématique.

Le backend BUILD est séparé du numérique active1 :flags Job0x2309,16processus actifs, commit individuel/Job2GiB, pas de breakaway et KILL_ON_JOB_CLOSE. Job anonyme non héritable ; trois endpoints seulement via handle-list ; création suspendue, affectation/quotas relus avant Resume. Accounting48/Pids136 attendus sont cohérents avec les structures x64 déclarées. Énumération Job, IsProcessInJob vérifie les PID après OpenProcess ; PID réutilisé hors Job ignoré. Après exit du driver, ActiveProcesses doit être0 avant succès, et encore confirmé en FIN ; descendants restant actifs sont attendus sous le même délai.

La [documentation des Jobs](https://learn.microsoft.com/en-us/windows/win32/procthread/job-objects) étaye les descendants sans breakaway et kill au dernier handle ; la [mémoire du Job](https://learn.microsoft.com/en-us/windows/win32/api/winnt/ns-winnt-jobobject_extended_limit_information) est du commit.16actifs est quota OS ;32processus cumulés par invocation est moniteur au polling, susceptible d'overshoot. Maximum working set Job demandé pour chaque membre, hard working-set demandé/relu spécifiquement pour le driver ; la source ne prouve pas que tous descendants ont le drapeau dur relu. PicRSS de membres observés et sommeRSS vivante4GiB sont monitors, pas quota RSS agrégée ; un membre très bref peut ne jamais être lu. Commit agrégé n'inclut pas le parent Python.

Délai partagé300s depuis ENTERED comprend preflight, hashes, deux builds, descendants et POST ; watchdog distinct du code compilé, os._exit+Job-close, marqueur POST_UNVERIFIED si interruption. Pas de FIN/conservation inventée lors du watchdog. Latence scheduler ou terminaison non confirmée restent sans verdict. Logs plafonnés avant stockage1MiB ; capture32MiB/metadata16MiB/two binaries64MiB/tmp64MiB/attempt256MiB sont gardes ou monitors selon l'objet, pas quota NTFS. Bounded GMP/inventaire6332bytes et snapshotRAM n'assurent pas coût/allocations réelles. No reservation/no measured300s/2GiB success.

Le parent vérifie le hash/exécutable Python mais ne vérifie pas sys.flags ; future invocation -I -S -B -Xutf8 doit être fixée/observée extérieurement. Les FIN de drivers sont écrites avant ajout de binary_sha256 à leurs rows mémoire ; le reçu final contient les hashes, le lecteur de métadonnées ne devra pas supposer égalité brute FIN-row/reçu-row. Les success flags ne paient pas une preuve machine. Le seul succès futur possible ici serait NATIVE_BUILD_EXIT0 avec0invocation des .exe ; il resterait distinct du coefficientN, du numérique/primitiveproof, H1, D_N et WIN. Aucune gate ou préparation automatique produite par ROLE5.
