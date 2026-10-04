# Revue indépendante BUILD_ONLY04 — SOURCE uniquement

ROLE5, auteur ROLE4 distinct. Verdict : **SOURCE_COHERENT_WITH_EXPLICIT_WINDOWS_GCC_TRUST** pour `NATIVE_BUILD_ONLY_TWO_FIXED_TARGETS`. Aucun défaut précis supplémentaire identifié dans le raccord04. Cette revue autorise sa prise en compte dans une future préparation ; elle ne crée aucune préparation, gate ou invocation. Baseline ROOT effectivement observée après20 : 80 modules / 1339 déclarations auxiliaires.

Le périmètre est le parent, le backend, le plan effectif, le contrat et la policy de `role4/circle_native_build_source04`. Les CPP et leur exactitude GMP/NTT ne sont pas réaudités ici. Aucun import du candidat, parser PE, appel Windows runtime, compilateur, programme produit ou calcul numérique n'a été exécuté.

## Sources et lectures vérifiables

Racine B = `D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002`. Les chemins du tableau sont relatifs à `B\round22\role4\circle_native_build_source04`.

| Fichier | SHA256 | Lecture propre |
|---|---|---|
| source_handoff22.json | 277af8bac79d344907222f1b3c481d97e551afb2d8b1cf5a2aca299dac7508b6 | FULL67a7ca |
| run_build_only_once22.py | d7d28b2eb0da5e712a242cb8f6428e7a35b53832753200a3da4c9c0ff7a89cc7 | FULLb6542a |
| windows_build_job22.py | 88d857ce33eece8f90906bc5088d5cac905b868e60ede1b6439b1a3af3126cc3 | FULLdaf2ac |
| build_execution_plan22.json | 538cc14faf3466bb8a0505e8f6aae3007fc84b2b6246afb2da55d37be5718156 | FULLa768c3 |
| build_controls_contract22.md | 574aef1f43b9ca328a62bc73a7b65466ff82e61c6a9bf822bdc5f5936ad154a5 | FULLa768c3 |
| compiler_trust_policy22.json | 72fd49d993e3291a174d4ba5a139a649ab916e9e757274c0e89f0a6092b4f6a6 | FULLa768c3 |
| revision_conservation22.json | 5ee37df533fd2ae53d5cf38503d8cc519e830ac27b12111afa62ad4019f9dc76 | FULL7d5b67 |
| read_receipts22.json | af53dbffbf677021249e0b628191aa5dda98264c798f3e76c38adbe830aacbeb | FULL7d5b67 |

Les FIN et receipt réels03 ont été lus FULLdfd4a3 : erreur1314 à SetInformationJobObject, pid0, sans création/reprise du driver, aucun exit de compilateur confirmé. Ils ne démontrent pas quel bit ou privilège a causé l'échec. Le retrait des working-set controls04 est une réparation SOURCE raisonnable, sans promesse que l'appel futur réussira.

## Raccords effectivement examinés

Le backend demande `0x2308 = 8968` : kill-on-close, active16, commit processus et Job de 2147483648 octets. Le bit WORKINGSET et les appels Set/GetProcessWorkingSetSizeEx ont été retirés. Il vérifie par QueryInformationJobObject les flags et limites avant CreateProcess suspendu, affecte le driver au Job avant ResumeThread et transmet seulement les handles des flux. Aucun breakaway n'est demandé. Les descendants de la construction standard restent dans le périmètre du Job sous la confiance GCC installée. Les définitions de commit, active-process, working-set et kill-on-close concordent avec les [flags Microsoft](https://learn.microsoft.com/en-us/windows/win32/api/winnt/ns-winnt-jobobject_basic_limit_information), les [limites étendues](https://learn.microsoft.com/en-us/windows/win32/api/winnt/ns-winnt-jobobject_extended_limit_information) et les [Job Objects](https://learn.microsoft.com/en-us/windows/win32/procthread/job-objects), consultés directement ; portée API TARGETED, aucune expérience runtime.

Le plan, le parent et les champs requis PREP/gate concordent : `rss_os_enforced=false`, `rss_control=SAMPLED_PROCESS_PEAK_AND_LIVE_JOB_SUM`, `working_set_limit_flag_requested=false`, flags8968. Le RSS processus2GiB et RSS vivant agrégé4GiB sont des moniteurs échantillonnés ; les descendants courts peuvent leur échapper. Le parent Python est hors Job. Le commit est une limite OS demandée qui nécessitera un appel et une relecture effectifs. Les limites disque sont également des moniteurs, sans quota NTFS universel.

Le wall300s est partagé depuis l'entrée du parent, incluant préflight, hashes, captures, deux drivers au plus et clôture ; premier échec arrête le lot. Un timeout peut empêcher une clôture complète et ne fournit alors aucun succès. Les sorties sont exclusivement `native02/build-final04`, le CWD `source04/actual_build04_attempt01`, TEMP/TMP son sous-dossier `tmp`, environnement réduit aux six variables gelées. CPP et arguments de compilation restent identiques, sauf les destinations `-o`. Le reçu distingue le plan natif historique330ef397… du plan effectivement appliqué538cc14f… . Aucun consumer numérique gelé n'est adapté implicitement à receipt04.

Le parent lie les revues MD/JSON, policy, plan, préparation, gate et bytes/copies PRE/POST ; il refuse une déclaration de fermeture universelle `all_non_OS_imports_bound=true`. La confiance Windows/GCC installés est une hypothèse opérationnelle explicite pour ces deux constructions standard. La future gate reste nécessaire et aucune exécution des .exe produits n'entre dans ce scope.

## Conservation et portée des contrôles statiques

Metadata propre1e1034 exit0 : les 29 bindings04, 12 bindings03 et 66 images déclarées donnent 95 fichiers uniques physiquement vérifiés SHA/size, tous intacts. Les 825 descripteurs normal/delay correspondent aux 825 arêtes sans trou ; 119 candidats locaux ont leur path/basename et bytes liés, 706 arêtes relèvent de la frontière Windows/API-set. Metadata936a82 vérifie aussi le handoff04, l'observation36032c45… et le snapshot12bd8ab8… ; les 66 images correspondent aux bindings du snapshot6332, zéro écart. Les 6332 fichiers du snapshot et 3089 archives ne sont pas tous rehashés dans cette revue : cette conservation exhaustive appartient au futur PRE/POST. Le JSON307212 octets des imports est lu comme métadonnées en totalité avec projection HEADER/TARGETED, sans faux RAW_FULL. La sortie de recherche05a609 tronquée est exclue du crédit FULL. Un premier contrôle metadatafd70ab a échoué en traitant un path candidat string comme objet ; correction metadata1e1034, aucune invocation de candidat dans les deux cas.

Les chargements DLL effectifs, helpers/specs/plugins réellement sélectionnés, ABI runtime et acceptation des limites Windows restent OPEN. Le build futur peut uniquement produire deux images et leurs hashes après observations réelles. Cette revue ne certifie ni primitives natives, ni coefficientN=10^8, ni H1, D_N ou WIN ; aucune extension des acquis Lean n'en résulte.
