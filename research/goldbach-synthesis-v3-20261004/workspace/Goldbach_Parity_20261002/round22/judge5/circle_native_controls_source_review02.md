# Revue indépendante Native02 : contrôles cohérents SOURCE, runtime ouvert

ROLE5, distinct de ROLE4 auteur. Verdict `SOURCE_STRUCTURALLY_COHERENT_RUNTIME_OPEN`, aucune invocation/import/probe/build/ABI ou banque numérique. Baseline officielle78modules/1304déclarations auxiliaires inchangée. Le volet BUILD_ONLY01 présente séparément le raccord CWD décrit dans `circle_native_build_controls_source_review01.md` ; aucun build n'est autorisé par cette revue.

## Versions et portée réellement lues

Sous `B/round22/role4/circle_native_revision02`, B=`D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002` :

| Fichier | SHA256 | Lecture ROLE5 |
|---|---|---|
| run_native_once22.py | 1cb5585e6e940afa3d4d7b3b1fb40259ed39a6bd8ca13a07877cb5651ac65908 | FULLc1e5b8 |
| windows_job22.py | 78db7ebf8292142a1c51b2d9f27a9c64b53768d0ee7e213e5e2ac8b2ded44a31 | FULLc1e5b8 |
| checker_dif22.cpp | 4275ef5afc07f23c2d4b860de8f452ff1e2c07e8ab0d01686c16bdb0d09fe0eb | FULL00e7ff |
| native_controls_contract22.md | a29d3fe1473ffbb38cc0df7ae8ea3a0f8851173f3d7d7781765533daaceedea1 | FULL52dbed |
| build_plan22.json | 330ef3979d5ad467c03682f2d9f1c791b946c752e0cdc6c5456d0d7f04301e92 | FULL52dbed |
| resource_observation22.json | d6cd25735dc5c92ac05b3b04d4243535f60bd0b2ca4542aa36ed56476aadd9e7 | FULL52dbed |
| source_handoff22.json | 889d4e221911bdfe75104361d62f36accf3770a17f48f29d84a9ba8d1952da88 | FULL52dbed,12bindings |
| read_receipts22.json | ca54f39379fa8bee83ac7c7c30ac6902ffae0b5681afcfa1781987a0a5717d9a | FULL52dbed |
| metadata_conservation22.json | 543bcacce66349667e99aa1581c34d20354e7c080acaee1c584b4d5d919f83ff | FULL52dbed |
| closure_snapshot22.json | 12bd8ab8c067e4881b837689ce705e7f029826b20482b85fbc6a6d18e3717e06 | HEADER_PROJECTION + ALL_BOUND_BYTES eb508e, pas rawFULL |

Producteur bdb7b022ae20ed8dce02959b77db62ca690a9798393292db62edf262d938ed74 byteidentique au FULLf3ae6b antérieur ; revue01 SHA6d6899b9c2fea5ca7fa000c85876c0a29f5dfdc0e1e412feb41c2b42541dfe1c conservée. Métadonnées eb508e :6332bindings/639196429B, et12+5 bindings de handoffs, soit6349 lignes de hashes/tailles recontrôlées, zéro écart. Ce n'est pas une fermeture effective des includes/imports ni une lecture FULL des headers/DLL. La lecture combinée initiale tronquée est exclue comme FULL ; les lectures ci-dessus la remplacent.

## Garanties exactes du contrôleur

Le parent reconstruit l'union exacte snapshot/handoff/deux binaries/build receipt/revue indépendante/revue loader, vérifie unicité des paths, SHA/tailles et captures obligatoires. Il refuse tentative déjà existante et reçoit exclusivement producer puis checker, sans compilateur/retry. Les originaux PREP/gate/manifest/reviews et captures sont rehashés en POST ; les3089archives du registre875cebdd sont rehashées avant/après. Le payload producteur est hashé avant et après checker, empêchant sa modification silencieuse. La photographie inclut les anciens native55/guard1005 ; elle contient cinq références Juge13/papier et ne revendique pas la conservation de tous fichiers des lots Juge01–17. Toute observation plus large appartient aux contrôles ROOT distincts.

ABI x64 déclarée cohérente avec les headers :Basic64, Extended144, Startup104, Process24, Memory80, StartupEx112 ; aucune taille effectivement calculée ici. Handles Job anonymes non héritables, STARTUPINFOEX/HANDLE_LIST limités à trois handles NUL/stdout/stderr ; pas de handle Job transmis au child. CreateProcessW reçoit chemin explicite, commande writable, CREATE_SUSPENDED+UNICODE_ENVIRONMENT+NO_WINDOW+EXTENDED_STARTUPINFO. Quotas Job relus, Assign avant Resume, ActiveProcessLimit1, commit process/job2GiB, pas de breakaway ; maximum working set dur demandé et relu. Les refus API/ABI/quotas ferment sans succès ; l'échec d'affectation prévoit TerminateProcess du child encore suspendu. Une sortie non confirmée conserve FIN_kind non confirmé et ne peut passer.

Ces propriétés correspondent aux [Windows Jobs](https://learn.microsoft.com/en-us/windows/win32/procthread/job-objects), à [AssignProcessToJobObject](https://learn.microsoft.com/en-us/windows/win32/api/jobapi2/nf-jobapi2-assignprocesstojobobject) et à [CreateProcessW](https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-createprocessw) : fermeture du dernier handle Job, descendants sans breakaway, et héritage limité sont des garanties conditionnées au succès des APIs. Les limites de [mémoire du Job](https://learn.microsoft.com/en-us/windows/win32/api/winnt/ns-winnt-jobobject_extended_limit_information) plafonnent le commit, distinct du RSS. La mémoire du parent Python n'est pas dans ce Job ; aucune limite2GiB du total parent+child n'est démontrée.

ENTERED et un watchdog partagé3600s couvrent preflight/hashes/deux enfants/POST, indépendamment des ticks natifs. Le watchdog os._exit ferme les handles du parent ; son marqueur est POST_UNVERIFIED, jamais un succès ni une FIN inventée. La latence OS n'est pas mesurée. PeakWorkingSetSize et peakcommit sont lus ; l'échec d'une lecture terminale entraîne absence de verdict. Pipes plafonnés avant stockage1MiB, captures32MiB, metadata16MiB ; outputs/payload sont surveillés, pas sous quota NTFS. Ni GMP bounded après opération, ni contrôle du disque au polling ne constitue un quota de toutes allocations intermédiaires ou écritures hostiles.

Le préflight vérifie chemin/hash du Python, sans vérifier sys.flags : l'isolation -I -S annoncée doit être fixée et observée par l'exécuteur sous la future gate, elle n'est pas une auto-garde de ces sources. Source/receipt du build, deux exit0 et SHA des binaries/plan sont exigés ; loader review reste une obligation réelle séparée, les booléens de statut ne la produisent pas.

## Correction et dettes de calcul

La comparaison textuelle00e7ff prouve que checker02 diffère de checker01 uniquement par `if((d&4095)==4095)tick();`. Pour d=3,5,…, cette condition est atteinte périodiquement ; le tick mort est corrigé SOURCE, aucun gain de temps mesuré. Les paramètres, constructeur canonique32 indépendant, encloser40 frais, catalogue Lucas/trial sans crible, DIT/DIF/CRT/fold et2E sont inchangés ; les conclusions mathématiques de la revue01 sont conservées. Lean17 a depuis payé le constructeur abstrait et son enveloppe, sans raffinement des opérations GMP/machine/C++.

Le coût40265318400 produits modulaires,288P termes de série et catalogue/recherches Lucas demeure réel symboliquement ; aucun coefficientN à10^8 calculé. Snapshot RAM21909696512B disponible est temporel, pas réservation. Compiler/link, PE/imports transitifs/OS trust-base, quotas exercés, correspondance catalogue→vraieΛ, carry/NTT/CRT machine et outputs restent OPEN. Le statut futur maximal annoncé est `NATIVE_NUMERICAL_COEFFICIENT_AUX_CHECKED_PENDING_FORMAL_PRIMITIVES`, aucune assimilation à H1 phase uniforme, correction PP/frontière, D_N ou WIN. Aucun manifeste/gate/runtime préparé par ROLE5.

APIs propres : TARGETED6ad735 (winnt Job structs/flags, winbase handle-list, processthreadsapi, psapi, memoryapi ; jobapi2.h absent, absence signalée), puis FULL jobapi.h et TARGETED winbase12b503. Ces headers sont lus aux signatures/structures utiles, pas FULL. Documentation Microsoft web officielle lue séparément ; aucun appel WinDLL/API/sizeof candidat exécuté.
