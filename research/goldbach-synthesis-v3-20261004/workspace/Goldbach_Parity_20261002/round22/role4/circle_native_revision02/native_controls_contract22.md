# Native02 — SOURCE, dépendances conservatrices et contrôleur parent non testé

Le sibling est distinct de source01 gelé7c5eb71c/55bindings. Le producteur est
byteidentique bdb7b022. Le checker corrige uniquement le tick mort identifié
dans la revue indépendante6d6899b9 : d impair rendait !(d&4095) toujours faux ;
la condition (d&4095)==4095 appelle tick tous2048 candidats impairs. Aucun
paramètre/log/NTT/CRT/fold ou définition mathématique n'est modifié. Les modèles PAPER80718/fbbf4 et guard02 ne
changent pas. Aucun compiler/version/preprocessor/binary/import Python ou calcul
de coefficient n'a été appelé par ce paquet.

## Fermeture observée et ce qu'elle ne démontre pas

La photographie metadata surinclut tout C:/msys64/ucrt64/include (3365fichiers,
118892575B), les146 GCCinclude (2851827B) et l'unique include-fixed (750B),
tout C:/msys64/ucrt64/lib (1888fichiers,424417399B), les55DLL du bin
(32182619B), ainsi que gcc/g++/as/ld. Les headers GCC et exécutables auxiliaires
cc1plus/collect2 sont donc conservés, sans les appeler. Les anciennes55bindings
native01 et les1005bindings guard02 restent liées readonly ; ces dernières
surincluent les972 fichiers du Python isolé. Doublons supprimés par path résolu,
et des hashes contradictoires provoquent échec metadata. L'ensemble attendu est
l'union exacte de ces objets et des cinq DLL système explicitement inventoriées.

Cette surinclusion ferme les *bytes des fichiers locaux sélectionnés* ; elle
n'est ni une exécution du préprocesseur, ni la preuve que la recherche effective
des includes/libs n'en sortirait jamais. Toutes includes/cache sont
BYTE_HASH_AND_DIRECTORY_ENUMERATION, aucune lecture FULL inventée. L'ensemble
des imports PE effectifs et de leurs dépendances OS n'est pas encore connu.
kernel32/kernelbase/ntdll/ucrtbase/psapi sont liés par hash comme base de confiance
Windows candidate, pas comme preuve de fermeture de tous imports système.
Les updates Windows imposeront une nouvelle photographie si leurs bytes changent.

Route build proposée, seulement écrite dans build_plan22.json : g++17/O2,
-static/-static-libgcc/-static-libstdc++, GMP statique. Cela vise à retirer les
DLL GMP/stdC++/pthread des futurs imports natifs. Aucun lien statique réussi ni
absence d'import non-OS n'est revendiqué. Les binaires build-final n'existent pas.
Une future autorisation build est séparée de l'autorisation du coefficient.
Le parent ne sait compiler ni substituer un binaire.

## Limites futures fermées par contrôles concrets

Le parent SOURCE n'accepte que le Python canonique isolé, une nouvelle
runtime_preparation22.json, un manifeste exactement lié, un reçu de deux vrais
builds exit0, une revue SOURCE et une revue réelle des imports/loader sous base
de confiance Windows. Tous ces contrôles nouveaux sont absents aujourd'hui.
Son jeu de paths attendu est reconstruit depuis snapshot/handoff/binaries/reçus,
pas accepté par un seul count. Toutes SHA/tailles sont vérifiées avant le child,
puis en POST, y compris originaux manifest/gate/reviews et copiesPREEXEC.
Les3089 archives sont vérifiées par le vrai registre875cebdd, avant/après.
Le dossier d'essai exclusif empêche toute relance ; deux enfants au maximum,
producteur puis checker, STOPFIRSTFAIL sans retry. Aucune banque précédente.

windows_job22.py demande au noyau Windows : CREATE_SUSPENDED, Job sans breakaway,
ActiveProcessLimit1, ProcessMemoryLimit et JobMemoryLimit2147483648B,
KILL_ON_JOB_CLOSE. Il relit ces quotas avant ResumeThread. La liste d'héritage de
handles est limitée à stdinNUL/stdout/stderr par STARTUPINFOEX. Il demande aussi
SetProcessWorkingSetSizeEx(HARDWS_MAX_ENABLE,2147483648B), puis vérifie ce drapeau
et la limite relus. Échec privilège/API/ABI/assignment ferme le child suspendu ;
aucune diminution silencieuse de garde. RSS et PeakWorkingSetSize sont observés
au polling et au FIN, tout excès historique supprime le verdict. Commit est une
quota OS distincte du RSS ; ce ne sont pas deux noms d'une mémoire mesurée.
ABI/semantique/quota sont SOURCE vérifiées contre headers ciblés, jamais exercées.

Le délai partagé3600s commence à l'entrée du parent et inclut hashes/métadata.
Un Timer d'urgence termine le parent, ce qui ferme ses Jobs. Le watchdog conserve
si possible une demande de terminaison avec POST_UNVERIFIED ; il ne forge pas
une FIN ni une conservation. Le moniteur enfant demande TerminateJobObject dès
expiration ou violation, et attend la fermeture. L'action dépend du scheduling
OS ; aucun dépassement réel en millisecondes ou durée de succès n'est mesuré.
Le parent source ferme au premier timeout et ne reprend pas un programme partiel.

stdout+stderr sont collectés par pipes et stockés sous une limite combinée1MiB,
appliquée avant chaque écriture. Métadonnées16MiB, copiesPREEXEC32MiB, reserve
de clôture64KiB. Le résultat du producteur reste fixedformat : facteur400000020B,
records<=800000040B, claim<=4096B. Ces fichiers sont seuls admissibles dans
payload. Somme maximale1200004156B ; avec logs/copies/métadata, plafond théorique
1251384380B<2147483648B. Le parent monitore toute la sous-arborescence et refuse
reparse/unexpectedpayload/oversize. Ce n'est **pas** une quota NTFS pour un
exécutable hostile : le plafond catalogue dérive des guards du SOURCE natif
fixé, le contrôle parent d'autres fichiers est un moniteur. Les invariants
machine/build et cette correspondance format→writers restent à auditer.

## Ressources et coût sans promesse de faisabilité

Get-Counter read-only réussi eb63cf à2026-10-03T17:33:07.429Z : mémoire disponible
21909696512B ; commit validé16046153728B, limitecommit39369342976B. Ce snapshot
ne donne pas la RAM physique totale, ne réserve rien et n'assure rien au START
futur. CIM précédent ACCESS_DENIED reste vrai ; aucune escalade. Le parent
réclame des quotas et ferme sur bad_alloc/API/refus, sans compter sur ce snapshot.

Payload pic1736870924B, réserve proposée134217728B, total1871088652B<quota2GiB.
Ce total n'est pas un RSS mesuré. Build et bibliothèques ajoutent de la mémoire.
Coût inchangé40265318400 products modulaires,288P termes exacts de série parce
que log2 est recalculé, jusqu'à10^12 trial-divisions et recherche de Lucas sans
durée payée. Pré/posthashes d'environ600MiB de toolchain/runtime plus catalogues
1.2GB doivent être ajoutés ; aucune seconde n'est attribuée à ces coûts.
Les limites choisies bornent une tentative et peuvent faire échouer un calcul
mathématiquement correct. L'absence de résultat à3600s ne falsifie pas l'identité.

## Statut et obligations avant exécution

SOURCE_ONLY_NOT_BUILT_NOT_RUNTIME_PREPARED. runtime_preparation, runtime_manifest,
ROOTgate, build_receipt, loader_review et actual_native02_attempt01 sont absents.
Restent OPEN : builds/ABI, imports effectifs et trust OS, review indépendante de
ce backend/parent, invariants GMP/carries/NTT/CRT/catalogue, contrôle quota exercé,
faisabilité/durée et vrais outputs. Au succès futur, le parent pourrait seulement
annoncer NATIVE_NUMERICAL_COEFFICIENT_AUX_CHECKED_PENDING_FORMAL_PRIMITIVES.
Ce statut ne paye ni primitives Lean, ni traceζ uniforme en phase, ni traitement
PP/frontière, ni D_N ou WIN. Aucun booléen de préparation n'est une hypothèse
mathématique du coefficient. Les données guard02 et ses samples restent séparées.
