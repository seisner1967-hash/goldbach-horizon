# BUILD_ONLY01 — SOURCE indépendant de l'exécution NTT

Ce sibling appelle seulement le driver fixe C:/msys64/ucrt64/bin/g++.exe, deux
fois au plus, avec les deux vectors d'arguments exacts de native02/build_plan22.
Il ne lance jamais les .exe qu'il produit, aucun --version/--help/probe. Les
CPP sont fixedbytes SOURCE ; ce plan ne comprend ni catalogue ni coefficient
numérique. Rien n'a été importé, parsé ou compilé à ce jour par ce dossier.

## Dépendances et autorisation distincte

build_preparation22.json, manifeste d'exécution, gate ROOT BUILD_ONLY et revue
du loader du compilateur sont absents aujourd'hui. Le préflight futur exige
exactement ces fichiers, le Python canonique byte4278cf2a sous -I -S -B -Xutf8,
la photographie conservative6332 bindings et les handoffs native02/build01.
L'union des paths ET leurs tailles/hashes/captures doivent coïncider avec le
manifeste futur. Les `.cpp`, plan, g++/cc1plus/collect2/as/ld, include/lib et
DLL locales sont surinclus en bytes. La photographie n'est pas un résultat du
préprocesseur ; le choix effectif des imports du compilateur reste à relire.
Le futur compiler_loader_review JSON doit réellement lier compilerSHA et
imports non-OS, sous base de confiance Windows explicitement reconnue.
Un statut SOURCE_REVIEW ou une préparation ne présume aucun exit0 du build.

Gate exacte prévue :
B/.arbor/sessions/parity/.coordinator/messages/round22_native_build01_authorization.json.
Elle doit dire scope NATIVE_BUILD_ONLY_TWO_FIXED_TARGETS et reprendre tous
FIXED de run_build_only_once22.py. Seul ROOT créera cette gate. L'exécuteur rôle6
sera distinct de ROLE4 auteur et ROLE5 lecteur ; aucune autorisation implicite
depuis PARAMETER_GUARD02 ou depuis le parent numérique NTT.

Deux sorties neuves : native02/build-final/producer_dit22.exe et checker_dif22.exe.
Le parent exige initialement absence du dossier, du reçu build_receipt22.json
et de son unique actual_build01_attempt01. Échec garde/compilation conserve les
partiels et ferme STOPFIRSTFAIL sans retry. Au vrai succès futur seulement, il
écrit un reçu NATIVE_BUILD_EXIT0 des deux drivers, SHA des sources/plan/binaries et
copies immuables START/FIN/logs/PREPOST. Le reçu ne dit aucun succès mathématique.
Il servira de nouvel input readonly d'une préparation numérique ultérieure.

## Quotas propres au build et descendants

Le job numérique native02 limite1 processus. Cela ne couvrirait pas le driver
de compilation et ses descendants. Le backend séparé windows_build_job22
demande16 processus actifs maximum par job, et observe32 processus cumulés
maximum par invocation du driver. Les descendants héritent du Job sans option
de breakaway. Le parent crée le driver suspendu, fixe les quotas, les relit et
reprend seulement après succès. L'héritage handles est limité à trois endpoints
stdinNUL/stdout/stderr. Aucun autre driver, shell ou commande n'est sélectionné.

ProcessMemoryLimit2GiB et JobMemoryLimit2GiB couvrent commit individuel/total
du driver et descendants. JOB_OBJECT_LIMIT_WORKINGSET fixe un maximum2GiB par
membre, puis le maximum dur du driver est demandé et relu. Le parent énumère
les PID du Job, vérifie leur appartenance avant de lire leurs compteurs, et
enregistre picRSS individuel, sommeRSS vivante observée et piccommit du Job.
SommeRSS>4GiB ferme la tentative ; cette limite agrégée est un MONITEUR,
pas une quota RSS agrégée OS. Les processus déjà terminés entre énumération et
OpenProcess peuvent être absents ; aucune valeur mémoire historique non lue
n'est inventée. JobTime/quotas privés et working-set ne sont pas confondus.
Un refus API/privilege/ABI/job-nesting ferme avant Resume ou tue le Job.
Les quotas et l'exhaustivité d'observation n'ont jamais été exercés.

Délai partagé300s depuis l'entrée du parent, comprenant preflight/hashes,
deux compilations et POST. Timer d'urgence termine le parent, fermant les Jobs
via KILL_ON_JOB_CLOSE ; il conserve si possible un marqueur POST_UNVERIFIED et
ne forge pas une FIN/POST. Le backend attend aussi la sortie des descendants
du Job après la fin du driver, sous le même délai. Les latences du scheduler
Windows ne sont pas mesurées. Un dépassement ou échec de ressource n'est pas
un contre-exemple d'identité, et ne donne aucune conclusion de parité.

Logs pipes combinés<=1MiB, appliqué AVANT stockage. CopiesPREEXEC<=32MiB,
metadata<=16MiB dont64KiB réservés. Deux binaries<=64MiB chacun ; tmp<=64MiB ;
répertoire d'essai +build-final<=256MiB. Les tailles/paths/reparse sont monitorés
pendant le driver et en FIN. Ce contrôle est une borne de tentative surveillée,
pas une quota NTFS face à un compilateur hostile. Au succès les .exe restent
des fichiers : deux bytes MZ et SHA sont lus, aucun code n'est exécuté.
Originaux manifest/gate/reviews, tousinputs/copies et3089archives sont rehashés
en POST. Copie du reçu build de taille bornée ajoutée à native02 au vrai succès.

## Ressources et état

La photographie native02 lie639196429B d'inputs ; au moins deux relectures/hash
de cette quantité plus copies/source/object/link doivent être ajoutées au coût.
Le snapshot RAM21909696512B disponibles est temporel, pas une réservation.
Aucune durée de compilation/link, taille binaire ou RSS mesurée.300s/2GiB
restent une proposition de limites susceptibles de fermer un build correct.
Le coût NTT40265318400 produits et288P séries est entièrement hors BUILD_ONLY.

SOURCE_ONLY_NOT_PREPARED_NOT_COMPILED. Au succès futur, seul NATIVE_BUILD_EXIT0
serait possible ; produced_binary_invocations=0, coefficient_N=false,
FORMAL_PRIMITIVES/H1/D_N/WIN=false. Imports effectifs natifs après link, raffinement
machine/arithmétique et résultat numérique demanderont d'autres revues/gates.
