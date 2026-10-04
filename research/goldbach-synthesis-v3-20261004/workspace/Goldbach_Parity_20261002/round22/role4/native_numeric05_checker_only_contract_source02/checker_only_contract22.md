# Consumer05 CHECKER_ONLY — engineering SOURCE révision02

Réparation documentaire sélectionnée ROOT après revue indépendante du parent
ROLE3 SOURCE05. L'ancien contrat SHA
8fd1e59d4c751d38a1320aadeed9686dd788eed8c1fb473151924afc7827ad30,
le parent SOURCE05 SHA2b073990ccb6b66248d6fb68df6b21141e04324f311e40ec0fae41c12a703001,
et la revue bloquée SOURCE01 demeurent intacts. Leur défaut précis est
DEADLINE_NO_CREATION_CONTRACT_MISMATCH, pas une réfutation mathématique.
Cette révision conserve toutes les valeurs3600/3300/300, le backend04,
les images, les CPP, les sorties et la portée de confiance existante. Elle
remplace seulement la promesse d'absence de création après le deadline par
les deux contrôles réels et demande une dernière garde après les hashes.
Le prochain parent ROLE3 révision02 devra recevoir sa propre revue SOURCE.
Aucun PREP, gate, candidat natif, import ou compilation n'est autorisé ici.

# Contrat proposé, autres exigences conservées

Statut : SOURCE seulement, non PREPARED, non autorisé, non exécuté. Auteur de
ce contrat d'ingénierie : ROLE4. Il ne constitue pas une nouvelle revue
indépendante des CPP02 écrits par ROLE4. Les revues CPP/backend de ROLE5
restent les références ; le nouveau parent ROLE3 devra être relu séparément.

## Reprise justifiable et provenance

Numeric04 est clos `CLOSED_STOP_NO_MATHEMATICAL_VERDICT`, parent exit1 après
watchdog de 3600s. Le producteur a un vrai FIN exit0 au
2026-10-03T21:35:22.455884Z. Le checker a commencé, mais son FIN, le reçu parent,
POST et le coefficient sont absents. La conservation physique externe payée
par la clôture ne remplace pas POST. Aucun résultat partiel du checker04
n'est repris. Consumer05 serait une nouvelle invocation complète du seul
checker, sous une nouvelle gate, pas un checkpoint du calcul interrompu.

Ancrage : `role3/native_numeric_closure_source01/numeric_execution_closure22.json`
SHA `a99a5e58768d09a16c7a1ae248448be41016cac228fc57c69372d6abb2774df3` ;
quiescence SHA `2763645031ab61fdbeae88a8cd5d699d4a11b60381f132dd8e5c5da2ba94402a`.
Cette quiescence porte sur la session close et les PID connus absents, sans
preuve universelle du graphe de processus. Les 6456 inputs,66 copies,
3089 archives,5 contrôles et83 outputs sont l'observation historique de clôture,
pas des comptes de PREP05.

Les trois entrées restent **non validées mathématiquement**. Leur origine est
`role3/native_numeric_consumer_source01/actual_numeric04_attempt01/payload` :

| Fichier | Octets | SHA256 figé |
|---|---:|---|
| factors.bin | 400000020 | `32450e19fb3d9d8a567cf03e262ddb4f46f44014da606ed5e27b69cb90c1baa2` |
| records.bin | 92183304 | `bf6bfeb2d8431326cf677df7605bac3d12caa189f22a87e7e4267aff6a093b6d` |
| producer.txt | 194 | `aeee44e0e6cdc503504d9ea3329ab6b83b3a665462472318265932200ab04383` |

Le vrai `producer_FIN.json` est lié au SHA
`fdbb8187fb1ab37ac19d301d0b475da3ee9e48df004732bd60d930905280a520` et
`producer_payload_hashes.json` au SHA
`470441f9e6af30a1be7c4c27999c6498ef6b66509521abdb4ac5cb1a2229d50e`.
Ces pièces attestent l'origine et les bytes, pas le catalogue, les logs ou CRT.

## Chemin natif inchangé et ressources

Image unique : `role4/circle_native_revision02/build-final04/checker_dif22.exe`,
3669445 octets, SHA
`2e7e095c2972fea09ee26500df9dae207ff52497d0f61f2052d76d464ebe6990`.
BUILD04 réel : reçu `04ce22f9ee05215ee9c7c335b41755b1da4e001a82fa20085cfe7dccca1a7fc8`,
plan `538cc14faf3466bb8a0505e8f6aae3007fc84b2b6246afb2da55d37be5718156`.
Backend04 readonly :
`88d857ce33eece8f90906bc5088d5cac905b868e60ede1b6439b1a3af3126cc3`.
Aucun producteur, compilateur, mutant ou autre image ne sera invoqué ; un seul
enfant direct maximum, zéro retry dans cette nouvelle tentative. L'historique
reste deux images créées pendant04, puis au plus un checker pendant05.

Le CPP checker exige `argc==2` : l'unique argument est le dossier des trois
fichiers. Il ouvre ceux-ci en lecture et écrit seulement stdout/stderr. Le
parent doit copier les trois fichiers dans un nouveau `ACTUAL05/payload`
exclusif et vérifier taille/SHA des originaux et des copies avant Resume.
Il ne lance jamais le checker sur l'ancien dossier04. La commande est
`[checker_dif22.exe, chemin_absolu_ACTUAL05/payload]`, CWD=`ACTUAL05`,
TEMP=TMP=`ACTUAL05/tmp`. PATH/Windows/runtime natif suivent la confiance scoped
BUILD04 ; effective loads, universal loader et all_non_OS restent false.
La confiance opérationnelle concerne Windows, GCC/GMP installé et l'image
native figée ; elle ne paie pas le raffinement Lean des primitives natives.

Chemins proposés pour le parent ROLE3 :
`role3/native_numeric_checker_only_consumer_source05_revision02/run_native05_checker_only_once22.py`
et ACTUAL05=`role3/native_numeric_checker_only_consumer_source05_revision02/actual_numeric05_checker_only_attempt01`.
Les futures revues distinctes du présent contrat seront sous
`role4/native_numeric05_checker_only_consumer_review_source02/{source_review22.json,trust_review22.json}`.
Il s'agit de destinations futures, pas de pièces produites ici.

Fenêtre sélectionnée par ROOT dans son message de continuation :3600s au total
depuis l'entrée du parent05, comprenant PRE, copies/hashes, unique checker,
lecture du rapport et POST. Le deadline du backend est T0+3300s afin de
réserver 300s à FIN/POST avant le watchdog parent T0+3600s. Aucun producteur ne
consomme cette fenêtre. Cela ne promet pas 3600s de calcul enfant, ni la fin des
hashes dans300s. Une garde monotonic supplémentaire doit être placée après les
hashes finaux, les ouvertures de logs et START_REQUEST, immédiatement avant
l'appel run_child. Si cette garde constate T0+3300s atteint, STOP sans appeler
le backend et sans créer d'enfant. La garde ne garantit pas de façon atomique
l'instant OS de CreateProcessW : le backend04 crée suspendu, puis vérifie encore
le deadline avant Resume. Un dépassement survenu entre ces contrôles entraîne
l'arrêt du processus suspendu ou du Job et un STOP, jamais un succès.
atomic_OS_CreateProcess_deadline_guarantee=false. Il n'y a aucune promesse de
certification temps réel des instructions CPU/OS. Si la clôture dépasse3600s,
watchdog et absence éventuelle de POST demeurent un STOP sans verdict à fermer
extérieurement. La réserve300s n'est pas une garantie de fin des hashes/POST.
Cette sélection de limites n'est pas une autorisation d'exécution05.

Job OS : commit processus/job2GiB, flags8968 relus avant Resume,
active16 ; total32 surveillé, mêmes contrôles backend04. Max1 enfant direct
ne signifie pas hard active1. RSS2GiB/processus et4GiB somme live sont des
moniteurs, pas une garantie OS ; le parent reste hors Job. Sorties2GiB,
logs combinés1MiB, métadonnées16MiB, captures32MiB sont surveillés, sans quota
NTFS hostile. La copie des payloads fait partie du budget de sortie.

## PRE, rapport et POST requis

Le futur manifeste doit reconstruire l'union exacte, avec dédoublonnage par
path et égalité de sets : fermeture runtime05, sources/outils/revues05,
BUILD04 reçu/plan/image/backend et anciennes revues readonly, fermeture04 et
ses contrôles, les83outputs figés et leurs66paires original/copie, les6456inputs
historiques et les3089archives. Les nombres05 seront constatés en metadata ;
aucun count ni revue/gate05 n'est fabriqué ici. PRE capture les petits contrôles
et sources avec SHA ; les gros payloads sont INPUT_BYTES_SHA_ONLY, pas FULL
texte ni copies PREEXEC supplémentaires. Les copies d'exécution sont liées
par original/copy/size/SHA. Refuser reparse, paths inattendus et tout ACTUAL05
déjà existant, sans effacer d'ancien dossier.

START_REQUEST, CREATED_SUSPENDED, START et FIN doivent décrire l'unique
checker réel. Exit0 doit être accompagné de wait signalled, Jobempty confirmé,
absence de contrôle/pipe fault et limites conformes. Le rapport stdout ne
peut être accepté qu'en entier : neuf lignes ASCII, quatre entiers canoniques
C_A,C_B,ERROR_NUMERATOR,ERROR_DENOMINATOR et les quatre false
FORMAL_PRIMITIVES/SPECTRAL_H1/D_N/WIN. Sa première ligne doit être exactement
`EXACT_INTEGER_PROJECTION_CHECKED_PENDING_PRIMITIVE_PROOF`.
Même gardes exactes que consumer04 :
N=100000000,K=2^27,S=2^58 ; A=(N+1)(64S+1) ; num=2A,den=S²,
|C_A−C_B|≤2A,2A·10^6≤S²,C_A,C_B<2^153. Le parent relie C_A au claim figé,
et ses cinq résidus canoniques modulo les cinq moduli fixes au même C_A.
Exit0 isolé, ancien producer.txt, stdout tronqué ou timeout ne suffisent pas.

POST relit toutes les attentes PRE, contrôles originaux et captures,
les trois payloads originaux et copies, l'image checker, tous les anciens
outputs04 et archives. FIN/POST/reçu05 sont neufs ; aucun reçu04 manquant
n'est reconstruit rétrospectivement. Un coefficient_result05 peut être publié
seulement après rapport valide et conservation réussie. Le niveau maximal
est `PAPER_AUDITED_EXACT_INTEGER_PROJECTION_AUX_CHECKED_PENDING_NATIVE_REFINEMENT`.
L'intervalle primaire est [(C_A−A)/S²,(C_A+A)/S²], la garde de référence2E,
E=A/S². Le pont des words/catalogue/GMP/CRT/NTT et B40 réel reste nonLean.

## Coût et conclusion bornée

Le checker recommence catalogue/Lucas, canonicalA32 indépendant, enclosure40,
cinq DIF, CRT et deux folds, puis les points frais40. Coût source :
5K(27+3)=20132659200 produits modulaires de butterflies/phase, plus cinq
normalisations finales, les exponentiations et contrôles ;224P termes de
séries pourP records premiers
acceptés, sans supposer les records corrects. Buffer théorique1736870924B
plus runtime ; ce n'est ni un pic du checker observé ni une garantie sous2GiB.
Les bytes lus/copiés/hashés s'ajoutent. Aucune durée05 n'est mesurée ou promise.

Conclusion SOURCE : réutilisation des bytes04 justifiable sous ces nouvelles
gardes ; parent05, revue indépendante, metadata, gate et calcul restent à
faire. Aucun déficit de l'interface CPP n'empêche CHECKER_ONLY. Le déficit
opérationnel précis est la clôture après timeout ; la réserve explicite
réduit ce risque et conserve le STOP honnête sans pouvoir garantir POST.
H1 spectral uniforme, PP/frontière, D_N et WIN restent ouverts.

Lectures de cette mission : clôture FULL005ca2 ; plan FULL02e1ed ; contrat04
FULL9e3e18 ; cinq petits contrôles réels FULL11ada6 ; quiescence et contrat de
clôture FULLc95c56. CPP et parent lus TARGETEDd73457/79f1a6/cc902b/cd40a9,
sans nouvel audit indépendant du CPP. Les17 fichiers petits/source/image
énumérés dans aa7d77 ont leurs bytes/SHA rehashés ; les trois gros payloads
sont seulement liés à la clôture, pas relus ni parsés ici. Les anciennes
lectures tronquées70dad3 et mauvaises adressesf8f486 ne sont pas FULL.
Revues readonly réutilisées : CPP01 `6d6899b9c2fea5ca7fa000c85876c0a29f5dfdc0e1e412feb41c2b42541dfe1c`,
contrôles04 `e72b4d3b61086f9cd2293de005af4e7c21457b8fcb357cf3201c5fd717fce1ef`,
trust04 `b4574128d6cc24bd15c547f3222c8456e1880cf993a036e237af9c568f13b899`.
Aucun import, parser candidat, runtime, probe, benchmark, PREP ou gate créé.
