# Clôture réelle de l'unique banque thermique 03

Statut observé : `THERMAL_TRACE_NUMERICAL_AUX_PASS_SOURCE_AUDITED`, controller et enfant exit 0. Banque `THERMAL_GLOBAL_H1_22_SOURCEPACK02`, acteur ROLE6, auteur des sources et métadonnées ROLE3, revue indépendante SOURCE/PAPER ROLE5. Ce document décrit des sorties déjà produites ; aucune nouvelle évaluation n'a été lancée pour le rédiger.

## Exécution et ressources

Gate ROOT exacte : `.arbor/sessions/parity/.coordinator/messages/round22_global_thermal_h1_authorization02.json`, SHA `6847fff85e007303594f3257f2a027a7a4ccfb31393674338ebae22307f7a5c9`. Invocation unique ff1104, session 57318 ; clôture réelle 82549c exit 0. Token `b104f84087a84a55a8ebfccdf5558a21`.

Controller START 2026-10-03 14:48:16.467623 UTC ; enfant START 14:48:16.609166 UTC ; fin numérique 16:03:31.580470 UTC ; fin du processus enfant 16:03:31.717554 UTC ; FIN controller 16:03:41.019653 UTC. Le dernier checkpoint numérique affiche 4514797 ms. Un seul enfant, zéro retry, zéro replay d'une ancienne banque, zéro invocation Lean. Limites autorisées : 10800 s et 2147483648 octets ; volume final observé 668069381 octets. `resource_failure=null`, `control_error=null`, `output_errors=[]`. stderr vide. Aucun rapport de gain relatif n'est déduit de l'ancien calcul incomplet.

## Résultats et enveloppes effectivement produits

Paramètres inchangés : N=100000000, Y=10000, T=100, X=Q=R=1000000 et tau=1/1000000. Les 204800 nœuds verticaux, 12288 nœuds Arch et 999999 entiers ont été effectivement produits puis refoldés par le checker structurel. Flux arithmétique : 78498 certificats premiers, 78734 puissances premières, dont 236 puissances propres, et 921265 autres composés. Aucun ancien tableau de premiers n'a servi.

Le résultat conserve séparément les quatre budgets `E_function`, `E_position`, `E_weights`, `E_accumulation` de la trace et de Arch. Leurs numérateurs et dénominateurs effectifs, toutes les queues fermées, les boîtes finales, le résidu et E_total sont copiés exactement dans `decision_projection22.json`. Cette projection exclut les longs catalogues de cercles et conserve leurs indices/compteurs ; elle ne réévalue aucune primitive ni aucune somme.

Le checker a réellement vérifié l'égalité d'E_total avec la somme des erreurs émises et fermées, puis la garde stricte **E_total < 1/100000000 < tau** (source figée du checker, lignes 267–275). Les erreurs ne sont donc pas des budgets fournis librement. La décision effective exige le recouvrement des deux boîtes finales, un résidu de module au plus tau, et la compatibilité avec zéro des deux composantes imaginaires. Le résidu réel émis a une borne inférieure négative et une borne supérieure positive.

Autres gardes réellement franchies : catalogue complet ; rayons nodaux fonction/position ≤2^-81 ; budgets intégrés poids/accumulation ≤2^-72 ; largeurs arithmétique et constantes ≤2^-50 ; 32768 pistes et 26181632 avances ; compteurs frais f1=1, constante demi-log(2pi)=1 et Gamma-value-only=204800. Le checker a redérivé les folds et les erreurs depuis les boîtes du producteur, sans recalculer zeta, zeta', Gamma ou les constantes élémentaires.

Trois mutants du contrat sont effectivement disjoints : `omit_Y`, `omit_one`, `remove_primal_four`. Le dernier retranche seulement le terme primal n=4, en conservant le dual ; il ne s'agit pas d'une suppression ambiguë sur les deux côtés. Le checker a vérifié la garde primal4 > 1/10000 et chacune des boîtes mutantes émises. Cette observation ne concerne pas les mutants du futur projecteur de cercle.

## Niveau de validation conservé

Niveau : `PAPER_AUDITED_DIRECTED_INTERVAL_PRODUCER_WITH_INDEPENDENT_STRUCTURAL_CHECKER` ; dérivations analytiques `PAPER_DERIVATIONS_WITH_EXACT_DOMAINS_NOT_LEAN_CERTIFICATION`. Le reçu lie la revue indépendante ROLE5 `638b1aaba849473a1806fe3b4bb967265b35f2ecb901b4003c0b661b114a1ddf` et son addendum de domaines `821d67b2f8448533d707e9e23a5c33c44c4b316b297bb7f8129ac8f7d89cb4b7`.

`primitives_recomputed=false`, `analytic_remainders_formalized=false`, `structural_PASS_is_enclosure_PASS=false` et `structural_checker_alone_is_primitive_certificate=false`. H1 formel et coefficient N restent OPEN, bord horizontal UNIMPLEMENTED, trace finie des zéros OPEN, D_N UNPAID et WIN=false. La banque est une comparaison thermique à phase zéro ; elle n'évalue ni S_K à phase variable ni le coefficient de Goldbach à N. Aucun crédit officiel Lean n'est ajouté par ce document.

## Conservation et scopes de lecture

PREEXEC a été clos avant START : 1016 bindings, 1018 captures, zéro enfant démarré ; POSTEXEC rapporte ces mêmes quantités toutes intactes, la préparation/contexte/gate intacts et les 3089 archives inchangées. Le lot clos 02 est lié comme conservation uniquement : 1003 inputs, 1005 captures, trois sorties, `numeric_values_reused=false`.

Contrôle metadata neuf 676736 exit 0 : SHA de chacun des 1016 inputs, 1018 captures, sept sorties du reçu et 3089 archives vérifiés ; zéro mismatch. Ce contrôle ne relance aucun calcul mathématique. Deux affichages metadata antérieurs avaient une erreur de champ (`files` absent dans le registre) puis une erreur de pipeline PowerShell ; ils n'ont invoqué ni producteur ni checker. La correction est limitée à l'affichage et au contrôle SHA.

Lectures FULL : reçu parent, child_FIN, résultat structurel et stderr vide (e74956/cace0f) ; stdout entier en cinq plages 1–100 9abd7d, 101–200 210e42, 201–300 48fe5e, 301–400 869fd8, 401–487 a0f124. FIN.json a le même SHA et les mêmes bytes que receipt.json. Global : champs hors catalogue lus FULL aux lignes 1–55 df38c7 et 6110–6346 6cffac ; catalogue TARGETED/PARSED_METADATA (indices exhaustifs 0..95 et 0..127, counts, premières/dernières boîtes 825f18). PRE/POST : PARSED_METADATA des headers/comptes 96d581/6ef7d1 et vérification de tous SHA 676736. Aucune prétention FULL pour les catalogues rationnels ni les deux NDJSON de 616 Mo. Les sorties brutes restent conservées et liées par SHA.

Les sorties tronquées 30875b (stdout) et b50264 (queue global) ne sont pas des lectures FULL ; leurs sections utiles ont été relues complètement dans les plages indiquées. La projection du registre 9d8ccd, tronquée, n'est pas une lecture FULL du registre. Toutes ces limitations sont documentaires et ne constituent ni une réfutation numérique ni une erreur Lean.
