# FINAL5 — Juge Lean indépendant, round19

Verdict : **PASS des identités auxiliaires ; aucune victoire de parité**.
L'unique audit réel a commencé le 2026-10-03T01:31:37.321820+00:00 et s'est terminé
le 2026-10-03T01:36:25.585304+00:00, exit0. Les onze compilations neuves ont chacune
réussi au premier passage indépendant. Aucun ancien producteur, kernel,
audit, PDF, sonde de version ou replay PASS n'a été exécuté.

Les nouveaux fichiers contiennent 185 théorèmes explicites, 78 définitions,
trois structures et 268 impressions d'axiomes, dont les deux extensions
générées. Les seuls axiomes observés sont propext, Classical.choice et
Quot.sound. Aucun sorry/admit/native_decide/trustMe/axiom ajouté n'est admis.
Les trois avertissements simpa de UnitLoss aux lignes 25/26/29 sont conservés ; ils ne
sont ni des erreurs ni des justifications pour relancer un PASS.

Le cumul antérieur officiel de 30 modules/507 auxiliaires a été conservé durant
le travail. Le résultat indépendant permet 41 modules/692 auxiliaires après
la clôture du coordinateur. Le présent rôle ne modifie aucun registre global.

| Module neuf | Théorèmes | Définitions | Structures | Prints | Exit |
| --- | ---: | ---: | ---: | ---: | ---: |
| RankCalibrationFace | 19 | 3 | 0 | 22 | 0 |
| RankCalibrationPrice | 24 | 7 | 0 | 31 | 0 |
| RankCalibrationArithmetic | 16 | 3 | 0 | 19 | 0 |
| RankCalibrationUnitLoss | 8 | 1 | 0 | 9 | 0 |
| RankCalibrationEuler | 12 | 5 | 0 | 17 | 0 |
| RankCalibrationEstimator | 6 | 4 | 0 | 10 | 0 |
| TerminalPrimeExtraction | 18 | 4 | 0 | 22 | 0 |
| BalancedResourceSwitch | 25 | 13 | 2 | 41 | 0 |
| SignedHyperbolicCRT | 19 | 13 | 1 | 34 | 0 |
| NonSSBracketSwitch | 21 | 18 | 0 | 39 | 0 |
| RankTwoHarmonic | 17 | 7 | 0 | 24 | 0 |

## Provenance et contrôles effectivement exécutés

L'autorisation canonique ROOT19_JUDGE_CANONICAL_ATTEMPT01 est gelée sous
SHA256 6da21513c45dac50c777390ffb8d55f0dd3b87c3a5f59ff81e82b2603dd07c3e. La préparation est liée sous
4763b4463708b6458186cd9872c94010c055487443801915e7fd487e307c7dae ; le manifeste PREEXEC est lié sous
e3f8bc9d3ad8cbd4649d86ba5bf3fa4680eb12ae802ed6901f668127991280df. Il conserve 307 entrées FINAL,
26 sources/oleans historiques readonly et 15 captures PREEXEC du lanceur,
de l'audit, de l'autorisation, de la préparation et des onze sources neuves.

Les sources finales des deux auteurs, leurs rapports/reçus, les deux banques
FINAL6 et les revues FINAL1/2 et papier ont été lus avant exécution. Le Juge
compilait seulement les copies fraîches des onze sources du round19. Les imports
Judge18/Judge16/13 et huit bibliothèques du cache mathlib étaient readonly ;
aucun olean auteur du round19 n'a servi. Chaque module possède sa source PREEXEC,
commande, environnement, horodatages, stdout/stderr séparés, log complet,
exit réel et contrôle de tous ses prints. Les onze logs compilateur ont
également été lus intégralement après exécution.

L'inventaire protégé de 1361 entrées et les hashes d'origine sont identiques avant et
après. Audit/lanceur restent respectivement 8aabf796… et f7e22678… : aucune
modification n'a eu lieu après leurs lectures intégrales par le coordinateur.
Le Lean utilisé est le binaire 4.15.0 lié par SHA 8a1ef185… ; la version connue
est metadata historique, sans nouvelle invocation --version.

Les contrôles numériques indépendants utilisent exclusivement les banques
stockées N=10^8. Ils vérifient 1001 positions q, 5120 coordonnées nonSS,
220 images physiques, 48 produits m1 et 47895 paires harmoniques avec diagonale.
Le contrôle de rang décompresse le bitmap stocké sans recrible : 12 millions
d'axes, 719062 bits, 514 fibres, 8868261 axes b et 28136 images physiques beta.
Il vérifie produits/PF fournis, IE complète avec mu0, fronts, P/gcd(P,d),
coefficient maps theta/raw/PP, indices AP et toutes les représentations
stockées. La multiplicité AP combinée stockée est 10 pour chacun des R=2/17.
Aucune primalité, factorisation, valeur W/D/log, fonction S ou signe nouveau
n'est calculé. Les certificats et leurs labels stockés ne sont pas une
expérience supplémentaire. Aucun onset source n'est appliqué à N=10^8.

Le reçu intégral fait 15 341 862 octets parce qu'il conserve les index de
certificats stockés. Une lecture brute affichée a été tronquée ; la synthèse
audit_summary.json lit ses champs stockés et lie son hash, sans prétendre
une lecture humaine intégrale de cet index. Les logs compilateur complets,
les champs structuraux et les obligations sémantiques ont été lus.

## Résultat arithmétique exact et portée

L'extraction terminale utilise les vrais facteurs premiers avec répétitions
et la longueur du multiset. Elle ne suppose pas gcd(h,r)=1. Le premier
manquant canonique, les unités et les fronts dérivent la coprimalité des
ressources à tous rangs. Le tag D/P réserve l'égalité à D. Le conducteur
est inférieur à N ; aucune borne sqrt(N) n'est déduite.

Le CRT est signé dans Z avec constantes, fronts, sélecteur indépendant et
reconstructions réciproques. Le nonSS utilise le sourceBracket importé,
theta/raw et le SS littéral minFac<=Z avec quotient premier. Il conserve
les trois sommes courte/medium/longue et la contribution properpower réelle.
L'injection du produit physique exige M²>N ; m0 raw zéro exige q premier>p0,
et mu(m1)=0 est un zéro littéral. L'identité harmonique porte sur les vrais
cofacteurs de rang 1/2, conserve p² et prouve la converse multiset puis le
raccord Ω(resource)=2/3 vers Ω(cofacteur)=1/2.

Ces équivalences restent sur StructuralSupport/ResourceCell déclaré avec
les deux ressources composites. Elles ne ferment pas le support original
entier : cellules premières/singletons, incidences e1/p0, comparaisons
parents et capacités physiques restent à raccorder au ledger fixé. Aucun
effacement de domaine n'est interprété comme victoire.

La calibration utilise le vrai PhysicalWitness18. La face donne A<=J' et
J'=0 implique A=0. Tous les conducteurs sont conservés avec P/gcd(P,d).
Les prix theta/raw/PP et la référence normalisée complète sont explicites ;
Gamma_rank reste présent. Le prix de perte inclut A*#lost/#U et les fronts+1.
La reconstruction de d*k et le niveau max(aR,R^4) sont arithmétiques.
Le lemme <=32 est celui d'un développement ; il ne paie pas seul les trois
familles AP combinées écrites 40/64. Les sept chi sont les totients exacts.

L'IE garde les diviseurs avec mu0 et le vrai theta_N ; la nullité non unitaire
utilise N-db. Le facteur de face1/phi(P_d) garde ses coprimalités. Les
remainders sont les véritables sommes moins X/phi(dk). L'estimateur exact
et sa borne triangulaire compilent avec X réel explicite ; aucune borne
analytique de ces remainders n'en découle gratuitement. rankMainMass peut
ne pas être positif. Le principal négatif exige M>0 comme garde séparée.

## Lacunes qui empêchent la condition de victoire

La revue papier FINAL19 justifie R1/R2 et la positivité de Md sous les vrais
fronts, y compris les recouvrements de 39 avec N ou d. Elle n'est pas une
attestation Lean de ces nouvelles assertions. La face 1771 exige (P,N)=1
et ne couvre pas tous les N pairs. L'identité Gamma0=Gamma_rank+Pi montre
la compensation exacte : le signe du principal seul ne contrôle pas le
prix physique restant ni l'incidence simultanée de q et N-crsq premiers.

K14 complet, les AP ordinaires non masquées, leurs exceptions N et fronts,
les familles combinées, l'agrégation K18 avec constantes/onset BV et
Gamma_rank restent ouverts. Le nouveau rho/Selberg composite, H7/H9
analytique et les canaux medium/long ne sont pas quantitativement payés.
Le seuil source logN>=10^24 est conservé ; le seuil local écrit 10^40 laisse
10^24..10^40 ouvert. Rangs>=4, T_A, comparaisons parents, capacités uniques
et tous postes du bilan D_N restent ouverts. Le bilan antérieur/A7/C2 est
préservé et aucune prémisse équivalente à la cible n'est introduite.

Aucun des onze modules ne prouve un nouveau contournement quantitatif de
parité applicable au résidu physique complet. D_N<=N/(256 logN loglogN)
n'est pas démontré. Score 0, victoire=false, full_fixed_D_N_ledger_paid=false.

## Échecs réels conservés

Les auteurs ont exécuté 29 invocations Lean : onze premiers PASS et dix-huit
FAIL techniques. Rôle 3 : 17 invocations, 6 PASS/11 FAIL ; rôle 4 : 12 invocations,
5 PASS/7 FAIL. Les sources échouées, leurs captures PREEXEC, logs et exits
restent dans les entrées FINAL. Un SyntaxError du premier lanceur Python
rôle4 avant toute Lean est conservé séparément. Les erreurs de casts,
réécriture dépendante, instances Decidable, récursion de tactiques et
élaboration ne sont pas attribuées au mur de parité. Les sorryAx internes
produits dans les logs d'élaboration échouée ne sont pas des preuves admises.
Le Juge a zéro échec et zéro replay ; toutes les onze compilations sont de
véritables premiers passages indépendants.

Rapport gelé par finalisation metadata seulement. Les reçus réel Lean,
source/log/runtime hashes et manifestes restent la preuve de compilation ;
le verdict sémantique réserve explicitement la victoire.
