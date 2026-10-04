# FINAL5 — Juge indépendant20 : PASS auxiliaire, victoire non atteinte

Les seize copies fraîches ont réellement compilé sous Lean4.15.0, exit0,
avec 250 théorèmes, 83 définitions, 1 structure et
334 impressions d'axiomes couvrant exactement toutes les déclarations
explicites. Aucun `sorryAx`, `sorry`, `admit`, axiome ajouté, `native_decide`,
`trustMe` ou déclaration unsafe n'est accepté. Les seuls axiomes imprimés sont
`propext`, `Classical.choice`, `Quot.sound`, ou aucun axiome.

Il s'agit d'un PASS indépendant **auxiliaire**. La borne globale
`D_N <= N/(256*log N*loglog N)` et le contournement de parité restent non prouvés.
Score0 ; WIN=false. Le cumul d'ingrédients indépendamment audités est désormais
57 modules/942 théorèmes, sous réserve de
l'enregistrement du coordinateur ; ce compte ne mesure pas une preuve Goldbach.

## Compilations effectivement observées

| Module neuf | Théorèmes | Définitions | Structures | Audits axiomes | Exit |
|---|---:|---:|---:|---:|---:|
| OddBonferroniArithmetic | 18 | 8 | 0 | 26 | 0 |
| LeastFactorComposite | 14 | 2 | 0 | 16 | 0 |
| SwitchedSelbergWeight | 15 | 7 | 0 | 22 | 0 |
| PhysicalCompositeSubtraction | 11 | 9 | 0 | 20 | 0 |
| CompositeAPConductor | 15 | 2 | 0 | 17 | 0 |
| SwitchedIncidenceEstimator | 18 | 22 | 0 | 40 | 0 |
| FriablePhysicalPrefix | 14 | 2 | 0 | 16 | 0 |
| FriableEulerRankin | 16 | 4 | 0 | 20 | 0 |
| FriableKernelEnvelope | 11 | 2 | 0 | 13 | 0 |
| FriablePrimeHarmonic | 16 | 0 | 0 | 16 | 0 |
| FriableTotientEnvelope | 14 | 3 | 0 | 17 | 0 |
| FriablePhysicalPayment | 23 | 4 | 0 | 27 | 0 |
| FriablePhysicalDemand | 5 | 0 | 0 | 5 | 0 |
| FriableDemandAggregation | 5 | 3 | 0 | 8 | 0 |
| FriableSourceGeometry | 47 | 14 | 1 | 62 | 0 |
| FriableSourceBudget | 8 | 1 | 0 | 9 | 0 |

Le START unique du Juge est 2026-10-03T04:42:00.888897+00:00 ; la fin du child est
2026-10-03T04:52:05.323764+00:00. Il n'y a qu'une invocation du lanceur et seize
invocations Lean nouvelles, zéro FAIL du Juge et zéro ancien module recompilé.
Les anciennes dépendances13/16/17/18/19 sont importées en lecture seule.
`LEAN_PATH` contient exclusivement `judge/audit`, les répertoires historiques
gelés et les huit bibliothèques cache. Il exclut tous les oleans auteurs20.
Chaque nouvelle dépendance est satisfaite par son propre PASS frais antérieur.

La gate root a le SHA a321f065d36d8d18529d12356d2502e12a75e78fd87a59effeb6db562fba7c03, la préparation finale
fe440243022cf4111c61827f7b6a387e4a2182cd3523b4aef41ae411abcda6a7, le manifeste PREEXEC
c37af3ac54572855e80a124f1f4f733997fbd61a6d7152be3205522e7b2c4305. Sources originales/captures/copies,
lanceurs/gate/préparation, runtimes, logs stdout/stderr, codes réels et oleans
sont conservés. Avant/après chaque module et à la clôture, tous les bindings
gelés sont inchangés ; 2837 chemins distincts ont encore été vérifiés
par cette clôture metadata. Aucun producteur, noyau D/W, logarithme, signe,
factorisation, test premier, banque, ancien PASS ou PDF n'a été réexécuté.

## Ce que les preuves démontrent

La piste13.12 construit le Bonferroni impair sur la vraie primoriale et ses
diviseurs. Les composites sont partitionnés par minFac avec p² et p|v permis ;
les cellules non minimales gardent leurs contributions non positives.
Le domaine q provient des vrais PhysicalWitness18 et n'est pas filtré par
Prime(j). Le poids Selberg est construit, lambda1=1 et Q=1/G sont établis.
La soustraction theta enlève tous les composites ; le raw vonMangoldt reste
distinct et conserve ses puissances propres, sans masque mu(j)².

Le conducteur est le vrai p*lcm(h,lcm(k,l)/gcd(lcm(k,l),p)), avec incompatibilités
et caps entiers. L'expansion AP conserve toutes les représentations signées.
L'identité finale est `Ttheta=mainQ-mainC+(actualRQ-actualRC)-Tail-Slack`.
Les deux remainders sont effectivement masse physique moins principal construit.
Leur majoration par ABS n'est pas une estimation de distribution source.
Le corollaire reference_price a un M0 réel **arbitraire** ; il ne prouve pas
son raccord au M0 littéral acquis. B6, SD, BV/onsets, principal favorable,
agrégation pondérée et bridge des frames restent ouverts.

La piste14.5 démontre une borne source réelle au seul seuil `log N>=10^24` :
`sourceFriableAbsoluteCost N <= N/(8192*log N*loglog N)`.
Ce coût est la demande theta en ABS sur H19 filtré F0 ou F1, plus la réciproque
F1 physique unique en ABS, après fusion des e en image q. TK, les vrais tails
Euler et les gardes de floors/ceils sont dérivés ; aucune petite masse libre
ou bonne disponibilité n'est prise en prémisse. Tous les +1 et tous les rangs
de ce domaine sont présents. Les enveloppes raw sont locales ; le budget
source agrégé retenu est theta, sans second paiement de Bpp.

Les m1 non friables de F0 privé de F1 restent hors du coût réciproque payé.
Le complément non friable, H19 vers support source entier, la réunion de tous
les vertices et capacités, singletons/e1/p0/faces/nonbulk, medium/long,
Gamma/T_A/parents/W et le ledger complet restent distincts et ouverts.
Le Juge ne déduit aucune partition croisée entre les deux nouvelles pistes.

## Échecs conservés et portée numérique

Les auteurs ont 38 invocations Lean réelles :
16 PASS nouveaux et 22 FAIL techniques. Tous les logs exacts,
START, snapshots et exits restent liés au manifeste gelé. Les `sorryAx`
propagés dans les FAIL ne reçoivent aucun crédit. Les corrections portent sur
binders, wrappers, coercions, API, algèbre et tactiques, sans nouvelle prémisse
analytique. Aucun FAIL n'est inventé comme preuve d'obstacle de parité.
L'incident cp1252 d'affichage est distinct de l'exit Lean déjà conservé.

Le Juge lit seulement les résultats et reçus des deux banques20 canoniques
exit0, avec gardes source FALSE à N=10^8. Il ne recalcule pas leurs signes.
Les labels stockés distinguent les Gamma theta/raw NEG et les nouveaux
principaux moins M0 POS dans les cinq configurations composites ; ceci ne
transporte aucun signe au régime source. Le banc friable observe ses quinze
réciproques F1 uniques et quatre F0 privé de F1 impayées, sans certifier le
budget analytique. Ces observations finies ne donnent pas le target D_N.

La préparation initiale v01 contenait une lecture de N au mauvais niveau JSON.
Ce schéma a été corrigé avant toute gate/START Juge ; source/préparation01 sont
archivées NOT_EXECUTED. Cette révision statique n'est aucun FAIL Lean ou numérique.

## Artefacts et compétences

`judge/audit_receipt.json` est le reçu machine complet ; `launch_receipt.json`
conserve l'exit réel et le hash du log ; `launch_post_integrity.json` accorde
le crédit seulement avec intégrité inchangée. Chaque module possède son
START, invocation brute, stdout/stderr/log, postcheck et reçu audité.
Le rapport mathématique du Juge s'appuie sur les FINAL1/2/3/4/6 et géométrie
lus intégralement, les sources finales Budget/Estimator/Subtraction/Conductor
lues intégralement, ainsi que les définitions/déclarations des seize sources
scannées et contrôlées par Lean. Il ne prétend pas avoir affiché FULL les
565KB de dictionnaires opaques de hashes ni les deux grands résultats JSON.

Les fichiers sont désormais gelés. Aucun PASS ni échec inchangé ne doit être
rejoué. Le coordinateur conserve les acquis, enregistre score0 et retourne à
l'idéation avec les obligations source effectivement manquantes.
