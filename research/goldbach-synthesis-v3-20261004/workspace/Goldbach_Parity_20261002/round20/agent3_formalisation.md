# FINAL3 — formalisation composite20, node13.12

Les six nouveaux modules ont chacun un PASS auteur neuf sous Lean4.15.0, sans
`sorryAx` dans leurs 141 audits finaux. Ils démontrent91 théorèmes auxiliaires et
construisent50 définitions. Il y a14 invocations Lean réelles :6 PASS nouveaux et
8 FAIL techniques conservés. Ce résultat est **auxiliaire, sans victoire**. Le
Juge doit encore compiler ses propres copies ; aucun olean auteur20 ne lui donne
un PASS indépendant.

## Résultat compilé et traçabilité

| Module | Tentative PASS | Théorèmes | Définitions | Audits | Exit Lean |
|---|---:|---:|---:|---:|---:|
| OddBonferroniArithmetic | 2 | 18 | 8 | 26 | 0 |
| LeastFactorComposite | 4 | 14 | 2 | 16 | 0 |
| SwitchedSelbergWeight | 6 | 15 | 7 | 22 | 0 |
| PhysicalCompositeSubtraction | 9 | 11 | 9 | 20 | 0 |
| CompositeAPConductor | 11 | 15 | 2 | 17 | 0 |
| SwitchedIncidenceEstimator | 14 | 18 | 22 | 40 | 0 |

Chaque tentative possède un START antérieur à Lean, sa commande réelle et son
LEAN_PATH, source/launcher/gate capturés, log brut UTF8, exit, audit et postchecks.
Sources, dépendances, runtime, gate et577 liaisons du banc canonique sont restés
inchangés pendant chaque PASS. Le launcher323fbb9474088a8b09d909815653cfc3137b8c5623c2f5fb94556cbb0433c7d3
et la préparation37c3275b9daff66e8734905be5f6f983ed610ad6f3a51d62e12835a1af87c72e
sont les versions lues et autorisées par root. La préparation est un snapshot
PREEXEC ; les résultats réels sont dans build_receipt.json et les receipts
individuels. Aucune source PASS n'a été rejouée ou modifiée après son PASS.

Les seuls axiomes des déclarations finales sont propext, Classical.choice et
Quot.sound. Certaines définitions n'en utilisent aucun. Les warnings finaux sont
des lint inutilisé/simpa/ring ; aucune erreur Lean ne subsiste dans les logs PASS.

## Portée mathématique précise

1. OddBonferroniArithmetic construit les petits premiers effectifs, leur
   primoriale, ses vrais diviseurs et xi(h)=mu(h) sous omega(h)<=2K+1. La formule
   binomiale utilise le cardinal effectivement rencontré. Le poids vaut1 en
   l'absence de petit facteur et -choose(r-1,2K+1) sinon, donc minore l'indicateur
   roughness. Il ne postule pas un cardinal ou un signe libre.
2. LeastFactorComposite construit minFac(j), son quotient, p²<=j et v>=p. Les
   cellules p non minimal gardent leurs contributions Bonferroni non positives.
   Le cas j=p² et les facteurs répétés sont couverts sans coprimalité(p,v).
3. SwitchedSelbergWeight spécialise les acquis17 au vrai support unitaire
   N*t*p0, avec g(p)=1/phi(p). N pair et z>=1 justifient G>0 et lambda1=1 avant
   toute division. Les coefficients, leur formule Möbius, le poids positif,
   l'expansion double et Q(lambda)=1/G sont construits. Q=1/G seul n'est pas
   une nouvelle estimation uniforme du principal.
4. PhysicalCompositeSubtraction utilise les vrais PhysicalWitness18 et garde
   leur ordre, bulk, unité et front original. Le domaine q est premier, mais
   n'est jamais filtré par Prime(j). L'identité theta=Q-C soustrait tous les
   composites. rawLambda conserve les puissances propres, sans mu(j)^2 ;
   raw=theta+la vraie différence raw-theta est explicite.
5. CompositeAPConductor démontre le conducteur partagé
   nu=p*lcm(h,lcm(k,l)/gcd(lcm(k,l),p)), les équivalences de divisibilité et AP,
   l'incompatibilité réelle des nonunités, le cap entier p²<=j et le kernel
   1/phi(lcm(k,l)). La primoriale p0 vide, la branche p0|t impossible et
   phi(p0*K0)=(p0-1)phi(K0) sont exactes. La compensation Euler totale et une
   amélioration nette de Gamma ne sont pas conclues.
6. SwitchedIncidenceEstimator réindexe les vrais facteurs en catalogue statique
   et développe littéralement Q et Cminus en AP avec les coefficients lambda,
   mu, p² et tous les h/d/e/p. La queue minFac>P et le slack réel restent des
   sommes séparées et non négatives. Le principal est l'intégrale réelle avec
   phi ; chaque reste réel est masse physique moins principal construit.

Sur le frame défini, l'identité finale est

    Ttheta = mainQ - mainC + (actualRQ - actualRC) - Tail - Slack.

La majoration remplace les deux restes par leurs valeurs absolues et garde la
queue soustraite. Les restes ne sont ni postulés petits ni remplacés par une
hypothèse cible. Le corollaire reference_price soustrait un M0 réel arbitraire :
il ne raccorde pas ce symbole au M0 source ni à Gamma0/global D_N.

## Échecs réellement imposés par Lean et corrections

| Tentative FAIL | Module | Nature technique | Exit réel |
|---|---|---|---:|
| 1 | OddBonferroniArithmetic | TECHNICAL_PROOF_ELABORATION_FAILURE | 1 |
| 3 | LeastFactorComposite | TECHNICAL_PROOF_ELABORATION_FAILURE | 1 |
| 5 | SwitchedSelbergWeight | TECHNICAL_DEFINITION_REDUCTION_FAILURE | 1 |
| 7 | PhysicalCompositeSubtraction | TECHNICAL_BINDER_PRECEDENCE_AND_BRANCH_ELABORATION_FAILURE | 1 |
| 8 | PhysicalCompositeSubtraction | TECHNICAL_REDUNDANT_TACTIC_AFTER_CLOSED_GOAL | 1 |
| 10 | CompositeAPConductor | TECHNICAL_REWRITE_SCOPE_AND_DEFINITION_MATCHING_FAILURE | 1 |
| 12 | SwitchedIncidenceEstimator | TECHNICAL_CONTRADICTION_GOAL_AND_IF_SIMPLIFICATION_FAILURE | 1 |
| 13 | SwitchedIncidenceEstimator | TECHNICAL_DEPENDENT_DECIDABLE_REWRITE_FAILURE | 1 |

Les analyses attempt01/03/05/07/08/10/12/13 décrivent les obligations exactes.
01 : cas if et lambda powerset ;03 : garde opaque et rewrite dans minFac ;
05 : wrappers G/produit vide ;07 : parenthèses du summand raw-theta et branches ;
08 : tactique après goal déjà clos ;10 : wrappers totient et rewrite du quotient ;
12 : contradiction sum_eq_single et types/règles if ;13 : Decidable dépendant
dans un if, résolu par simp de la même équivalence prouvée. Aucune correction
n'ajoute axiome, disponibilité première, petite Gamma ou hypothèse B6/SD.
Ces FAIL ne sont pas des contre-exemples mathématiques et ne prouvent pas que
le mur de la parité a bloqué une déduction.

Incident distinct : après le receipt FAIL01, l'affichage Python cp1252 a rejeté
un caractère Unicode du log. Le log brut et l'exit Lean1 étaient déjà conservés.
Les lancements suivants utilisent PYTHONIOENCODING=utf-8, sans modifier le
launcher gate. La correction de fermeture de section antérieure au premier
EXEC est archivée dans scope_correction20 ; elle ne compte pas comme FAIL Lean.

## Limites et prochain contrôle

Le banc nouveau N=10^8 a un exit canonique0 vérifié par root ; ROLE3 n'a exécuté
aucun producteur numérique. Son statut est
PASS_NEW_COMPOSITE20_FINITE_IDENTITIES_SOURCE_GUARDS_FALSE. Les cinq configurations
ont Gamma0_theta/raw NEG sur toute la boîte acquise de S(N), tandis que
new_principal_minus_M0 est POS. Ces observations finies ont des signes différents
et ne sont pas interchangées. La garde u>=10^24 et la garde x_test<=N/4 sont
fausses au banc. Le seuil source fixé logN>=10^24 est conservé.

Restent ouverts : la bijection complète des frames/AP physiques vers les
fenêtres ordinaires de source et leurs exceptions, B6 analytique avec variation
et constantes, BV/SD au seuil source, la comparaison favorable du principal
total, la compensation et cap p0 à l'échelle source, l'agrégation pondérée par
kappa_c de toutes les incidences et références, capacités/parents, grands
modules et queues, ainsi que le ledger complet D_N. La cible
D_N<=N/(256 logN loglogN) n'est pas démontrée. Aucune victoire n'est déclarée.

Les huit dépendances historiques sont utilisées via leurs olean Judge immuables :
RankCalibrationFace19→SeparatedTypeII18 ; SelbergFourForms17→FourFormRoots17 ;
EulerAnchor16→LeastMissingPrimeMargin16 et ThreeAdicPrimePairing13→ShortDivisorComplement13.
Aucun ancien module, producteur, PASS ou D/W kernel n'est réexécuté.

Fichiers durables : role3/final_manifest.json, role3/final_receipt.json,
role3/build_receipt.json,14 START/log/receipts et huit analyses de FAIL. Sources
et logs PASS listés avec leurs empreintes dans le manifest. Le score reste0.
