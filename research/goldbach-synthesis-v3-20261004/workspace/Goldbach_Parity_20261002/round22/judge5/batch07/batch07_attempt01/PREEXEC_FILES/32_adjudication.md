# Adjudication indépendante — batch06 — échec partiel

Verdict réel `INDEPENDENT_BATCH06_FAILED`. Deux enfants effectivement invoqués, arrêt au premier FAIL : `ZetaEulerDirect22` PASS indépendant (4 théorèmes, 1 définition), `ZetaReflection22` FAIL (zéro déclaration acquise), sept modules `NOT_INVOKED`. Aucun retry, probe, ancienne compilation ou banc numérique.

## Exécution et portée des audits

Gate ROOT `D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\.arbor\sessions\parity\.coordinator\messages\round22_judge5_batch06_authorization.json`, SHA `f7ea9c8de7247c4ae931cae494344d9b98e457616af565dc2ed8437ed4992b0a`, lecture FULL223645. Unique exécution 3c1fda/session15618 → 2efffa exit1. START global `2026-10-03T13:06:18.403314+00:00`, FIN globale `2026-10-03T13:07:06.804427+00:00`.

| Module | START UTC | FIN UTC | Exit | Crédit indépendant |
|---|---|---|---|---|
| ZetaEulerDirect22 | 13:06:18.421201 | 13:06:34.403027 | 0 | 4 théorèmes + 1 définition |
| ZetaReflection22 | 13:06:34.403027 | 13:06:57.853735 | 1 | 0 |

Les cinq déclarations Euler ont chacune un audit exact ne dépendant que de `propext`, `Classical.choice`, `Quot.sound`. Olean frais `555b108cb867d2f87686539b647cda24600e4b747ebc25aa253b0c71a327c454`, log `e8baadfec45f2aa93a5019a703488a9b85f3c1e66a03461a6daa9289fd308eaa`, source `0d790ed67706e2f3c3556d2c5e7fefd50664177f5fb54584beee1d137e430a71`. Aucun token `sorry`, `admit`, déclaration `axiom`, `native_decide`, `unsafe` dans cette source ; aucun recovery dans son log.

Le log Reflection `f6c0a712edb08aa949ae0f86fa768cbc0c46ec7fba1f37765c5545daacfffbb2` couvre ses sept prints. Les cinq premiers audits standards ne constituent pas un module compilé. Les deux derniers, `contourChi_differentiableAt` et `contourZeta_logDeriv_reflection`, contiennent `sorryAx` de récupération. Aucun olean produit, aucun crédit. Sa source gelée `54e32a95a62929c7251bf130156adbc7da7d66ceb1cb77609382e33c025f4a42` demeure intacte, sans token de preuve admise.

Sept non-invoqués : GammaPsiDuplication22, GammaPsiReflection22, ContourChiPsi22, ContourChiScaled22, PsiKernelEnvelope22, PsiKernelDomination22, PsiMixedFubini22. Absence constatée de START/FIN/log/olean pour chacun. Duplication conserve son ancien PASS auteur distinct ; il n'a pas de PASS indépendant dans ce lot. Ces sept modules ne sont pas déclarés FAIL.

## Diagnostic précis

Dix messages techniques se regroupent en trois incidents :

1. Lignes 94–95 : le `have hf` non typé applique `DifferentiableAt.const_cpow` sans fixer le point s. Lean ne synthétise pas x, puis la branche b de `Or.inl`, le placeholder et le type du `have`. Le but de différentiabilité ligne 82 reste ouvert. Une future source distincte doit fixer explicitement le point ou le type ; aucune correction de la source gelée ici.
2. Ligne 124 : `add_neg_eq_sub` est absent du cache fixé. La simplification laisse `(riemannZeta ∘ HSub.hSub 1) s` et le produit par 1 dans hd ; le but exige l'évaluation et la soustraction normalisées. Ce sont des défauts d'API/normalisation.
3. Ligne 131 : une tactique s'exécute après que `field_simp` a déjà fermé le but, `no goals to be solved`.

Le journal ne démontre aucune contradiction de l'identité analytique ni obstruction de parité. Les buts analytiques ne sont pas payés par ces diagnostics ; aucune victoire ne suit du PASS Euler.

## Mathématique effectivement acquise et charges ouvertes

Euler porte sur la vraie `riemannZeta`, sa série dans Re(s)>1 et la sommabilité en norme. Le produit Euler analytique de mathlib, sous ces charges vérifiées dans la preuve, identifie exp de la somme des logarithmes premiers à ζ et entraîne son absence de zéro à droite. Aucune cible D_N, aucune non-annulation ζ libre, aucune hypothèse d'intégrabilité finale ne remplace la conclusion. Les prémisses de domaine et les usages de l'API sont visibles dans la source. Ce module ne donne ni identité de contour globale ni minoration arithmétique.

L'audit SOURCE de Reflection, duplication, χ′/χ, noyau apparié, domination et Fubini reste documentaire pour tout ce qui n'a pas compilé. Le domaine −1<Re(s)<0, les dénominateurs, la continuité, les enveloppes et les vrais passages intégrables ont été examinés en préparation ; aucune de leurs conclusions aval n'est acquise par batch06. Mellin, Arch global, orientations/normalisations finales, queues horizontales, certificat intervalle des primitives, compte exhaustif des zéros, coefficient additif N, D_N restent ouverts.

## Conservation, lectures et compte

7019 inputs, 270 anciens fichiers Juge, 3089 archives et 64 captures source/copie sont re-vérifiés sur tous leurs bytes actuels. Bindings PRE/POST identiques, gate inchangée. Sept dépendances indépendantes readonly, aucune recompilation ; LEAN_PATH contient seulement l'output neuf, leurs copies readonly et huit bibliothèques cache. Aucun olean auteur. Lean4.15/mathlib9837ca9d fixés.

PREEXEC SHA `cfd1131ac990f86ce77ce2ed9add1a7d5ecd59b9d9d932b3938628077a1ebcc5` ; POSTEXEC SHA `dae3e6893de2087971f5610bf4222497c41ee49367761bda9345a7ea5895d520` ; reçu effectif SHA `0f1494d07997e45540f0abcb3e553a985ef9b5a8435ae5b267beb990a4b7da2d`. Logs complets FULL83947d, puis Reflection reread FULL5eee57 ; START/FIN/reçu FULL5dfb6c, puis reçu reread FULLc84866. Sources propres FULL e37773/7f2cb8/ed619f/624c6e/fbcf86/69fda6/d24b1f/844cbd/c7b9c0. Catalogue FULL9c7c55, reads FULLbb5d19, préparation FULL0473df. Les gros PRE/POST ont seulement été lus en projection header/entrée fb1f08, hashés sur tous leurs bytes et vérifiés intégralement par ce helper ; aucune prétention raw FULL de ces JSON ou de toutes les sources mathlib. L'ancienne lecture f3c2c8 tronquée est exclue, remplacée par c7b9c0.

Officiel ROOT avant observation : 68 modules /1132 déclarations auxiliaires incluant définitions. Crédit possible de ce lot : un module/cinq déclarations, soit 69/1137 uniquement après observation ROOT. Aucune extension pour les cinq prints diagnostiques de Reflection. Aucun H1, C3, C5 global, C6 global, trace globale, D_N ou WIN acquis.

Document créé à 2026-10-03T13:16:39.186294+00:00. Sources, résultats et anciennes archives restent immuables.
