# Adjudication indépendante — lot23

Statut réel : INDEPENDENT_BATCH23_FAILED. Zéro module et zéro déclaration crédités.

Une seule tentative batch23_attempt01, un enfant Lean : START 2026-10-03T21:37:14.356259+00:00, FIN global 2026-10-03T21:37:55.161352+00:00 ; module FIN 2026-10-03T21:37:45.406858+00:00, exit1, aucun timeout et aucun olean.

La source exacte AngularMellinBorder22 (30 déclarations : 22 théorèmes, 8 définitions) n'a pas compilé. Trois diagnostics techniques sont observés :

- Ligne80 : le dérivé exponentiel obtenu pour `exp(y*(I*-N))` ne se normalise pas automatiquement en la fonction `angularCharacter N`.
- Ligne116 : le calcul du caractère à pi laisse le but `((-1)^N)⁻¹ = (-1)^N`.
- Ligne176 : la lambda issue de `congrArg (fun z => I*z)` n'est pas réduite avant la réécriture par `he`.

Ces diagnostics concernent les raccords de preuve. Ils ne montrent ni contradiction de l'identité analytique sur papier, ni obstruction de parité. La revue SOURCE antérieure reste une revue non élaborée ; elle n'avait attribué aucun PASS.

Couverture textuelle exacte : 30 noms/30 prints dans l'ordre du catalogue, 19 listes standard [propext, Classical.choice, Quot.sound], 11 listes avec sorryAx de récupération, aucune liste vide, aucun autre axiome ni native_decide/ofReduceBool. Les cinq warnings sont des lint unnecessarySeqFocus. Aucun de ces prints ne donne un crédit partiel à un module ayant échoué.

Conservation physique après FIN : 7748 entrées, 1459 anciens fichiers Juge (y compris lot21 ROLE4 clos), 3089 archives et 81 captures source/copie rehashés intacts ; gate et PRE/POST concordent. Zéro dépendance locale, aucun olean auteur, aucune ancienne compilation, aucun banc numérique ou exécutable natif invoqué.

La baseline officielle demeure 82 modules/1367 déclarations. H1, C5 global, corrélation globale, coefficient N=10^8, D_N et WIN restent ouverts. Une correction éventuelle doit être une nouvelle source et une nouvelle gate ; cet essai est clos sans reprise.

Reçu réel : D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round22\judge5\batch23\batch23_attempt01\receipt.json ; SHA256 38d1b67caed9630fa24cdb587e0e98c303ab0dc02217efb69881602561b55b6d.
PREEXEC : b4d74c3467e38ef7d37b7f67be0270e428716b188c2be022908daf51270b44a6 ; POSTEXEC : 17a7f9691d03f99f571e13ff3a4f872c4d7f551b0aedf014e9f88a3cae343976.
Source 3719a79cfd8aa0915cb15aa57111ac0529a3fa245387ceff19540395aa5756ea ; log a9c287bf1dff63999fa115dd1e71e9b83d142883c62b89254b522e51002fc0a9 ; aucun olean.

