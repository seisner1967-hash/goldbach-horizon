# Clôture factuelle Gamma22 — auxiliaire uniquement

L'unique tentative autorisée a terminé avec `exit_code = 0` et le statut
`GAMMA_ROTATED_LAPLACE_AUX_PASS`. Ce document ajouté après l'exécution ne
modifie aucun fichier gelé de préparation, de source ou de résultat. Il
consigne un contrôle fini de Gamma par une intégrale complexe et des
références indépendantes. Il ne certifie ni la formule de Weil, ni la
complétude des zéros, ni la chaleur, ni le coefficient de Goldbach, ni une
borne sur D_N. `WIN = false`.

## Tentative réelle

La gate distincte `round22_gamma_numeric_authorization.json`, créée par
ROOT, a pour SHA256
`a1c30ab747bd3395fecb8dd4a250c0146338dfc0dad3f85c2174f9743b9b8835`.
L'acteur ROLE6 a invoqué une fois `run_gamma_numeric_once22.py`, avec le
runtime Python canonique, les options `-B -X utf8` et cette gate exacte.
ROOT n'a pas exécuté le producteur mathématique.

| Champ | Valeur réelle |
|---|---|
| Invocation de lancement | `3013f3`, session `50679` |
| Fin de session | `48d9f6`, exit0 |
| Jeton | `bd36b071eadf487fa05981855dd4ea0a` |
| START UTC | `2026-10-03T07:28:40.526891+00:00` |
| FINISH UTC | `2026-10-03T07:34:55.431199+00:00` |
| PREEXEC | 17 copies réelles : 15 bindings, préparation et gate |
| POSTEXEC | 15 bindings inchangés ; préparation et gate inchangées |
| launch_error | null |
| post_integrity | true |

La réservation est antérieure au START ; son champ historique
`no_math_started_yet = true` décrit cet instant et ne décrit pas l'état
final. Les captures PREEXEC sont antérieures au START. Aucun second
lancement n'a été effectué.

## Portée et résultats

Les 21 cas sont le produit de sigma dans `{1, 3/2, 2}` et gamma dans
`{0, -1, 1, -10, 10, -100, 100}`. Chaque cas a réellement évalué les 9728
cellules de l'intégrale tournée en variable logarithmique sur `[-32,6]` :
204288 couples cas-cellule, et non une simple vérification de la formule
cible contre elle-même. Les références utilisent réflexion et récurrence
aux trois valeurs de sigma. Les queues et le reste de quadrature figurent
explicitement dans les rayons du résultat. L'étiquette N=100000000 ne
transforme pas ce contrôle de Gamma en une extraction du coefficient N.

Tous les 21 cas satisfont les gardes du contrat et la tolérance absolue
normalisée `1/100000000`. Les 12 mutations déclarées omettant l'atténuation,
pour `|gamma|` égal à 1 ou 10, sont détectées avec des intervalles disjoints
des références et une borne inférieure mutée supérieure à 2. Les six cas
`gamma = +/-100` portent explicitement le drapeau non informatif pour une
mutation zéro à cette tolérance absolue ; leur PASS d'enclosure n'est pas
présenté comme cette falsification.

Le producteur rapporte les appels effectifs suivants : exp 38981,
sin_cos 68117, sqrt 43 et pi 1. Les 43 certificats de racines sont produits
par les inégalités entières du code. Ce rapport ne prétend pas avoir
effectué une seconde recomputation indépendante de ces certificats.
L'AST contrôlé rapporte zéro flottant ; aucune API Gamma n'est appelée.

Le majorant Cauchy est construit avec rayon 1/8, norme 2^26, degré 12,
demi-cellule 1/512. Le reste global de quadrature vaut
`38*64/(63*2^52) = 19/2216615441596416`. Les queues sont `(3/8)^32` et
`516/2^128`. Les primitives utilisent des intervalles dyadiques à 768 bits,
des séries avec restes explicites et un arrondi extérieur. La garde de
largeur des primitives est un contrôle d'efficience, pas une hypothèse
d'enclosure.

## Artefacts effectifs et SHA256

Tous les fichiers ci-dessous sont dans `gamma_h2/actual_gamma22/`.

| Fichier | Octets | SHA256 |
|---|---:|---|
| gamma_result22.json | 244209 | `595b15340efe03bd215eebe7f6d526cd1f2f5d07865f074a3b7927687beb967a` |
| actual.log | 5113 | `8c0e2febec17d75b95c73e6aef85fdb67c6322b3049ebb5473c4b9c94bdacbd5` |
| gamma_sqrt_certificates22.jsonl | 52352 | `c1ad2c55609947d95cfdb779b5c808ac334b0c77c5cc72f11f2891d17438077e` |
| actual_receipt.json | 1685 | `6247f1dca226bdd052ae968a5131a882a8ed40764cae48759ef15942845a2106` |
| actual_START.json | 1243 | `450e2e0434f091e5c180910d98e366ac17b9b8a5339019a460583b4781b39ada` |
| attempt_reservation.json | 256 | `86f644a567e8c6ea63b612dbe56e7534f0f801240d60e3cf71246b49784624d9` |
| PREEXEC_captures.json | 7082 | `7adb94975a5ca5c936d8f05faa858c2512837e19cef96c25279b45dc54572d14` |
| POSTEXEC_integrity.json | 5768 | `4de3a9592e17a00eeb3ea40b7a132471c1ca8a39ace77f8d70b42551f9c49eba` |

La préparation gelée reste SHA
`c9596f415b725d5db92dbdcd3a5de0bd7b972c35113e2dd16cd7aa87d6b25588`.
Le runtime reste SHA
`4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c`.

## Lecture intégrale réellement effectuée

Les 2193 lignes brutes de `gamma_result22.json` ont été lues dans les
portions suivantes. Les premiers appels tronqués `002bcd` et la deuxième
portion tronquée `30de9b` ne sont pas crédités comme lectures complètes.
La première portion `b6cee1` de cet appel combiné est complète.

| Lignes inclusives | Chunk intégral |
|---|---|
| 1–400 | be2473 |
| 401–800 | b6cee1 |
| 801–1000 | b69ca3 |
| 1001–1200 | 418d34 |
| 1201–1400 | ef6acf |
| 1401–1600 | 82b412 |
| 1601–1800 | a154bc |
| 1801–2000 | 3fc635 |
| 2001–2193 | de50a3 |

Autres lectures FULL : log `bf2884`, PREEXEC `63631b`, POSTEXEC `b92cec`,
receipt `d5ecdc`. Une nouvelle lecture documentaire du receipt, du START
et de la réservation est `59b679` ; elle n'exécute aucun calcul du banc.
L'inventaire et les hashes effectifs ont été lus par `b63a0f`.
Le JSONL de certificats est inventorié, compté et hashé ; aucune lecture
FULL de ses 43 lignes ni audit indépendant de ses inégalités n'est
revendiqué ici.

## Note extérieure aux bindings

La note `gamma_period_width_note22.md`, SHA
`19b238411a5252c375a89b16c95a7d9296509fb509396ab2df9d049dd48b76a3`,
a été annoncée avant le START. Pour le domaine générique de phase
`[-4096,4096]`, la borne sûre de contribution de l'incertitude de période
est `2^18` unités de grille plutôt que la clause `2^16` du papier gelé.
La garde d'efficience `2^48` demeure suffisante. Les enclosures effectives
reposent sur les intervalles complets de pi et les restes de séries,
indépendamment de cette estimation d'efficience. Aucun fichier gelé n'a
été modifié pour cette note.

## Compteurs et obligations restantes

ROLE6 a exécuté deux tentatives mathématiques distinctes en ROUND22 :
G0 Epstein, puis Gamma. Aucune tentative n'a été rejouée. ROLE6 a exécuté
zéro compilation Lean22, zéro trace Weil, zéro banc chaleur et zéro
extraction du coefficient N. La conservation metadata ROUND21 reste un
événement historique distinct, sans crédit mathématique.

La preuve Lean H2 sur tout le strip appartient à ROLE4 et nécessite sa
gate de compilation distincte. Pour l'annexe Weil 15.2 restent ouvertes
la complétude et les boîtes certifiées des zéros, l'évaluation Gamma aux
boîtes générales, les constantes et logs certifiés, la quadrature
archimédienne et la trace arithmétique globale. L'interface Gamma-prime
sur une boîte est un prochain travail papier/source uniquement, sans
invocation mathématique autorisée par la gate consommée ici.
