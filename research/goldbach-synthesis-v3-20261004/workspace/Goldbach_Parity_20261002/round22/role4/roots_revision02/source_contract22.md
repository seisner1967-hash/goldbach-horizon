# Roots révision02 — réparation SOURCE du vrai FAIL21

Statut : SOURCE uniquement, non préparé pour exécution, aucune compilation de l'auteur. La base officielle communiquée par ROOT reste 80 modules / 1339 déclarations. Les fichiers du lot21 et ses sorties restent immuables. BORD reste suspendu à son point documentaire conservé.

`ConcreteNTTRoots22.lean` contient les mêmes 18 déclarations (17 théorèmes, 1 définition) et 18 audits. `ConcreteNTTA32Projection22.lean` reste byte-identique, avec 10 déclarations (5 théorèmes, 5 définitions) et 10 audits. Ordre futur : Roots puis Projection ; total 28 déclarations, 22 théorèmes et 6 définitions. La lecture SOURCE des en-têtes et des audits ne remplace pas leur élaboration Lean.

## Diagnostic réel et correction minimale

Le seul enfant du lot21 a réellement commencé à 20:26:43.459989 UTC et fini à 20:26:52.151451 UTC le 3 octobre 2026, exit1. Son log SHA `ff1a8a6604d45cf2ad3336ef8b433c33b974f7766845c9411c29d68dd04e399f` contient seize buts non résolus : lignes47/51/55,70/74,87/91,104/108,121/125,137/149/161/173/185. Le log, FIN et reçu ont été lus intégralement. Huit audits utilisent seulement les axiomes standards ; dix contiennent l'axiome de récupération `sorryAx` après les erreurs. Aucun olean Roots, zéro crédit au module entier ; Projection n'a pas été invoqué. Aucun contre-exemple mathématique ou preuve d'obstruction de parité n'en découle.

Aux seize sites, `reduce_mod_char at hv` a déjà ramené l'hypothèse de contradiction à `ZMod.val <résidu> = 1`. L'ancien `norm_num [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv` ne réécrit pas la forme `OfNat` de la valeur. La révision remplace exactement ces lignes par :

```lean
change (((<résidu> : ℕ) : ZMod <module>).val) = 1 at hv
rw [ZMod.val_natCast] at hv
norm_num at hv
```

Le résidu est celui du diagnostic réel : aucune valeur de puissance n'est offerte comme hypothèse. `reduce_mod_char` reste chargé de produire la preuve de l'exponentiation modulaire. `change` ne donne aucune nouvelle égalité et doit être accepté par conversion définitionnelle ; le prochain compilateur reste seul juge. `ZMod.val_natCast` transforme ensuite la valeur du cast naturel en `%`, laissant une contradiction entre naturels au `norm_num` final.

API SOURCE ciblée : `Nat.instOfNatAtLeastTwo` définit les numéraux au moins2 par le cast naturel ; `Nat.cast_ofNat` est `rfl`. `ZMod.val_natCast {n : ℕ} (a : ℕ)` conclut `(a : ZMod n).val = a % n` sans hypothèse de primalité. Sa preuve se ramène à `Fin.val_natCast` pour un module positif. Les textes de ces API ont été lus localement ; aucune invocation ou sonde n'a été faite.

## Domaines et charges préservés

K=2^27. `bankRoot p g=(g : ZMod p)^((p-1)/K)`. Les couples exacts restent (2013265921,31), (2281701377,3), (3221225473,5), (3489660929,3), (3892314113,3). Les preuves de Lucas conservent les factorisations complètes p−1 : 2^27·3·5, 2^27·17, 2^30·3, 2^28·13, 2^27·29. Les cinq preuves d'ordre conservent les puissances entière et demi-puissance non triviale, puis `orderOf_eq_prime_pow`. Ni primalité, ni racine primitive ni projection finale ne devient une prémisse.

Projection conserve N=M=100000000, K=2^27 et les véritables poids A32 de toutes les puissances premières. Ses dépendances indépendantes restent en lecture seule : FiniteFieldProjection19 olean `0304400125a93cfddace45bcc4428d835c8ee204817f88f156e9fd44ee856f4f`, QuantizedLambdaEnvelope17 olean `e821070b97b3fa4b71a3e279ecb9bc6c0de6cafdfe9dc8712b5d5a22858a6485`, RationalLogQuantization17 olean `20db07cdfb5717d7f9ab0b3e75d3c15b9e16c6820ad5285bd7debb62b0a31434`. Aucun de ces trois modules ne doit être recompilé pour cette révision. Le présent paquet ne copie ou ne construit aucun olean.

Le contrat original de ROLE3, lu intégralement, reste la référence détaillée des dépendances19/17. Son ancienne base79/1328 est historique ; la base actuelle80/1339 ne donne aucun crédit nouveau à cette révision. La future revue indépendante et préparation de lot22 devront lier les sources corrigées et les véritables traces FAIL21, sans modifier les anciennes sources433903…/cefc071… ni les préparations et archives.

Restent ouverts : compilation de cette révision28, évaluation du coefficient à N=10^8, catalogue natif exhaustif, raffinement des opérations machine/GMP/NTT/CRT, annulation continue globale, corrections PP/frontière, D_N et WIN. Aucun outil arithmétique interdit n'a été ajouté.
