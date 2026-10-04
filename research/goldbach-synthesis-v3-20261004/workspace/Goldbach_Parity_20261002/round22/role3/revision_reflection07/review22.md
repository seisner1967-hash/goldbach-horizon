# Révision de réflexion ζ — SOURCE ONLY

La copie distincte `ZetaReflection22.lean` a le SHA cc39bd76e00889d154a3acefea0588ca1ec7408836210f68752d5d2055f8ca2f. Elle conserve exactement la définition contourChi, les six énoncés, leurs domaines et les sept commandes qualifiées `#print axioms`. Elle n'a pas été compilée. Le module EulerDirect est une dépendance réellement PASS du Juge ; son olean devra être conservé en lecture seule lors d'un éventuel nouveau lot, sans rejeu auteur/Juge.

La source antérieure du lot06, SHA 54e32a95a62929c7251bf130156adbc7da7d66ceb1cb77609382e33c025f4a42, et son log réel f6c0a712edb08aa949ae0f86fa768cbc0c46ec7fba1f37765c5545daacfffbb2 restent immuables. Source et log ont été lus FULL dans 07faac et 2ec8d9. Le log prouve un échec technique d'élaboration ; il ne réfute ni l'équation fonctionnelle, ni une assertion de parité. Les sept modules aval n'ont pas été invoqués.

La première erreur est le point implicite x de la chaîne `differentiableAt_id.const_sub ... .neg.const_cpow`. Les nouvelles variables hid et harg ont chacune un type complet, corps ℂ→ℂ et point s. hf a également le type exact de la puissance à ce point. La composition de Gamma réutilise harg explicitement. Les obligations analytiques existantes — éviter les pôles de Gamma et le zéro de la base 2π — sont conservées et payées par les mêmes preuves.

La deuxième erreur porte sur un identifiant absent et sur une simplification incomplète. La règle `Function.comp_apply` déroule la vraie composition de ζ avec w↦1−w. `mul_neg_one`, `mul_neg` et `mul_one` réduisent la dérivée −1 et les produits correspondants. L'orientation inverse de `sub_eq_add_neg`, présente dans les sources mathlib examinées, rétablit la soustraction. L'égalité de dérivées provient toujours de l'équation fonctionnelle exacte valable dans un voisinage ouvert de s ; aucune relation de trace n'est supposée.

La troisième erreur est une tactique `ring` exécutée après la fermeture du but par `field_simp`. Elle est retirée. Les deux preuves de non-annulation χ(s) et ζ(1−s) sont maintenues avant la simplification des quotients. Aucun domaine ou dénominateur n'a été élargi.

Les lectures API sont TARGETED, pas FULL : Pow/Deriv 86–112, FDeriv/Add 666–684, FDeriv/Comp 90–112 et Deriv/Mul 130–158 dans d975c4 ; FDeriv/Basic 956–974 et Deriv/Add 314–326 dans 74a5ce. Le résultat de recherche 182286 est seulement un repérage. Le nouveau fichier complet et ses sept prints ont été lus FULL c38d5d. Un scan lexical ne trouve ni trou de preuve, ni axiome ajouté, ni unsafe/native_decide ; ce scan est une lecture de texte et non une vérification Lean.

La révision ne touche ni le lot06, ni les six sources C5 provisoires, ni les quatorze sources numériques, ni le controller02, ni la gate numérique. Le banc global actuel continue avec son unique enfant et ses limites 3600 s / 2147483648 octets. Aucune invocation Lean, probe ou calcul mathématique supplémentaire n'est autorisée ici. La compilation de cette copie exige un nouveau lot et une gate ROOT distincte.

La preuve globale H1/C5, le volet horizontal, le coefficient additif N et D_N restent ouverts. Aucun crédit officiel et aucune victoire ne sont attribués à cette rédaction SOURCE.
