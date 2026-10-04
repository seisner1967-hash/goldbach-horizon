# Boucle 5 — Agent 4 : profil physique d'unités et coefficient de Gauss réel

Sources lues : `round5/agent2_conductor_descent.md`, source finale `round4/lean/CompositeCompletion.lean`, lemmes mathlib `MulChar.star_eq_inv`, `star_apply'`, `AddChar.map_neg_eq_conj`, et `Complex.normSq_eq_conj_mul_self`. Le filtre spectral `round5/frequency.json`, statut PASS, a été lu avant la compilation01. Les sources acquises et les journaux précédents restent inchangés.

## Certificat final et dépendance

Le nouveau fichier `round5/lean/UnitSupportedCompletion.lean` compile avec code 0 sous Lean 4.15.0. La version finale correspond au journal `round5/logs/agent4_unit_support_compile04.log`. Les onze théorèmes impriment exclusivement `propext`, `Classical.choice`, `Quot.sound`, sans diagnostic. Aucun nouvel axiome, preuve omise ni décision native n'est utilisé.

La source importe `CompositeCompletion`, c'est-à-dire la source finale de la boucle 4, ainsi que `Mathlib.NumberTheory.MulChar.Lemmas` et `Mathlib.Tactic`. Le Juge est informé qu'il doit reconstruire `CompositeCompletion.lean` depuis son source avant le nouveau module ; aucune dépendance recherche cachée n'est ajoutée. La source de la boucle 5 est gelée après PASS.

## Hypothèses et définitions exactes

Le modulus q est quelconque et non nul, avec `[NeZero q]`. `χ : DirichletCharacter ℂ q` est arbitraire, sans primitivité ni borne de conducteur. F,G sont de véritables fonctions complexes sur ZMod q ; leur seule hypothèse supplémentaire pour C7–C10 est `∀z, ¬IsUnit z → F z=0`, et de même pour G. Cette condition demeure explicite dans les signatures.

Les définitions `fourierWeight`, `unitFrequencyMoment`, `physicalMoment`, `nonunitDefect` sont celles déjà prouvées dans la boucle 4, avec le vrai caractère additif standard. On définit les coefficients arithmétiques :

`tau(χ)=gaussSum χ ZMod.stdAddChar`,

`kappa(χ)=χ^{-1}(−1) tau(χ^{-1}) tau(χ)`.

Les deux sommes tau(χ) et tau(χ^{-1}) restent distinctes dans tous les énoncés. Aucun comportement quadratique n'est étendu aux caractères généraux.

## Résultats C7–C10

`physicalMoment_eq_sum` raccorde la somme physique sur Units à la somme sur tout ZMod q, en annulant les nonunités par le caractère multiplicatif réel. `unit_supported_frequencyMoment` échange les vraies sommes de h et de z. Pour z unité, `unit_phase_inner` applique le changement multiplicatif déjà prouvé à l'unité −z. Pour z non unité, le coefficient F(z)=0 est utilisé exactement.

Il en résulte C7 :

`H(F,χ)=χ^{-1}(−1) tau(χ) M(F,χ)`.

La conjugaison de Gauss est obtenue en conjuguant la somme finie, en utilisant les conjugaisons du caractère multiplicatif et du caractère additif, puis la bijection x↦−x de ZMod q :

`star(tauχ)=χ^{-1}(−1) tau(χ^{-1})`,

`tau(χ^{-1})=χ(−1) star(tauχ)`.

`character_neg_one_cancellation` et `character_neg_one_square` prouvent les facteurs de signe exacts. Leur non-nullité provient de l'unité −1, sans assertion de corps source. C9 est ensuite prouvé :

`kappaχ=(Complex.normSq(tauχ):ℂ)`.

Ce résultat établit la nature réelle non négative du coefficient ; aucune positivité n'était une hypothèse. Il n'établit aucune positivité du moment M, qui reste une somme complexe signée.

Par multiplication de C7 et usage du J9 composite conservant le défaut, C8 devient :

`tau(χ^{-1}) H(F,χ)=kappaχ M(F,χ)`,

`E_nonunit(F,χ)=(q−kappaχ) M(F,χ)`.

Enfin C10 est une égalité multiplicative exacte :

`(tau(χ^{-1})²/q²) H(F,χ) H(G,χ)=(kappaχ/q)² M(F,χ) M(G,χ)`.

Aucun tau n'est inversé. Le cas tau=0 est inclus : kappa=0 et E=qM. La correction peut donc porter toute la masse physique. Aucune valeur r ou zéro de kappa selon un conducteur primitif n'est ajoutée comme hypothèse à ces lemmes.

## Filtre spectral réellement attendu

Le reçu `round5/frequency.json` couvre le paramètre N=100000000 : 81 strata de diviseurs, 89988 vérifications exactes de réduction de phase sur 7499 fréquences échantillonnées, et les huit fréquences actives du caractère modulo 5 induit. La couverture structurelle par orbites est distincte d'une énumération de tous les résidus. Le Gauss au modulus N est zéro ; les deux contributions physiques q=5 et q=10 gardent ensemble E=N sur delta_1.

Le test crucial supplémentaire utilise les caractères d'ordre 4 modulo 5 et 10, avec χ(2)=i et réduction exacte des phases dans le corps cyclotomique d'ordre 20. Tau(χ) et tau(χ^{-1}) y sont réellement différents. Le banc valide néanmoins C7, C8, C9 et C10, avec kappa=normSq tau=5. Le moment physique n'est pas supposé réel ni positif. Le profil delta_2 modulo 10 falsifie l'omission du support d'unités.

Les contrôles de conductor r=5 à moduli 385 et 70630 vérifient la descente décrite par l'Agent 2 et réfutent l'inférence « petit conducteur implique petit modulus additif ». Ce sont des diagnostics exacts externes ; ils ne sont pas des théorèmes Lean de descente dans le présent fichier.

## Échecs Lean documentés

`agent4_unit_support_compile01.log` : C7 et les identités C8/C10 sont prouvées. La conjugaison complexifie la somme avec l'ordre inversé des facteurs par `star_mul`; le changement de variable initial référait à l'autre ordre. Le lemme de reparamétrage est corrigé pour la somme réellement obtenue. Deux alertes de variables de section inutilisées sont également réparées en retirant `[NeZero q]` des seuls lemmes généraux de −1, où cette instance n'est pas nécessaire.

`agent4_unit_support_compile02.log` : la simplification globale `neg_eq_neg_one_mul` se réappliquait au −1 nouvellement créé, atteignant la profondeur maximale de récurrence. Cette erreur est une boucle de simplification, pas une contradiction ni un obstacle de parité.

`agent4_unit_support_compile03.log` : la forme encore universelle `χ^{-1}(−x)↦χ^{-1}(−1)χ^{-1}(x)` réécrivait à son tour son propre coefficient χ^{-1}(−1). La réparation applique l'égalité uniquement au x fixé dans chaque terme de la somme, puis normalise l'associativité par `ring`.

`agent4_unit_support_compile04.log` : version finale, code 0, onze théorèmes avec uniquement les axiomes standards. Les trois premiers reçus échoués sont conservés et ne sont jamais présentés comme preuves admises.

## Portée mathématique et objectif ouvert

Ces seuls lemmes ne formalisent pas toute la théorie des conducteurs de Montgomery–Vaughan : ni la surjectivité et cardinalité des fibres de réduction d'unités, ni C1–C6, ni l'évaluation primitive de Gauss, ni le support complet des strata ne sont certifiés en Lean ici. Ils démontrent le corollaire court C7–C10 indépendamment de cette théorie et avec les vrais objets de Fourier et de Gauss.

Le support d'unités ne rend pas indépendants les autres masques de HH ; le moment M peut garder une dépendance de C et tout masque physique restant. Un poids dépendant directement de h ne peut pas être absorbé dans un profil F sans une identité supplémentaire. Le coefficient réel kappa et le nombre de strata ne produisent aucun gain signé sur M. La borne C11 envisagée pour certains profils carré-libres tordus n'est pas formalisée ou importée comme un contrôle global par ce module.

Le gain nécessaire sur les grandes directions, les masques couplés et le raccord couvert de `D_N=−Sfull+2max(e,0)` reste à démontrer. Le statut de la boucle 5 est PARTIAL, aucune victoire et aucune borne nouvelle de D_N.
