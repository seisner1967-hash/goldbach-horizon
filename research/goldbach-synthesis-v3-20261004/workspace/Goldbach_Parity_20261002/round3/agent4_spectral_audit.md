# Boucle 3 — Agent 4 : transformée exacte sur les unités

Sources lues : `round3/agent2_projection.md`, filtre exact `round3/multifibre.json`, sources mathlib4.15 `NumberTheory/GaussSum.lean`, `DirichletCharacter/GaussSum.lean`, `MulChar/Basic.lean`, `MulChar/Lemmas.lean`, et `Complex/CircleAddChar.lean`. Les sources et preuves acquises restent intactes.

## Verdict de faisabilité

P3 est démontrable pour un module composite quelconque, et a été démontré dans `round3/lean/QuotientGauss.lean`. La source finale compile avec code 0 sous Lean 4.15.0, journal `round3/logs/agent4_quotient_gauss_compile04.log`. Les onze théorèmes impriment uniquement les axiomes standards `propext`, `Classical.choice`, `Quot.sound`. Aucune hypothèse de primalité de N, de conducteur, de caractère primitif, de signe ou de petitesse n'est introduite.

Le résultat principal est même prouvé pour un anneau commutatif fini R quelconque (avec égalité décidable pour l'instance des unités), un caractère multiplicatif `χ : MulChar R ℂ` et un caractère additif `ψ : AddChar R ℂ`. Ces hypothèses portent seulement sur les structures effectivement présentes. Le théorème terminal `zmod_standard_transform` prend `N : ℕ`, `[NeZero N]`, `χ : DirichletCharacter ℂ N`, et `h b l : (ZMod N)ˣ`. Il utilise le caractère standard `ZMod.stdAddChar`, dont la valeur est bien exp(2πij/N).

## Définitions et égalité arithmétique

`kloosterman ψ A B = sum_{x in Rˣ} ψ(A*x + B*x^{-1})`.

`unitGauss χ ψ = sum_{u in Rˣ} χ(u) ψ(u)`.

Le théorème `unitGauss_eq_gaussSum` raccorde explicitement cette définition au `gaussSum` standard de mathlib, qui somme sur tout R. La preuve insère l'image des unités et utilise `MulChar.map_nonunit` pour annuler tous les termes hors image ; aucune hypothèse de corps ne remplace l'ensemble des unités.

Pour h,b,l unités :

`sum_eta χ^{-1}(eta) K(eta*h*b,l) = gaussSum(χ^{-1},ψ)^2 χ(h*b*l)`.

La preuve développe la vraie somme double. Pour chaque x unité, elle reparamètre eta par multiplication par l'unité `(h*b*x)^{-1}`. Elle reparamètre ensuite x par inversion, puis par multiplication par l^{-1}. Ces bijections donnent les deux facteurs identiques `gaussSum(χ^{-1},ψ)`. Le facteur restant est exactement χ(h*b*l). Les trois contraintes d'unité sont matérialisées dans les types, et ne sont jamais éliminées par une assertion numérique.

La variante `kloosterman_conjugate_transform` traduit explicitement l'inverse du caractère en conjugaison complexe avec `MulChar.star_eq_inv` et `star_apply'` ; il ne s'agit donc pas d'une inversion silencieusement supposée identique à la conjugaison. La partie réelle est conservée dans `kloosterman_transform_real_part`. `weighted_transform_real_part` permet en outre un ensemble fini d'indices arbitraires, des paramètres h(t),b(t),l(t) tous unités et des coefficients réels c(t). Il ne transforme que la somme en eta effectivement affichée, sans prétendre supprimer un masque dépendant d'eta.

## Filtre préalable

Le reçu `round3/multifibre.json` était PASS avant la compilation01. Il vérifie notamment le regroupement exact en quotient des vrais poids à N=100000000, 18081 tuples et 2214 résidus non nuls. Il réfute la factorisation après oubli du masque couplé a<s : au résidu eta=122399, coefficient séparé −4 contre coefficient réel −2.

Les deux histogrammes de phases quadratiques pour q=11 et q=829 sont exacts et donnent respectivement −11 et +829 après la relation cyclotomique. Ils valident le signe de P3 et empêchent d'en déduire une contraction ou une positivité automatique. Le point HH à N=1658 avec conducteur 829 conserve une projection non nulle. Ces domaines finis ne sont pas présentés comme vérification exhaustive de tous les modules ni comme borne asymptotique.

## Journaux des compilations

`agent4_quotient_gauss_compile01.log` : les sommes sur Units exigeaient l'instance `[DecidableEq R]`, le nom `Units.val_injective` n'existe pas (l'injectivité est `Units.ext`), et la résolution de `.sum_comp` choisissait le lemme sur une permutation d'un Finset au lieu du lemme global `Equiv.sum_comp`. Ces erreurs d'API/instances ne concernent pas la parité. Certaines déclarations dépendant d'erreurs exposent des preuves manquantes dans le journal ; ce reçu échoué n'est pas retenu.

`agent4_quotient_gauss_compile02.log` : le bridge sur tout R est déjà compilé. Deux noms supplémentaires de lemmes manquaient (`Equiv.mulLeft_apply`, `Units.val_inv_mul`). La preuve de substitution passe alors par un `change` explicite et la coercition d'un produit d'unités. Deux buts utilisaient une décomposition `congr 1` trop forte avant l'association des produits complexes ; une égalité de phase dans R puis `ring` répare exactement ces buts. La dernière expansion χ(h*b*l) doit également être faite dans toute l'expression, avec `simp only`, au lieu d'une seule occurrence de réécriture.

`agent4_quotient_gauss_compile03.log` : code 0, huit théorèmes fondamentaux, axiomes standards seuls. Cette version est ensuite étendue par la conjugaison explicite et deux résultats réels.

`agent4_quotient_gauss_compile04.log` : version finale, code 0, onze théorèmes, aucun diagnostic et aucun axiome non standard. Le Juge 5 reçoit cette version gelée pour rejeu indépendant. Les quatre journaux sont conservés pour audit.

## Limite exacte à la frontière analytique

Les lemmes mathlib `gaussSum_sq` et `gaussSum_mul_gaussSum_eq_card` supposent un corps source dans leurs résultats de taille. Ils ne sont pas employés pour prétendre une taille ou un signe sur ZMod N composite. Notre preuve de P3 est une identité de reparamétrage, valide sur le vrai groupe d'unités ; elle ne rend pas les grandes directions de caractères petites.

La projection d'un masque couplé dépendant de eta reste une somme pondérée non factorisée. `weighted_transform_real_part` conserve des poids extérieurs à la somme en eta et n'autorise pas à faire sortir un tel masque. Les phases nonunitaires et h=0 ne sont pas couvertes par la signature h,b,l : Units ; elles constituent le reste P7, qui reste obligatoire. Le principal caractère multiplicatif n'est pas identifié à la fréquence additive zéro.

P3 ne déduit donc ni P10 (petitesse de la véritable projection haute de Möbius), ni un paiement du défaut séparé P6, ni un contrôle du reste nonunitaire P7. Les préfixes autorisés pour les petits conducteurs ne s'étendent pas gratuitement à tous les caractères modulo N. Le lemme quantitatif recherché doit encore contrôler ces trois objets avec leur couplage réel, puis le raccord `D_N=−Sfull+2 max(e,0)`. Cette compilation constitue un résultat partiel exact, aucune victoire.
