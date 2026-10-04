# Boucle 4 — Agent 4 : complétion composite avec défaut exact

Sources lues : `round4/agent2_joint_frequency.md`, cache mathlib4.15 `Analysis/Fourier/ZMod.lean` et `DirichletCharacter/GaussSum.lean`. Avant toute compilation centrale, `round4/inverse.json` est lu avec statut PASS. Les anciens sources restent inchangés.

## Résultat Lean

Le fichier nouveau `round4/lean/CompositeCompletion.lean` importe uniquement `Mathlib.Analysis.Fourier.ZMod` et `Mathlib.Tactic`. Il ne dépend d'aucun fichier de recherche compilé antérieurement. La version finale compile avec code 0 dans `round4/logs/agent4_composite_compile03.log` : douze théorèmes, axiomes standards `propext`, `Classical.choice`, `Quot.sound` uniquement, aucun diagnostic, aucune preuve omise ni axiome nouveau.

Le modulus q est un entier naturel quelconque avec `[NeZero q]`. `χ : DirichletCharacter ℂ q` n'est pas supposé primitif ; aucun corps source ou module premier n'est introduit. Les poids F,G sont de véritables fonctions arbitraires `ZMod q → ℂ`. Les signes de Fourier utilisent le vrai `ZMod.stdAddChar`.

Définitions conservées :

`Fhat(h)=sum_z F(z) e_q(−h*z)`.

`gχ(h)=sum_{x in (ZMod q)ˣ} χ^{-1}(x)e_q(h*x)`.

`Fmoment=sum_{x unit}F(x)χ^{-1}(x)`.

`Hmoment=sum_{h unit}Fhat(h)χ(h)`.

`E_nonunit=sum_{h mod q, not IsUnit(h)}Fhat(h)gχ(h)`.

Le reste est donc une somme arithmétique affichée, pas une variable libre choisie pour rendre vraie la conclusion. Dans le cas non trivial de ZMod q, `zero_frequency_is_nonunit` prouve que h=0 appartient réellement à ce support. Lorsque q=1, ZMod q est l'anneau trivial et zéro y est une unité ; la somme complète reste valide, tandis que le lemme d'inclusion de zéro porte explicitement `[Nontrivial (ZMod q)]`.

`fourierWeight_eq_dft` raccorde exactement la convention de signes à la transformée mathlib `ZMod.dft`. Le théorème de reconstruction `inverse_fourier_sum` est déduit de `ZMod.dft_dft`, identité de Fourier déjà prouvée dans mathlib, et non d'une hypothèse ajoutée à notre theorem.

Une expansion de la somme double et cette reconstruction prouvent l'orthogonalité complète :

`sum_{h all} Fhat(h)gχ(h) = q Fmoment`.

Le raccord `characterPhase_eq_gaussShift` identifie la somme sur unités au `gaussSum` standard : les nonunités de x s'annulent par `MulChar.map_nonunit`. Pour chaque h unité, le vrai changement de variable multiplicatif donne `gχ(h)=τ(χ^{-1})χ(h)`, sans hypothèse de primitivité. Une partition finie exacte sépare les fréquences unités et nonunités.

Les conclusions principales `composite_completion` et `double_composite_completion` sont donc :

`τ Hmoment = q Fmoment − E_nonunit`,

`(τ²/q²) Hmoment(F) Hmoment(G) = (Fmoment−E_F/q)(Gmoment−E_G/q)`.

La division porte exclusivement sur q, dont la non-nullité est déduite de `[NeZero q]`. Elle ne porte jamais sur τ. Le corollaire `zero_gauss_retains_defect` montre que τ=0 impose `q Fmoment=E_nonunit` : le défaut peut porter toute la masse physique. Aucune suppression des caractères induits n'est autorisée par ce corollaire.

## Filtre exact préalable

Le reçu `round4/inverse.json` valide J9/J10 par histogrammes entiers de phases et division exacte par les polynômes cyclotomiques. À q=11, le caractère quadratique primitif donne E=0 sur la masse delta_1. À q=15, le caractère modulo 3 induit donne τ²=−3, τH=3 et E=12 ; le produit unitaire seul vaut 1/25 contre une masse physique 1. À q=100, le caractère modulo 5 induit donne τ=0 et E=100 sur delta_1.

À N=100000000, l'argument exact par orbites de translation de pas N/5 certifie τ=0 pour le caractère modulo 5 induit. Chaque orbite de cinq unités conserve χ et somme ses cinq racines cinquièmes en zéro. Le reçu précise qu'il couvre le groupe des unités par cet argument structurel, sans prétendre énumérer les 40 millions d'unités. Sur delta_1, l'identité implique E=N.

Le filtre conserve aussi la dépendance de F_C en C=s*t au benchmark q=100. Pour C=33, la masse physique réelle vaut 1 ; figer F_C au profil C=21 donne 2. Ce contre-exemple exclut une séparation gratuite du poids Fourier. Ces tests sont des vérifications finies et structurelles, pas une estimation asymptotique de HH.

## Journaux des réparations

`agent4_composite_compile01.log` : deux erreurs techniques. La réécriture de la somme sur Units requiert le coefficient explicite `fun x => χ^{-1}(x)e_q(hx)` pour que Lean identifie le paramètre de la fonction à reindexer. Dans l'identité divisée, `field_simp` normalisait également l'inverse du caractère à l'intérieur de l'atome `gaussSum`, produisant une différence de représentation entre `χ^{-1}` et `1/χ`. La réparation utilise d'abord J9 puis ne simplifie le dénominateur q que dans l'expression physique résultante. Ni l'une ni l'autre n'est un blocage de parité.

`agent4_composite_compile02.log` : J9 et les huit résultats antérieurs sont entièrement compilés. Une seule commutativité résiduelle `q*Fmoment=Fmoment*q` subsiste après la simplification du dénominateur ; un `ring` la résout.

`agent4_composite_compile03.log` : version finale, douze déclarations, code 0, axiomes standards seuls. Les trois journaux restent archivés, les reçus échoués ne sont pas traités comme preuves. Le Juge 5 reçoit la source gelée pour son rejeu indépendant avec le même filtre.

## Portée et obligation restante

La complétion composite règle exactement l'oubli des fréquences nonunitaires dans J9/J10. Elle peut être appliquée séparément à chaque véritable profil F_C sans prétendre que celui-ci est indépendant de C. Elle ne transforme pas un masque couplé des variables HH en produit de moments séparés.

Le retour Fourier physique restitue une identité à l'échelle q, et supprime un coût artificiel introduit en prenant séparément les valeurs absolues des fréquences. Il ne fournit aucun gain signé nouveau, aucun contrôle de E_nonunit, aucun contrôle des directions hautes de Möbius et aucun paiement de la partie positive du défaut couvert. Le raccord terminal `D_N=−Sfull+2 max(e,0)` et la cible quantitative restent ouverts. Ce certificat est un résultat partiel exact, aucune victoire.
