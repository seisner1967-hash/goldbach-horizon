# Raccords réels du rayon scalaire — SOURCE uniquement

Un module autonome, `ScalarRadiusRealConnectors22.lean`, contient 26 déclarations manuellement cataloguées : 19 théorèmes et 7 définitions, avec 26 demandes `#print axioms`. Il importe uniquement mathlib ; aucun import local prospectif, olean auteur, PREP, gate ou ACTUAL n'est créé. Son élaboration n'a pas été exécutée. Les sources numériques ROLE6 et leur revue ROLE4 restent byte-identiques et gardent leurs statuts historiques au gel.

Les fonctions réelles sont définies sans oracle ni hypothèse finale :

\[
a_0=10^{-8},\quad H_0=10^{11},\quad\tau=10^{-6},\qquad
U(a)=\frac{e^{-a}}{(1-e^{-a})^2},\quad d(a)=\frac{\arctan(a/\pi)}2,
\]
\[
\varepsilon(a,H)=\frac{24e^{-d(a)H}}{\pi a^2d(a)},\qquad
E_N(a,H)=e^{aN}\bigl(2U(a)\varepsilon(a,H)+\varepsilon(a,H)^2\bigr).
\]

Le théorème final vise exactement `radiusError pointA pointHeight 100000000 < pointTau`. Tous ses raccords sont construits dans la source :

1. Pour x≥0, le quotient est dérivable puisque 1+x>0 ; la différence atan(x)−x/(1+x) a dérivée 2x/((1+x²)(1+x)²)≥0. Sa continuité et sa monotonie sur [0,∞) sont déduites du vrai calcul différentiel, puis sa valeur zéro donne atan(x)≥x/(1+x). Aucun énoncé de cette borne n'est offert en prémisse.
2. Pour a>0, sinh(a/2)≥a/2. Les identités exp(u)exp(−u)=1 et exp(−a/2)²=exp(−a) donnent U(a)=1/(2sinh(a/2))² et la positivité du dénominateur ; donc U(a)≤a⁻². Au point fixé U≤10¹⁶.
3. Les bornes mathlib π>3 et π<3.15, ainsi que a₀<1/2, donnent π+a₀<4. Le quotient positif se rationalise exactement : (a₀/π)/(1+a₀/π)=a₀/(π+a₀). Par la borne arctan, d(a₀)>a₀/8=1/(8·10⁸)>0. Toutes les divisions utilisées sont justifiées.
4. La somme finie réelle Σ_{k=0}^6 5ᵏ/k!=16289/144>100 est évaluée par une preuve rationnelle écrite ; la vraie API `Real.sum_le_exp_of_nonneg` la minore par exp(5). La monotonie de la puissance25 et `Real.exp_nat_mul` donnent exp(125)>100²⁵=10⁵⁰. Ainsi exp(−125)<10⁻⁵⁰. L'identité exp(−250)=exp(−125)² est prouvée séparément, sans approximation ni reste numérique.
5. Le strict d(a₀)H₀>125, la monotonie de l'exponentielle et π a₀²d(a₀)>3/(8·10²⁴) donnent ε(a₀,H₀)≤64·10²⁴exp(−125)<64·10⁻²⁶. La constante ε² n'est pas supprimée : ε≤10¹⁶ entraîne ε²≤10¹⁶ε ; avec U≤10¹⁶ et exp(a₀·10⁸)=exp(1)<3, on obtient E≤9·10¹⁶ε≤576·10⁻¹⁰<τ.

Le paquet certifie en SOURCE les raccords réels conservateurs du test `radius_point01`. Il ne prétend pas élaborer le témoin multinomial S₆(5)²⁵≤S₁₅₀(125) ni reconstruire son grand numérateur rationnel. Il fournit directement une autre minoration finie explicite suffisante de exp(125), via le petit bloc réel et la loi exacte exp(25·5). L'ancien programme a été invoqué une seule fois sous son gate et a fourni une comparaison rationnelle scalaire ; ce résultat ne paie pas l'élaboration du présent module. Aucun replay, import candidat ou nouvelle expérience n'a eu lieu.

La correspondance de E à une erreur de coefficient exige le contrat `LambdaCircleTruncationEnvelope22` et ses dépendances indépendantes validées selon leur état réel. Elles ne sont ni importées ni attribuées PASS ici. Le présent module ne calcule P, P_H, D, un coefficient C_N ou D_N. Il ne paie pas les erreurs de troncature D, de quadrature, de positions, de poids ni d'arrondi d'un évaluateur complet. Les puissances premières et les corrections de frontière restent dans les contrats arithmétiques ; aucune annulation signée, minoration ou victoire n'est conclue.

Les seules obligations restantes pour ce paquet sont l'audit SOURCE indépendant et l'élaboration Lean dans un futur lot distinct, avec contrôle des 26 sorties d'axiomes. Les raccords d'API et les normalisations écrits peuvent encore nécessiter des corrections techniques ; aucune réussite du compilateur n'est anticipée. Le catalogue est manuel, sans analyseur de la source Lean. Les reçus distinguent FULL du paquet propre, TARGETED des vraies signatures mathlib, découverte de chemins et lectures absentes ; aucun cache complet n'est prétendu lu.
