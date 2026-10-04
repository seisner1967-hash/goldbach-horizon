# Révision Λ–Mellin02 après le vrai FAIL31 : SOURCE uniquement

Ce paquet distinct conserve le module `ComplexGammaMellinLambda22`, ses 30 déclarations (24 théorèmes, 6 définitions), ses 30 impressions qualifiées d'axiomes et tous ses énoncés, domaines et imports. Il ne modifie aucune SOURCE01, copie ou sortie du lot31. Aucun compilateur ni probe n'a été invoqué par l'auteur pour cette révision. Le statut est SOURCE non élaborée, non PREPARED ; seul un futur Juge peut valider les corrections.

Le vrai enfant indépendant31 a commencé le 2026-10-04 à 01:32:49.390502 UTC et fini à 01:33:30.707890 UTC, exit1, sans olean. Son journal SHA `baf6fe9d6f7ba57c9259eaec5481de08f993228748891793a9234626737bc367` a été lu FULL85c9a4, ainsi que le reçu `470f798110abde794b6742605c5dc66e4c7aabe7bc6a9e81e502e3c41aab9d1c`. Les 30 prints se répartissent en 20 standards et 10 récupérations sorryAx ; aucun crédit n'est attribué au module entier. Ces récupérations du compilateur ne sont pas des axiomes écrits dans la SOURCE. Ce journal montre cinq diagnostics à trois raccords d'élaboration ; il ne montre pas de contre-exemple analytique ni d'obstruction de parité.

## Trois corrections bornées

1. À l'ancien site84–85, `[[1,1+K]]` a été lu comme une liste imbriquée, car la portée de notation `Interval` n'était pas ouverte. La révision emploie directement `Set.uIcc (1:ℝ) (1+(K:ℝ))` et construit une inégalité `hle` explicitement réelle, avant `uIcc_of_le hle`. La définition, la notation et la signature réelles de `uIcc_of_le` ont été lues TARGETED6743aa dans `UnorderedInterval.lean`. Aucun intervalle final ou hypothèse d'intégrabilité n'est offert.
2. À l'ancien site110, `norm_num` avait laissé la somme sur `Finset.range 2`. La révision demande sa réduction par `Finset.sum_range_succ` et `Real.zero_rpow`. La première API est bien la déclaration additive générée depuis `prod_range_succ` par `to_additive` (TARGETEDdb0470), la seconde a la condition exposant non nul (TARGETED6743aa), que la normalisation rationnelle doit payer. Le terme0 vaut0 et le terme1 vaut1 ; aucune constante de série finale n'est ajoutée.
3. À l'ancien site146, le `simp only` isolé ne progressait pas dans la branche n=0. La révision fournit le vrai théorème général `continuous_const` typé pour la fonction ℝ→ℂ nulle, puis transporte par `simpa [lambdaMellinCoefficient]`. La nullité de Λ(0) est celle de la vraie fonction arithmétique, via `ArithmeticFunction.map_zero` (TARGETEDdb0470) ; aucune continuité du coefficient final n'est donnée comme prémisse.

Ces trois blocs de preuve sont les seules modifications Lean. Les six définitions, les vingt-quatre énoncés, les imports et les trente lignes `#print axioms` sont inchangés par inspection manuelle FULL.

## Contrat arithmétique et analytique conservé

Avec le cpow principal, la vraie `ArithmeticFunction.vonMangoldt` et tous les termes de puissances premières conservés, on pose

\[
Q=\sum_{n\ge0}\Lambda(n)n^{-2},\quad
D(t)=\sum_{n\ge0}\Lambda(n)n^{-2-it},\quad
K(w,t)=\Gamma(2+it)w^{-2-it},\quad
P(w)=\sum_{n\ge0}\Lambda(n)e^{-nw}.
\]

Pour \(\Re w>0\), la conclusion SOURCE reste exactement

\[
P(w)=\frac1{2\pi}\int_{\mathbb R}D(t)K(w,t)\,dt.\tag{MΛ}
\]

Le module construit directement Λ≤log n, Λ(n)n⁻²≤2n⁻³ᐟ², la sommabilité et le test intégral donnant Q≤6. La norme de chaque coefficient vaut Λ(n)n⁻² ; la convergence uniforme donne D continu et |D|≤6. Le L1 de chaque terme, le L1 du produit D·K et la sommabilité de la série des intégrales de normes sont démontrés, pour justifier l'échange infini. Le vrai logarithme principal de la multiplication par un réel positif paie la factorisation de (nw)⁻ˢ, sans saut de branche. L'inversion Gamma acquise s'applique à nw car n>0 et Re(w)>0 ; le terme0 est séparément nul.

La seule dépendance locale directe reste le véritable `ComplexGammaMellinHolomorphy22` indépendant PASS27, SOURCE b8b69c16…, olean f831358e…. Transitivement, Local26 est la seule ligne Local22 acquise du reçu global FAILED26, avec olean364ac79a… ; l'inversion réelle20 et Gamma02 restent readonly. Aucun de ces modules ne doit être recompilé pour cette SOURCE. Les références exactes, leurs receipts et les observations ROOT sont conservées dans les bindings anciens, vérifiés physiquement e6094f : 32 intacts, aucun écart.

Le majorant local du produit et son intégrabilité restent ceux effectivement écrits dans le module. Il n'existe pas ici de constante fournie en paramètre pour l'erreur finale, de formule ζ/log-derivative supposée, d'inversion Mellin finale offerte, de crible ni d'inversion de Möbius utilisée.

## Frontières de statut

La SOURCE du bridge2 est préservée et exclue de ce paquet ; Tail03 est depuis lors indépendamment PASS30 et observé ROOT, mais cela ne compile rétroactivement ni le bridge2, ni EΛ16, ni cette révision main30. EΛ16 et Geometry25 restent des paquets SOURCE distincts. Leur preuve et leur précision ne servent pas de prémisses dans ce module.

Cette SOURCE ne démontre pas un compte de zéros, une formule spectrale de ζ, une évaluation numérique, une annulation signée en phase ni la cible D_N. Les corrections PP et de la frontière r>α restent dans leur cadre canonique. Les acquisitions de la monographie sont conservées ; aucune victoire n'est annoncée.

Les risques d'élaboration restent visibles : normalisation de la somme finie conditionnelle et réduction de la fonction constante par le simplificateur. Il faut une revue indépendante, une sélection ROOT puis une nouvelle gate avant toute compilation. Le présent handoff contient uniquement des bindings directs de provenance et de lecture, sans fermeture transitive d'import/cache ni lanceur ni préparation runtime.

