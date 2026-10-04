# Agent 4 — identité quartique de Möbius et insertion réelle

Sources lues : `CONTRACT.md`, `agent2.md`, source acquise `GoldbachMoebiusShortLong.lean` et rapport de l'Agent 3. Le candidat C de l'Agent 2 est l'identité finie classique de Heath–Brown, avec troncature de la vraie fonction de Möbius. L'identité et ses supports exacts sont formalisés, sans nouveauté mathématique ni contrôle du résidu terminal revendiqué.

## Filtre et environnement

Avant la première compilation, `numerical/numerical.json` annonçait PASS pour C : 18866 vérifications exactes, comprenant 8192 tests des deux faces n et N−n à N=100000000, alpha=100. Le domaine est celui déclaré dans ce reçu ; il ne s'agit pas d'un test exhaustif de tous les entiers inférieurs à N. Le seuil 101^4=104060401, où le reste est indispensable, demeure dans le rapport conceptuel de l'Agent 2 et dans le script numérique. Ce seuil n'est pas prolongé illicitement jusqu'à une assertion globale sans reste.

Compilateur : `C:/Users/Utilisateur/.elan/toolchains/leanprover--lean4---v4.15.0/bin/lean.exe`. Les huit bibliothèques mathlib du cache `q356-canonical-binding-replay/.lake/packages` sont utilisées ; l'import projet préparatoire vient de `Goldbach_Research_20260930/sprint15/agents/full_project_replayfresh`. Le Juge 5 reçoit le source final pour reconstruction des dépendances dans son répertoire frais.

## Résultats exacts

Le fichier `lean/QuarticMobius.lean` ajoute onze théorèmes. En notant M=shortMoebius(alpha), L=moebius−M et zeta l'unité de sommation de Dirichlet :

`moebius = 4 M − 6 M² zeta + 4 M³ zeta² − M⁴ zeta³ + L⁴ zeta³`.

Tous les produits et puissances de fonctions arithmétiques sont des convolutions de Dirichlet. Le reste `longQuartic(alpha)(n)` est exactement nul pour `n < (alpha+1)^4`, prouvé par deux applications du support multiplicatif au carré, puis par conservation du support sous convolution arbitraire. La spécialisation `n<N≤alpha^4` fournit l'identité finie sans reste. Dans la région `alpha<r<N`, le premier terme disparaît parce que M(r)=0.

Deux insertions pondérées sont prouvées : une somme à coefficients entiers c(r), et `weighted_boundary_identity_real` sur un ensemble fini d'indices arbitraires ι, avec c:ι→ℝ et r:ι→ℕ. Dans ce dernier énoncé, l'indice peut représenter le tuple complet de la convolution additive ; les logarithmes, modules ar, sélecteurs, caps et coprimalités peuvent tous demeurer dans le coefficient c(t). La preuve remplace seulement le facteur réel mu(r(t)) point par point. Elle ne remplace ni le module ar ni le grand argument r par le produit d'une sélection de facteurs courts.

## Journaux Lean

`logs/agent4_quartic_compile01.log` : trois erreurs techniques. Le `simp only` de la récurrence sur les coefficients avait déjà résolu le but, donc le `ring` suivant signalait « no goals to be solved ». La constante `ArithmeticFunction.sub_apply` n'existe pas dans mathlib4.15 ; le résultat ponctuel devait être obtenu par `change`. Enfin `Nat.pow_le_pow_left` attend l'exposant explicite 4. L'identité dans l'anneau et le support quartique étaient déjà compilés. Les déclarations dépendant des buts échoués imprimaient l'axiome de preuve manquante ; ce reçu d'échec n'est pas une preuve acceptée.

`logs/agent4_quartic_compile02.log` : la seule erreur restante concernait la normalisation des numéraux 4 et 6 de l'anneau des fonctions arithmétiques vers la conversion explicite d'entiers naturels. Le lemme générique de coefficients était prouvé ; `simp only` ne normalisait pas les numéraux. Des lemmes locaux h4 et h6, utilisant `simpa` sur le résultat générique, réparent cette différence de représentation. Aucun de ces échecs n'est un blocage du crible ou une impossibilité analytique.

`logs/agent4_quartic_compile03.log` : code de sortie 0, onze déclarations avec uniquement `propext`, `Classical.choice`, `Quot.sound`. Aucune erreur ou alerte. Le source n'utilise aucune preuve omise, aucune nouvelle déclaration d'axiome ni décision native. Le fichier `lean/QuarticMobius.olean` correspond à cette version.

## Portée analytique

La combinaison signée −6,+4,−1 conserve le couplage additif, tous les masques et les modules originaux. Rien dans cette formalisation ne prouve que ses trois sommes ont un signe favorable ou que leur somme gagne le facteur nécessaire pour D_N. Le passage exact à des facteurs courts n'implique pas une estimation de leur distribution dans les grands modules issus de r.

Le lemme manquant est donc toujours une borne signée de la combinaison entière sur le support original, avec paiement de la partie positive du défaut couvert e dans `D_N=−Sfull+2 max(e,0)`. La compilation est un résultat partiel vérifié, pas la condition de victoire demandée.
