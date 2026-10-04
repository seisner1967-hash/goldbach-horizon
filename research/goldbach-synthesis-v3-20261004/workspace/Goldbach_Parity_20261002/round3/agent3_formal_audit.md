# Agent 3 — boucle 3 : obstruction à la compensation bloc par bloc

## Verdict formel

Le module nouveau `round3\lean\MultifibreObstruction.lean` compile sous Lean 4.15.0 : 20 théorèmes, aucun avertissement, aucun but incomplet ni axiome ajouté. Le journal final est `round3\logs\agent3_compile04.log`. Chaque théorème a son `#print axioms` : seulement `propext`, `Classical.choice`, `Quot.sound` ; le théorème de support numérique n'utilise pas le choix classique. SHA256 de la source gelée : `93a5d98934c2f2349ddcc8b61e90a7fc393a03d1c100bc081f3bc92379b76902`.

Le filtre numérique de l'Agent 6 a été reçu AVANT la première compilation : `round3\multifibre.json`, statut PASS, calcul de noyaux symboliques et intervalles rationnels artanh. Le module ne suppose pas leur signe : il démontre ensuite les signes dans les réels de Lean.

## Poids et obstruction effectivement certifiés

`firstAxis(n)=Λ(n)−log n` est prouvé ≤0 pour tout entier n au moyen du théorème mathlib `vonMangoldt_le_log`. Pour les quatre premières variables, les valeurs suivantes sont prouvées :

* 99999899 = 17·5882347 : `firstAxis=−log 99999899` ;
* 99999697 = 7·41·348431 : `firstAxis=−log 99999697` ;
* 99999293 = 577·173309 : `firstAxis=−log 99999293` ;
* 99997879 : premier, donc `firstAxis=0`.

Les primalités des facteurs et de la dernière valeur sont démontrées par `norm_num`, sans `native_decide`. Les zéros de Λ aux trois sites composites sont obtenus de leurs factorisations en premiers distincts : μ non nul et absence de primalité excluent une puissance de premier. Aucun de ces zéros n'est postulé.

Les définitions littérales prennent N=100000000, α=100, Q=999999, le préfixe exact `R(m)=min(Q,floor((m−1)/α))`, les diviseurs positifs k≤R(m), et le masque harmonique `k.Coprime((N−m)*N)`. Le lemme `literal_prefix_cut_iff` prouve l'équivalence exacte de ce préfixe avec `k≤Q ∧ α*k<m` pour m>0. Il n'y a ni remplacement de face entière par une limite réelle ni gel du masque nN.

`literalDivisor` et `literalHarmonic` sont les formules D/W de la monographie réécrites au préfixe exact ; le premier conserve k|m, le second μ(k)/φ(k). L'égalité avec le nom `cappedDivisorWeight` du module acquis n'est pas ajoutée comme théorème intermodule ; les définitions affichées et le lemme de support précisent la correspondance. Les sommes concrètes elles-mêmes sont toutes prouvées dans le nouveau module.

Avec `literalKernel(m)=μ(m)(D(m)−W(N−m,m))`, les trois valeurs utiles sont certifiées sans hypothèse de noyau :

`K(101)=0`,
`K(303)=log(101)/2 >0`,
`K(707)=log(101)/3−log(7)/2+log(3)/2 >0`.

La dernière positivité suit dans Lean de `log(101²·3³/7³)>0`, dont l'argument est >1 par une comparaison exacte d'entiers. Les seules valeurs de φ nécessaires sont φ(1)=1, φ(3)=2 et φ(7)=6, démontrées par réduction du noyau. Les valeurs μ(303)=μ(707)=1 proviennent de la multiplicativité et des premiers 3,7,101. Le noyau à m=2121 est laissé dans sa définition littérale complète : le véritable poids `firstAxis(99997879)=0` annule ce site, sans supposer K(2121)=0.

Le théorème final `literalFourSiteBlock_neg` prouve strictement négative la somme des QUATRE termes réels, et pas seulement une expression log réduite munie de deux hypothèses sur K. Les quatre m sont positifs et <N, et leurs premières variables sont premières à N ; ces supports sont certifiés dans `concrete_prefix_and_unit_support`. Aucun partenaire n'est hors de la face d*m<N.

## Auxiliaires de transport et poids déplacés

L'identité réelle E5 avec les deux différences de poids croisés est démontrée par anneau. La différence des produits affines vaut exactement `N*b*(p−1)*(q−1)`. Sous positivité explicite des quatre arguments logarithmiques, les identités `logarithmic_shift_identity` et `logarithmic_curvature_pos` démontrent la courbure strictement positive. Leurs hypothèses sont conservées ; cette courbure ne supprime pas les valeurs Λ déplacées, les différences des noyaux ni les signes μ(b).

Cette combinaison établit un blocage mathématique effectif : les poids réels ne sont pas invariants sous changement de fibre, et la compensation favorable de CHAQUE bloc complet est fausse. Une positivité archimédienne partielle et une identité de transport ne changent pas ce contre-exemple.

## Historique des compilations

* `agent3_compile01.log` : 12 théorèmes compilés, quatre avertissements de tactiques superflues après deux `convert`; ces tactiques ont été retirées. Le raccord aux sommes littérales n'était pas encore présent.
* `agent3_compile02.log` : erreurs techniques lors de l'ajout du raccord. Deux égalités résiduelles `1=(-1)*(-1)` nécessitaient normalisation ; `norm_num` avait déjà réduit `3/303` à `1/101`, rendant superflue la réécriture `log(3/303)`. Ces erreurs concernent les tactiques et les formes normales, pas une déduction de signe impossible.
* `agent3_compile03.log` : 18 théorèmes compilés sans avertissement, noyaux littéraux et bloc strictement négatif certifiés.
* `agent3_compile04.log` : 20 théorèmes compilés sans avertissement, ajout du raccord exact préfixe/face et des supports unités.

Le Juge a été informé du gel et prépare un rejeu indépendant avec toutes les dépendances Goldbach compilées fraîchement depuis leurs sources. Aucun acquis n'a été modifié.

## Limite de la conclusion

Le contre-exemple appartient au scalaire direct U=V=1 avec son masque unité ; les premières variables sont 2-rugueuses dans le banc exact. Une restriction supplémentaire de secteur doit être évaluée à CHAQUE fibre ; une rugosité beaucoup plus forte de n peut supprimer certains sites et n'est pas supposée invariante. Ce certificat ne réfute ni la compensation globale entre blocs ni une estimation correctement supportée dans un secteur différent.

Le résidu D_N reste connecté à une somme agrégée et à sa charge couverte. Aucun majorant asymptotique de cette somme, des extrémités de blocs incomplets ou des corrélations Λ déplacées n'est démontré. Le résultat de la boucle est donc une falsification formelle du mécanisme local proposé, accompagnée d'identités exactes ; aucune victoire sur la cible quantitative n'est revendiquée.
