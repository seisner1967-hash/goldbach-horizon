# Agent 3 — boucle 4 : cœur exact de l'obstruction affine

Nouveau module : `round4\lean\AffineHHObstruction.lean`. Il importe uniquement `Mathlib.Tactic` et compile sous Lean 4.15.0, sans dépendance Goldbach précompilée. Neuf théorèmes, neuf sorties `#print axioms`, uniquement `propext`, `Classical.choice`, `Quot.sound`. Aucun avertissement, axiome ajouté ni preuve omise dans `round4\logs\agent3_compile02.log`.

Le filtre rationnel de l'Agent 6 a été reçu AVANT toute compilation : `round4\affine.json`, statut PASS. Les 12 400 configurations indépendantes du domaine de six coefficients dans {-2,-1,0,1,2} donnent les points communs exacts attendus. La preuve Lean ne dépend pas de l'exhaustivité de ce banc fini.

## Énoncé prouvé

Dans tout corps K, soient

`A(X,Y)=aX+bY+c`, `B(X,Y)=dX+eY+f`,

et R,S deux fonctions quelconques, PARTOUT définies sur K². Si

`∀ X Y, A(X,Y)*R(X,Y)+B(X,Y)*S(X,Y)=N`, avec `N≠0`,

alors `a*e−b*d=0`. Des corollaires explicites sont donnés pour les rationnels et les réels. La régularité, polynomialité ou primalité de R,S n'est pas supposée ; la force nécessaire est l'identité pour TOUS les paramètres.

Sous déterminant non nul, le théorème auxiliaire certifie le point commun

`X=(b*f−c*e)/(a*e−b*d)`, `Y=(c*d−a*f)/(a*e−b*d)`.

La vérification des deux zéros est `field_simp` puis `ring`. L'identité universelle s'y spécialise en 0=N, contradiction. Le corollaire d'impossibilité exprime que deux formes de branches opposées à gradients indépendants ne peuvent satisfaire cette identité universelle de somme non nulle avec leurs facteurs restants.

## Énoncés auxiliaires et cas dégénéré

`zero_factor_allows_two_same_branch_directions` donne les facteurs X et Y dans la MÊME branche, avec déterminant des gradients égal à un, mais multipliés par un facteur identiquement nul. La branche opposée constante vaut un : l'identité globale est valide, et il n'existe aucun point où la première branche est non nulle. Cela ne contredit pas le cœur prouvé, qui compare les gradients de branches OPPOSÉES. Cela montre qu'une conclusion sur le rang TOTAL des facteurs demanderait bien la non-dégénérescence du rapport de l'Agent 1.

`exact_mixed_product_difference` certifie la différence mixte `b*h*j` de `b*u*v+k*s*t−N`. Le tuple rationnel positif `13*3*7+7951*12577=100000000` est certifié, avec les deux produits strictement positifs. Ses quatre coins u=3/11, v=7/17 donnent la différence mixte exactement 1040. Cette valeur ne peut être retirée d'une linéarisation conservant le même niveau additif.

## Limites d'application

Le résultat formalisé est volontairement plus étroit que le lemme de rigidité complet de l'Agent 1. Il n'établit ni l'additivité du degré de produits multivariés, ni l'existence de gradients non nuls dans les deux branches, ni le rang total un en dimension supérieure. Aucune conclusion de ce genre ne doit être attribuée à ce module.

L'identité universelle n'est pas remplacée par une identité dans une boîte d'entiers ni dans une région positive. Pour illustrer cette distinction au niveau mathématique, `A=X`, `B=Y`, `R=1/X`, `S=0` donnent A·R+B·S=1 seulement sur X≠0, malgré un déterminant égal à un. Le point commun X=Y=0 est précisément hors du domaine où cette identité est vraie. La preuve Lean du cœur ne possède donc aucune extension tacite depuis une boîte. Pour des produits de formes affines, une extension par identité polynomiale devrait être démontrée séparément avec un domaine suffisant.

Un chart HH contenant un tuple strictement positif a le point non dégénéré requis pour le lemme écrit plus complet. Le nouveau certificat empêche uniquement, sous son identité globale explicite, une paire de gradients indépendants choisie dans les branches opposées. Les charts rationnels, les quotients entiers, les variétés non linéaires, les moyennes en N et les formes sur domaines restreints ne sont pas interdits par ce certificat.

Le module ne formalise aucun théorème externe de normes Gowers ou de nilsuites. Il ne démontre pas que leurs hypothèses s'identifient au support HH réel avec ses masques, ses caps et son module CRT. Il n'établit aucune estimation de Möbius, de Λ ou de D_N.

## Journal de développement

`agent3_compile01.log` conserve une erreur d'inférence des paramètres implicites c et f lors de l'appel au point commun : ces deux constantes ne figurent pas dans le déterminant, donc Lean ne pouvait les reconstruire à partir de son seul non-zéro. Correction explicite `(c := c) (f := f)`. Les diagnostics `sorryAx` de cette compilation échouée ne sont pas des axiomes ajoutés ni des preuves acceptées.

`agent3_compile02.log` compile toute la version corrigée avec code de sortie zéro et aucun avertissement. Les quatre assertions numériques du module sont démontrées par normalisation rationnelle, sans oracle natif. La source est gelée pour le rejeu indépendant du Juge.

Le gain de cette boucle est un défaut d'identification désormais certifié. La borne quantitative demandée demeure ouverte ; aucune victoire de parité n'est revendiquée.
