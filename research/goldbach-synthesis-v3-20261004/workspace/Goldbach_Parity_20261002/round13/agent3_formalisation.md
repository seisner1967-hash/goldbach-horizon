# Rôle 3 — échange premier/semipremier réel, boucle 13

**FINAL — COMPILÉ, IDENTITÉS PARTIELLES.** Le module neuf `lean/PrimeSemiprimeSwitch.lean` contient **23 théorèmes nouveaux**, compilés par Lean **4.15.0**, sans `sorry`, `admit`, déclaration `axiom` ou `native_decide`. Chaque théorème et les douze définitions utilisées ont un audit imprimé ne contenant que `propext`, `Classical.choice`, `Quot.sound`. Aucun coefficient du crochet n'est une hypothèse libre. Le commutateur est conservé exactement. Le score de victoire reste **0**, `global_D_N=false`, `victory=false`.

## Entrées relues et périmètre

Les premiers fichiers lus sont `agent1_exchange.md`, `PROBE_BLOCK.md`, `agent6.md`, `numeric_manifest.json`. Les SHA prescrites concordent : échange idéateur `2b64a5434c1dfde766436d5abd44b62a2714615992193a3f0e21bf90554d8c54`, rôle 6 `00e234c7543fbb77d41f3f7d297c15b6bb649b6d940179509f7d916e68bb6bc0`, manifeste numérique `c8468f94a118555c842a47879772620bf9dca9d520a6b89cec54f2895a38f932`, gate échange `d120360aeebf570b9cf75ca0922070bd40e750607e77d8362a8fff636eb6352d`.

Les seules écritures sont le module neuf, `role3/**`, ce rapport et `role3_final_receipt.json`. Les dépendances nécessaires sont des copies **de sources**, intégralement identiques aux historiques protégés : round10 `ShortDivisorComplement.lean` SHA `25f38fcb6f84b73551bf9d4131745d5c234a3187dd3e92a8402f8e81b721b447`, round11 `ThreeAdicPrimePairing.lean` SHA `b3c22b714566b3d6e1fa864c4414201c9a2215c506350bdf1c8373a598d26f48`. Elles sont recompilées depuis ces sources dans `role3/dependencies`. Aucun ancien olean producteur n'a été copié ou réutilisé. Les bibliothèques mathlib et packages installées fournissent les imports standards. Les **17/19 théorèmes historiques ne sont pas recomptés**.

Le registre numérique protège 514 anciens artefacts. Aucun ancien banc PASS ou workflow de validation historique, PDF ou rendu n'a été relancé. Seule la reconstruction des deux dépendances nécessaires détaillées plus haut a compilé des sources historiques. La vérification finale recalcule les SHA protégées en lecture seule, ainsi que celles des sources originales. Il s'agit d'un contrôle de conservation, pas d'un nouveau banc historique.

## Contrat mathématique retenu

**Mechanism :** Remplacer un facteur premier (p) par les deux premiers distincts (r<s), avec (rs+2=p), pour raccorder une fibre J2 à une fibre J1 dont le préfixe court est réellement incomplet.

**Hypothesis :** Primalité et ordre (c<r<s\le a<p<q), coupes (cr,cs\le a<rs), (crs>a), unités et deux véritables premiers complémentaires ; les gardes bulk et (n_i>Q) restent celles du sous-ensemble choisi.

**Observable :** Diviseurs courts littéraux, (mu(m_0)=-1), (mu(m_1)=1), Mangoldt nul, deux vrais crochets source, déplacement (n_1-n_0=2cq), et récupération canonique des cinq facteurs depuis chaque vertex.

**Conflicts :** Aucune couverture universelle, densité de tuples, petite somme restante ou égalité (W_0=W_1) n'est supposée ; aucun crédit BV, rough, face ou NG54 nouveau n'est attribué.

## X2 et X3 : les préfixes sont des objets arithmétiques

Le module emploie directement `GoldbachRound10.ShortDivisorComplement.shortDivisorSum` et `mu`.

`short_filter_parent` démontre que les diviseurs de (m_0=cpq) au plus (a) sont exactement ({1,c}). Il utilise le retrait des deux grands premiers du filtre de diviseurs, déjà acquis, puis les véritables diviseurs d'un premier. `short_sum_parent` donne donc (U_a(m_0)=-\log c).

Pour l'image, `divisor_prime_extension` démontre l'alternative réelle d'un diviseur de (tp), avec (p) premier : il divise (t), ou vaut (ep) avec (e\mid t). `divisor_three_primes` en déduit les huit candidats pour un diviseur de (crs). `short_filter_large_prime` retire (q>a) du filtre sans modifier les autres diviseurs. `short_filter_image` impose ensuite exactement

\[
\operatorname{Div}(crsq)\cap[1,a]=\{1,c,r,s,cr,cs\}.
\]

Les coupes faibles conservent (cr=a) et (cs=a) ; les coupes strictes excluent (rs) et (crs). `short_sum_image` applique les vraies valeurs de Möbius, avec les coprimalités déduites de l'ordre des premiers, et les logarithmes multiplicatifs. Le terme (cr) ne peut être égal à (s), puisque (s) est premier et (c,r>1). Les six membres sont distincts. Le résultat est (U_a(m_1)=+\log c), sans remplacer ce préfixe incomplet par le Mangoldt de (crs).

`parent_arithmetic` et `image_arithmetic` démontrent squarefreeness, (mu(m_0)=-1), (mu(m_1)=1), et (Lambda(m_i)=0). Pour l'image, les quatre coprimalités et les quatre signes premiers sont explicitement assemblés ; son Mangoldt nul est obtenu par squarefreeness et non-primalité du produit.

## X4 et X5 : raccord exact au SOURCE bracket

Le module importe littéralement les définitions round11 `harmonicKernel`, `theta`, `sourceBracket`. Il applique `physical_short_divisor_complement_source` au vrai `physicalDivisorKernel`, à cap ((N-1)/\alpha), front strict (ak<m), masque (k\perp nN), et unités des deux premiers complémentaires.

`actual_source_coefficients` démontre, avec (W_i=\texttt{harmonicKernel}((N-1)/\alpha,a,N,n_i,m_i)),

\[
\texttt{sourceBracket}(n_0,m_0)=\log n_0(\log c-W_0),\qquad
\texttt{sourceBracket}(n_1,m_1)=\log n_1(-\log c+W_1).
\]

Ces coefficients sont **déduits** de la physique entière, des préfixes et des signes arithmétiques précédents. Ils ne sont ni deux paramètres (C_0,C_1), ni un remplacement principal du kernel.

`downward_displacement` utilise (rs+2=p) et les deux sommes (m_i+n_i=N) pour établir (m_0=m_1+2cq), (n_1=n_0+2cq), puis (n_0<n_1). `actual_source_pair` dérive directement

\[
B_{\rm pair}=-(\log c-W_0)\log(n_1/n_0)+\log n_1(W_1-W_0).
\]

`actual_admissible_switch` fixe enfin (n_i=N-m_i), conserve explicitement les unités des cinq facteurs, les deux gardes (M\le m_i\le N-2), les deux primalités/unités complémentaires et (Q<n_i). Le cap reste le quotient source. Les gardes bulk et (Q<n_i) ne sont pas requises par l'algèbre finie ; elles situent le sous-ensemble sur lequel un paiement analytique séparé peut être appliqué. Les deux kernels demeurent différents, avec (k=1) inclus dans chacun.

## Canonicalité et disjonction réellement prouvées

`prime_dvd_two/three/four` récupèrent les membres possibles d'une factorisation de deux, trois ou quatre premiers. `ordered_two/three/four_primes_unique` récupèrent le plus petit premier par deux divisibilités inverses, puis annulent le facteur non nul et procèdent sur les facteurs restants.

`parent_canonical` conclut de l'égalité des parents ordonnés (cpq=c'p'q') et des deux relations (rs+2=p) que **les cinq facteurs sont égaux**. Les deux grands facteurs sont distingués par (p<q), puis la factorisation ordonnée (r<s) de (p-2) est unique.

`image_canonical` récupère les quatre premiers ordonnés de l'image, puis (p=rs+2). Aucune prémisse d'injectivité n'est présente dans l'un ou l'autre théorème. Ils démontrent l'unicité arithmétique des applications parent et image sur le contrat. `parent_image_disjoint` compare leurs vrais signes de Möbius (-1) et (+1) pour interdire l'égalité d'un parent et d'une image, même issus de tuples différents.

Ces preuves d'unicité ne constituent pas une minoration du cardinal des tuples. Aucun théorème de densité ou existence d'un partenaire premier n'est ajouté ; le parent à complément image composite du gate numérique reste non couvert.

## Essais, audits et compte

Six compilations réelles du module sont conservées. Les essais **01, 02 et 04** ont échoué ; leurs sources exactes et leurs logs sont archivés avant correction. Les essais **03, 05 et 06** ont réussi. Le premier groupe d'erreurs portait sur la sélection d'un diviseur exclu, les non-nullités des produits, le nom de lemmes et la justification des membres distincts. L'essai 04 signalait le nom d'un lemme de diviseurs et le besoin de réécrire les égalités des facteurs avant de récupérer (p). Aucune erreur n'a été fabriquée. Les traces `sorryAx` dans les logs échoués sont celles des termes incomplets générés par Lean après erreur ; le log final et le module final n'en contiennent aucun.

Le dernier essai **06**, exit **0**, n'a ni erreur ni avertissement. Sa source SHA est **`21462365bb2fe343015161fc67639ed7bbba1234cfbbd985c90bb3d591a84da4`**. L'audit porte sur les **23 théorèmes** et les **12 définitions importées** utilisés. Toutes les listes d'axiomes imprimées sont exactement les trois axiomes standards autorisés. `role3/build_receipt.json` lie chaque snapshot, log, commande et olean frais. `role3_final_receipt.json` lie le rapport final, les inputs, ces hashes et le périmètre.

## Limite logique exacte

Ce module établit une **antisymétrie arithmétique nouvelle raccordée au crochet source réel**, avec canonicalité et direction. Il ne démontre ni X7 ni le paiement analytique X8–X18, confiés au rôle 4 séparé ; il ne certifie pas la constante (21N^{31/32}u^2). Il ne suppose pas cette borne pour prouver ses identités.

Même un paiement complet du commutateur sur ce sous-ensemble ne contrôle pas (B_{J0}+B_{J1\setminus T}+B_{J2\setminus P}). Le cardinal (K) n'est pas minoré. Le reste des célibataires, faces, nonbulk, la bande physique, la référence bilatérale et (2\max(e,0)) conservent leurs obligations. Le source (u\ge10^{24}) demeure le domaine analytique prescrit ; le banc (N=10^8) est hors de ce domaine. La cible globale (D_N\le N/(256u\log u)) reste non démontrée. **Score 0 ; victoire fausse ; recherche globale ouverte.**
