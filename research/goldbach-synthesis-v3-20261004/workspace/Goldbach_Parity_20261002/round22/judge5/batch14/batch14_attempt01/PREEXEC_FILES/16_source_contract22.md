# Contrat SOURCE de la projection discrète, 3 octobre 2026

Statut : SOURCE_ONLY, non compilé, non PREPARED, aucune gate et aucune nouvelle évaluation. Auteur ROLE3. La banque numérique thermique déjà active reste le seul processus de calcul ; elle ne teste pas cette projection.

Le module autonome `DiscreteThermalProjection22.lean` contient 29 déclarations explicites (20 théorèmes, 9 définitions) et 29 commandes `#print axioms` qualifiées. Il n'importe aucune source ou olean des modules de projection en réparation. Les primitives sont la véritable exponentielle complexe de mathlib et `ArithmeticFunction.vonMangoldt`, qui conserve toutes les puissances de premiers.

Le caractère concret est

\[
\chi_{K,k}(j)=\exp\!\left(k\frac{2\pi i j}{K}\right).
\]

Pour K>0, la première identité construite dans la source est

\[
\sum_{j=0}^{K-1}\chi_{K,k}(j)
=\begin{cases}K,&K\mid k,\\0,&K\nmid k.\end{cases}
\]

La racine `exp(2*pi*I/K)` est primitive par le théorème concret de mathlib. Le test de divisibilité signé vient de `IsPrimitiveRoot.zpow_eq_one_iff_dvd`. Dans le second cas, `mul_geom_sum` et la période K annulent la somme ; aucune orthogonalité finale n'est une hypothèse. Les deux signes de k sont traités par les puissances entières.

La garde A0 est exactement `max N (2*M-N) < K`, avec la soustraction naturelle de Lean. Pour tous m,n≤M, elle donne −K<m+n−N<K dans les entiers. Un multiple de K dans cet intervalle est nul, par les signes du multiplicateur entier et K>0. La source déduit donc une seule fréquence survivante m+n=N. La garde implique K>0 même lorsque N=0.

Posons

\[
T_{a,M}(\theta)=\sum_{n=0}^{M}\Lambda(n)e^{-an}e^{in\theta},
\qquad \theta_j=2\pi j/K.
\]

Sous les seules gardes finies M≥N et A0, la cible SOURCE est

\[
\frac{e^{aN}}{K}\sum_{j=0}^{K-1}T_{a,M}(\theta_j)^2e^{-iN\theta_j}
=\sum_{n=0}^{N}\Lambda(n)\Lambda(N-n).
\]

Ici a est un réel quelconque : aucune convergence infinie n'est utilisée. Le pont explicite `heatRatio_pow` raccorde `(exp(-a))^n` à la véritable `exp(-a*n)`. Le produit des caractères, les échanges des sommes finies, l'annulation du facteur thermique et de K, puis l'égalité entre le rectangle filtré et l'antidiagonale sont chacun construits. `sampled_trueCircle_eq_coefficient` réécrit la conclusion sur les angles concrets et le vrai poids exponentiel. Les seuls poids sont les valeurs de Λ ; aucune suppression de puissances de premiers n'est introduite.

La source ne contient aucune prémisse de coefficient cible, de somme orthogonale, de majorant libre ou de précision numérique. Aucun `sorry`, `admit`, axiome ajouté, `unsafe` ou `native_decide` n'a été introduit. Les tactiques portent sur la géométrique finie, l'algèbre des caractères, les coercions et les bornes entières. Aucun crible, inversion de Möbius, décomposition de Vaughan ou reste scalaire de progression arithmétique n'est appliqué. Le fichier mathlib définissant Λ contient d'autres résultats ; ils ne sont pas utilisés ici.

Les API ont été lues en SOURCE, avec les scopes exacts dans `read_receipts22.json`. Les recherches de trois chemins initialement inexacts sont signalées comme erreurs de lecture et corrigées ; elles ne sont pas des observations Lean. L'import `Mathlib.Tactic` est explicite. La fermeture transitive des imports et les audits des 29 déclarations devront appartenir à une préparation et à une compilation futures autorisées séparément.

La dette d'élaboration demeure ouverte : aucune exécution Lean, aucun probe et aucun parseur de Lean n'ont vérifié les coercions, réécritures ou tactiques de cette source. La preuve doit être relue puis compilée par le Juge. Les erreurs effectives seront enregistrées si une compilation ultérieure est autorisée. Un éventuel PASS ne prouverait que l'orthogonalité et l'identité finie CIRCLE ; il ne certifierait ni les primitives dirigées d'un producteur, ni une quadrature numérique pratique à N=10^8, ni H1, ni la suppression des puissances de premiers, ni D_N, ni une victoire Goldbach.

La spécification numérique finale séparée reste `role3/coefficient_projection_contract_source22/coefficient_circle_contract22_revision02.md`, SHA256 `9e6d349ff283b1914750c05473d50982795a641cf6b429369504fc7b9ef73ddf`. Le présent module paie en SOURCE la dette d'orthogonalité discrète et A0/CIRCLE de cette note. Son producteur, son checker, ses rayons effectifs et ses ressources sont toujours ouverts.
