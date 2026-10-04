# ROLE3 — plan d’API pour le déroulement Epstein à s=3/2

Statut : inspection de sources seulement. Aucun fichier Lean de preuve, aucune compilation, aucun calcul numérique. Le rapport ROLE2 lu est encore DRAFT. Une sélection effective par root et un contrat FINAL2 figé restent nécessaires avant toute écriture de preuve.

## Périmètre réel proposé

Le premier objectif formel réalisable est l’identité géométrique auxiliaire

`∫ x in 0..1, ∑' n : ℤ, y^(3/2) * ((m*x+n)^2+(m*y)^2)^(-3/2) = 2/(m^2*sqrt y)`

pour `0 < y` et `m : ℤ`, `m ≠ 0`. Les puissances dans cet énoncé sont réelles et leurs bases sont strictement positives. L’objet de gauche est défini par le noyau et par l’intégrale, sans contenir la valeur de droite ni le coefficient de Goldbach.

Cette identité est le déroulement d’une seule ligne non nulle de la série non primitive. Elle ne certifie ni le coefficient de diffusion de la Laplacienne, ni un déterminant Fredholm, ni la formule Mellin, ni un coefficient de Goldbach, ni une borne sur D_N. Une réduction à `s=3/2` doit rester visible dans le nom des théorèmes et dans les rapports. La formule générale complexe `Re(s)>1` demeure distincte.

Dans ce plan, `Q_cut` désigne uniquement la coupure des coordonnées entières du banc ROLE6; ce n’est pas le Q de l’architecture Goldbach archivée. Le JSON de ROLE6 nomme cette coupure `Q`.

## A. Noyau réel, primitive, intégrabilité

Définir séparément, pour `a>0`,

`K_a(u) = 1 / ((u^2+a^2) * sqrt(u^2+a^2))`,

`H_a(u) = u / sqrt(u^2+a^2)`,

`P_a(u) = H_a(u) / a^2`.

Obligations :

1. `u^2+a^2>0`, donc tous les dénominateurs sont non nuls.
2. `K_a(u)=(u^2+a^2)^(-3/2)` par `Real.sqrt_eq_rpow`, `Real.rpow_add`, `Real.rpow_neg`, `Real.rpow_one`. Cette égalité doit être prouvée; choisir le noyau rationnel ne dispense pas du raccord à la série Epstein du contrat.
3. `HasDerivAt P_a (K_a u) u`. Routes exactes lues : `HasDerivAt.sqrt` sur `u^2+a^2`; dérivée du quotient; `Real.sq_sqrt` pour la simplification. Le résultat attendu est une dérivée positive, non un axiome de primitive.
4. Continuité de K_a sur ℝ, puis `Continuous.intervalIntegrable` pour chaque intervalle fini.
5. FTC : `intervalIntegral.integral_eq_sub_of_hasDerivAt` donne `∫ u in A..B, K_a u = P_a B - P_a A`, même pour les intervalles orientés.
6. Limites de P_a à `atTop` et `atBot` égales à `1/a^2` et `-1/a^2`. Les preuves peuvent factoriser par u et ramener la racine à `sqrt(1+a^2/u^2)` dans chaque demi-droite; les signes ne doivent pas être perdus.
7. Intégrabilité globale de K_a. Route disponible : dérivée non négative de P_a et limites, avec `integrableOn_Ioi_deriv_of_nonneg'`, puis réflexion pour la demi-droite négative et réunion `Iic 0 ∪ Ioi 0`. Une autre route utilise un majorant `|u|^(-3)` hors d’un compact avec `Real.integrableOn_Ioi_rpow_of_lt`. Aucune intégrabilité globale ne doit être ajoutée comme prémisse sans preuve.
8. `MeasureTheory.integral_of_hasDerivAt_of_tendsto` donne alors `∫ u, K_a u = 2/a^2`.

Sources exactes : Mathlib/Analysis/SpecialFunctions/Sqrt.lean, Pow/Real.lean; MeasureTheory/Integral/FundThmCalculus.lean; IntegralEqImproper.lean; Analysis/SpecialFunctions/ImproperIntegrals.lean.

## B. Cellules affines et fenêtre finie du banc

Pour `m≠0`, `a=|m|y`, chaque cellule est calculée avant toute somme par

`∫ x in 0..1, y^(3/2)*K_a(m*x+n)`

`= y^(3/2)/(m*a^2) * (H_a(n+m)-H_a(n))`.

La source `intervalIntegral.integral_comp_mul_add` comporte un facteur signé `m⁻¹` et l’intervalle orienté `n..n+m`. Ce théorème ne fournit pas automatiquement un facteur `|m|⁻¹`. Le code ROLE6 `finite_direct` garde précisément le facteur signé.

Pour la somme sur `n∈[-Q_cut,Q_cut]`, utiliser `intervalIntegral.integral_finset_sum` avec les preuves individuelles d’intégrabilité. Prouver l’isométrie finie `m→-m, n→-n` avant la réduction positive : la bijection conserve exactement la fenêtre symétrique et les carrés du noyau.

Pour `q=|m|>0`, `Q_cut>q`, le télescopage fini doit produire exactement

`y^(3/2)/(q*(q*y)^2) *`

`(Σ u=Q_cut+1..Q_cut+q H_(qy)(u) - Σ u=-Q_cut..-Q_cut+q-1 H_(qy)(u))`.

Le haut contient q termes, le bas contient q termes; n=±Q_cut sont inclus dans la fenêtre originelle. La preuve peut utiliser les sommes de Finset.Icc et les différences de sommes décalées, ou reindexer en Finset.range avec `sum_range_sub'` puis traiter les q cellules de bord. Les réductions d’indices et les conversions ℤ/ℕ/ℝ sont des charges effectives à vérifier par compilation.

Les six cas de grande échelle du banc n’évaluent individuellement que ces bords. Leur certificat doit donc être intitulé «télescope fini aux bords», jamais «quadrature de tous les termes». Les 18 cas originaux évaluent aussi chaque décalage et vérifient l’intersection des deux routes.

## C. Déroulement infini sans identité cible admise

Deux routes sont compatibles avec la directive. La route par periodisation utilise uniquement une translation géométrique de cellules.

Définir `S_a(v)=∑' n:ℤ, K_a(v+n)` et prouver :

1. Sommabilité pointwise et convergence uniforme sur chaque intervalle compact. Pour `|v|≤R` et `|n|≥2R`, `|v+n|≥|n|/2`, donc `K_a(v+n)≤8|n|^(-3)`. Les indices exceptionnels sont FINIS et doivent recevoir des bornes explicites. `Real.summable_abs_int_rpow` et `continuousOn_tsum` sont disponibles. Le majorant global constant en n n’est pas sommable et ne convient pas.
2. `Function.Periodic S_a 1` par reindexation `n→n+1`, avec `Equiv.tsum_eq`. Cette égalité de series doit conserver les preuves de sommabilité au moment où elles sont nécessaires pour les échanges.
3. Intégrabilité de S_a sur tous les intervalles, par la continuité locale obtenue.
4. Échange somme/intégrale sur `Ioc 0 1` avec `MeasureTheory.integral_tsum_of_summable_integral_norm`. Ce lemme requiert réellement `∀n, Integrable` et `Summable (fun n => ∫ ‖f_n‖)`. La positivité et les bornes de cellules fournissent cette charge; elle ne peut être masquée par le `tsum` totalisé de Lean.
5. `Integrable.hasSum_intervalIntegral_comp_add_int`, disponible dans IntervalIntegral.lean, découpe exactement ℝ en cellules `(n,n+1]` et identifie la somme de leurs intégrales avec `∫ ℝ K_a`.
6. `Function.Periodic.intervalIntegral_add_zsmul_eq` prouve `∫ v in 0..m, S_a v = m • ∫ v in 0..1, S_a v` pour tout entier m. Avec le changement affine signé, le m du recouvrement annule le jacobien `1/m`; la norme `|m|` apparaît dans a=|m|y. Cela prouve le bon facteur pour m négatif également.
7. Simplifier `y^(3/2) * 2/(|m|y)^2 = 2/(m^2*sqrt y)` à partir de `y>0` et m≠0.

La seconde route prouve un recouvrement de multiplicité |m| presque partout puis utilise Fubini. Elle est possible mais n’est pas nécessaire si la route de période ci-dessus compile. Aucune de ces routes n’utilise crible, Möbius, Vaughan ou restes AP.

## D. Queue fermée du banc et continuité

Pour `Q_cut>q=|m|`, `x∈[0,1]`, les coordonnées omises satisfont

`|m*x+n|≥|n|-q` et `((m*x+n)^2+(m*y)^2)^(-3/2)≤(|n|-q)^(-3)`.

Positivité + comparaison somme/intégrale donnent

`0 ≤ rowInfinite - rowFinite ≤ y^(3/2)/(Q_cut-q)^2`.

La charge scalaire ici est la queue de coordonnées d’une intégrale géométrique, pas un reste de progression arithmétique. La comparaison doit être prouvée pour les deux demi-axes entiers, à partir des sommes finies et de leur limite :

`2 * Σ_(r≥Q_cut+1-q) r^(-3) ≤ 2 * ∫_(Q_cut-q)^∞ u^(-3) du = (Q_cut-q)^(-2)`.

APIs inspectées : `AntitoneOn.sum_le_integral`, `AntitoneOn.sum_le_integral_Ico`, `Real.integral_Ioi_rpow_of_lt`, p-séries. Le passage fini→infini reste à écrire; le commentaire TODO du fichier SumIntegralComparisons ne constitue pas un théorème de queue infini déjà disponible.

L’enveloppe est continue en y>0 pour q et Q_cut fixes; les dénominateurs restent strictement positifs. Sa valeur numérique doit provenir des intervalles ROLE6, avec leur rayon construit. Pour les racines, un isqrt ne prouve que l’encadrement dyadique local qu’il a effectivement calculé. Le banc est encore non exécuté et ces intervalles ne sont pas une preuve Lean.

## E. Cusp0 et ponts toujours distincts

Un éventuel prolongement s=3/2 doit conserver le facteur1/2 de E_full, les termes m=0,n≠0 et les deux signes m. Le mode m=0 donne `ζ(3)y^(3/2)`; les lignes m≠0 donnent `2ζ(2)y^(-1/2)` après la sommation des lignes. Pour raccorder les séries à `riemannZeta`, le cache offre `zeta_nat_eq_tsum_of_gt_one` et `zeta_eq_tsum_one_div_nat_add_one_cpow`; les conversions complexes/réelles et les sommabilités sont requises.

Ce raccord ne construit pas encore la Laplacienne de Friedrichs ni son coefficient de diffusion. Les charges de résolution/normalisation, dérivée φ'/φ, queue gamma, Mellin-Poisson, chaleur et coefficient global N sont indépendantes. Le coût astronomique du contrat complet proposé par ROLE2 n’est pas payé par le banc de 24 lignes. Une compilation d’un télescope abstrait `L(w)=Σ(L(w+k)-L(w+k+1))+L(w+K)` resterait un lemme algébrique; elle ne certifierait pas l’égalité de ses termes avec la vraie diffusion.

Le seuil source `log N≥10^24`, la fenêtre finie `N=10^8`, G_N et D_N restent distincts. Statut de victoire : NON.
