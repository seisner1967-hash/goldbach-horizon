# EΛ : queues pondérées réelles et rayon fermé — SOURCE PENDING

Le module distinct [ComplexGammaMellinLambdaTail22.lean](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/complex_gamma_mellin_lambda_tail_source01/ComplexGammaMellinLambdaTail22.lean) contient **16 déclarations : 12 théorèmes, 4 définitions et 16 impressions qualifiées**. Il est SOURCE seulement, `PENDING_DEPENDENCIES`, sans préparation ni compilation. Lambda30 est gelé non compilé. Le vrai lot Tail29 est FAILED ; la réparation [Tail03 gelée](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/complex_gamma_mellin_tail_source03/source_handoff22.json) a été revue indépendamment en SOURCE, sans compiler verdict. Ce module attend les vrais PASS nécessaires. Les preuves écrites n'ajoutent aucune intégrabilité, égalité finale ou majorant cible comme hypothèse.

## Objets et domaine exacts

Avec la vraie Λ de mathlib, toutes les puissances premières sont conservées. Les objets du [module Lambda30 gelé](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/complex_gamma_mellin_lambda_source01/ComplexGammaMellinLambda22.lean) sont

\[
D(t)=\sum_{n\ge0}\Lambda(n)n^{-2-it},\qquad
P(w)=\sum_{n\ge0}\Lambda(n)e^{-nw},\qquad
K(w,t)=\Gamma(2+it)w^{-2-it}.
\]

Le cpow est principal ; Λ(0)=Λ(1)=0. Pour Re(w)>0, Lambda30 écrit la convergence absolue, Q=ΣΛ(n)n^{-2}≤6, la continuité de D, |D(t)|≤6, L1 de D·K et la vraie identité Mellin P(w)=(1/(2π))∫ℝD(t)K(w,t)dt. Ces résultats Lambda30 restent SOURCE et ne sont pas des acquis PASS de ce paquet.

On pose, pour H≥0,

\[
T_+(w,H)=\int_H^\infty D(t)K(w,t)dt,\qquad
T_-(w,H)=\int_H^\infty D(-t)K(w,-t)dt,
\]
\[
\mathcal T_\Lambda(w,H)=\frac{T_-(w,H)+T_+(w,H)}{2\pi},\qquad
P_H(w)=\frac1{2\pi}\int_{[-H,H]}D(t)K(w,t)dt.
\]

Le signe de D est transporté avec celui de K ; ni D(-t)=D(t), ni une positivité, ni une périodicité du cpow n'est utilisée. Le volume de Lebesgue rend les choix d'extrémités Icc/Ioc/Ioo équivalents pour ces intégrales.

## Construction des deux queues

La vraie domination Local26 est |K(w,t)|≤C(w)e^{-δ(w)|t|}, où

\[
\eta(w)=\frac{\pi/2+|\operatorname{Arg}w|}{2},\quad
\delta(w)=\frac{\pi/2-|\operatorname{Arg}w|}{2}>0,\quad
C(w)=|w|^{-2}\sec^2\eta(w).
\]

Le nouveau théorème `lambdaMellinProduct_bound` combine cette domination avec le vrai |D|≤6 de Lambda30. La continuité de D·K assure sa mesurabilité. Sur Ioi(H), H≥0 donne t>0 et |±t|=t ; le majorant concret est donc 6C(w)e^{-δ(w)t}. L'intégrabilité des deux intégrandes est construite par ce majorant Laplace, dont Tail écrit l'intégrabilité et l'évaluation réelle

\[
\int_H^\infty e^{-\delta t}dt=\frac{e^{-\delta H}}\delta.
\]

`signedLambdaMellinTail_norm_le` intègre le majorant, et non la valeur d'une intégrale Gamma non pondérée. Chaque rayon signé vaut 6C(w)e^{-δ(w)H}/δ(w). La somme des deux rayons multipliée par 1/(2π) donne exactement

\[
E_\Lambda(w,H)=6R(w,H)
=\frac{6C(w)e^{-\delta(w)H}}{\pi\delta(w)}.\tag{EΛ}
\]

Tous les dénominateurs sont payés par Re(w)>0 ⇒ δ(w)>0 et π>0. Le facteur 1/π vient des deux queues et de la normalisation 1/(2π).

## Identité et continuité écrites en SOURCE

La réflexion de Lebesgue donne T_-(w,H)=∫_{t<-H}D(t)K(w,t)dt. Pour H≥0, les deux demi-droites sont disjointes et constituent le complément de [-H,H]. `lambdaMellinProduct_integrable` est invoqué depuis la preuve concrète Lambda30, pas fourni en prémisse. `integral_add_compl` reçoit volume, le vrai produit et Icc(-H)H explicitement. Le raccord à l'identité Mellin Lambda30 donne ainsi

\[
P(w)-P_H(w)=\mathcal T_\Lambda(w,H),\qquad
|P(w)-P_H(w)|\le E_\Lambda(w,H).\tag{TRUNC}
\]

`lambdaMellinTailRadius_continuousAt` construit la continuité conjointe du rayon fermé sur **Re(w)>0, H réel quelconque** depuis la continuité de R. Il prouve aussi sa positivité et sa décroissance en H. Pour chaque centre w et seuil H≥0, une boule réelle construite par continuité donne, pour z dans cette boule et T≥H,

\[
|\mathcal T_\Lambda(z,T)|\le2E_\Lambda(w,H).
\]

Aucun rayon de boule final n'est offert comme hypothèse. Cette conclusion est une existence locale, sans calcul d'un rayon numérique. La continuité de l'intégrale complexe à seuil mobile et un théorème de limite H→∞ ne sont pas annoncés.

## Éléments mathématiques du futur contrat lisible07

**PASS indépendant déjà observé.** Local26 paie le vrai majorant Gamma et L1 ; Holomorphy27 paie e^{-w}=(1/(2π))∫ℝΓ(2+it)w^{-2-it}dt pour Re(w)>0. Leurs SOURCES, oleans, reçus et observations ROOT sont readonly. Le reçu global26 est FAILED : seule la ligne Local22 est acquise.

**SOURCE sans PASS.** Lambda30 écrit l'échange réel avec la série Λ amortie et |D|≤6. Ce nouveau module EΛ écrit les deux queues pondérées, TRUNC et le rayon continu 6R. Sa validité formelle attend les vrais verdicts sur Lambda30, Tail et ce module ; aucun enchaînement SOURCE ne remplace le Juge.

**PAPER.** Sur w=a−iθ, a>0, |θ|≤Θ, Θ≥0, les constantes compactes proposées restent
A=atan(Θ/a), η*=(π/2+A)/2, d*=(π/2−A)/2, C*=a^{-2}sec²η*. Le rayon proposé est 6C*e^{-d*H}/(πd*), continu pour a>0, Θ≥0, H≥0. Le transport géométrique Arg(a−iθ)=−atan(θ/a) et le majorant uniforme compact ne sont pas prouvés dans ce module. Quand Θ/a devient grand, d*~a/(2Θ) et C*~4Θ²/a⁴ : aucun coût près du bord n'est masqué.

**D_N encore ouvert.** Une représentation Mellin et une enveloppe d'erreur ne paient pas une annulation signée des corrélations de la trace canonique. Restent l'évaluation spectrale uniforme effective, son reste contrôlé, le nouveau mécanisme d'annulation indépendant de la cible et les raccords PP/front r>α de la monographie. La cible D_N≤N/(256 log N log log N) dans le régime fixé log N≥10^24 n'est ni une hypothèse ni une conclusion de EΛ. Le coefficient numérique à N=10^8 et la tentative checker05 sont séparés de ce paquet, sans verdict importé.

## Lectures et limites

La SOURCE Tail02 gelée a été lue FULL 8cacc3, puis Tail03 FULL029894 ; le premier DRAFT EΛ FULL e9cc43. Les signatures réelles `integral_add_compl`, `integral_Iic_eq_integral_Iio` et `integral_comp_neg_Ioi` ont été relues TARGETED 07dda2. L'appel à `ContinuousAt.comp` du nouveau module fixe aussi explicitement l'intérieur f, l'extérieur g et x=w, selon la vraie signature TARGETED378f98. Les anciens reçus de lecture Lambda30/Tail sont liés, sans prétendre à une nouvelle lecture FULL du cache. Les risques restants sont d'élaboration : réduction des fonctions composées dans la mesurabilité/réflexion, égalités de fonctions lors du découpage et simplification des définitions de rayon. Aucun probe, parser candidat, compilateur, numérique ni PREP n'a été exécuté.
