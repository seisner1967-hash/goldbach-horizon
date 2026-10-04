# Coefficient centré et troncature Mellin–Λ — SOURCE

Ce paquet distinct contient un module, **34 déclarations (28 théorèmes, 6 définitions), 34 impressions qualifiées**. Le code est écrit et relu en SOURCE ; il n'a été ni élaboré, ni compilé, ni préparé pour exécution. Aucun résultat numérique n'entre dans ses hypothèses.

Les dépendances `ThermalProjectionIdentity22` (lot indépendant13) et son `ThermalProjectionEnvelope22` (lot11) sont réellement PASS, readonly, sans recompilation demandée. Les imports `ComplexGammaMellinLambdaTail22` (EΛ16) et `ComplexGammaCircleGeometry22` (Geometry25), ainsi que le mainΛ réparé SOURCE02 requis par EΛ, restent **prospectifs et impayés au compilateur au gel présent**. La SOURCE EΛ historique ne sera pas modifiée pour remplacer rétroactivement son statut. Le futur pipeline doit sélectionner explicitement les réparations nécessaires et leurs vrais verdicts. Tail30, Local26 et Hol27 ont des PASS indépendants ; leur existence ne valide pas les modules prospectifs.

## Objets exacts

Pour la vraie fonction de von Mangoldt de mathlib, toutes les puissances premières sont conservées :

\[
P(w)=\sum_{n\ge0}\Lambda(n)e^{-nw},\quad
D(t)=\sum_{n\ge0}\Lambda(n)n^{-2-it},\quad
K(w,t)=\Gamma(2+it)w^{-2-it},
\]
\[
P_H(w)=\frac1{2\pi}\int_{[-H,H]}D(t)K(w,t)\,dt,
\qquad w=a-i\theta.
\]

Le cpow est principal. Pour a>0, Re(w)=a>0 établit la branche admissible. La série et le noyau sont exactement ceux du mainΛ et de EΛ, sans fonction abstraite de remplacement ni intégrabilité finale offerte en prémisse.

On définit

\[
C_N=\sum_{m=0}^N\Lambda(m)\Lambda(N-m),\qquad
C_{N,H}(a)=\frac{e^{aN}}{2\pi}\int_{-\pi}^{\pi}P_H(a-i\theta)^2e^{-iN\theta}\,d\theta.
\]

Ici N est naturel quelconque ; il n'est pas nécessaire de poser N>0. H est réel, H≥0 pour l'erreur de troncature. Le coefficient de la vraie trace complète est transporté de [0,2π] à [-π,π] :

\[
C_N=\frac{e^{aN}}{2\pi}\int_{-\pi}^{\pi}P(a-i\theta)^2e^{-iN\theta}\,d\theta.\tag{CENTRE}
\]

## Transport payé par la série réelle

`lambdaCircleTerm_eq_heatTerm` identifie chaque terme Λ(n)e^{-n(a-iθ)} au terme de la trace déjà validée. Le théorème exact exp(2πik)=1 paie la période de chaque caractère entier, puis `tsum_congr` la période de P. La conjugaison de la trace en -θ est prouvée avec `tsum_star` et le vrai lemme terme à terme ; la corrélation acquise vaut donc P².

`Function.Periodic.intervalIntegral_add_eq` déplace la vraie intégrale périodique complète. L'identité de coefficient indépendante13 fournit ensuite CENTRE. Aucune périodicité de w^{-2-it}, de P_H, ni annulation de ses deux bords n'est supposée.

## Rayon uniforme construit

Les constantes géométriques prospectives25 sont

\[
d(a)=\frac12\arctan(a/\pi)>0,\qquad
C(a-i\theta)\le\frac4{a^2},\qquad
\delta(a-i\theta)\ge d(a)\quad(|\theta|\le\pi).
\]

EΛ écrit la borne réelle des deux queues pondérées D·K :

\[
|P(w)-P_H(w)|\le\frac{6C(w)e^{-\delta(w)H}}{\pi\delta(w)}.
\]

La multiplication par H≥0, la monotonie de exp, et la comparaison des divisions par πδ et πd donnent dans ce nouveau module

\[
|P(a-i\theta)-P_H(a-i\theta)|\le
\varepsilon(a,H):=\frac{24e^{-d(a)H}}{\pi a^2d(a)}
\quad(|\theta|\le\pi).\tag{UNIF}
\]

La positivité de tous les dénominateurs est construite à partir de a>0, d(a)>0 et π>0. Aucun epsilon n'est un paramètre libre. La vraie trace a la borne déjà indépendante11

\[
|P(a-i\theta)|\le U(a):=\frac{e^{-a}}{(1-e^{-a})^2}.
\]

## Intégrabilité réelle et erreur de coefficient

La continuité de P sur le cercle vient de son égalité à la vraie trace acquise. Pour P_H, le code construit **la continuité à H fixé** : une boule locale du mainΛ contient seulement des points Re(z)>0 et admet le majorant intégrable explicite

\[
6\Big[(|w|/2)^{-2}\sec^2\eta(w)\Big]e^{-\delta_{\rm loc}(w)|t|}.
\]

On le restreint au vrai volume de [-H,H]. La continuité du cpow sur le plan fendu et le théorème de continuité dominée de Bochner fournissent la continuité de l'intégrale en z. La composition θ↦a−iθ reçoit ses fonctions et point explicitement typés. Les deux intégrandes sur [-π,π] sont ensuite effectivement `IntervalIntegrable ... volume`, et non offerts comme hypothèses.

Les identités y=x−(x−y) et x²−y²=(x−y)(x+y) donnent

\[
|P_H|\le U+\varepsilon,\qquad
|P^2-P_H^2|\le2U\varepsilon+\varepsilon^2.
\]

Le vrai caractère a norme1. La soustraction des deux intégrales intégrables, leur majorant constant et la longueur2π paient exactement

\[
\boxed{|C_N-C_{N,H}(a)|\le
\mathcal E_N(a,H):=e^{aN}\bigl(2U(a)\varepsilon(a,H)+\varepsilon(a,H)^2\bigr).}\tag{COEFF}
\]

Le module écrit aussi la positivité et la continuité conjointe de ce **rayon fermé**, pour a>0 et H réel quelconque. La validité de COEFF utilise H≥0. Il ne conclut aucune continuité mobile de P_H en H, ni limite H→∞, ni évaluation effective.

## Frontières du livrable

CENTRE est raccordé à l'identité indépendante13 ; UNIF/COEFF sont ici des preuves SOURCE avec dépendances prospectives EΛ16/mainΛ02/Geometry25, sans crédit PASS. Aucun producteur spectral uniforme ni point évalué n'est fourni. Une future estimation numérique doit encore ajouter ses erreurs de troncature de D, quadrature sur t et θ, position des nœuds et arrondi ; le présent rayon paie seulement la coupure Mellin H.

Le coefficient garde les puissances premières. L'annulation signée canonique, leur retrait avec les raccords PP de la monographie, la contribution de frontière r>α et la cible D_N sont ouverts. Ni Fourier, ni ce rayon scalaire, ni un éventuel futur PASS du module ne contournent à eux seuls le mur de la parité. Aucune approche bilinéaire arithmétique, crible, Möbius/Vaughan ou estimation des restes de progressions n'est introduite.

## Lectures et risques d'élaboration

Les deux sources payées Identity13/Envelope11 ont été lues FULL f1d6df/ff8391. EΛ16 et Geometry25 ont été relues FULL2586f9. Le mainΛ02 provient de la SOURCE gelée FULLd925dd ; son enveloppe locale a été relue TARGETED702afd. Les signatures cache4.15 `intervalIntegral_add_eq`, `continuousAt_of_dominated`, `integral_sub`, `integral_congr`, `Integrable.integrableOn`, `ContinuousAt.comp` et `uIoc_of_le` ont été relues TARGETED, avec scopes et SHA dans les reçus.

Le code final a été lu intégralement en deux parties dedb45/141090. Les risques restants sont d'élaboration, notamment casts exponentiels, inférence de la mesure restreinte en DCT, et normalisation des produits de constantes. Aucune sonde ni compilation n'a testé ces raccords. Les recherches tronquées ou chemins absents ne valent jamais une lecture FULL et sont consignés séparément.
