# Raccord direct Λ–Gamma : SOURCE seulement

Le présent handoff gèle uniquement `ComplexGammaMellinLambda22.lean` : 30 déclarations (24 théorèmes, 6 définitions) et 30 impressions d'axiomes en SOURCE. Le bridge distinct `ComplexGammaMellinExpTailBridge22.lean` conserve 2 théorèmes et son propre catalogue PENDING. Aucun élaborateur ni compilateur n'a été invoqué, aucun axiome observé n'est revendiqué. Ce paquet n'est ni PREPARED ni un verdict PASS.

Le module de 30 déclarations dépend de l'inversion complexe réellement PASS27, et transitivement de Local26, de l'inversion réelle20 et de Gamma02. Il n'importe ni Tail22 ni les anciens `MellinLambdaInterchange22`, `ZetaEulerLambda22` ou `ThermalArithmeticTrace22`, qui ne servent pas d'acquis à ce raccord. Le bridge séparé importe l'inversion27 et Tail22, encore **PENDING_TAIL_DEPENDENCY** : le vrai lot28 a échoué à trois raccords d'API ; sa SOURCE revision02 a été remise séparément au Juge. Le bridge ne doit pas être exécuté avant un vrai verdict sur cette dépendance et une sélection/gate distincte. Le gel de ce module Λ ne donne aucun crédit au bridge.

## Identité concrète et charges construites

Pour `Re(w)>0`, on définit, avec le cpow principal et la véritable fonction `ArithmeticFunction.vonMangoldt`,

\[
D(t)=\sum_{n\ge0}\Lambda(n)n^{-2-it},\qquad
P(w)=\sum_{n\ge0}\Lambda(n)e^{-nw}.
\]

Les termes n=0 et n=1 de Λ sont nuls ; aucune puissance première n'est retirée. La conclusion SOURCE proposée est

\[
P(w)=\frac1{2\pi}\int_\mathbb R D(t)\Gamma(2+it)w^{-2-it}\,dt.\tag{MΛ}
\]

La minoration de D_N, le compte de zéros ou une formule spectrale de ζ ne sont pas des prémisses de (MΛ). La preuve utilise seulement les conditions géométriques `Re(w)>0`, les définitions, des résultats mathlib généraux et les vrais théorèmes Gamma déjà indépendamment compilés.

1. La définition prime-power donne directement `0≤Λ(n)≤log n` pour n>0, via minFac≤n. Le module ne fait pas appel au théorème cache `vonMangoldt_le_log`, dont la preuve emploie une somme de diviseurs ; aucun crible/inversion/décomposition arithmétique n'est utilisé.
2. `log(n)≤2n^(1/2)` découle de `log(x)≤x−1` appliqué à x=n^(1/2). Donc `Λ(n)n^(-2)≤2n^(-3/2)`.
3. Le test intégral réellement écrit compare les sommes des n≥2 à `∫_1^(K+1) x^(-3/2)dx≤2`. Le terme n=1 ajoute 1. Ainsi la SOURCE démontre `Σ n^(-3/2)≤3`, puis la masse exacte `Q=Σ Λ(n)n^(-2)≤6`, sans fournir Q ou une précision finale en hypothèse.
4. La norme de chaque coefficient complexe vaut exactement `Λ(n)n^(-2)`, indépendante de t. La convergence uniforme donne D continu sur toute la droite réelle et `|D(t)|≤6`.
5. Local26 fournit L1 du vrai noyau K(w,t)=Γ(2+it)w^(-2-it). Chaque terme `Λ(n)n^(-2-it)K(w,t)` est L1 et la série de ses intégrales de normes est sommable : elle vaut Q fois l'intégrale de |K|. `integral_tsum_of_summable_integral_norm` justifie donc l'échange infini ; ni Fubini ni la sommabilité finale ne sont offerts comme hypothèses.
6. Pour n>0, `log(nw)=log(n)+log(w)` vient du vrai logarithme principal de la multiplication par un réel positif. Cela paie `(nw)^(-s)=n^(-s)w^(-s)` sans saut de branche. `Re(nw)=n Re(w)>0` permet l'inversion27 à nw. L'inversion du terme n=0 est nulle et traitée séparément. La série thermique est également démontrée absolument convergente depuis les intégrales de normes et cette inversion terme par terme.

## Majorant uniforme réellement écrit

Pour chaque w du demi-plan droit, Holo27 démontre l'existence d'une boule, sans rayon numérique calculé, dont tous les z vérifient Re(z)>0, `|z|≥|w|/2` et `|Arg(z)|≤A_w`, où

\[
\eta_w=(\pi/2+|\operatorname{Arg}w|)/2,\quad
A_w=(\eta_w+|\operatorname{Arg}w|)/2,\quad
d_w=\eta_w-A_w>0.
\]

Le nouveau module construit sur cette boule le majorant commun

\[
|D(t)K(z,t)|\le
6(|w|/2)^{-2}\sec^2(\eta_w)e^{-d_w|t|}.\tag{DOM}
\]

Son intégrabilité sur ℝ est prouvée depuis le moment exponentiel réel Holo27, en majorant l'exponentielle simple par `(2+|t|)` fois cette exponentielle. Le coefficient et le taux ne sont pas des prémisses finales libres. La preuve SOURCE est locale uniforme ; aucune uniformité jusqu'au bord Re(w)=0 n'est annoncée.

Pour un segment compact de phases w=a−iθ, a>0, |θ|≤Θ, le prolongement **PAPER**, non encore traduit dans ce module, peut rendre les constantes uniformes explicites :

\[
A=\arctan(\Theta/a),\quad \eta=(\pi/2+A)/2,\quad
d=(\pi/2-A)/2>0,\quad C_*=a^{-2}\sec^2\eta.
\]

En effet |w|≥a et |Arg(w)|≤A. La vraie rotation Gamma à ±η donne `|D(t)K(w,t)|≤6C_*exp(−d|t|)`. Une preuve Lean du transport géométrique `Arg(a−iθ)=−arctan(θ/a)` et du majorant sur ce rectangle n'est pas fournie ici ; les signatures recherchées dans `Complex/Arg` n'offrent pas directement ce raccord. La borne locale (DOM), elle, est écrite intégralement. Une couverture finie de tout compact intérieur donne aussi un majorant commun, mais cette couverture n'est pas un théorème du présent catalogue.

## Raccord Tail et prochaine queue arithmétique

Le petit second module propose exactement

\[
e^{-w}-K_H(w)=\mathrm{Tail}_H(w),\quad
|e^{-w}-K_H(w)|\le R(w,H),\qquad H\ge0,
\]

en réécrivant avec le vrai PASS27 puis les deux théorèmes **SOURCE PENDING** Tail22. Le rayon importé est `R=C(w)exp(−δ(w)H)/(πδ(w))`, `C=|w|^(-2)sec²η_w`, `δ=(π/2−|Arg(w)|)/2`. Les deux signes et le facteur 1/π sont conservés.

La prochaine conséquence **PAPER, pas encore un théorème des 30 déclarations Λ ni des 2 déclarations du bridge** est la troncature de (MΛ) elle-même : pour

\[
P_H(w)=\frac1{2\pi}\int_{-H}^{H}D(t)K(w,t)dt,
\quad |P(w)-P_H(w)|\le6R(w,H).\tag{EΛ}
\]

Elle demande de refaire pour le produit concret D·K le découpage L1 des deux demi-droites utilisé par Tail22, avec `|D|≤6`. Le rayon fermé ne peut pas être obtenu en remplaçant la norme d'une intégrale Gamma par la norme de l'intégrale pondérée : il faut effectivement intégrer `6Cexp(−δ|t|)` sur les deux queues. Sur le compact de phases ci-dessus, le rayon PAPER devient `6C_*exp(−dH)/(πd)`, continu pour a>0, Θ≥0, H≥0. Les constantes se dégradent près du bord : pour Θ/a grand, d est de l'ordre de a/(2Θ), C_* de l'ordre de 4Θ²/a⁴. Aucun coût uniforme en a→0 n'est masqué.

## Frontières conservées

L'identité D(t)=−ζ′(2+it)/ζ(2+it), la vraie formule de trace globale en phase, l'évaluation uniforme de cette trace, le signe canonique des corrélations, la correction PP, la frontière r>α, le coefficient numérique N=10^8 et D_N restent séparés. Le test numérique05 séparé n'est pas une preuve de (MΛ) et aucun de ses payloads n'est utilisé ici. Ce raccord n'affirme aucune victoire ni dépassement du mur de parité.

Les risques restants du module sont ceux d'une SOURCE non élaborée : inférence du paramètre du test intégral, normalisation des casts/exposants et applications des API d'intégrales/séries. Un futur juge doit constater les vrais résultats et les axiomes, après une gate distincte. La fermeture d'import/cache et un lanceur n'ont pas été préparés par ce handoff.

## Sources exactes et portée du livrable lisible

La fonction Λ utilisée est la vraie définition mathlib [VonMangoldt.lean](D:/Users/Utilisateur/Desktop/Maths/q356-canonical-binding-replay/.lake/packages/mathlib/Mathlib/NumberTheory/VonMangoldt.lean). Le module [ComplexGammaMellinLambda22.lean](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/complex_gamma_mellin_lambda_source01/ComplexGammaMellinLambda22.lean) écrit les preuves de la masse Q≤6, de l'intégrabilité et de (MΛ) sous les noms qualifiés `lambdaMellinMass_le_six`, `lambdaMellinProduct_integrable` et `lambdaMellinThermal_eq_integral`. Il reste SOURCE non élaborée ; ces noms ne constituent pas un verdict du compilateur.

Le résultat analytique importé est [ComplexGammaMellinHolomorphy22.lean](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/judge5/batch27/sources/ComplexGammaMellinHolomorphy22.lean), SOURCE b8b69c16cdbe1afc6e0cbccf28b4a64903d91266bb4eae68652f8ebe5640b7f2, vraie olean f831358e15e1a088988b8bc102a3f7ca23df4a32c3210cfb072273ae4abcccbf. Le [reçu indépendant27](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/judge5/batch27/batch27_attempt01/receipt.json) et l'observation ROOT27 liés dans le handoff attestent cette provenance. Local26 est également readonly ; son reçu global FAILED ne doit jamais être présenté comme un PASS global26, seule sa ligne Local22 est acquise.

Pour w=a−iθ, le domaine exact de (MΛ) est **a>0, θ réel quelconque**. Son coefficient D(t) inclut toutes les puissances premières. La garantie Γ R(w,H) concerne d'abord l'inverse Gamma **sans D(t)**. Le rayon arithmétique 6R(w,H) concerne le produit concret **avec D(t)** et reste PAPER jusqu'à la construction de ses deux queues pondérées. La continuité du rayon fermé ne prouve pas, à elle seule, l'identité spectrale ni une précision d'un producteur numérique.

Pour atteindre la cible D_N≤N/(256 log N log log N), il reste une charge globale de signe/annulation en phase appliquée à la trace canonique, avec reste certifié, puis les raccords PP et r>α déjà définis par la monographie. (MΛ), (DOM) et une future borne scalaire de queue n'apportent aucune telle annulation. On ne suppose ni cette cible, ni une condition équivalente, ni une positivité géométrique. Les acquis et le régime canonique log N≥10^24 restent fixés. Un coefficient éventuellement vérifié à N=10^8 serait un résultat fini séparé et ne fermerait pas cette charge asymptotique.
