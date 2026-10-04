# MainΛ SOURCE03 — réduction explicite de la fonction nulle

Cette révision distincte répare **un seul bloc de preuve** du mainΛ30 : la branche n=0 de `lambdaMellinCoefficient_continuous`. Les 30 déclarations (24 théorèmes, 6 définitions), leurs énoncés, domaines, imports, définitions, autres preuves et 30 impressions qualifiées sont conservés. Aucun nouveau majorant, égalité finale, axiome, hypothèse L1 ou dépendance n'est ajouté. Le code reste SOURCE uniquement, sans préparation, sonde ni compilation auteur.

## Diagnostic du vrai lot33

Le log entier et le reçu de `judge5/batch33/batch33_attempt01` ont été lus FULL8f1ceb. Le compilateur a produit une seule erreur à 149:4 : la simplification de la preuve `continuous_const` fournit `Continuous (fun x => 0)` alors que le but reste `Continuous (lambdaMellinCoefficient 0)`. Les fonctions sont mathématiquement égales, mais l'ancienne simplification n'a pas exposé les arguments de la fonction partiellement appliquée dans le but.

Le module réel est FAILED : enfant START2026-10-04T02:32:38.082310UTC, FIN02:33:26.832197UTC, exit1, aucune olean. Les 30 impressions contiennent25 standards et5 récupérations `sorryAx` dans les déclarations dépendantes de cette continuité ; elles ne constituent aucun crédit de module. Le warning181:62 `unused hw` est conservé. Il n'y a ni réfutation analytique ni obstruction de parité dans ce diagnostic. Le lot33, son source dd044492… et les anciens lots31 restent immuables ; aucun rejeu n'est demandé.

## Correction proposée

Après `subst n`, la nouvelle branche construit une **égalité de fonctions** typée

\[
\texttt{lambdaMellinCoefficient 0}=(\lambda t:\mathbb R,0:\mathbb C).
\]

`funext t` expose le vrai terme `(Λ(0):ℂ)·0^{-verticalS(t)}`. Les signatures réelles du cache4.15 sont relues TARGETED072482/d2d7f9 :

- `ArithmeticFunction.map_zero {f : ArithmeticFunction R} : f 0 = 0`, namespace confirmé ;
- `vonMangoldt : ArithmeticFunction ℝ`, avec sa vraie définition directe de puissance première ;
- `Complex.ofReal_zero : ((0:ℝ):ℂ)=0` ;
- `continuous_const : Continuous (fun _ : X => y)`.

La preuve `simp only [lambdaMellinCoefficient, ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_mul]` ferme l'égalité pointwise sans devoir choisir la valeur de cpow à zéro. `rw [he]` réécrit ensuite exactement la fonction du but ; `continuous_const` porte sur cette même fonction, sans `simpa` de fonction partiellement appliquée. La branche n≠0 et toutes les autres preuves sont laissées identiques.

## Contrat mathématique inchangé

Les objets sont la vraie Λ, avec toutes les puissances premières,

\[
Q=\sum_n\Lambda(n)n^{-2}\le6,\quad
D(t)=\sum_n\Lambda(n)n^{-2-it},\quad
P(w)=\sum_n\Lambda(n)e^{-nw},\quad
K(w,t)=\Gamma(2+it)w^{-2-it}.
\]

Le domaine est Re(w)>0, t réel. Le module construit la sommabilité, |D(t)|≤6, l'intégrabilité réelle du produit D·K et de chaque terme, la domination locale, l'échange infini des intégrales et la véritable inversion

\[
P(w)=\frac1{2\pi}\int_{\mathbb R}D(t)K(w,t)\,dt.
\]

Le cpow est principal ; ses branches sont payées par le demi-plan droit et les facteurs réels strictement positifs. Aucun logarithme dérivé de ζ ou formule finale n'entre comme hypothèse. Cette révision n'importe pas Tail, EΛ, Geometry, coefficient34, bridge2 ni l'ancien MellinLambdaInterchange SOURCE.

Les quatre dépendances analytiques Γ02, réelMellin20, Local26 et Hol27 sont indépendamment PASS et readonly ; le reçu global26 est FAILED, seule sa ligne Local22 est acquise. Leurs sources, oleans et preuves de provenance liées par le handoff SOURCE02 restent les références. Aucune de ces dépendances n'est recompilée par l'auteur. Les anciens outils34 fondés sur le main33 restent bloqués et immuables ; cette révision ne leur attribue aucun PASS.

## Statut et portée

Seuls la revue SOURCE indépendante puis un nouveau véritable verdict du compilateur pourront valider cette correction. Aucun auteur olean, PREP, gate, programme candidat, numérique ou banc n'est produit. Le coefficient, son évaluation effective, les queues Λ prospectives, la géométrie prospective, les phases signées, les corrections PP/front et D_N restent leurs obligations séparées. Aucune nouvelle victoire n'est revendiquée.

Lectures : original SOURCE02 relu FULLf4a865, vrai log/reçu FULL8f1ceb ; API TARGETED072482/d2d7f9. La copie distincte et le patch littéral sont SOURCE seulement. Les reçus du nouveau dossier indiquent le FULL final et les hashes ; un contrôle textuel du seul remplacement ne vaut ni parseur Lean, ni élaboration, ni preuve du théorème.
