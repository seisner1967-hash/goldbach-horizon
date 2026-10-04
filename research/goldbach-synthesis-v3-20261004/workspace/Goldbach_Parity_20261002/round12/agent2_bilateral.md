# Agent 2 — boucle 12 : suppression première normalisée et moment couplé

**FINAL — direction non sélectionnée quantitativement.** La suppression d'un facteur premier donne une identité exacte du détecteur physique de B13. Elle ne donne aucune minoration indépendante de B13. Le noyau restant contient encore l'incidence première de `p` et celle de `N−cp`; une tentative de dispersion fait apparaître trois formes premières. Le secteur `c=1`, le principal de référence `−S(N)N` et le complément `c>a` restent impayés. Aucun nouveau module Lean n'est soumis pour cette identité standard. Le test de log-concavité est une réfutation locale d'une extension universelle sur les sélections physiques; il ne réfute pas une propriété éventuelle du polynôme global.

## 1. Contraintes et interrogation préalable

Le rôle 2 est repris après le gel de la boucle 11. Les contraintes ont été relues par le coordinateur après Judge11 FINAL et le contrôle strict des artefacts. Ont été lus intégralement : PROBE_BLOCK12, feedback11, agent2_bilateral_compensation11, agent3_formalisation11 et agent5_11. Le présent fichier est l'unique production écrite de ce rôle; les acquis et les 487 fichiers protégés restent figés.

Q1 — Classe de blocage : **mauvaise représentation et mauvais crédit quantitatif**. B6 développe exactement les coefficients et les deux queues sans minorer le moment signé. P1/P2 raccordent de vrais brackets mais le paiement P5 porte seulement le modèle commun. Le nouveau point `m=561`, `N−m=99999439` premier, donne `G_N(m)/S(N)=−1`. Le nouveau premier axe `8017²` a un poids raw non nul alors que son poids premier et son masque carré-libre sont nuls. Ce sont des contraintes de support et de signe distinctes.

Q2 — Hypothèse cachée à abandonner : supprimer un facteur premier conserverait l'incidence première du premier axe, son poids ou son modèle singulier. Après abandon, le noyau devient littéralement `Λ_N(N−cp)` avec son front, son masque `S(cN)` et tous les cofacteurs longs. La multiplicativité de μ ne rend pas cette incidence indépendante de c.

Q3 — Problème restant : contrôler un moment signé sur deux variables avec un premier axe réellement premier ou puissance première, puis le comparer au principal `S(N)N` et à la masse favorable déjà présente. Une identité de transfert et une petite erreur technique ne fournissent pas cette comparaison.

Q4 — Question de Hamming : **oui**. Le moment B13 et son diagonal premier portent directement la compensation exigée; le travail vise ce poste, sans payer une seconde fois les queues, les faces ou le modèle commun.

Les quatre mouvements d'idéation ont été employés. L'inversion conserve les deux incidences et le masque entier au lieu de les rendre invariants. Le raisonnement depuis une réussite exige une estimation centrée indépendante et un raccord signé du diagonal au principal. Le transfert analogique envisage un transport probabiliste sur les facteurs premiers, puis un polynôme de partition à coefficients positifs. L'analyse des échecs demande la normalisation sur `561`, la garde sur `1251` et le complément long sur `35727711`. Ces deux mécanismes sont distincts; aucun ne survit comme candidat quantitatif complet.

Mechanism: suppression d'un facteur premier avec poids logarithmique normalisé, suivie d'une dispersion sur le noyau physique de dilatation première.
Hypothesis: une représentation conservant exactement la masse peut exposer un moment centré accessible; aucune petite énergie, indépendance première ou borne de cible n'est postulée.
Observable: identité du vrai G_N, modèle local complet, puis estimation indépendante du noyau centré et paiement explicite de son diagonal et de ses compléments.
Conflicts: les transports antérieurs n'avaient pas de noyau invariant, la norme nue ne contrôlait pas le poids physique, et la positivité ponctuelle de G_N était fausse; la présente représentation garde ces défauts au lieu de les supprimer, mais ne les résout pas.

## 2. Détecteur physique et identité de suppression

On conserve `u=log N`, `ell=log u`, `a=ceil(N^(7/16))`, `alpha=ceil(N^(1/4))` et `Q=floor((N−1)/alpha)`. `Λ_N(n)` désigne le vrai von Mangoldt du premier axe, avec la garde d'unité de la source. Aucune multiplication par `μ(n)²` ne lui est ajoutée. Écrivons `S=S(N)` et

\[
G_N(m)=\mu(m)^2\Lambda(m)+S\mu(m),\qquad
\mathcal B_N=\sum_{1\le m\le N-2}\Lambda_N(N-m)G_N(m)-SN.
\tag{D1}
\]

La somme des unités peut être écrite explicitement; la garde de `Λ_N` annule le complément. Ce complément garde son rôle dans le raccord à la source et ne reçoit aucun paiement neuf dans ce rapport. Pour `m>1`, posons

\[
L_{\rm del}(m)=\sum_{p\in\operatorname{primeFactors}(m)}\mu(m/p)\log p.
\]

L'identité entière est

\[
\mu(m)\log m=-\mu(m)^2L_{\rm del}(m)\qquad(m>1).
\tag{D2}
\]

Si m est carré-libre, `m/p` est carré-libre et premier à p, donc `μ(m/p)=−μ(m)`; la somme des `log p` vaut `log m`. Si m n'est pas carré-libre, les deux côtés de D2 sont nuls à cause du coefficient entier `μ(m)²`. Il serait faux de retirer ce coefficient avant la somme. Le cas `m=1` est traité séparément par `μ(1)=1`, somme vide et `Λ(1)=0`.

Avec le quotient nul quand `log m=0`, on peut écrire pour tout `m≥1`

\[
\mu(m)=\mathbf1_{m=1}
-\frac{\mu(m)^2}{\log m}L_{\rm del}(m).
\tag{D3}
\]

Le raccord au vrai détecteur est alors

\[
G_N(m)=S\mathbf1_{m=1}
+\mu(m)^2\sum_{p\in\operatorname{primeFactors}(m)}
\log p\left[\mathbf1_{m=p}-S\frac{\mu(m/p)}{\log m}\right].
\tag{D4}
\]

Le premier terme de la somme est exactement `μ(m)²Λ(m)`: sur un carré-libre supérieur à 1, Λ n'est non nul que lorsque m est premier. Sur un non carré-libre, le coefficient entier l'annule. D4 ne prend donc pas Λ comme un coefficient libre, ne suppose aucune identité manquante et conserve le terme de parité original.

Les arêtes admissibles du changement de variables sont exactement

\[
\mathscr E_N=\{(p,c):p\text{ premier},\ c\ge1\text{ carré-libre},\ p\nmid c,
\ pc\le N-2,\ (pc,N)=1\}.
\]

Le quotient est `c=m/p` avec `pc=m`; la réciproque donne m carré-libre. Les poids `log p/log(pc)` sont positifs et leur somme sur les arêtes d'un même m vaut 1. On obtient

\[
\mathcal B_N+SN
=S\Lambda_N(N-1)
+\sum_{(p,c)\in\mathscr E_N}
\Lambda_N(N-pc)\log p
\left[\mathbf1_{c=1}-S\frac{\mu(c)}{\log(pc)}\right].
\tag{D5}
\]

Cette identité conserve exactement les fronts `N−pc≥2`, les unités, le signe, les cofacteurs longs et le premier axe raw. La variable p est un facteur premier de m, pas la variable k de la source; aucun cap arbitraire `p≤Q` ou `p≤a` ne peut lui être transféré. La scission `c≤a` et `c>a` est une partition entière. Elle ne supprime ni le préfixe bas de `U_a`, ni J0/J1, ni une face géométrique. Le terme `m=1` reste `SΛ_N(N−1)`; il est au plus `Su<3u ell` au domaine source. Cette observation ne constitue pas un second paiement de la face déjà couverte.

## 3. Modèle local complet et exceptions d'unité

Pour le morceau où p et `N−cp` sont premiers, le polynôme de crible est `x(N−cx)`. Sous `(c,N)=1`, son nombre de racines modulo un premier l est

\[
\rho_l(c,N)=
\begin{cases}1,&l\mid cN,\\2,&l\nmid cN.\end{cases}
\tag{D6}
\]

Dans le premier cas admissible, l divise exactement l'un de c et N; le polynôme ne s'annule pas identiquement. La singularité du modèle est celle de `cN`:

\[
S(cN)=S(N)\prod_{l\mid c}\frac{l-1}{l-2},
\tag{D7}
\]

pour les c unités admissibles; N est pair, donc c est impair et les dénominateurs sont non nuls. D7 identifie les facteurs locaux de la singularité acquise. Elle n'affirme aucune asymptotique pour la somme physique. Les exceptions `p|cN` restent exclues littéralement; le premier axe properpower reste dans la différence raw à estimer. Une substitution de `theta_N` à `Λ_N` serait un changement du problème.

Par exemple, les trois arêtes de `m=561` ont `c=187,51,33`. Leurs rapports de singularité sont respectivement `32/27`, `32/15` et `20/9`. Un modèle uniforme `S(N)` sur ces trois lignes manquerait des facteurs locaux réels. Omettre la garde `(c,N)=1` est également faux: pour `c=5`, `N=10^8` et `l=5`, toutes les cinq classes sont racines, au lieu d'une seule. Le nouveau banc contrôle ces racines et les rapports finis; il n'évalue pas un produit infini et ne suppose pas une densité première.

## 4. Estimateur indépendant proposé et raison précise du non-aboutissement

La quantité testable sur des blocs positifs C,P est

\[
\mathcal E_N(C,P)=
\sum_{\substack{C<c\le2C\\c\text{ carré-libre}\\(c,N)=1}}\mu(c)
\sum_{\substack{P<p\le2P\\p\text{ premier}\\p\nmid cN\\pc\le N-2}}
\frac{\log p}{\log(pc)}
\big[\Lambda_N(N-cp)-S(cN)\big].
\tag{D8}
\]

Les blocs sont disjoints lorsqu'on les emploie pour reconstruire le domaine. Le modèle garde les p effectivement premiers, le front exact et la garde `p∤cN`; on ne remplace pas leur somme par une intégrale sans erreur contrôlée. D8 est une observable définie avec des coefficients arithmétiques réels. **Aucune estimation de D8 n'est acquise ici.** La poser petite comme hypothèse serait déplacer le gain recherché dans le contrat.

Même une stratégie de second moment conserve cette difficulté. En posant

\[
h_c(p)=\mathbf1_{C<c\le2C}\mathbf1_{c\ {m sf}}
\mathbf1_{(c,N)=1}\mathbf1_{p\nmid cN}\mathbf1_{pc\le N-2}
\frac{\log p}{\log(pc)},
\]

une dispersion regroupée par p fait apparaître littéralement

\[
\sum_{\substack{P<p\le2P\\p\text{ premier}}}
\sum_{c,c'}\mu(c)\mu(c')h_c(p)h_{c'}(p)
[\Lambda_N(N-cp)-S(cN)]
[\Lambda_N(N-c'p)-S(c'N)].
\tag{D9}
\]

L'expansion comporte ses quatre termes physique–physique, physique–modèle, modèle–physique et modèle–modèle. Dans le terme physique–physique sur deux premiers axes, les trois formes sont `p`, `N−cp` et `N−c'p`. Les collisions locales se situent parmi les premiers divisant

\[
Ncc'(c-c').
\tag{D10}
\]

En dehors de ce masque, les trois racines sont distinctes. Le diagonal `c=c'` garde deux formes avec une racine répétée; il ne disparaît pas. Pour les premiers du masque, les racines fusionnées, les coefficients nuls, les exceptions d'unité et les masques singuliers doivent être calculés avant toute inversion. Le CRT donnerait un compte avec son `+1` par classe; aucun regroupement ne le transforme gratuitement en erreur signée petite. Ces faits locaux ne constituent pas une borne de variance.

L'estimation BV ordinaire acquise pour Λ dans les progressions ne contrôle pas ces deux incidences premières couplées avec μ(c), et une majoration de crible des trois formes ne donne pas l'annulation centrée de D9. Aucun petit second moment n'est déduit d'une norme nue. Cette insuffisance concerne le raccord proposé; elle n'est ni une réfutation de D8, ni une impossibilité générale de toute méthode de dispersion.

Deux défauts demeurent même si un bloc de D8 était estimé. D'abord, le modèle signé lui-même

\[
\sum_{\substack{c\ge1\\c\text{ carré-libre}\\(c,N)=1}}\mu(c)S(cN)
\sum_{\substack{p\ {m premier}\\(p,cN)=1\\pc\le N-2}}
\frac{\log p}{\log(pc)}
\tag{D11}
\]

doit être rapproché du principal de référence avec les mêmes fronts, sans effacer `−SN`. Une estimation de D8 ne fournit pas ce raccord. Ensuite, D5 contient tout le complément `c>a`; aucun contrôle signé n'est donné pour ce complément. Les deux files AP/lcm et le préfixe bas de la source sont conservés avec leurs paiements acquis, sans crédit nouveau.

Le diagonal `c=1` exige une attention particulière. Définissons avec le premier axe raw

\[
R_N^{(\Lambda)}=\sum_{\substack{p\text{ premier}\\2\le p\le N-2\\(p,N)=1}}
\Lambda_N(N-p)\log p,\qquad
L_N^{(\Lambda)}=\sum_{\substack{p\text{ premier}\\2\le p\le N-2\\(p,N)=1}}
\Lambda_N(N-p).
\]

Sa contribution à D5 est exactement `R_N^(Λ)−S L_N^(Λ)`. Sa partie premier/premier contient la vraie masse favorable; sa partie premier/properpower garde le poste déjà prévu. Remplacer cette ligne par son modèle reviendrait à estimer directement un motif de deux premiers. Aucune minoration de Goldbach ni indépendance première n'est introduite pour le payer. La séparation du diagonal n'augmente pas le crédit rough déjà présent dans K2.

## 5. Deuxième mécanisme : polynôme de parité et réfutation locale

Mechanism: polynôme de partition selon le nombre de facteurs premiers, avec les poids physiques couplés comme coefficients.
Hypothesis: une propriété de stabilité ou de log-concavité transmise aux sélections physiques pourrait relier le terme alterné à un coefficient premier favorable, sans remplacer les coefficients par un produit d'Euler.
Observable: propriété structurale vérifiée sur les mêmes sélections de m des deux côtés, puis comparaison indépendante du terme alterné et du coefficient premier pondéré.
Conflicts: les coefficients dépendent de N−m et ne sont pas multiplicatifs; la transmission universelle aux sélections est réfutée par le nouveau support {29,561}, sans conclusion sur le polynôme global.

Pour une même sélection physique finie E, définissons

\[
\mathcal P_E(z)=\sum_{m\in E}\Lambda_N(N-m)\mu(m)^2z^{\omega(m)}.
\tag{D12}
\]

Son évaluation en `−1` est le vrai moment μ sur E. Le coefficient d'ordre 1, avec le poids `log m` approprié, fournit la partie première favorable; il n'est pas permis de donner ce poids à tous les degrés. Pour `E={29,561}`, les deux `N−m` sont premiers et unités. Ainsi

\[
\mathcal P_E(z)=Az+Bz^3,\quad
A=\log99999971>0,\quad B=\log99999439>0.
\]

Le coefficient d'ordre 2 est nul, et `a_2²−a_1a_3=−AB<0`. La log-concavité sur **toute** sélection physique est donc fausse. Les racines `±i sqrt(A/B)` montrent aussi pourquoi une stabilité réelle héritée automatiquement de la multiplicativité ne serait pas disponible sur cette sélection. Le producteur numérique certifie le signe négatif par intervalles rationnels stricts. Il ne teste pas le polynôme global de tous les m et ne donne aucun théorème d'impossibilité global. Une autre propriété structurale globale demanderait une preuve nouvelle sur les coefficients couplés; aucun mécanisme de cette nature n'est établi ici.

## 6. Témoins neufs et gate final lié

Le rôle 6 a confirmé explicitement le gel du gate2 après un rejeu isolé champ pour champ et octet pour octet. Aucun ancien banc réussi n'a été relancé. Les statuts sont `PASS_NEW_NORMALIZED_DELETION_IDENTITY_ONLY` pour deletion.json, `PASS_NEW_FINITE_MATCHING_ROOT_IDENTITY_ONLY` pour le modèle fini et `ERROR_FALSIFIER` pour les extensions précisément fausses. Le rejeu commun est `PASS_NEW_ROUND12_BYTES_AND_FIELDS_REPLAY`; il contrôle aussi le banc indépendant du rôle 1 sans attribuer ses résultats au présent mécanisme.

| Nouveau point | Obligation ou extension testée | Résultat exact |
|---|---|---|
| `m=561=3·11·17`, `n=99999439` premier | D2–D5, coefficients 1 et S séparés | μ(m)=−1; suppression normalisée exacte |
| même point | poids 1 à la place de `log p/log m` | valeur −3 au lieu de −1 |
| même point | suppression du dénominateur | après multiplication par log m, erreur `log m−(log m)²<0` |
| `m=1251=3²·139`, `n=99998749` premier | garde entière `μ(m)²` | identité gardée nulle; sans garde, erreur `−log3<0` |
| `m=29`, `n=99999971` premier | vrai diagonal c=1 | `G_N(29)=log29−S`, raccord exact |
| `m=10526181=3·1061·3307` | complément long et signe J1 | toutes les arêtes ont c>a; signe μ(m)=−1 conservé |
| `m=10663289=7·13·37·3167` | complément long et signe J1 | toutes les arêtes ont c>a; signe μ(m)=+1 conservé |
| `n=64272289=8017²`, `m=35727711=3·43·419·661` | premier axe raw et complément long | Λ_N(n)=log8017, theta_N(n)=0; les quatre cofacteurs sont >a |
| `c=5`, `l=5` | omission de l'unité du modèle | cinq racines réelles contre une annoncée |
| `E={29,561}` | log-concavité sur toute sélection | signe strict `−log99999971·log99999439<0` |

Pour le properpower, les cofacteurs sont `11909237`, `830877`, `85269` et `54051`, tous supérieurs à `a=3163`. Une complétion par les seuls c courts serait fausse sur un premier axe raw admissible. Le cas `m=1` est conservé explicitement; son poids `Λ_N(99999999)` est nul à cette taille, sans être supposé nul en général.

| Artefact final du rôle 6 | SHA256 |
|---|---|
| `round12/deletion_checks.py` | `ec4e465a866c94a9a8cc6f2ce11e571f9bf34b074150f03165e5f4e4de64044c` |
| `round12/deletion.json` | `1b71dfdf22387479b468840ff38bb2546e3674182b5364d72f42305ea26086c3` |
| `round12/numerical_replay.json` | `653b4089491e6f18050394e226208dcdd287c1e16e97adf64fe0b9f0b082bcc0` |
| `round12/witnesses.json` | `bd5a575a7dbf102447f4a414c7a98e4f6810bdcd976d8ae57a10e0f2343faf48` |
| `round12/agent6.md` | `ee2383547abc96817911f7120e09246a2d36e579e940004cd8d2062688198759` |
| `round12/numeric_manifest.json` | `e6c7321c0584827e72e1850f0053018b598e35229bc818affaf1b83462198592` |
| registre des 487 artefacts antérieurs | `9a0a1010cdc4ad16eeb28b15f960f1d7dd3621bc91cc4d241a8781ccc2e543b1` |

Les domaines `N=10^8`, `alpha=100`, `a=3163`, `Q=999999` sont contrôlés. Les coefficients 1 et S sont séparés, les dénominateurs sont éliminés par multiplication exacte par `log m`, et les signes retenus ont des certificats rationnels stricts. S(N) n'est pas évalué numériquement. Les booléens `global_D_N`, `asymptotic`, `payments`, `Lean_called` et `victory` restent faux. Les gates ne testent ni le domaine source `u≥10^24`, ni le seuil BV supplémentaire, ni une borne asymptotique de D8.

## 7. Portée formelle et verdict

Un théorème Lean local utile à cette représentation aurait le contrat D4 avec les vraies fonctions de Möbius et de von Mangoldt, `primeFactors`, le quotient exact, le cas m=1, puis D5 avec les fronts et les unités. Il certifierait une conservation, pas une minoration. Le rapport ne fournit aucune estimation indépendante de D8/D9/D11, aucune propriété globale de stabilité et aucun paiement du diagonal premier ou du complément long. Le coordinateur a donc décidé de ne pas lancer une compilation standard pour remplacer la cible par cette conservation.

Ce classement intervient **avant compilation du candidat**. Il ne s'agit pas d'une erreur Lean, d'un `sorry` nécessaire ou d'une victoire refusée par le compilateur. Les faux contrats ont été rejetés mathématiquement avant toute soumission. Les sources Lean acquises en 10/11 ne sont ni recompilées ni présentées comme innovations de 12.

Le ledger reste littéral : B_prime^a, B_pp^a, P_band_ge2, Z_face_ge2, I_alpha et `2max(e,0)`. Les deux queues et leur lcm, le préfixe bas, les unités, le principal, les properpowers du premier axe, la mobilité singulière et les coins gardent leurs crédits uniques. Les dettes H2, célibataires, faces, J0/J1, le seuil effectif de la bande et e ne sont pas acquittées par le présent changement de variables.

Classification finale : `EXACT_GUARDED_NORMALIZED_PRIME_DELETION_PROBE`; `PRIME_DILATION_DISPERSION_UNESTIMATED`; `LOCAL_SELECTED_LOG_CONCAVITY_FALSIFIED`; `C1_REFERENCE_AND_LONG_COFACTOR_UNPAID`; `NO_QUANTITATIVE_CANDIDATE_SELECTED`; `VICTORY_FALSE`. Aucun nouveau théorème Lean n'est ajouté au compteur de la boucle 12 par ce rôle.
