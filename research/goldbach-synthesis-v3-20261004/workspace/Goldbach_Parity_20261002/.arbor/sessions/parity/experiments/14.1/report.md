# Boucle16 — incidence OR, union et capacité du premier manquant

**FINAL conceptuel — résultat partiel sélectionné, cible globale non démontrée.** Une tentative de payer F6 par un simple crible ou d’étendre le matching d’un seul E ne fournit pas l’information indépendante requise. La voie retenue cherche une autre capacité du même bilan : le cœur premier p0, plus petit premier impair qui ne divise pas N. Le produit singulier source donne une marge uniforme S(N)−logp0 ; elle rend ce vrai coefficient négatif au source, sans supposer l’existence d’une première incidence. Cette propriété traite une branche Λ(e) restée hors de F2–F5. Elle ne paie ni F6 ni toutes les capacités globales. Le root sélectionne A7 et son raccord A9 pour formalisation indépendante ; ce rapport est gelé avant la banque nouvelle. Score0, victoryfalse.

Périmètre de ce rôle : ce seul rapport et, si nécessaire, round16/role2. FINAL15 et les701 archives ne sont pas modifiés. PROBE_BLOCK16 et retour15 sont lus d’abord. La vue fraîche `constraints` est obtenue en lecture seule par `arbor_state.py view ... --format constraints`, Python -B -X utf8. Le rôle6 prépare uniquement des contrôles nouveaux après sélection root ; aucun ancien test, Lean, dépendance ou rendu n’est relancé.

## 1. Probe, mouvements et auto-filtrage

Q1 First principles : **mauvais crédit des coefficients et disponibilité manquante**. F15 a400 labels premiers pour360 capacités physiques ; F4 ne peut donc pas être ajouté sur tous E sans union. F15 a aussi112 principaux négatifs et41 paires réelles positives. Le résultat zéro orphelin n’est propre qu’à21 q et un seul cœur E3003. Enfin F1 conserve Λ(e) sur les cœurs premiers : leur coefficient n’est pas ±S(N) comme celui d’un cœur composite.

Q2 Hidden assumption : conserver Λ(e) signifierait que tous les cœurs premiers doivent rester nuisibles ou inclassables. En abandonnant cette supposition et en couplant e au produit singulier réel, le premier p0 absent des facteurs de N a un signe uniformément favorable. Ce choix est arithmétique, pas un coefficient libre choisi après observation des premières incidences.

Q3 Elephant : une capacité avec coefficient négatif peut être vide ; une capacité présente ne peut pas être dépensée pour plusieurs cibles. F6 et la masse après union demeurent couplées à q et aux vrais N−eq premiers. Les branches e1, cœurs premiers, rang2 et couches supérieures restent dans leurs postes.

Q4 Hamming : **oui, gain partiel dans une branche du bilan ouverte**. Le lemme S(N)>logp0 n’est ni une disponibilité supposée ni une reformulation de D_N petit. Il transforme une sous-famille de vrais semipremiers J1 à cœur premier en capacité unilatérale, avec une constante et le seuil source. Il ne résout pas la comparaison entière.

Les quatre mouvements sont appliqués. L’inversion abandonne un signe commun à tous les cœurs premiers. Le raisonnement depuis une réussite demande d’abord un coefficient de capacité réel, ensuite son incidence et une dépense unique. Le transfert analogique couple une sélection de premier au produit eulérien qui décrit exactement les premiers déjà divisant N, sans norme générique. Le retour d’échec sépare le signe source, les vrais kernels finis et la consommation de plusieurs labels.

Trois familles sont filtrées. A : développer l’OR et cribler ses compléments ; sans information de première incidence de dimension supérieure, c’est seulement un développement, non une borne de F6. B : refaire un graphe ordonné ou un flot générique sur toutes les couches ; cela organise une somme mais ne compare pas les incidences et répète le défaut non estimé14. C : couplage du premier absent avec S(N), coefficient négatif uniforme de la branche e premier ; cette relation indépendante est retenue comme gain partiel. Une éventuelle allocation du banc entier est un contrôle de dépenses, pas une nouvelle estimation revendiquée.

Mechanism: sélection du plus petit premier absent de N et raccord eulérien au vrai coefficient du cœur premier, puis consommation physique unique dans la comparaison entière.
Hypothesis: les facteurs locaux forcés avant p0 donnent S(N)−logp0≥1/144 ; le même U4 source rend C_(p0q)≤−1/288 sur les vrais points bulk à deux axes premiers, sans hypothèse d’existence ou densité de ces points, et cette capacité ne peut être réutilisée pour les autres cœurs.
Observable: preuve écrite indépendante du produit source, gardes p0≤a/Q et kernels réels ; éventuelle fenêtre entière neuve avec e1, e3, autres cœurs premiers et rang2, tous les signes et les déficits après dépense unique.
Conflicts: F4 pour un E et zéro orphelin15 ne sont pas réemployés comme estimations ; la branche Λ(e), les incidences manquantes, les modèles S(bN), le principal et tous les postes du ledger restent conservés.

## 2. Sources primaires lues et cadre fixe

La monographie primaire déjà extraite est lue sans nouvelle extraction ni rendu : `monographie.txt`, p4 équation(1), §7 Lemma7.1 p14–15, et p34. Elle définit, pour N pair positif≥2,

\[
S(N)=2C_2\prod_{\substack{\ell\mid N\\\ell>2}}
\frac{\ell-1}{\ell-2},\qquad
C_2=\prod_{\ell>2\ \mathrm{premier}}
\left(1-\frac1{(\ell-1)^2}\right).
\tag{A1}
\]

L’enclosure acquise est 2541/4096≤C2≤11011/16384. Elle n’est ni recalculée ni comptée comme nouveau lemme16. Le majorant acquis S(N)<3logu et la formule effective U4 sont conservés dans leur domaine source. Aucun nouveau résultat Mertens/Chen/BV ou une disponibilité de premiers n’est invoqué.

u=logN, ell=logu, alpha=ceil(N^(1/4)), Q=floor((N−1)/alpha), a=ceil(N^(7/16)), M=ceil(N^(3/4)). U_a contient tous les diviseurs≤a, y compris ceux≤alpha. Les kernels source réels gardent Q, k1, le front strict ak<m et les unités `(k,nN)=1`. Le raccord U1 acquis est

\[
C_m=\mu(m)^2[-\Lambda(m)-U_a(m)]+\mu(m)W_a(n,m),\quad m+n=N.
\tag{A2}
\]

Sur q>a, 2≤e≤a carré libre, unitaire et copremier à q, les diviseurs courts de eq sont Div(e) et

\[
C_{eq}=\Lambda(e)-\mu(e)W_a(N-eq,eq).
\tag{A3}
\]

Pour e1, m=q est premier et C_q=−logq−W, branche séparée. A3 est F1 corrigé acquis, pas un nouvel énoncé16. L’axe premier est theta_N(n)=1_(n premier,(n,N)=1)logn. Le raw Lambda_N(n) garde ses puissances propres, sans μ(n)^2.

## 3. Relation eulérienne indépendante : S(N)−logp0≥1/144

Définir p0 comme le plus petit premier impair ne divisant pas N. Il existe par l’infinitude des premiers et est au moins3. Tous les premiers ℓ<p0 divisent N, y compris2 puisque N est pair. Les facteurs additionnels de A1 sont≥1. Après raccord des facteurs eulériens, sans enlever la queue infinie,

\[
S(N)\ge P(p_0)T(p_0),\quad
P(p)=\prod_{\ell<p}\frac\ell{\ell-1},\quad
T(p)=\prod_{\ell\ge p}
\left(1-\frac1{(\ell-1)^2}\right).
\tag{A4}
\]

En effet, pour un premier impair ℓ<p,
`(1−1/(ℓ−1)^2)*(ℓ−1)/(ℓ−2)=ℓ/(ℓ−1)` ; le facteur2 de S(N) est celui de ℓ2 dans P. Les primes restant dans N au-delà de p ne sont pas omises avec un signe incorrect : leurs multiplicateurs sont≥1 et donnent une minoration A4.

Le développement positif du produit géométrique fini P(p) contient tous les entiers j≤p−1, dont les facteurs premiers sont<p. Ainsi P(p)≥H_(p−1)=sum_(j=1)^(p−1)1/j. La queue T est un sous-produit de la queue sur tous les entiers j≥p−1 ; chaque facteur est dans(0,1), et le produit entier télescope :

\[
T(p)\ge\prod_{j=p-1}^{\infty}(1-j^{-2})=
\frac{p-2}{p-1}.
\tag{A5}
\]

La convergence et la direction de la minoration sont celles de l’argument primaire de Lemma7.1. Un produit fini de premiers seul aurait été un majorant et ne suffirait pas.

La suite H_n−log(n+1) est croissante, car `1/(n+1)>log(1+1/(n+1))`. Son premier terme est1−log2>1/4. Donc, pour p≥3,

\[
S(N)-\log p\ge
g(p):=\frac{(p-2)/4-\log p}{p-1}.
\tag{A6}
\]

Pour t≥13, `g'(t)=(logt−3/4+1/t)/(t−1)^2>0`. Comme log13<8/3,
`g(13)>(11/4−8/3)/12=1/144`. A6 prouve donc la marge pour tout p0≥13.

Les quatre petits cas utilisent uniquement l’enclosure C2 acquise et les facteurs locaux forcés :

| p0 | Facteurs impairs forcés dans N | Minorant de S(N) | Majorant suffisant de logp0 |
|---|---|---:|---:|
| 3 | aucun | 2541/2048 | 9/8 |
| 5 | 3 | 2541/1024 | 2 |
| 7 | 3,5 | 847/256 | 2 |
| 11 | 3,5,7 | 2541/640 | 5/2 |

Les différences de ces deux colonnes dépassent1/144. Les logarithmes stricts sont des inégalités élémentaires, vérifiables par série exponentielle positive ou intervalles rationnels. On obtient, pour **tout N pair positif≥2** dans la définition source de S,

\[
\boxed{S(N)-\log p_0\ge1/144.}
\tag{A7}
\]

A7 compare un coefficient arithmétique du modèle à un premier déterminé par N. Il ne porte aucune première incidence et n’est pas une hypothèse sur F6.

## 4. Gardes et vrai signe du cœur premier au source

Au source u≥10^24, A7 et S(N)<3logu donnent logp0<3logu, donc p0<u³<a : le front original reste inchangé. L’inégalité3logu<7u/16 à cet onset puis sa monotonie rendent la dernière comparaison effective. Si q>a premier unitaire, m=p0q<N donne aussi p0 alpha<N, donc p0≤Q.

Sur les points réellement premiers `n=N−p0q>Q` et bulk m≥M, les diviseurs courts sont {1,p0}. U=−logp0, μ(m)=+1, Λ(m)=0, D_a=−logp0 et le vrai coefficient est

\[
C_{p_0q}=\log p_0+W_a(n,p_0q)
=-(S(N)-\log p_0)+\delta_{p_0q}.
\tag{A8}
\]

Le même input U4 acquis est

`epsilon_W(u)=4*10^8*u^4*exp(−sqrt(u)/60)+160*u*exp(−u/40)`.

À u0=10^24, les facteurs des deux termes sont respectivement<2^349 et<2^88, tandis que les exponentielles sont<2^(−10000). Les dérivées logarithmiques utilisées dans l’audit U4 sont négatives ensuite. Ainsi ce même epsilon_W est<1/288 sur le domaine source ; aucun nouveau prix de variation ou nouveau NG54 n’est ajouté. A7/A8 donnent

\[
\boxed{C_{p_0q}\le-1/288.}
\tag{A9}
\]

En notant R_p0 la famille physique correspondante, sa contribution vérifie

\[
B_{R_{p_0}}\le-\frac1{288}
\sum_{q\in R_{p_0}}\log(N-p_0q).
\tag{A10}
\]

Si aucune paire de premiers q,N−p0q n’existe, cette somme vaut0. A10 ne la minore pas et ne propose pas un théorème sous l’hypothèse de la cible. Les n properpowers ne satisfont pas le masque premier>Q de U4 : ils restent dans B_pp^a. Les points nonbulk ou hors Q restent au complément initial, sans nouvelle charge de front revendiquée.

## 5. OR et réutilisation : limite exacte du gain

A9 fournit une nouvelle capacité vraie de la branche e premier ; il ne rend pas l’OR de F6 petit. Le vertex (p0,q) existe dans le bilan à travers sa seule vraie incidence I_N(N−p0q). Il a une seule masse physique, quel que soit le nombre de cœurs E auxquels on le compare. Les autres cœurs premiers gardent loge−S(N), les cœurs composites gardent leur signe μ(e) et les couches non complètes gardent tous les diviseurs courts.

La tentative d’allocation générale sans nouvelle information de primes est filtrée : un flot avec un défaut exact ou une somme de capacités après union est une comptabilité correcte, pas une estimation. Un majorant de F6 par inclusion-exclusion ne sait pas si les N−eq restants sont premiers. Le simple fait que le petit e ou p0 est sous a ne fournit pas une estimation d’un produit Λ(q)Λ(N−eq) ; en fixant q et le common c, le conducteur cq peut dépasser sqrtN.

La nouvelle obligation quantitative reste soit la comparaison pondérée entière après union de tous les e/E, soit une borne de l’OR et de la réutilisation des parents. A10 permet de retirer une sous-famille non positive ou d’en garder la capacité effective ; il n’assume ni Hall ni densité ni disponibilité uniforme. Aucune égalité avec un reste libre n’est substituée à cette obligation.

## 6. Contrat nouveau proposé, séparé du résultat source

Contrat finiment falsifiable proposé : N=10^8, alpha100,a3163,Q999999,M1000000. Énumérer TOUS q premiers unitaires de1000100 à1000300 et, pour chaque q, TOUS e carrés libres unitaires

`1<=e<=min(a,floor((N−Q−1)/q))`.

Le cap vaut98 sur cette fenêtre. Tous les m=eq sont bulk, y compris e1 car q>M ; les n dépassent Q strict. Les couches réellement présentes incluent e1, p0=3, les autres cœurs premiers et les rangs2 composites. Les rangs≥3 sont vides dans ce cap (premier produit unitaire à trois facteurs distincts231>98) : cette absence finie n’est pas transférée au source. Aucun a auxiliaire n’est utilisé.

Pour tous les vertices candidats, garder les facteurs e/q/n, μ, Λ(e), Λ(m), raw Lambda_N(n), theta_N(n), tous les diviseurs courts, D/W réels sur les axes actifs et kernels littéraux sur les termes zéro. e1 est évalué par C=−logq−W, e premier par loge+W, e composé rang2 par−W. Les puissances propres n actives gardent leurs unités supplémentaires dans W ; aucun μ(n)^2 ni remplacement raw→theta.

À ce N, les facteurs de N sont2 et5. L’enclosure primaire acquise donne

`847/512<=S(N)<=11011/6144`.

Le principal, affine en S(N), reste symbolique puis reçoit des intervalles rationnels. Les coefficients principaux e1 et e3 sont négatifs ; ceux des autres cores du cap98 sont positifs. Cette classification principale ne fixe pas les signes des vrais kernels finis. Tous les vertices, y compris les positives sans aucune capacité active, demeurent dans la comparaison entière.

Question nouvelle : le nouveau signe du cœur p0 ne doit pas être promu en assez de capacité pour tout le corps J1 sélectionné. Enregistrer séparément la demande entière, chaque capacité physique e1/e3 **une fois**, l’excès après consommation unique et la somme signée réelle. Les mêmes e1/e3 ne sont pas dépensés pour plusieurs cœurs ; aucune arête artificiellement première n’est ajoutée. Une allocation scalaire est étiquetée comme comptabilité, et son signe n’est pas fixé avant le calcul.

Falsifiers : supprimer Λ(e) sur les cœurs premiers ; prendre le signe source A9 pour un signe fini hors onset ; réutiliser e3 pour toutes les cibles ; promouvoir une capacité observée au contrôle de F6 ou à toutes les couches. Une absence de contre-exemple reste finie. Toute véritable assertion ratée conserve source/snapshot/log avant correction. Aucun ancien banc n’est relancé.

La complétude des premiers est propre à cette fenêtre : tous les201 entiers q sont testés, pas une liste q≤10000. Pour factoriser n≤10^8, des premiers jusqu’à10000 suffisent ; pour tester q≤1000300, sa racine suffit. Les bornes d’énumération et de factorisation sont distinctes. Le modèle bilatéral conserve S(bN) pour b=m/l à chaque premier supprimé l, notamment b1 pour e1, et ne reçoit pas S(N) arbitrairement sur les cofacteurs longs.

## 7. Ledger et portée finale à conserver

R_p0 est un sous-ensemble de la branche J1 à cœur premier déjà présente dans B_prime^a. Son nouveau signe reclasse ces vertices ; ce n’est pas une seconde masse ajoutée au bilan. La capacité e1 de l’ancien secteur rough est également déjà dans B_prime : si un retrait antérieur −R_pair est utilisé, e1 n’est pas crédité de nouveau. Les extractions E11/E12 sont des comparaisons alternatives sur des supports qui se recoupent, pas des paiements à additionner.

P5/K2 reste sur J2bulk ENTIER avant tout retrait exact des principaux et erreurs. R_p0, avec p0<a<q, est disjoint des semipremiers rough p,q>a. Le contrôle U4 sert au signe A9 sur son support et n’est pas une deuxième charge NG54. Les priors F1/F2 gardent leurs domaines e≥2/e1 séparé et E rangpair≥4/parents composites rangimpair≥3 ; les autres couches demeurent explicitement hors de ce dernier mécanisme.

Le ledger reste `D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0)`. Originalalpha/Q, whole U_a, k1 conjoint, rawproperpowers, principal−S(N)N, modèles S(bN), b1/c1/e1, cofacteurs longs, J0/J1/J2 restants, célibataires/faces/nonbulk, terme couvert et onset BV effectif supplémentaire restent présents. N=10^8 est hors source u≥10^24. Aucun signe fini ni impossibilité de couche finie ne réfute un futur résultat limité au source.

## 8. Empreintes et obligations de formalisation

Les inputs lus sont les sources immuables suivantes ; aucune d’elles n’est recompilée ou modifiée par ce rôle :

| Input | SHA256 |
|---|---|
| monographie.txt, définition(1), Lemma7.1 et borne source | ded7e6252ed3b620537fc471d11778fe16abd1305ec4c6959fa185546a5be687 |
| round11/lean/ThreeAdicPrimePairing.lean | b3c22b714566b3d6e1fa864c4414201c9a2215c506350bdf1c8373a598d26f48 |
| round10/lean/PrimeCofactorIdentity.lean | a31895518a60c169a81cdc43201742b4f91efce6d9b032a6a07cc1a8617a4819 |
| round10/agent1_prime_signed.md, input U4 écrit | e439a43eea07380643c233ca6e48442d79e0c6cd1bdff4d67adc590797791064 |

Le vrai `GoldbachRound11.singularSeries` est défini aux lignes309–316 de la source liée par `twinConstant=∏'p, if p.Prime∧p≠2 then 1−1/(p−1)^2 else 1`, puis par le produit fini des facteurs premiers de N. A7 vise ce produit réel ; un paramètre S supposé supérieur à logp0+1/144 ne serait pas son certificat.

Les obligations de formalisation sont précisément : existence et définition du premier absent pour Npairpositif ; tous les premiers avant p0 divisant N ; raccord du front eulérien réel A4 ; comparaison de la queue T avec le produit entier télescopé A5 et convergence/non-annulation nécessaires ; produit géométrique fini contenant H_(p−1) ; minoration harmonique, monotonie de g et cas3/5/7/11 avec enclosure source réelle. Ces étapes doivent être prouvées, non remplacées par A7 posé comme hypothèse.

Le passage A7→A9 utilise ensuite les inputs analytiques acquis `S(N)<3logu` et U4 au domaine source, la garde p0≤a/Q dérivée, les deux axes vraiment premiers et le coefficient arithmétique A8. La preuve écrite donne ce passage effectif ; elle n’est pas une compilation Lean de ces inputs analytiques. Un module conditionné seulement par une erreur de kernel explicitement issue de U4 doit garder ce raccord, et un module A7 seul reste auxiliaire. Aucune hypothèse égale à F6 petit, disponibilité des partenaires ou D_N cible n’est admissible.

**Statut FINAL :** `LEAST_MISSING_PRIME_SINGULAR_MARGIN`, `WRITTEN_UNIFORM_NEGATIVE_PRIME_CORE_AT_SOURCE`, `OR_INCIDENCE_AND_GLOBAL_CAPACITY_UNESTIMATED`, `NO_NEW_LEAN_BY_ROLE2`, `SCORE_ZERO`, `VICTORY_FALSE`. Le résultat conceptuel et ses obligations sont terminés, indépendamment de la banque. Le contrat numérique ci-dessus sera exécuté uniquement après sélection root ; son reçu et ses résultats formeront une annexe distincte, sans modifier ce FINAL. Le seul paiement nouveau est le signe unilatéral de cette sous-famille existante ; aucune densité ou borne globale n’est revendiquée.
