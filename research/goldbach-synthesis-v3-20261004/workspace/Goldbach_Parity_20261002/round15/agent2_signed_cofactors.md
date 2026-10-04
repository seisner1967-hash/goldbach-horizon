# Boucle15 — cofacteurs signés et fusion des petits cœurs

**FINAL — étude arithmétique et nouveau banc terminés ; couverture du complément signé non démontrée.** Le candidat retenu fusionne deux facteurs d’un petit cœur composite en un premier plus petit. Il agit dans J1 à cœur entièrement sous a, conserve les deux signes de Möbius et compte les représentations par union de vertices physiques. Une comparaison pondérée déterministe réduit son principal à des cibles sans aucun premier partenaire réel. Cette dernière incidence n’est pas estimée au source. Dans la fenêtre neuve, le principal entier et le bracket réel entier sont négatifs, tandis que41 des112 paires réelles sont positives. La généralisation des formules à c carré libre et l’absence d’orphelin observée ne sont pas présentées comme un paiement global de parité. Score0, victoryfalse.

Périmètre de ce rôle : ce seul rapport dans round15. PROBE_BLOCK15, retour définitif14 et contraintes courantes de l’arbre sont lus. Les 651 productions historiques restent immuables ; FINAL2/4_13 et FINAL2_14 ne sont pas modifiés. Aucun producteur ancien, Lean ni rendu ancien n’est relancé. Le banc15 décrit ci-dessous appartient au rôle6 après sélection root. Source et Lean acquis sont lus, sans reconstruire leurs dépendances.

## 1. Probe et sélection

Q1 First principles : **mauvais espace d’action et mauvais crédit du signe**. Le retour14 conserve une fibre c3/q3581 avec12 parents,11 images et défaut de matching5, mais C16 est indépendant de ce matching ; ses sept paires réelles ont six signes positifs et un négatif malgré leur principal formel négatif. Les cuts CRT14 portent une dette courte positive et un défaut élargi négatif. Ces deux observations interdisent de confondre degrés, signe principal et capacité réelle. Elles ne traitent pas une famille de cœurs composites entièrement sous a.

Q2 Hidden assumption : le coefficient d’un cofacteur carré libre resterait celui d’un petit premier c, et une scission descendante conserverait la même orientation favorable. En abandonnant cette hypothèse, Λ(c) s’annule pour c composé et le signe μ(c) devient essentiel. La fusion de petits facteurs et la scission d’un grand facteur sont alors deux actions distinctes.

Q3 Elephant : l’incidence première `N−eq` n’est pas monotone en e. Même lorsque tout U_a est calculé et qu’un partenaire aurait individuellement assez de poids principal, son complément peut être composite. La disponibilité simultanée de q, du complément cible et d’au moins un complément partenaire reste l’obligation indépendante.

Q4 Hamming : **oui, avec portée partielle explicite**. Le nouveau support est J1 à petit cœur complet, disjoint de J2 et des images13 dont le cœur crs dépasse a. Il fait entrer de véritables cofacteurs composites des deux signes dans le complément signé. L’ordre arithmétique des poids y supprime un problème de capacité pour une seule cible par q ; il ne supprime pas l’incidence manquante ni le reste global.

Les quatre mouvements sont employés. L’inversion remplace « scinder uniquement un grand premier » par la fusion de deux petits facteurs. Le raisonnement depuis une réussite exige une cible physique unique et une union de capacités réellement premières, plutôt qu’une égalité avec un reste libre. Le transfert analogique utilise un ordre sur les petits cœurs et un rang de factorisation, sans norme spectrale. Le retour d’échec conserve les signes μ(c), l’exception c1, les axes premiers manquants et les vertices qui n’ont aucune arête.

Deux familles sont filtrées. A : extension de l’échange13 aux c carrés libres ; sa formule parent est déjà acquise et l’identité image seule ne compare aucune incidence, donc elle est rejetée comme seule contribution quantitative. B : fusion de parité des petits cœurs, union des six cofacteurs et majorant explicite par les cibles sans partenaire réel ; elle est retenue comme mécanisme partiel falsifiable. Elle diffère du rôle1 par le support J1 complet et par la variation du petit cœur, plutôt que par une nouvelle comparaison de familles p>a avec conducteur cq.

Mechanism: fusion de parité des petits cœurs complets sous a, avec rang arithmétique et union des représentations de cofacteurs.
Hypothesis: l’annulation complète de U_a sur les cœurs composites et les signes réels μ(m) donnent des coefficients opposés ; un cœur favorable plus petit a un poids principal strictement supérieur à celui de sa cible, ce qui réduit la comparaison entière à un sélecteur explicite de premières incidences sans partenaire.
Observable: fenêtre complète neuve q8000..8200, c21 et c231 de signes opposés, branche c1, tous les diviseurs, union des six cofacteurs, degrés et multiplicités physiques, majorant du principal et signes des deux vrais W.
Conflicts: une généralisation formelle n’est pas une couverture ; aucune disponibilité, densité, Hall, positivité des paires réelles, norme ou borne cible n’est supposée ; le modèle bilatéral, le principal, tous les fronts et le ledger demeurent présents.

## 2. Raccord source et toutes les fonctions réelles

Fixer N pair, u=logN, ell=logu, alpha=ceil(N^(1/4)), a=ceil(N^(7/16)), Q=floor((N−1)/alpha), M=ceil(N^(3/4)). Le domaine d’emploi des acquis analytiques reste u≥10^24. Les identités arithmétiques demandent leurs gardes finies, notamment alpha≤a, m+n=N, n>0, `(n,N)=1` et m<N. Le N=10^8 des contrôles est hors du domaine source.

Conserver littéralement

\[
D_a(n,m)=\sum_{\substack{k\mid m,\ 1\le k\le Q\\ak<m,\ (k,nN)=1}}
\mu(k)\log(k/m),\qquad
W_a(n,m)=\sum_{\substack{1\le k\le Q\\ak<m,\ (k,nN)=1}}
\frac{\mu(k)}{\varphi(k)}\log(k/m).
\tag{S1}
\]

La coprimalité n,N rend toutes les unités des diviseurs physiques automatiques ; elle ne retire pas la condition unitaire de la somme harmonique. k1 est présent conjointement. U1 source, déjà compilé dans `round10/lean/ShortDivisorComplement.lean`, donne le vrai coefficient

\[
C_m=-\mu(m)(D_a-W_a)
=\mu(m)^2[-\Lambda(m)-U_a(m)]+\mu(m)W_a(n,m),
\quad U_a(m)=\sum_{\substack{d\mid m\\d\le a}}\mu(d)\log d.
\tag{S2}
\]

Le moins devant U_a est conservé. U_a est entier, y compris d≤alpha. `GoldbachRound11.sourceBracket` est theta_N(n)C_m, avec theta_N(n)=I_N(n)logn et I_N l’indicatrice de vrai premier unitaire. Le raw original est Lambda_N(n)=1_(n>1,(n,N)=1)Lambda(n), sans μ(n)^2 ; ses puissances propres demeurent au poste B_pp^a.

U4 source écrit W_a=−S(N)+δ_m, avec |δ_m|≤epsilon_W dans son domaine acquis. S(N)>0 est un acquis source, pas une valeur expérimentale substituée au kernel. Les erreurs δ_m des vertices distincts sont conservées une fois ; leur route U4 est alternative au coût de variation déjà acquis, sans deuxième NG54.

## 3. Extension carré libre : dérivation et signes, sans crédit de couverture

Soit c≥1 carré libre, c≤a, et p<q premiers>a, tous facteurs unitaires à N. La factorisation donne c coprime à p et q. Tout diviseur court de cpq ne contient ni p ni q et est un diviseur de c ; réciproquement tout d|c est ≤c≤a. Ainsi

\[
\operatorname{Short}(cpq)=\operatorname{Div}(c),\qquad
U_a(cpq)=-\Lambda(c),\quad
\mu(cpq)=\mu(c),\quad \Lambda(cpq)=0.
\tag{S3}
\]

S3 et son raccord source sont déjà acquis par `round11/lean/ThreeAdicPrimePairing.lean`, sans hypothèse c premier. Ils ne sont pas comptés comme résultat nouveau15.

Pour une image crsq, demander r<s≤a, q>a, `(c,rsq)=1`, cr,cs≤a<rs et crs>a. Les coupes imposent r,s>c : si r≤c, alors cs≥rs>a, contradiction ; de même pour s. Les facteurs de c sont donc séparés de r,s. Les diviseurs courts sont exactement les trois familles disjointes

\[
\{d:d\mid c\}\ \sqcup\ \{dr:d\mid c\}\ \sqcup\ \{ds:d\mid c\}.
\tag{S4}
\]

Un diviseur contenant q dépasse a. Un diviseur contenant rs dépasse a. Les trois autres types sont courts puisque cr,cs≤a. Le plus petit d=1, tous les diviseurs composites de c et les endpoints dr=a,ds=a sont inclus ; aucun quatrième type n’est omis.

Pour c≥1, la convolution μ*1 donne sum_(d|c)μ(d)=1_(c=1), et la convolution logarithmique donne sum_(d|c)μ(d)logd=−Λ(c). Ces deux identités sont déjà compilées dans `round10/lean/PrimeCofactorIdentity.lean`. En développant les trois familles S4, sans changer leur front,

\[
U_a(crsq)=\Lambda(c)-\mathbf1_{c=1}\log(rs),\qquad
\mu(crsq)=-\mu(c),\qquad \Lambda(crsq)=0.
\tag{S5}
\]

Il s’ensuit, avec les deux vrais kernels W_i et n_i=N−m_i,

\[
C_0=\Lambda(c)+\mu(c)W_0,\qquad
C_1=-\Lambda(c)+\mathbf1_{c=1}\log(rs)-\mu(c)W_1.
\tag{S6}
\]

La paire de premiers réels vaut logn0 C0+logn1 C1. Son principal U4 est

\[
P_c=(\Lambda(c)-\mu(c)S(N))(\log n_0-\log n_1)
 +\mathbf1_{c=1}\log(rs)\log n_1.
\tag{S7}
\]

L’erreur exacte est μ(c)(logn0 δ0−logn1 δ1). Pour c composé carré libre, Λ(c)=0 ; S7 devient μ(c)S(N)(logn1−logn0). Une descente rs<p est favorable au principal pour μ(c)=−1 et défavorable pour μ(c)=+1. Une montée inverse ces signes. Pour c premier, la descente13 garde son facteur logc+S(N). Pour c1, U_a(parent)=0 et U_a(image)=−logrs : l’entropie log(rs)logn1 demeure. Il serait faux d’étendre l’antisymétrie des préfixes ou le signe favorable du petit premier à tous c sans ces branches.

Si les coupes S4 échouent, la formule complète reste disponible. Poser H_c(x)=sum_(d|c,d≤floorx)μ(d) et L_c(x)=sum_(d|c,d≤floorx)μ(d)logd. Les ensembles sont vides pour floorx<1. Pour q>a et des facteurs distincts/copremiers, tous les diviseurs du petit cœur donnent

\[
U_a(crsq)=L_c(a)-L_c(a/r)-\log r\,H_c(a/r)
 -L_c(a/s)-\log s\,H_c(a/s)
 +L_c(a/(rs))+\log(rs)H_c(a/(rs)).
\tag{S8}
\]

Chaque front ≤a est entier. S8 conserve la tête, les deux faces et la dernière famille ; aucun coefficient libre W ou reste arbitraire ne remplace les diviseurs.

Dans J2, c est le produit de tous les petits facteurs et p<q sont les grands facteurs : le parent est canonique. Sous S4, r,s sont les deux plus grands petits facteurs et leur complément multiplicatif est c, donc la factorisation image retrouve ce triplet. Des déplacements multiples garderaient cependant leurs degrés. Dans la famille sous-front étudiée ensuite, ces coupes ne sont pas utilisées : la représentation par un common c n’est plus unique et doit être fusionnée physiquement.

## 4. Nouveau support : cœurs complets sous a et fusion de parité

Soit q>a premier, 2≤e≤a carré libre unitaire, `(e,q)=1`, et m=eq dans le bulk avec n=N−eq>Q premier/unitaire. Aucun diviseur contenant q ne peut être ≤a. Tous les diviseurs de e le sont. D’où

\[
\operatorname{Short}(eq)=\operatorname{Div}(e),\quad
U_a(eq)=-\Lambda(e),\quad \mu(eq)=-\mu(e),\quad \Lambda(eq)=0,
\]
\[
C_{eq}=\Lambda(e)-\mu(e)W_a(n,eq)
       =\Lambda(e)+\mu(eq)W_a(n,eq).
\tag{F1}
\]

La dernière égalité est le raccord S2, pas un changement de signe de W. La réduction à un cœur complet est aussi un acquis de l’extraction10 ; son usage arithmétique dans la fusion et l’union15 est nouveau, pas cette convolution seule.

Pour les e composites considérés, le noyau physique D_a vaut même exactement0 : ses diviseurs actifs sont Div(e), et sum_(d|e)μ(d)=sum_(d|e)μ(d)logd=0. Le cap original est automatique ici : eq<N et q>a≥alpha donnent e alpha≤N−1, donc e≤Q ; q>a assure ak<m pour tous k|e, et un k contenant q échoue au front car e≤a. Les unités physiques découlent de n+m=N et `(n,N)=1`. Les coefficients ±W sont donc les vrais brackets après extraction physique, et non deux masses D arbitrairement choisies. Pour e premier p, D_a=−logp, d’où le terme logp conservé dans F1.

Le cœur physique e1 est une autre branche, non incluse dans F1 : m=q est premier, U_a(q)=0, μ(q)=−1 et Λ(q)=logq, donc C_q=−logq−W_a(N−q,q). Cette capacité de vrai couple premier q,N−q reste dans le complément source ; elle n’est pas supposée disponible. Le contrôle numérique common c1/e131 ci-dessous conserve une branche semipremière, et ne remplace pas cette branche physique e1 ni le cofacteur bilatéral b1.

Si e est composite carré libre, Λ(e)=0. Un cœur de rang impair a μ(e)=−1, μ(eq)=+1 et C=W ; il est favorable au principal source −S(N). Un cœur de rang pair a μ(e)=+1, μ(eq)=−1 et C=−W ; il est nuisible au principal source +S(N). Pour e premier, Λ(e)=loge reste présent. Le terme c1 ne se fond donc pas dans le cas composite.

Prendre un cœur cible E carré libre de rang pair **au moins4**, E≤a. Pour chaque paire de facteurs premiers r<s de E, poser c=E/(rs). Remplacer rs par un premier p<rs, coprime à cN, et former e=cp<E. Le rang de c est pair au moins2 et celui de e est impair au moins3 : c et e sont composites et Λ(e)=0. Le parent favorable eq et la cible nuisible Eq ont chacun un seul grand facteur q, leurs courts sont deux ensembles complets distincts, et leur principal de paire est

\[
S(N)[\log(N-Eq)-\log(N-eq)]<0.
\tag{F2}
\]

Cette relation est indépendante d’une densité ou d’un matching : elle découle de e<E, des deux signes Möbius et de F1. Elle ne donne le signe de la paire réelle qu’après conservation de son erreur logn_e δ_e−logn_E δ_E. Les valeurs W_e et W_E restent distinctes.

La garde de rang ne peut pas être supprimée : pour E de rang2, c=1 et e=p est premier, C_e=logp+W_e. La paire ajoute logp logn_e au principal F2 et n’a pas le même signe garanti. Les cibles de rang2, les cœurs premiers et e1 restent donc hors de la famille F2–F5. Cette correction de domaine a été signalée par le Juge15 pendant la lecture provisoire ; aucun script ni énoncé gelé n’est modifié.

Pour un E général, les mêmes parents peuvent provenir de plusieurs couples r,s. Les vertices sont (e,q), jamais les labels (c,p,q). Puisque e≤a<q et q est premier, sa factorisation retrouve l’unique grand facteur q ; deux q différents ne donnent pas le même vertex. Le cœur e est ensuite déterminé. La cible (E,q) est unique, tandis que ses labels de fusion restent des arêtes distinctes. Un graphe couvrant plusieurs E peut réutiliser un parent ; aucune capacité globale injective n’en est déduite.

## 5. Relation entière indépendante et obligation encore ouverte

Fixer E de rang pair au moins4 et une union arithmétique finie U_E de cœurs favorables composites e<E, de rang impair au moins3, construits par la fusion. Garder un domaine fini de q premiers sur lequel tous les couples sélectionnés respectent les gardes bulk/unit/Q. Pour chaque q définir I_e=I_N(N−eq), I_E=I_N(N−Eq), et D(q)=sum_(e∈U_E) I_e ; ces incidences sont réelles, pas des densités. Une incidence hors des gardes sélectionnées laisse sa contribution au complément initial, sans modifier I_N.

Le principal entier de cette famille, incluant les parents favorables même lorsque I_E=0, est S(N)Δ avec

\[
\Delta=\sum_q\left[I_E\log(N-Eq)
 -\sum_{e\in U_E}I_e\log(N-eq)\right].
\tag{F3}
\]

Les parents non utilisés et les cibles sans parent restent dans F3. Le matching choisi ne modifie pas cette somme. L’ordre e<E donne pour chaque q le **majorant déterministe**

\[
I_E\log(N-Eq)-\sum_{e\in U_E}I_e\log(N-eq)
\le I_E\log(N-Eq)\,\mathbf1_{D(q)=0}.
\tag{F4}
\]

Preuve : si I_E=0, le membre gauche est ≤0. Si I_E=1 et D(q)=0, c’est une égalité. Si I_E=1 et D(q)≥1, un seul parent possède déjà log(N−eq)>log(N−Eq), et les autres poids sont soustraits. Aucune positivité d’un kernel réel ni hypothèse de capacité n’est utilisée. Pour cette unique cible par q, le poids principal ne demande donc pas un Hall pondéré ; **l’absence de voisins réels reste décisive**.

Le bracket entier réel de ce support est exactement

\[
B_E=S(N)\Delta
 +\sum_{q,e\in U_E} I_e\log(N-eq)\delta_e
 -\sum_q I_E\log(N-Eq)\delta_E.
\tag{F5}
\]

F4 est une inégalité nouvelle sur une sélection et un sélecteur complètement définis ; F5 seule serait une identité sans estimation. Le problème restant est précisément de majorer la masse

\[
\mathcal O_E=\sum_q I_E\log(N-Eq)
 \prod_{e\in U_E}(1-I_e),
\tag{F6}
\]

puis de traiter l’union de tous les cœurs et les supports non sélectionnés. F6 n’est pas postulée petite dans un théorème : son caractère premier dépend de q et de N−eq sur plusieurs conducteurs, avec primalité de q conservée. Le fait qu’e≤a n’est pas à lui seul une estimation BV d’un produit de deux premières incidences. Au-delà d’un seul E, la réutilisation d’un cœur favorable demande aussi une capacité après union, et F4 ne permet pas de compter le même vertex plusieurs fois.

Les deux lectures du conducteur ne résolvent pas cette obligation. En fixant e et en sommant sur q, le module e est petit, mais le poids q premier garde une corrélation binaire Λ(q)Λ(N−eq). En fixant q et c dans e=cp, le conducteur cq de N−cqp peut dépasser sqrtN ; on ne le remplace pas par c ou par e. Les moyennes AP acquises sur Λ seule ne majorent pas le produit OR de F6.

L’estimation quantitative globale absente est donc une information sur cette incidence OR couplée et sur les fibres restantes, plutôt qu’un coût local de variation supplémentaire. Les relations F2/F4 n’établissent ni existence d’un partenaire ni densité, et ne contournent pas la parité.

## 6. Faisabilité finie et information de rang

Au N=10^8 avec alpha100,a3163,Q999999,M1000000, tout cpq de J2 avec p,q>a et n>Q satisfait c≤floor((N−Q−1)/(a+1)^2)=9. Les seuls c carrés libres unitaires à N entre1 et9 sont1,3,7. Le premier composite carré libre unitaire serait21. Il n’y a donc **aucun parent J2 à c composite** à tester physiquement dans ce banc original. On ne change pas a pour créer un témoin et on ne transfère pas une identité hors secteur à un paiement J2.

En J1, une scission à partir d’un c à trois facteurs premiers distincts produirait cinq petits facteurs unitaires distincts, plus le grand q>a. Leur produit est au moins

\[
3\cdot7\cdot11\cdot13\cdot17\,(a+1)
=51051\cdot3164=161525364>N.
\tag{R1}
\]

R1 est une obstruction entière de rang, indépendante des déplacements CRT14 et de la première incidence. Elle interdit ces images de rang6 à ce N, pour toute valeur de déplacement, lorsque squarefreeness et unités sont conservées. Elle n’interdit pas une fusion inverse vers un cœur de rang3. La borne finit par perdre cet effet quand N/a grandit ; elle ne donne aucun no-go au source u≥10^24.

À ce même front a3163, E3003 est aussi l’unique cœur carré libre unitaire de rang au moins4 sous a. Les quatre premiers facteurs unitaires possibles sont3,7,11,13. Si la liste des quatre premiers facteurs diffère, le plus petit autre produit est3·7·11·17=3927>a ; un cinquième facteur donnerait au moins51051>a. Cette portée finie supplémentaire concerne les rangs≥4 seulement. Les nombreux cœurs de rang2, les cœurs premiers et e1 restent dans les branches non traitées. Au source, les couches de rang supérieur et la réutilisation de leurs partenaires réapparaissent.

## 7. Contrat numérique15 sélectionné et falsifiable

Le root accepte une **fenêtre complète déclarée**, non l’ensemble de tous q : TOUS q premiers unitaires de8000 à8200, au N=10^8 et avec les paramètres originaux. Le rôle6 a reçu le contrat FINAL avant lancement. Aucun signe ni disponibilité n’est fixé à l’avance.

Trois contrôles arithmétiques, pour chaque q de cette fenêtre :

| Cœur | Factorisation | Représentation contrôlée | μ(c) | μ(m) | Courts | U_a | C réel |
|---|---|---|---:|---:|---|---|---|
| 2751 | 3·7·131 | c21,p131 | +1 | +1 | Div(2751),8 éléments | 0 | W_2751 |
| 3003 | 3·7·11·13 | c231,p13 canonique | −1 | −1 | Div(3003),16 éléments | 0 | −W_3003 |
| 131 | premier | c1,p131 | +1 | +1 | {1,131} | −log131 | log131+W_131 |

Les deux premières lignes ne remplacent pas leurs diviseurs par une constante : les8/16 termes μ(d)logd sont explicitement développés et comparés au noyau physique D_a. Tous les m sont squarefree, unitaires, bulk ; les n dépassent Q, leur primalité n’est pas supposée. Lambda(m)=0 est déduite de leur factorisation composite squarefree. Le contrôle c1 appartient à une branche disjointe et conserve Λ(131).

Les gardes de l’union sont communes : son cœur minimum est231 et son maximum est<3003, donc m≥231·8000=1848000>M et n≥N−3003·8200=75375400>Q. Le contrôle c1/e131 vérifie séparément m≥1048000>M. Les facteurs sont unitaires à N et q dépasse tous les petits facteurs. Cette vérification n’est pas un filtre de primalité : les I_N et les rawLambda gardent leurs définitions originales.

Le graphe complet de fusion cible E3003 utilise les six labels c=21,33,39,77,91,143, avec t=3003/c. Pour chacun, TOUS p<t premiers, `(p,cN)=1`, donnent e=cp. Fusionner tous les e égaux AVANT la première incidence et AVANT de sommer une capacité. Puis garder pour chaque q les vrais parents premiers/unitaires/bulk, et toutes les cibles réellement premières. Une arête physique existe seulement si les deux premiers complémentaires existent. Si la cible est composite, ses parents premiers demeurent dans F3/F5. Si un parent est absent, sa cible conserve D(q)=0 lorsque aucun autre e n’est présent.

Exemple de multiplicité : e231 a les trois labels (21,11),(33,7),(77,3). Le vertex 231q n’est compté qu’une fois ; le vertex 3003q reste une seule cible malgré tous ses labels entrants. Le grand q>a est unique dans chaque factorisation. Les factorisations et degrés sont gardés, même si une incidence première annule une arête.

Pour TOUS q/cœurs du domaine, enregistrer n, factorisation/primalité, raw Lambda_N(n), theta_N(n) et flags d’éligibilité séparés. Un nonpremier ayant rawLambda non nul doit garder son poste properpower, sans μ(n)^2. Les D/W réels sont évalués pour les trois contrôles et tous les vertices premiers ou properpowers actifs. Lorsque theta=raw=0, le terme réel est exactement zéro et la formule littérale du kernel peut rester non évaluée ; aucun W libre ne reçoit un signe. Les kernels actifs gardent `(k,nN)=1`, Q, le front ak<m, k1 et les logarithmes exacts. Le masque se réduit à N seulement lorsque n est réellement premier>Q.

Calculer : union de cœurs et labels, ensemble q complet, incidences et cibles orphelines, degrés physiques, multiplicité maximale et canonicalités, Δ(q), majorant F4, sommes de vrais brackets F5 et signes stricts rationnels. Si aucune cible orpheline n’existe dans la fenêtre, ce n’est pas une disponibilité universelle ; si une existe, son vrai terme reste positif ou négatif suivant son W calculé, sans signe imposé depuis le source. Les cas où le signe principal et le signe réel diffèrent sont des falsifiers de leur identification, pas une réfutation de U4 au source.

Le calcul doit aussi vérifier R1, l’absence de c composite dans J2 à ce N, la branche c1 et l’annulation de tous les préfixes composites complets. Une promotion « c composite garde le coefficient logc−W », « tous les μ(c) sont nuisibles », « toute paire fusion réelle est négative », « labels = capacité », « toute cible a un premier voisin » est testable et ne doit jamais être introduite comme garde d’entrée. Conserver source/log de tout véritable échec avant correctif ; ne pas fabriquer un diagnostic Lean.

### Reçus du nouveau banc terminé

Le gate `PASS_NEW_COMPLETE_SMALL_CORE_FUSION_UNION_AND_PRINCIPAL_MAJORANT_ONLY` conserve les21 q premiers de la fenêtre entière. Les86 labels de cofacteurs donnent78 cœurs parents physiques distincts, puis1680 vertices candidats sur ces78 cœurs, la cible E et le contrôle e131. Les D/W sont évalués dans416 profils ;1264 autres vertices gardent un terme theta/raw exactement nul avec kernel littéral non évalué. Le raw est lu sur tous les candidats, avec zéro properpower présent dans cette fenêtre ; cette absence finie ne remplace pas le raw global par theta.

Il y a360 parents réellement premiers au complément,7 cibles réellement premières et112 arêtes physiques. Les248 parents premiers dont la cible est composite restent dans la somme entière. Aucune des7 cibles n’est orpheline dans la fenêtre ; le statut de disponibilité est `NO_COUNTEREXAMPLE_IN_WINDOW`, sans promotion au source ni à tous q. Les incidences des labels auraient donné400 parents premiers au lieu des360 vertices, avec multiplicité maximale3 ; le faux crédit par représentation est donc réfuté.

Les certificats rationnels stricts à96 bits donnent Δ NEGATIVE, le bracket entier B_E NEGATIVE et le gap F4 `(orphan−Delta)` POSITIVE. Les112 principaux de paires sont tous NEGATIVE ; les112 paires réelles ont71 signes NEGATIVE et41 POSITIVE. Un témoin nouveau est e429,q8017 : m_parent3439293,n_parent96560707 ; m_cible24075051,n_cible75924949. Les deux compléments sont premiers et la paire réelle est strictement positive malgré son principal strictement négatif. La somme entière après union demeure négative. Aucun coefficient δ ni W n’est amputé pour concilier ces deux résultats.

Les trois falsifications précises du gate sont : capacité comptée par labels, identification des signes principaux aux signes réels de toutes les paires, et existence finie d’une scission à six facteurs distincts unitaires sous N avec q>a. La disponibilité de chaque cible n’a pas de contre-exemple dans cette fenêtre ; elle n’est pas classée comme prouvée universellement. Les formules arithmétiques exactes et les gardes corrigées sont conservées. Le producteur fusion a un seul essai canonique, exit0 ; aucune erreur de compilation ni assertion de producteur n’est fabriquée.

Producteur `round15/fusion_checks.py` SHA256 `5cee100cad1f5bb3d725687e073f5d165f389c3a99643b51c30f81a912a063ce` ; gate `round15/fusion.json` SHA256 `00886e77d4ca6f25236e30e95f0a955ad80e74e0b3eabab64c05cf17a251b85e`. Le reçu `role6/fusion_canonical_success.json` lie source, snapshot, commande et sortie de l’essai1 ; son log porte SHA256 `0b9aa7be8e1cf33099700c58771b76fb777d32c38f96f91fd65aadb4ed807c14`.

L’unique rejeu séparé sous `isolated_fusion` a exit0, champs et octets identiques. `role6/fusion_replay_receipt.json` SHA256 `b43b4eade440e30d02f33456d98024b8f0d82597fa0141f7bd807615207019f3`, statut `PASS_NEW_ROUND15_SEPARATE_ISOLATED_BYTES_AND_FIELDS_REPLAY`, lie ces sorties et les651 fichiers historiques conservés avant/après. Le contrôle lie les47 entrées du controller14 et son gel ; baseline SHA256 `d43941b27a4325a841282d389476c9c6fa9af920138b9b0deebe1c484a4ff7f4`. Ce rôle a lu les reçus et leurs SHAs, sans appeler ni rejouer les producteurs. Aucun Lean ou ancien PASS n’est relancé.

## 8. Modèle, principal, onset et ledger conservés

S(N) dans F3/F5 est uniquement le principal U4 des kernels W locaux. Dans le transfert bilatéral, le cofacteur d’une suppression de premier l est b=m/l : son modèle est S(bN). Par exemple supprimer q donne b=e, supprimer p d’un m=cpq donne b=cq. Le common c d’une fusion n’est pas automatiquement cet indice b. Tous les poids logl/logm, les deux incidences, b1, les cofacteurs b>a, la référence −S(N)N et S(bN) demeurent dans le transfert exact ; aucune substitution arbitraire par S(N) n’est faite.

La sélection15 porte sur des supports J1 complets disjoints des parents J2 et des images13 à crs>a. Ses termes réels sont retirés une seule fois de B_prime^a si l’on utilise cette partition ; les autres vertices restent à leur place. Les contrôles c1 ne sont pas un second crédit. Les properpowers raw, J0/J1/J2 restants, célibataires, faces, nonbulk et fibres incomplètes ne disparaissent pas parce qu’un q ou un partenaire manque.

P5 demeure sur K2 du J2 bulk ENTIER avant les retraits exacts des parents, principaux et erreurs. La nouvelle famille J1 ne fournit pas un deuxième paiement de cette masse rough. U4 sur les vertices distincts peut remplacer le coût de variation de ceux-ci ; il ne s’ajoute pas à un deuxième NG54. Aucun coût de front/charge14 n’est redérivé ou présenté comme le gain15.

Le ledger unique reste

`D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0)`.

Alpha/Q originaux, whole U_a, I_alpha, bande/face, terme couvert et onset BV effectif supplémentaire restent ceux du source. Le budget ouvert est toujours la majoration globale D_N≤N/(256u ell). N=10^8 ne certifie ni le seuil u≥10^24 ni une incidence asymptotique. R1 et un éventuel falsifier fini ne constituent pas un no-go global.

**Statut FINAL :** `SIGNED_SMALL_CORE_FUSION_AND_PHYSICAL_UNION`, `EXACT_PRINCIPAL_ORPHAN_MAJORANT`, `FINITE_FULL_SUM_NEGATIVE_WITH_MIXED_PAIR_SIGNS`, `SOURCE_OR_INCIDENCE_UNESTIMATED`, `GLOBAL_UNION_REUSE_UNPAID`, `LEAN_NOT_CALLED`, `SCORE_ZERO`, `VICTORY_FALSE`. Les domaines F1 e≥2/e1 séparé et F2–F5 E de rang pair≥4/e composite de rang impair≥3 sont explicites. Le contrat, le nouveau banc et son seul rejeu sont terminés et gelés. Un Lean ciblé pourrait certifier S4/S5 et F4 avec les vrais entiers ; ces identités seules ne paient pas F6 ni le complément global. Aucune compilation n’est demandée comme substitut à l’estimation absente. Ce rapport est l’unique production de ce rôle15 et reste immuable après son SHA FINAL.
