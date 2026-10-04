# Boucle 12 — compensation signée : deux mécanismes examinés, deux fermetures non obtenues

Rôle 1, idéation. Rapport autonome limité à ce fichier. Les fichiers 1–11 et le cadre source sont conservés. Aucun ancien banc PASS n'a été relancé par ce rôle ; aucune compilation n'a été demandée pour substituer une identité standard à l'estimation recherchée.

**Conclusion de portée.** Un flot fondé sur la suppression de facteurs premiers ne peut déplacer la capacité favorable entre les noyaux de grands facteurs dans le bulk. Son composant à trois incidences réelles est déjà déficitaire. Un détecteur qui annule les premiers et les puissances propres du second axe conserve exactement le signe de Möbius sur les composites squarefree ; la normalisation logarithmique ne réduit pas sa masse absolue après couverture complète. Aucun des deux mécanismes ne fournit une estimation arithmétique indépendante permettant de fermer le résidu. Ce sont deux retours d'échec précis, pas une impossibilité générale ni une victoire.

## 1. Probe Block avant sélection

**Q1 — Classe de panne.** La capacité favorable n'est pas disponible dans chaque fibre, et une couverture exacte peut consommer toute l'économie apparente d'un poids. Deux preuves finies sont distinctes : (i) la paire 11 à $p=3167,q=3191$ a seulement le complément tripled premier, tandis que la face $c=7,p=3167,q=3169$ a un complément premier sans face tripled ; le crédit logarithmique commun ne paie ni cette incidence célibataire ni cette face ; (ii) les nouveaux points 12 $m=10526181=3\cdot1061\cdot3307$ et $m=10663289=7\cdot13\cdot37\cdot3167$ ont un vrai complément premier, un cofacteur court incomplet $c>a$, et des signes de Möbius opposés. La panne ne vient donc pas seulement du nombre de grands facteurs. Références : rapports finaux 11, rôle 6 `round12/witnesses.json`, puis nouveau contrat `round12/star_detector.json`.

**Q2 — Hypothèse cachée inversée.** « Chaque demande nuisible dispose d'un crédit favorable dans sa fibre » est faux. « Un facteur $1/\log m$ reste petit après le regroupement de tous les diviseurs premiers » est également faux. Si ces deux idées sont retirées, il faut une véritable capacité entre fibres de noyaux distincts, ou une estimation signée des incidences couplées ; ni l'une ni l'autre ne découle du seul crible d'une progression.

**Q3 — Problème volumineux.** Le préfixe $U_a$ contient $r\le\alpha$. Dans J1 il donne notamment une masse logarithmique principale, et le principal de référence (S(N)N) demeure dans la voie bilatérale. L'annulus déjà payé, la petite erreur de Mellin, le contrôle commun P5 et la correction des puissances propres ne peuvent servir à payer ce principal une seconde fois. J0, J1 incomplet, les célibataires et les faces ont des signes réels qui doivent être conservés.

**Q4 — Test de Hamming.** Oui, seulement au sens où l'on vise la vraie compensation entre demandes nuisibles et masses favorables plutôt qu'un nouveau coût technique. Les deux essais ci-dessous échouent avant la demande de compilation. Leurs identités exactes ne suffisent pas à remplir la condition de victoire.

Les quatre mouvements d'idéation ont été utilisés : inversion de la capacité locale ; recherche à rebours d'un certificat de flot couvrant les vraies demandes ; transfert analogique de la dualité de flot et d'un détecteur annihilant les premiers ; rétro-ingénierie des célibataires, de la face $c=7$, des deux parités de J1 et du secteur de puissances propres. Le premier essai appartient à la classe « capacité arithmétique entre incidences » ; le second à la classe « renouvellement logarithmique d'un détecteur composite ». Leur échec n'est pas la même déduction.

## 2. Supports, signes et unique ledger

On conserve

\[
u=\log N,\qquad \ell=\log u,\qquad
\alpha=\lceil N^{1/4}\rceil,\qquad
a=\lceil N^{7/16}\rceil,\qquad
Q=\lfloor(N-1)/\alpha\rfloor,\qquad M=\lceil N^{3/4}\rceil.
\]

Le seuil $M$ est le bulk déjà employé, pas une modification de $\alpha,Q,I_\alpha,e$. Les kernels sont littéralement

\[
D_a(m)=\sum_{\substack{k\mid m,\ 1\le k\le Q\\ak<m}}
 \mu(k)\log(k/m),
\]
\[
W_a(n,m)=\sum_{\substack{1\le k\le Q,\ (k,nN)=1\\ak<m}}
 \frac{\mu(k)\log(k/m)}{\varphi(k)}.
\tag{A0}
\]

Il s'agit du kernel de signe principal (-S(N)). Les deux points $k=1$ sont conservés et s'annulent ensemble dans $D_a-W_a$. La face est stricte $ak<m$. Pour l'axe premier, $\theta_N(n)=\mathbf1_{n\text{ premier},(n,N)=1}\log n$. Pour la voie bilatérale, $\Lambda_N(n)=\mathbf1_{n>1,(n,N)=1}\Lambda(n)$, avec toutes les puissances propres du premier axe.

Le coefficient entier réel est

\[
C_m=-\mu(m)\{D_a(m)-W_a(N-m,m)\}.
\tag{A1}
\]

Le théorème U1 acquis donne, après l'expression entière et non comme filtre raw,

\[
C_m=\mu(m)^2[-\Lambda(m)-U_a(m)]
       +\mu(m)W_a(N-m,m),\quad
U_a(m)=\sum_{\substack{r\mid m\\r\le a}}\mu(r)\log r.
\tag{A2}
\]

La partition J0/J1/J2 est canonique par le nombre de facteurs premiers $>a$. Elle ne superpose pas les deux essais. Dans J2, $m=cpq$, $a<p<q$, $c$ squarefree, $(c,pqN)=1$, et U2 acquis donne le vrai raccord

\[
C_{cpq}=\Lambda(c)+\mu(c)W_a(N-cpq,cpq).
\tag{A3}
\]

Dans J1, $m=cp$, $c>1$, le coefficient entier conserve $-U_a(c)-\mu(c)W_a$. Lorsque $c>a$, $U_a(c)$ reste une fibre incomplète ; ni $c=3183$ ni $c=3367$ ne peut être remplacé par une convolution complète. Dans J0 on conserve (A2). Le préfixe $r\le\alpha$ ne disparaît dans aucun de ces secteurs.

Le seul ledger est

\[
D_N=B_{\rm prime}^a+B_{\rm pp}^a+P_{\rm band}^{\ge2}
 +Z_{\rm face}^{\ge2}+I_\alpha+2\max(e,0).
\tag{L}
\]

Le paiement acquis de $I_\alpha$, la charge properpower du premier axe, la face harmonique, l'union des corners et la mobilité singulière sont chacun comptés une fois. P5 paie seulement le positif du modèle commun et remplace P4. (NG54) est une unique erreur globale de J2. On conserve $-R_{\rm pair}$ et $-S A_{{\rm common},+}$, sans en inventer la minoration. Le domaine effectif source est $u\ge10^{24}$. L'onset BV supplémentaire de la bande physique et $2\max(e,0)$ restent ouverts.

## 3. Essai A : flot signé sur le graphe de suppression de facteurs

### Quatre lignes pour l'arbre — candidat examiné puis rejeté localement

**Mechanism :** Router la demande positive $\theta_N(N-m)\max(C_m,0)$ vers les capacités négatives réelles $-\theta_N(N-m)\min(C_m,0)$ au moyen de suppressions de facteurs premiers, en gardant les trois secteurs J0/J1/J2 et chaque incidence première.

**Hypothesis :** Une expansion arithmétique du graphe devrait permettre un flot couvrant les demandes avec les capacités effectivement présentes ; elle doit se démontrer sur les deux axes premiers, pas être supposée comme une petitesse du résidu. La version locale par noyau de grands facteurs est réfutée ci-dessous.

**Observable :** Coupes fermées, demande moins capacité par composant, coefficients littéraux de $D_a-W_a$, singleton/face et volume de flot non couvert. L'étoile $t=3167\cdot3169,c\in\{1,3,7\}$ possède un défaut strictement positif avec le vrai modèle entier.

**Conflicts :** Aucun crédit rough ou P5 ajouté deux fois ; aucune unité supprimée ; les arêtes sortant du bulk ne reçoivent pas un paiement gratuit de corner. Le cadre source et les anciens transports sont intacts. Le mécanisme n'est pas retenu comme voie de fermeture.

### A4 — Contrat global exact et garde arithmétique

Les vertices sont les $m$ satisfaisant

\[
1\le m\le N-2,\quad m\ge M,\quad N-m>Q,
\quad N-m\text{ premier},\quad (m,N)=1,
\quad m\text{ squarefree}.
\tag{A4}
\]

Le support squarefree ici intervient après (A2), qui annule le coefficient entier hors de ce support. Il n'est ajouté ni au raw ni à une tête tronquée. Une arête de suppression $m\to m/p$ exige $p\mid m$ premier et que le child satisfasse toutes les gardes (A4), avec son propre kernel et sa propre incidence. Les modèles n'y sont pas rendus invariants.

Si $m/p\ge M$, alors

\[
p\le (N-2)/M < a
\tag{A5}
\]

dès que $aM>N-2$, condition vraie au domaine source et au témoin. Une suppression gardant le bulk ne peut donc retirer un premier $>a$. Le noyau de grands premiers est invariant le long de toute chaîne autorisée. En particulier, la demande J2 ne peut atteindre le pool de $m$ premiers donnant $-R_{\rm pair}$. J0 et J1 restent d'autres composants, avec leur propre préfixe incomplet ; cette construction n'a pas fourni une compensation entre ces composants.

Pour un flot non négatif $f_{v,w}$ allant d'un vertex positif vers un vertex négatif accessible, les demandes $A_v=\theta_N(N-v)\max(C_v,0)$ et capacités $B_w=-\theta_N(N-w)\min(C_w,0)$ sont fixes. Si le flot respecte lignes et colonnes, son bilan exact est

\[
\sum_v\theta_N(N-v)C_v
 =\sum_{v:C_v>0}\left(A_v-\sum_w f_{v,w}\right)
  -\sum_{w:C_w<0}\left(B_w-\sum_v f_{v,w}\right).
\tag{A6}
\]

Cette égalité est seulement une comptabilité. Une hypothèse de Hall pondérée couvrant toutes les demandes serait une nouvelle information arithmétique. La postuler comme capacité globale au lieu de la prouver déplacerait l'objectif sans le résoudre. Les arêtes rejetées par la garde bulk, les incidences non premières et les faces ne sont pas effacées. Le coût original d'un corner ne paie pas une multiplicité arbitraire de parents transportés sur ce corner.

### A7 — Premier lemme vulnérable, cut fermé à trois incidences

La fermeture locale tentée était : « dans un composant J2 de noyau $t=pq$, les capacités négatives réelles couvrent les demandes positives ». Elle est arithmétiquement fausse au contrat fini suivant.

À $N=100000000$,

\[
\alpha=100,\quad a=3163,\quad Q=999999,\quad M=1000000,
\quad t=3167\cdot3169=10036223.
\]

Le cap de cofacteur bulk $n>Q$ est $C_t=\lfloor(N-Q-1)/t\rfloor=9$. Les cofactors squarefree unitaires sont exactement $X_t=\{1,3,7\}$. Les trois vrais compléments sont

\[
n_1=89963777,\quad n_3=69891331,\quad n_7=29746439,
\]

tous premiers et unitaires. Les trois $m=t,3t,7t$ restent bulk. Toute suppression de (3167) ou (3169) sort du bulk ; supprimer (3) ou (7) revient à $t$. Il s'agit donc d'un composant fermé du graphe (A4), pas d'une paire dont la face a été perdue.

Son coefficient principal entier est

\[
K_{\rm star}
=\log3\log n_3+\log7\log n_7
 +S(N)[\log n_3+\log n_7-\log n_1].
\tag{A7}
\]

Les deux premiers termes sont positifs et $n_3n_7>n_1$. Donc $K_{\rm star}>0$ pour tout $S(N)>0$, sans valeur numérique postulée de la singular series. La variante avec les vrais kernels est

\[
K_{\rm real}=\log n_1\,W_a(n_1,t)
 +\log n_3[\log3-W_a(n_3,3t)]
 +\log n_7[\log7-W_a(n_7,7t)].
\tag{A8}
\]

Le rôle 6 a certifié $K_{\rm real}>0$ par intervalles rationnels stricts. Les kernels sont chacun complets, avec leur propre front et leurs propres unités. Ce signe fini ne prétend pas appliquer le seuil source à $u=\log10^8$.

L'étoile raccorde bien l'entropie et la face ouvertes : l'incidence $c=3$ fait partie de la paire $1/3$, tandis que $c=7$ est une face tripled absente. P5 ne paie ni l'entropie $\log3\log n_3$, ni celle $\log7\log n_7$, ni la capacité supplémentaire de la face. L'erreur analytique (W+S) ne peut annuler le principal de (A7) par sa seule petitesse.

### A9 — Différence avec les essais précédents et budget indépendant

Le nœud 4 transportait un seul commutateur et rencontrait les témoins 101/303/707/2121. Ici le candidat est un certificat de capacité avec plusieurs incidences, des poids logarithmiques et la totalité du modèle, puis une obstruction à la communication entre noyaux de grands facteurs. Ce changement conceptuel ne donne toutefois aucune estimation : il produit un cut nuisible fermé avant Lean.

Le premier lemme arithmétique local utile serait (A5), avec l'invariance du noyau et le raccord de l'étoile au vrai bracket (A3). Il n'assume aucune cible. Il expliquerait un échec de ce mécanisme, et ne serait pas présenté comme un contournement de parité. Conformément au retour du coordinateur, on ne demande pas sa compilation comme substitut à l'estimation manquante.

Une borne indépendante mais insuffisante est, sur J2,

\[
0\le H_2\le (u/8)\Theta_{J2},\quad
|M_2|\le\Theta_{J2},\quad
\Theta_{J2}=\sum_{m\in J2}\theta_N(N-m)\le N u.
\tag{A9}
\]

La représentation canonique assure l'injection dans $m$, sans uniformité des $J_c$. Ce budget ne ferme pas $H_2+S\Delta_{\rm single}+S\Delta_{\rm face}$, encore moins J0/J1. Pour dépasser (A5), il faudrait un opérateur reliant des noyaux distincts, avec une estimation de ses vraies incidences premières et de ses faces, ou une information arithmétique indépendante assurant une capacité favorable globale. Aucune minoration de ce type n'est acquise ici. En particulier, on ne suppose pas une masse Goldbach pour remplir le pool.

La construction générale de graphe ne requiert pas $3\nmid N$, mais le contrat $c=1,3,7$ exige $3,7\nmid N$. L'emploi de P2/P5 3-adique demeure limité à $3\nmid N$. Pour $3\mid N$, la route source initiale reste intacte.

## 4. Essai B : détecteur composite et renouvellement logarithmique gardé

### Quatre lignes pour l'arbre — candidat examiné, aucune estimation de fermeture

**Mechanism :** Annuler exactement les premiers et les puissances propres du second axe dans un détecteur (E(m)), absorber sa diagonale première dans le vrai terme bilatéral, puis chercher une estimation indépendante du résidu couplé à $\Lambda_N(N-m)$.

**Hypothesis :** Le résidu de renouvellement pourrait bénéficier du facteur $1/\log m$ après couverture complète. L'économie absolue ainsi annoncée est réfutée : les poids des facteurs premiers totalisent exactement un sur chaque composite squarefree.

**Observable :** Les masses premières inclinées $R_{\rm tilt}$, composites squarefree de parité paire/impair $P_{\rm even},P_{\rm odd}$, unité $m=1$, et correction exacte des puissances propres du second axe. La première hypothèse de positivité du détecteur est fausse sur un vrai J1 à complément premier.

**Conflicts :** Aucun filtre $\mu(n)^2$, aucun retrait des puissances propres de $\Lambda_N$, aucun produit faux à la place d'un lcm, aucune application de BV à $\mu(d)\Lambda(N-dk)$. La référence (S(N)N), le principal et le covered $e$ demeurent.

### B1 — Identité complète, diagonal et puissances propres

Pour $m>1$, définir

\[
E(m)=\mu(m)+\mu(m)^2\frac{\Lambda(m)}{\log m},
\quad V(m)=-\frac{1}{\log m}
  \sum_{\substack{d\mid m\\d>1}}\mu(d)\Lambda(m/d),
\]
\[
P(m)=(1-\mu(m)^2)\frac{\Lambda(m)}{\log m}.
\]

L'identité exacte est

\[
E(m)=V(m)-P(m).
\tag{B1}
\]

Elle est dérivée de la couverture complète $\mu(m)\log m=-(\mu*\Lambda)(m)$. La convolution standard seule n'est pas une nouveauté revendiquée. Le mécanisme examiné est son raccord à un détecteur qui annule les premiers, au vrai moment bilatéral et à une comparaison de capacités.

Le comportement de (E) est exact :

- $m$ premier : $E=0$, $V=P=0$ ;
- $m=p^j$, $j\ge2$ : $E=0$, $V=P=1/j$ ;
- $m$ squarefree composite : $E=V=\mu(m)$, $P=0$ ;
- $m$ non squarefree et non puissance première : $E=V=P=0$.

L'unité $m=1$ est traitée séparément, parce que $\log1=0$. Aucun $d=1$ ou $k=1$ n'est effacé artificiellement : le $d=1$ de la convolution vaut $\Lambda(m)$, et les termes $k=m/d=1$ valent $\Lambda(1)=0$.

### B2 — Raccord au moment bilatéral réel

Conserver le moment de la route B13

\[
\mathcal T_N=\sum_{m=1}^{N-2}\Lambda_N(N-m)
 [\mu(m)^2\Lambda(m)+S(N)\mu(m)]-S(N)N.
\tag{B2}
\]

Ce n'est ni le $I_\alpha$ bilantiel ni une moyenne sur $N$. On pose

\[
R_{\rm tilt}=\sum_{m=2}^{N-2}\Lambda_N(N-m)\mu(m)^2\Lambda(m)
 \left(1-\frac{S(N)}{\log m}\right).
\]

Le raccord exact garde toutes les branches :

\[
\mathcal T_N=R_{\rm tilt}
 +S(N)\sum_{m=2}^{N-2}\Lambda_N(N-m)V(m)
 -S(N)\sum_{m=2}^{N-2}\Lambda_N(N-m)P(m)
 +S(N)\Lambda_N(N-1)-S(N)N.
\tag{B3}
\]

En combinant les deux corrections au lieu de perdre une puissance propre,

\[
\mathcal T_N=R_{\rm tilt}
 +S(N)(P_{\rm even}-P_{\rm odd})
 +S(N)\Lambda_N(N-1)-S(N)N,
\tag{B4}
\]

où $P_{\rm even}$ et $P_{\rm odd}$ sont les sommes de $\Lambda_N(N-m)$ sur les composites squarefree avec un nombre respectivement pair et impair de facteurs premiers. Ces masses sont des observables exactes, pas des hypothèses de densité indépendante.

Le renouvellement couplé est lui-même

\[
\sum_{m=2}^{N-2}\Lambda_N(N-m)V(m)
=-\sum_{\substack{d\ge2,\ k\ge2\\dk\le N-2}}
 \frac{\mu(d)\Lambda(k)\Lambda_N(N-dk)}{\log(dk)}.
\tag{B5}
\]

Toutes les puissances premières $k=p^j$ sont gardées. Le masque $\Lambda_N$ conserve les unités ; il implique $(dk,N)=1$ pour tout terme non nul, et l'on peut l'écrire explicitement sans changer le coefficient. Aucune phase native n'offre une oscillation de caractère : lorsque le conducteur divise $k$ ou $d$ sur une fibre physique, $n=N\pmod q$, et $\chi(n)\overline{\chi(N)}=1$.

### B6 — Premier lemme vulnérable et disparition de l'économie annoncée

Sur un composite squarefree, $\Lambda(m)=0$. Dans (B1), les seuls quotients $m/d$ pouvant contribuer sont les premiers $p\mid m$, et

\[
-\mu(m/p)\frac{\log p}{\log m}
 =\mu(m)\frac{\log p}{\log m},\qquad
\sum_{p\mid m}\frac{\log p}{\log m}=1.
\tag{B6}
\]

Par conséquent,

\[
\sum_{\substack{d\mid m\\d>1}}
 \left|\frac{\mu(d)\Lambda(m/d)}{\log m}\right|=1
\quad(m\text{ squarefree composite}).
\tag{B7}
\]

Le petit facteur $1/\log m$ n'est donc pas une économie après couverture complète. Le paiement absolu exact sur ce secteur est

\[
S(N)\sum_{\substack{2\le m\le N-2\\m\text{ squarefree composite}}}
 \Lambda_N(N-m),
\tag{B8}
\]

et non cette masse divisée par $u$. Le premier promoteur « détecteur composite non négatif » est faux. Les nouveaux points J1 ont

\[
m_-=10526181=3\cdot1061\cdot3307,
\quad N-m_-=89473819\text{ premier},\quad E(m_-)=-1,
\]
\[
m_+=10663289=7\cdot13\cdot37\cdot3167,
\quad N-m_+=89336711\text{ premier},\quad E(m_+)=+1.
\tag{B9}
\]

Le signe du résidu couplé reste exactement celui de Möbius. La même classe J1 et le même nombre de grands facteurs ne suffisent pas à le fixer. La couverture absolue vaut un sur les deux points.

La nouvelle puissance propre gardée par le rôle 6 est

\[
m=4913=17^3,\quad N-m=99995087\text{ premier},\quad
V(m)=P(m)=1/3,\quad E(m)=0.
\tag{B10}
\]

L'omission de (P) aurait créé à tort $\frac13\log99995087$. Il s'agit d'une puissance propre du **second** axe ; aucune puissance propre du premier axe n'est retirée par cette correction.

Le rôle 6 conserve aussi un nouveau témoin du **premier** axe :

\[
m=35727711=3\cdot43\cdot419\cdot661,\qquad
n=64272289=8017^2,\qquad
E(m)=1,\quad\Lambda_N(n)=\log8017,\quad\theta_N(n)=0.
\tag{B10a}
\]

Le détecteur bilatéral est donc actif sur ce point properpower raw. Lui ajouter un filtre $\mu(n)^2$ supprimerait indûment cette contribution. Sa présence ne crée pas un second paiement du poste properpower déjà acquis.

### B11 — Budgets indépendants et obligation duale restante

La correction (P), si elle est provisoirement séparée dans cette voie alternative, satisfait la borne élémentaire

\[
0\le S(N)\sum_m\Lambda_N(N-m)P(m)
 \le \frac{S(N)}{2\log2}\sqrt N\,u^2.
\tag{B11}
\]

En effet $j\ge2$, $P(p^j)=1/j\le1/2$, $p\le\sqrt N$, et le nombre d'exposants possibles est au plus $u/\log2$. Avec $S(N)<3\ell$, ce coût est minuscule au seuil source. Dans (B3)–(B4) il s'annule exactement avec son jumeau dans (V). On ne l'ajoute donc pas au paiement acquis $B_{\rm pp}^a$, ni aux pertes $P_{\rm ret},T_{\rm pairs}$ de l'autre comptabilité.

Sur les $m\$ premiers bulk, $\log m\ge3u/4$, donc

\[
R_{\rm tilt,bulk}
 \ge\left(1-\frac{4S(N)}{3u}\right)R_{\rm sf,bulk}.
\tag{B12}
\]

Cette inclinaison est petite, mais elle ne fournit aucune minoration de la masse réelle $R_{\rm sf,bulk}$. Les petits $m$ et $m=1$ conservent leurs expressions exactes ; les corners ne se créditent pas une deuxième fois.

Le budget sans information signée est seulement

\[
|P_{\rm even}-P_{\rm odd}|
 \le P_{\rm even}+P_{\rm odd}
 \le\sum_{n<N}\Lambda_N(n)\le N u.
\tag{B13}
\]

Il est trop grand. Deux obstacles analytiques différents restent dans (B5) : fixer un petit $d$ donne deux véritables axes premiers (k,N-dk), dont une comparaison de masses ne découle pas d'une borne BV de progression ; fixer un petit $k$ laisse le poids $\mu(d)/\log(dk)$ sur les indices de la progression $N\pmod k$. Le supprimer est précisément une promotion illégitime de BV. Le secteur long conserve le moment bilinéaire couplé et ses fronts.

Même une borne ordinaire de Mertens ne remplace pas cette information : par sommation partielle, une borne hypothétique à $\sup_{t\le N}|\sum_{d\le t}\mu(d)|\le N\eta$, combinée au seul contrôle de variation de $\Lambda_N(N-d)$, donnerait au mieux $2N^2u\eta$. Une décroissance du type $\exp(-\sqrt u/60)$ ne compense pas le facteur $N=e^u$. Ceci n'est pas l'attribution d'une nouvelle hypothèse source ; c'est l'explication quantitative de l'échec d'un promoteur Mertens ordinaire.

La véritable obligation duale est une estimation de la combinaison

\[
R_{\rm tilt}+S(N)(P_{\rm even}-P_{\rm odd})
 +S(N)\Lambda_N(N-1)-S(N)N,
\tag{B14}
\]

avec le raccord source de B13, ses unités, son principal et ses pertes. Postuler sa petitesse ou une masse Goldbach remplissant la demande (S(N)N) n'est pas une hypothèse indépendante admissible. Aucune estimation nouvelle de (B14) n'est dérivée ici.

Le théorème local proposé avant filtrage aurait certifié (B1), (B6) et le raccord (B3) sur les vrais objets ; il ne contient pas d'hypothèse-cible. Le filtrage le rejette comme compilation de substitution : ces identités ne contrôlent pas le signe couplé. On n'écrit donc aucun nouveau module Lean standard pour cet essai.

## 5. Contrat numérique neuf et qualification des retours

Le contrat transmis au rôle 6 porte uniquement sur de nouveaux énoncés :

1. Étoile entière à trois incidences, enumeration $X_t=\{1,3,7\}$, ses enfants admissibles/rejetés par bulk, coefficient principal affine en $S>0$ et coefficient réel avec les trois kernels complets ;
2. détecteur $E=V-P$ sur les deux nouvelles parités de J1 ;
3. couverture absolue égale à un après sommation de tous les facteurs premiers ;
4. puissance propre seconde-axe $17^3$ avec vrai premier complément et correction $V=P=1/3$.

Le reçu `round12/star_detector.json` communiqué par le rôle 6 porte le statut **PASS_NEW_STAR_AND_GUARDED_DETECTOR_IDENTITIES_ONLY**. L'étoile réelle, sa constante principale et son coefficient de $S$ sont strictement positifs par intervalles rationnels. Les enfants sortant du bulk sont prouvés par inégalités entières. L'omission de la correction properpower et l'économie absolue $1/\log m$ portent des **ERROR_FALSIFIER**, distincts d'erreurs de compilation Lean. Le point $E(m_-)=-1$ réfute également la positivité pointwise du détecteur, qui n'a pas été supposée dans le banc. Le rôle 6 a ensuite annoncé le gel de ce gate et son rejeu isolé, champs et octets identiques ; cela ne paie aucune borne analytique.

Empreintes communiquées et vérifiées par ce rôle : reçu `star_detector.json` **ea074f16953f96c038c3d124394b182ffb5549a3951052c5e883263e8c0b6545** ; script **b758b026ba648b19067ff9341832a48fc44dbced5e1bb53ebf6f76e318147343** ; reçu de rejeu isolé **653b4089491e6f18050394e226208dcdd287c1e16e97adf64fe0b9f0b082bcc0**.

L'observable global facultatif $P_{\rm even}-P_{\rm odd}$ a été défini exactement mais aucune sommation complète à $N=10^8$ n'est nécessaire au rejet des deux promoteurs locaux. Aucun résultat numérique ne paie une borne analytique au seuil $u\ge10^{24}$.

## 6. Conservation et décision

Le contrôle commun P5 et les raccords P1/P2 restent acquis. Ils ne sont pas redérivés comme gain. La nouvelle obstruction A5 explique pourquoi un opérateur de suppression de premiers préservant le bulk ne peut réunir les capacités des secteurs ; l'étoile complète A7–A8 réfute sa fermeture locale. B6–B8 expliquent pourquoi la couverture logarithmique complète retrouve la masse signée Möbius, tandis que B10 protège la correction de puissances propres.

Les deux essais sont conceptuellement indépendants, mais aucun ne produit la capacité globale ou l'estimation duale manquante. Les quatre postes ouverts de portée différente restent visibles : compensation principale de $B_{\rm prime}^a$ incluant J0/J1 et les défauts J2 ; threshold effectif supplémentaire de $P_{\rm band}^{\ge2}$ ; $2\max(e,0)$ de la comptabilité couverte ; raccord intégral de toute alternative au ledger source sans double crédit. Il n'y a ni nouvelle victoire ni nouvelle certification Lean de la cible.
