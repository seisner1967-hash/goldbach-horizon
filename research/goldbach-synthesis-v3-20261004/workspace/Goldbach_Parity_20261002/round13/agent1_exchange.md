# Boucle 13 — échange premier/semipremier traversant les grands noyaux

Rôle 1, idéation autonome. Sources et productions 1–12 immuables. Les deux inputs prescrits et la vue constraints courante ont été lus. Le présent rapport est le seul fichier écrit par ce rôle dans la boucle 13.

**Portée.** L'opérateur remplace un grand premier \(p\) par le semipremier squarefree \(p-2=rs\). Il change le noyau des grands facteurs et transforme, au domaine source U4, un parent J2 nuisible en une image J1 favorable, avec cofacteur court incomplet. Le préfixe physique change exactement de signe. La variation des deux vrais kernels est conservée et reçoit un paiement écrit indépendant, au plus \(21N^{31/32}u^2\) sur l'ensemble apparié. Ce paiement est partiel : aucune densité des parents admissibles ni première incidence image n'est minorée. La fermeture globale et la condition de victoire ne sont pas obtenues.

## 1. Probe Block

**Q1 — Information nouvelle exigée.** Le graphe 12 ne pouvait supprimer un grand facteur sans quitter le bulk. Ici une substitution proche, \(p\mapsto rs=p-2\), retire un grand facteur et le remplace par deux petits facteurs tout en conservant le bulk par garde explicite. La nouvelle information n'est pas le changement de variables : elle est l'antisymétrie de deux préfixes incomplets réellement différents, puis une borne de variation du modèle sur une translation relative \(2/p\).

**Q2 — Contre-exemples qui obligent à changer.** L'étoile 12 \(c=1,3,7\), noyau \(3167\cdot3169\), interdit une capacité locale obtenue par simple suppression bulk. La couverture complète \(\sum_{p\mid m}\log p/\log m=1\) interdit une économie tirée du seul poids \(1/\log m\). Le nouvel échange n'utilise aucune de ces deux hypothèses : il change la factorisation du grand premier et paie le commutateur \(W_1-W_0\), avec chaque incidence. Le témoin downward 13 réfute à son tour la suppression de ce commutateur : son principal est négatif, mais sa paire réelle finie est positive.

**Q3 — Hypothèse cachée inversée.** On ne demande ni « tous les parents possèdent une image première », ni « \(W_0=W_1\) », ni « toute paire réelle est non positive ». L'information utile est une majoration de la somme des paires avec son défaut explicite. Un parent admissible arithmétiquement mais dont le complément image est composite reste non apparié.

**Q4 — Problème volumineux et Hamming.** Oui : l'on vise une capacité réelle entre J2 et J1, plutôt qu'une petite erreur supplémentaire sur une somme inchangée. Cependant, cette capacité ne concerne qu'un sous-ensemble. J0, J1 restant, J2 non apparié, célibataires/faces P2 et la référence bilatérale ne sont pas payés par la petitesse du commutateur.

Deux mouvements conceptuels ont été combinés : inversion de la contrainte « supprimer un grand facteur » en une substitution première/semipremière proche qui change la parité ; transfert analogique d'un opérateur à petit déplacement, dont la variation de front est bornée avant les normes. La recherche à rebours impose une image canonique injective et les deux premiers complémentaires réels. Le retour d'échec numérique filtre les promotions de signe et de couverture.

## 2. Quatre lignes Mechanism / Hypothesis / Observable / Conflicts

**Mechanism :** Apparier \(m_0=cpq\) de J2 avec \(m_1=crsq\) de J1, où \(p-2=rs\), et montrer sur les vrais kernels que leur bracket vaut une masse favorable conservée plus un commutateur de front payable.

**Hypothesis :** Les coupes \(cr,cs\le a<rs\), la primalité/canonicalité des cinq facteurs et des deux compléments donnent une antisymétrie exacte de \(U_a\). La petite translation \(2cq\) permet une borne indépendante de \(W_1-W_0\). Aucune hypothèse de capacité globale, d'uniformité \(J_c\) ou de petitesse cible n'est ajoutée.

**Observable :** Ensemble injectif de couples J2/J1, masse réelle favorable \(A_{\rm real}\), coût total \(E_{\rm switch}\), kernels et fronts distincts, parents arithmétiquement admissibles sans premier image, et miroir \(p+2=rs\).

**Conflicts :** \(Q,\alpha,I,e\) restent source ; \(k=1\) est conservé conjointement ; aucune hypothèse \(W_0=W_1\), aucun filtre raw \(\mu(n)^2\), aucune face gratuite et aucun second crédit rough/P5/NG54. Les restes sont littéraux. Le gain est un certificat partiel, sans victoire.

## 3. Définition du bracket et ledger fixes

Fixer \(N\) pair, \(N\ge4\), comme dans le cadre source. Les identités finies demandent seulement les gardes explicites ; le paiement élémentaire ci-dessous demande \(u\ge16\), et l'usage de U4 et du ledger acquis conserve son domaine \(u\ge10^{24}\).

\[
u=\log N,\quad \ell=\log u,\quad
\alpha=\lceil N^{1/4}\rceil,\quad a=\lceil N^{7/16}\rceil,\quad
Q=\lfloor(N-1)/\alpha\rfloor,\quad M=\lceil N^{3/4}\rceil.
\]

Conserver littéralement

\[
D_a(m)=\sum_{\substack{k\mid m,\ 1\le k\le Q\\ak<m}}
 \mu(k)\log(k/m),
\]
\[
W_a(n,m)=\sum_{\substack{1\le k\le Q,\ (k,nN)=1\\ak<m}}
 \frac{\mu(k)\log(k/m)}{\varphi(k)},\qquad
C_m=-\mu(m)\{D_a(m)-W_a(N-m,m)\}.
\tag{X0}
\]

\(W_a\) a le signe principal \(-S(N)\). L'axe premier de cette extraction est \(\theta_N(n)=\mathbf1_{n\ {\rm premier},(n,N)=1}\log n\). Le raw du cadre garde \(\Lambda_N(n)=\mathbf1_{n>1,(n,N)=1}\Lambda(n)\) et ses puissances propres. L'opérateur porte seulement sur un sous-ensemble du \(B_{\rm prime}^a\) déjà séparé ; il ne retire aucune autre contribution raw.

U1 acquis est le raccord entier

\[
C_m=\mu(m)^2[-\Lambda(m)-U_a(m)]
       +\mu(m)W_a(N-m,m),\quad
U_a(m)=\sum_{\substack{r\mid m\\r\le a}}\mu(r)\log r.
\tag{X1}
\]

\(\mu(m)^2\) intervient après l'identité entière, et non comme un filtre sur une tête tronquée. \(U_a\) contient \(r\le\alpha\), sans crédit de l'annulus pour le remplacer. Le seul ledger est

\[
D_N=B_{\rm prime}^a+B_{\rm pp}^a
 +P_{\rm band}^{\ge2}+Z_{\rm face}^{\ge2}
 +I_\alpha+2\max(e,0).
\tag{L}
\]

Source \(u\ge10^{24}\), frais acquis une fois. Le coût BV effectif supplémentaire de la bande physique et \(2\max(e,0)\) restent ouverts.

## 4. Domaine canonique réel du nouvel échange

Un tuple \((c,p,q,r,s)\) est admissible si :

1. \(c,p,q,r,s\) sont premiers, distincts, et \(c<r<s\le a<p<q\) ;
2. \((c p q r s,N)=1\), \(rs=p-2>a\), \(cr\le a,\ cs\le a,\ crs>a\) ;
3. \(m_0=cpq,\ m_1=crsq=m_0-2cq\) satisfont \(M\le m_i\le N-2\) ;
4. \(n_i=N-m_i>Q\) sont réellement premiers et \((n_i,N)=1\).

Ces gardes sont des conditions du sous-ensemble sélectionné, pas des théorèmes d'existence. \(n_1=n_0+2cq>n_0\). Les images non premières, nonbulk, nonunitaires, non squarefree, ou ne satisfaisant pas les coupes ne sont pas effacées de la somme globale : elles laissent leur parent dans le reste.

L'exigence \(c<r,s\) découle aussi des coupes : si \(c\ge r\), alors \(cs\ge rs>a\), contradiction ; même argument pour \(s\). L'ordre \(r<s\) fixe la factorisation squarefree de \(p-2\), et \(p<q\) choisit le grand premier remplacé.

**Injection parent.** \(m_0\) possède exactement un petit facteur premier \(c\) et deux grands premiers \(p<q\). Sa factorisation retrouve \(c,p,q\), puis \(r<s\) sont déterminés par \(p-2=rs\). Chaque parent est utilisé au plus une fois.

**Injection image.** \(m_1\) possède exactement un grand facteur premier \(q>a\), et trois petits facteurs \(c<r<s\). Sa factorisation retrouve \(q\), son plus petit facteur \(c\), puis \(r,s\) et \(p=rs+2\). Chaque image est utilisée au plus une fois. Parents J2 et images J1 sont disjoints. En particulier, le nombre \(K\) de tuples admissibles est au plus \(N\) (et même au plus \(N/2\), marge non utilisée).

Cette injection doit être dérivée de la factorisation réelle. Elle ne prend pas l'injectivité ou la valeur des coefficients comme hypothèses libres.

## 5. Premier lemme arithmétique réel : antisymétrie du préfixe incomplet

Les diviseurs courts de \(m_0\) sont exactement \(1,c\), puisque \(p,q>a\). Les diviseurs courts de \(m_1\) sont exactement

\[
\{1,c,r,s,cr,cs\}.
\tag{X2}
\]

Les autres candidats \(rs,crs\) dépassent \(a\), et toute occurrence de \(q\) dépasse \(a\). Les cinq facteurs sont premiers distincts ; les signes de Möbius sont ceux de la factorisation entière. Donc

\[
U_a(m_0)=-\log c,\qquad
U_a(m_1)=-\log c-\log r-\log s+\log(cr)+\log(cs)
         =+\log c.
\tag{X3}
\]

Il ne s'agit pas de remplacer un préfixe incomplet par \(-\Lambda(crs)\), qui vaudrait zéro. Le profil J1 incomplet est précisément la source du signe opposé. Les frontières \(cr=a\) et \(cs=a\) sont incluses ; \(rs=a\) serait exclu par la garde stricte et ne doit pas être ajouté.

Avec \(\mu(m_0)=-1,\ \mu(m_1)=+1,\ \Lambda(m_i)=0\), le raccord X1 donne

\[
C_{m_0}=\log c-W_0,\qquad
C_{m_1}=-\log c+W_1,
\quad W_i=W_a(n_i,m_i).
\tag{X4}
\]

Les coefficients de \(D_a\), son cap source et ses unités ne sont pas remplacés par des constantes hypothétiques. \(k=1\) reste dans les deux branches de X0 ; son annulation est jointe.

La paire arithmétique réelle est

\[
B_{\rm pair}=\log n_0\,C_{m_0}+\log n_1\,C_{m_1}
 =-(\log c-W_0)\log(n_1/n_0)+\log n_1(W_1-W_0).
\tag{X5}
\]

Avec le seul remplacement principal formel \(W_i=-S(N)\), elle vaut

\[
-(\log c+S(N))\log(n_1/n_0)<0.
\tag{X6}
\]

X6 ne permet pas de supprimer le deuxième terme réel de X5. Le premier lemme vulnérable « toute paire downward réelle est non positive » est réfuté au §9. Le contrat retenu est X5 avec paiement explicite de son commutateur.

## 6. Identité du vrai commutateur avec les fronts et le modèle

Comme \(n_i\) est premier et \(n_i>Q\), le masque de X0 est exactement \((k,N)=1\) sur le cap. Définir

\[
R_i=\min\{Q,\lfloor(m_i-1)/a\rfloor\},\qquad
A_N(R)=\sum_{\substack{1\le k\le R\\(k,N)=1}}\frac{\mu(k)}{\varphi(k)}.
\]

La face stricte \(ak<m_i\) donne \((m_i-1)/a\), jamais \(m_i/a\) sans correction. \(m_1<m_0\) implique \(R_1\le R_0\). L'identité exacte est

\[
W_1-W_0=
\log(m_0/m_1)A_N(R_1)
-\sum_{\substack{R_1<k\le R_0\\(k,N)=1}}
 \frac{\mu(k)}{\varphi(k)}\log(k/m_0).
\tag{X7}
\]

Le terme endpoint entier et le secteur \(k=1\) sont conservés. Les deux modèles, leur logarithme de dénominateur et leur tail ne sont pas identifiés. Si \(n_i\le Q\) ou si \(n_i\) est composite, la réduction du masque n'est pas autorisée ; le tuple n'est pas sélectionné et son parent reste dans le reste.

La phase native ne contribue aucune oscillation gratuite : sur une fibre physique \(q_0\mid k\), \(n=N\pmod {q_0}\) et \(\chi(n)\overline{\chi(N)}=1\). La borne ci-dessous n'utilise pas cette phase, ni BV appliqué à un poids Möbius.

## 7. Paiement indépendant total du commutateur

Cette section dérive une borne écrite, sans nouvel input analytique. Elle n'est pas encore un théorème Lean de la cible.

### 7.1 Borne élémentaire du totient

Pour tout entier \(k\ge1\),

\[
\varphi(k)^2\ge k/2,\qquad
\frac1{\varphi(k)}\le\sqrt2\,k^{-1/2}.
\tag{X8}
\]

Preuve multiplicative : pour \(p^e\), \(\varphi(p^e)^2/p^e=p^{e-2}(p-1)^2\). Pour tout premier impair cette quantité est au moins un. Pour \(p=2\), elle est \(1/2\) seulement quand \(e=1\), et au moins un ensuite. Il existe au plus un facteur \(2\) dans la décomposition en puissances premières. \(k=1\) est immédiat. En intégrant \(t^{-1/2}\),

\[
\sum_{1\le k\le R}\frac1{\varphi(k)}
\le2\sqrt2\sqrt R<3\sqrt R \quad(R\ge1).
\tag{X9}
\]

Aucune donnée de primes ni capacité Goldbach n'intervient.

### 7.2 Ceil, floor, cap, petit déplacement

Pour \(u\ge16\), on a \(N^{7/16}\le a\le2N^{7/16}\), \(M\ge N^{3/4}\), et \(M\ge2a+2\). Pour cette dernière marge, \(N^{5/16}\ge e^5>8\) et \(N^{7/16}\ge1\), donc \(M\ge8N^{7/16}\ge4N^{7/16}+2\ge2a+2\). Puisque \(\alpha\le a\) et \(m_i\le N-2\), le cap source vérifie

\[
Q\ge\lfloor(N-1)/a\rfloor
 \ge\lfloor(m_i-1)/a\rfloor.
\]

Ainsi \(R_i=\lfloor(m_i-1)/a\rfloor\), sans changer \(Q\). Les bornes utiles sont

\[
R_0\le N/a,\quad
R_1\ge m_1/(2a)\ge N^{5/16}/4,
\tag{X10}
\]
\[
R_0-R_1\le (m_0-m_1)/a+1
=2cq/a+1\le2N/a^2+1\le2N^{1/8}+1.
\tag{X11}
\]

Le \(+1\) est obligatoire. Comme \(p>a\), \(m_0/m_1=p/(p-2)\), et

\[
0<\log(m_0/m_1)\le 2/(p-2)\le4/p\le4/a.
\tag{X12}
\]

Tous les \(k\) de la tail ont \(1\le k<m_0\), donc \(|\log(k/m_0)|\le u\).

### 7.3 Constantes après toutes les incidences

Le premier terme de X7 satisfait

\[
|\log(m_0/m_1)A_N(R_1)|
 \le (4/a)\,3\sqrt{N/a}
 \le12N^{-5/32}.
\tag{X13}
\]

Pour la tail, X8 et X10 donnent \(1/\varphi(k)<3N^{-5/32}\). X11 conduit à

\[
|{\rm tail}|
 \le3uN^{-5/32}(2N^{1/8}+1)
 =6uN^{-1/32}+3uN^{-5/32}.
\tag{X14}
\]

En combinant X13–X14, pour \(u\ge16\),

\[
|W_1-W_0|\le21uN^{-1/32}.
\tag{X15}
\]

Chaque image est distincte, \(\log n_1\le u\), et \(K\le N\). Donc le coût total sur le sous-ensemble effectivement apparié est

\[
E_{\rm switch}
 :=\sum_{\rm tuples}\log n_1|W_1-W_0|
 \le21K u^2N^{-1/32}
 \le21N^{31/32}u^2.
\tag{X16}
\]

Cette borne ne suppose ni faible énergie couplée ni densité première. Elle paie toutes les variations de modèle de ces deux vertices, pas seulement une branche isolée.

Au seuil source \(u\ge10^{24}\),

\[
\frac{21N^{31/32}u^2}{N/(u\ell)}
=21u^3\ell\,e^{-u/32}<10^{-12}.
\tag{X17}
\]

À \(u=10^{24}\), le logarithme du facteur préexponentiel est inférieur à \(200\), tandis que \(u/32>10^{22}\). Ensuite \(3/u+1/(u\log u)-1/32<0\). Le seuil effectif de ce paiement est donc vérifié au source ; il ne remplace pas le seuil BV supplémentaire non évalué de la bande physique.

### 7.4 Masse favorable réelle conservée

Le raccord uniforme U4 acquis (round10, agent1, §5) pour tous les bulk \(m\ge M,n>Q\) donne \(W_0=-S(N)+\delta_0\), avec

\[
\epsilon_W(u)=4\cdot10^8u^4e^{-\sqrt u/60}
 +160u e^{-u/40},\qquad
|\delta_0|\le\epsilon_W\le1/4
\quad(u\ge10^{24}).
\]

L'exponentielle \(-\sqrt u/60\) est le majorant explicitement affaibli du \(-\sqrt{u/60}\) littéral de (54), avec les prémisses source et son endpoint. X10 fournit ici le même domaine de préfixe que cet acquis. \(S(N)\ge1\) est également conservé. Ainsi, au domaine source seulement, \(W_i\le-3/4\), \(C_{m_0}\ge\log c+3/4>0\) et \(C_{m_1}\le-\log c-3/4<0\). Les vertices parent/image possèdent donc réellement les signes annoncés. Définir

\[
A_{\rm real}=\sum_{\rm tuples}(\log c-W_0)\log(n_1/n_0)>0
\]

si l'ensemble est non vide ; la masse est zéro si l'ensemble est vide. X5–X16 donnent

\[
\sum_{\rm tuples}B_{\rm pair}
\le -A_{\rm real}+E_{\rm switch}.
\tag{X18}
\]

On ne remplace pas \(-A_{\rm real}\) par une minoration présumée. Le contrôle de signe de \(W_0\) réutilise son acquis ; il ne constitue pas un deuxième frais \(NG54\) sur ce même vertex. La comparaison alternative par deux erreurs U4 serait \(\epsilon_W\sum(\log n_0+\log n_1)\), mais ces deux paiements sont alternatifs, jamais additionnés.

## 8. Partition disjointe et obligation de capacité restante

Soient \(P\) les parents appariés et \(T\) leurs images. \(P\subset J2,\ T\subset J1,c>1\), et \(P\cap T=\varnothing\). L'identité finie est

\[
B_{\rm prime}^a=B_{J0}+B_{J1\setminus T}
 +B_{J2\setminus P}+\sum_{\rm tuples}B_{\rm pair}.
\tag{X19}
\]

Les secteurs rough et les coins sont les sous-secteurs littéraux de cette partition ; les parties déjà payées se créditent une fois. Les nonbulk et les gardes échouées restent dans \(J1\setminus T\) ou \(J2\setminus P\). Aucun frais de corner ne paie une multiplicité de parents transportée sur un corner.

Sous X18, cette route donne une majoration avec le bénéfice réel \(-A_{\rm real}\) et le coût X16, mais laisse **toute** la somme \(B_{J0}+B_{J1\setminus T}+B_{J2\setminus P}\). Le cardinal \(K\) n'a aucune minoration acquise. Une capacité globale supposée ou la petitesse de cette somme restante seraient une nouvelle forme de l'objectif, pas une hypothèse acceptable.

Pour conserver P5 sans le réappliquer illégalement à une sélection tronquée, garder son \(K_2\) entier sur le **J2 bulk** et écrire le retrait exact des parents. Les points J2 nonbulk sont conservés séparément, avec leur charge corner acquise une seule fois. Avec \(\kappa_m=(\log c+S(N))\log n_0\) sur les parents et \(e_m=-\delta_0\log n_0\),

\[
B_{J2,{\rm bulk}}=K_2+R_{J2,{\rm bulk}},\quad
B_{J2,{\rm bulk}\setminus P}
 =K_2-\sum_{m\in P}\kappa_m
  +(R_{J2,{\rm bulk}}-\sum_{m\in P}e_m).
\tag{X20}
\]

P5 demeure appliqué au \(K_2\) **entier**, y compris ses vraies incidences célibataires, faces et son crédit rough. L'erreur U4 de la dernière parenthèse porte seulement sur \(J2,{\rm bulk}\setminus P\), et vaut au plus \(\epsilon_W\sum_{m\in J2,{\rm bulk}\setminus P}\log(N-m)\). Les parents/images de X18 sont payés uniquement par X16. On ne somme pas \(NG54\) du J2 entier et une nouvelle erreur pour ses mêmes \(W_0\).

Le paiement X18 ne couvre donc pas \(H_2+S\Delta_{\rm single}+S\Delta_{\rm face}\) restant, J0/J1, ni le principal de B13. \(-R_{\rm pair}\), le bénéfice commun P5 et \(-A_{\rm real}\) sont des masses distinctes avec leurs supports propres ; aucune minoration n'est inventée. Pour \(3\mid N\), le tuple avec \(c=3\) n'est pas autorisé ; la famille générale prend seulement \(c\nmid N\), et la route initiale demeure, sans extension de P5 3-adique.

## 9. Contrat numérique neuf et promoteurs vulnérables

Les gardes sont celles du §4, \(\alpha=100,a=3163,Q=999999,M=1000000\). Le rôle 6 a gelé le nouveau reçu échange avec son rejeu isolé ; leurs empreintes ont été relues par ce rôle sans exécuter un ancien banc.

### 9.1 Downward conjoint réel

\[
c=3,\ p=3229,\ q=3467,\ r=7,\ s=461,\quad p-2=7\cdot461.
\]
\[
m_0=33584829,\quad m_1=33564027,\quad
n_0=66415171,\quad n_1=66435973.
\tag{F1}
\]

Les deux \(n_i\) sont premiers/unitaires ; \(cr=21,\ cs=1383\le3163<rs=3227\), et les fronts sont incomplets. Le principal X6 est strictement négatif. La paire réelle finie avec ses deux kernels est **positive** : le promoteur universel « downward réel non positif sans commutateur » est faux. Cela ne réfute pas X18 et ne prétend pas appliquer U4 à \(u=\log10^8\).

Le même nouveau point vérifie aussi \(U_\alpha(m_0)=-\log3\), \(U_\alpha(m_1)=0\), tandis que l'annulus vaut zéro sur le parent et \(+\log3\) sur l'image. L'identité X3 porte bien sur le préfixe entier, qui contient le low prefix source ; la bande déjà payée ne remplace aucun de ses membres.

### 9.2 Miroir upward

\[
c=3,\ p=3191,\ q=3319,\quad p+2=31\cdot103,\quad
n_0=68227213,\quad n_1=68207299.
\tag{F2}
\]

Les deux compléments sont réellement premiers, mais \(n_1<n_0\). Le principal analogue est positif. On ne peut oublier la direction \(p-2\) pour conserver le bénéfice X6 ; l'identité générale garde le signe de son logarithme.

### 9.3 Parent non couvert malgré le bon semipremier

\[
c=3,\ p=3229,\ q=3343,\quad p-2=7\cdot461,\quad
n_0=67616359\ {\rm premier},\quad n_1=67636417\ {\rm composite}.
\tag{F3}
\]

La factorisation et les coupes sont correctes, mais il n'y a pas de vertex image de l'axe premier. La promotion « tout parent à bonne factorisation reçoit une image première » est fausse. Ce parent reste dans \(J2\setminus P\), sans paiement.

### 9.4 Omission de la tail : falsificateur réel du deuxième modèle

Au downward F1,

\[
R_0=10618,\quad R_1=10611.
\]

La tail de X7 possède exactement les deux termes unitaires non nuls

\[
T=-\frac1{10612}\log(10613/m_0)
  +\frac1{7076}\log(10617/m_0).
\tag{F4}
\]

Les autres entiers de \(10611<k\le10618\) sont nonunitaires. Le reçu certifie strictement \(T<0\). La formule raccourcie \(W_1-W_0=\log(m_0/m_1)A_N(R_1)\) est donc fausse : elle diffère de X7 par la tail non nulle, avec son signe de soustraction. \(k=1\) reste dans le préfixe commun. Il n'y a pas de face gratuite.

### 9.5 Vérifications finales et portée

Le nouveau banc a vérifié les factorisations, toutes les gardes, les préfixes courts réels, X4/X5 avec les véritables \(D_a,W_a\), X7 comme identité de polynômes logarithmiques rationnels, les deux fronts stricts et leur tail, le joint \(k=1\), la paire réelle positive de F1 et le principal de F2. Aucun ancien banc PASS n'a été relancé.

Ces signes finis ont des certificats rationnels stricts. Les quatre ERROR_FALSIFIER sont attachés aux promotions fausses de signe, de direction, de couverture et de tail gratuite ; ce ne sont pas des erreurs Lean. Le statut numérique est **PASS_NEW_CROSS_KERNEL_EXCHANGE_IDENTITY_ONLY**, et celui de X7 est **PASS_NEW_LITERAL_TWO_FRONT_W_IDENTITY_ONLY**. X8–X18 sont des dérivations écrites indépendantes ; ces PASS ne sont pas une certification Lean ou analytique de la cible.

Bindings finaux relus :

- exchange_checks.py : **cdb1721ce1da9e92485c337f94fe5ce9410856b34b73ac2898cd4a8155c22264** ;
- exchange.json : **d120360aeebf570b9cf75ca0922070bd40e750607e77d8362a8fff636eb6352d** ;
- numerical_replay.json : **73b8b29449601032016218afa9a49873925426b9d32efe33393fe312a3163b3c**, annoncé par le rôle 6 comme rejeu isolé champs et octets identiques.

## 10. Premier contrat utile de formalisation et décision de portée

Une formalisation utile candidate doit dériver, sur les objets arithmétiques actuels :

- la classification réelle des diviseurs courts X2, les deux égalités X3 et les signes Möbius de \(m_0,m_1\), à partir de primalité/distinction/coupes ; aucune hypothèse libre donnant \(C_0,C_1\) ;
- le raccord source entier X4 et la paire réelle X5, sans perdre les unités, \(Q\), les fronts ou \(k=1\) ;
- la différence des vrais modèles X7, après la preuve du masque identique sous les deux primalités \(n_i>Q\) ;
- si l'étape est sélectionnée, la canonicalité/injection parent et image par factorisation entière.

Ces identités contribuent au paiement **partiel** X18 : elles relient une demande J2 à une capacité J1 de signe contraire et à un défaut quantitativement contrôlé. Elles sont plus que la convolution standard seule ou une permutation conservative. Elles ne prouvent cependant aucune minoration de \(K\), aucune estimation du reste de X19, ni \(D_N\le N/(256u\ell)\).

Les bornes X8–X18 devront être auditées/formalisées séparément si une certification analytique est exigée ; aucun nouvel axiome analytique ne les remplace. Le rôle 1 n'écrit ni ne compile du Lean avant la décision du coordinateur et le gate numérique final.

Statut actuel : **NOUVELLE_ANTISYMETRIE_ARITHMETIQUE_ET_COMMUTATEUR_PAYABLE_PARTIEL_ECRIT** ; **PROMOTION_SIGNE_REEL_SANS_DEFAUT_REFUTEE** ; **COUVERTURE_PREMIERE_UNIVERSELLE_REFUTEE** ; **COMPENSATION_GLOBALE_NON_OBTENUE** ; **VICTOIRE_FAUSSE**.
