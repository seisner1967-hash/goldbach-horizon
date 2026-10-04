# Agent 3 — audit de formalisation, couverture complète, boucle 7

**Verdict : identité exacte acceptée, queue de Mellin payable, gain signé non obtenu.** La couverture logarithmique du nœud 9.1 répare réellement le défaut d'incidence de la boucle 6. Son identité n'est pas falsifiée. Le paiement absolu séparé de son secteur l=1 est en revanche incompatible, éventuellement sur la sous-famille étudiée, avec le budget cible. Aucun fichier Lean standard auxiliaire n'est ajouté, aucune compilation n'est alléguée et aucune erreur Lean n'est fabriquée.

## 1. Profil arithmétique et faces conservés

J'ai lu `agent1_complete_coverage.md`, les versions disponibles de `logarithmic_checks.py` et `logarithmic.json`, ainsi que les définitions et la Lemma 10.1 de la monographie. Les rapports et les pièces jointes sont des sources ; la condition de victoire demeure celle demandée par l'utilisateur.

Le profil utilisé est le profil quartique, alpha=ceil(N^(1/4)) et Q=floor((N-1)/alpha). Avec m=N-n, ses noyaux réels conservent k<=Q, alpha*k<m, et respectivement k|m ou gcd(k,nN)=1. Leur préfixe harmonique est min(Q,floor((m-1)/alpha)). Le profil raw est

```
F_N(m)=1_(0<m<N)1_(N-m>1)1_(gcd(N-m,N)=1)
       [Lambda(N-m)-log(N-m)] [D(m)-W(N-m,m)].
```

Aucun facteur mu(N-m)^2 n'y est ajouté. Les puissances premières propres du premier axe ont toujours fII(p^j)=-(j-1)log p. Les masques, les noyaux et leurs fronts sont réévalués à chaque argument p^j*l ou p*l ; ils ne deviennent pas des masques constants du cofacteur l. F_N(m)=0 pour m<=alpha découle exactement de la face stricte : même k=1 n'est pas admis.

L'audit conserve le scalaire complet et son pont : S_full=sum_(1<=m<N)mu(m)F_N(m), S_full=-E_cov+e+S_unc et D_N=-S_full+2max(e,0). Un calcul numérique de S_X ne calcule pas la queue X<m<N.

## 2. Convolution complète et cancellation des puissances

Pour m>1, la convolution standard est

```
mu(m) log m = -sum_(d|m) mu(m/d)Lambda(d).
```

Elle donne, puisque Lambda(d) ne porte que les puissances premières,

```
S_full = -sum_(p^j*l<N, p prime, j>=1, l>=1)
              mu(l) log p/log(p^j*l) F_N(p^j*l).       (L1)
```

Toutes les sommes sont finies. Le terme m=1 est zéro par le noyau réel, et tous les dénominateurs restants sont strictement positifs. La division par log m n'est donc pas une opération formelle illégitime. La condition p^j*l<N est stricte, contrairement au front inclusif p^j*l<=X d'une tête S_X.

La réduction exacte aux seuls premiers est également correcte :

```
mu(m)log m = -sum_(p|m, p prime, p∤m/p) mu(m/p)log p,
S_full = -sum_(p*l<N, p prime, p∤l)
              mu(l)log p/log(p*l) F_N(p*l).           (L2)
```

Si m est carré-libre, chaque quotient m/p est premier à p, mu(m/p)=-mu(m), et la somme des log p vaut log m. Si q^2|m, le premier q est exclu et tous les autres quotients conservent q^2 ; leurs coefficients Möbius sont nuls. C'est une preuve de cancellation, pas une suppression des puissances premières. Le coefficient mu du second axe conserve son support réel, sans filtrer le premier axe.

Dans L1, pour m=p^a avec a>=2, les deux seuls coefficients Möbius non nuls sont ceux de j=a-1 et j=a : -log p et +log p. Ils s'annulent au même argument m. Garder seulement j=1 sans imposer p∤l serait faux. Dans L2, la couverture d'un m carré-libre est exactement sum_(p|m)log p/log m=1. Un m premier reçoit donc tout le poids au tuple l=1.

La troncature p<=Y crée bien le défaut R_Y écrit dans L3. Les m non carré-libres y sont annulés par leur coefficient mu(m), mais un premier m>Y garde le poids entier 1. Ce défaut ne peut pas être oublié au motif que la couverture complète était exacte.

Les reçus finis L1 et L2 vérifient des coefficients logarithmiques avant division par leur dénominateur commun positif ; cela suffit pour leur égalité numérique exacte. Mon contrôle supplémentaire en lecture seule confirme L2 sur les 19 999 entiers 2<=m<=20000, avec 41 120 termes premiers admissibles, et son insertion dans le profil pour les 1 023 arguments 2<=m<=1024. Les témoins m=303, 311, 841 et 10201 ont la portée indiquée par l'Agent 1. Le reçu ne calcule ni S_full ni son seuil analytique.

## 3. Paiement indépendant de la queue de Mellin

Posons A(t)=sum_(p^j*l<N)mu(l)log p F_N(p^j*l)(p^j*l)^(-t). Pour m>1, l'intégrale de m^(-t) sur t>=0 vaut 1/log m. L1 donne donc S_full=-integral_0^infinity A(t)dt. La permutation est une permutation de sommes finies et d'intégrales convergentes de chacun des termes. Avec S(t)=sum_m mu(m)F_N(m)m^(-t), on a exactement A(t)=S'(t). La représentation n'est ainsi pas, à elle seule, un nouveau gain sur le moment signé.

La queue t>=T possède cependant un majorant indépendant valide. Pour tout m>1,

```
sum_(d|m) Lambda(d)|mu(m/d)| <= log m,
|integral_T^infinity A(t)dt| <= sum_m |F_N(m)|m^(-T).
```

La norme réelle de la boucle 6 est ||F_N||_2^2<=20u^4(N-1)(1+u)^3, avec u=log N. Cauchy donne sum|F_N|<=sqrt(20)u^2(N-1)(1+u)^(3/2). Comme F_N est nul jusqu'à alpha, on peut utiliser alpha^(-T) comme facteur supérieur. Posons ell=log u et

```
B=1024 sqrt(20)u^3(1+u)^(3/2)ell,
T=(4/u)log B.
```

Sous u>1 et B>1, T>0 et alpha>=exp(u/4). On obtient exactement

```
alpha^(-T) <= 1/B,
|integral_T^infinity A(t)dt| <= (N-1)/(1024u ell)
                             <= N/(1024u ell).
```

Les constantes se simplifient sans supposer la cible. Il s'agit d'une preuve mathématique écrite, pas d'un théorème Lean validé. Le morceau 0<=t<T demeure : au tuple l=1 de L2, il reçoit le poids 1-p^(-T). Puisque T=(18ell+4log ell+O(1))/u, les premiers de taille comparable à N gardent presque tout leur poids dans ce morceau. La queue payable ne supprime pas ce secteur.

## 4. Audit du minorant du secteur l=1

Définissons C1=sum_(p<N, p prime)F_N(p) avec les unités déjà dans F_N. L2 donne S_full=-C1+S_rest, puis

```
D_N=C1-S_rest+2max(e,0).                              (L6)
```

Le minorant proposé **C1>=N log N/384 éventuellement**, pour N pair et 3∤N, est cohérent avec les inputs conservés. Il n'est pas un contrôle de D_N. Voici l'audit des constantes et de l'uniformité.

### Préfixe quartique réel et masque polynomial

Pour p>=N^(1/3), alpha<=2N^(1/4) et les inégalités de partie entière donnent R=min(Q,floor((p-1)/alpha))>=N^(1/12)/4 pour N suffisamment grand. La présence de Q ne crée pas une petite longueur concurrente : Q est d'ordre N^(3/4), bien plus grand que cette borne inférieure. Par conséquent

```
log R >= u/12-log4 >= u/13 pour u>=156log4,
K=(N-p)N < N^2 <= R^26.
```

Sur les arguments actifs n=N-p>1, K est positif et pair. Les autres arguments ont F_N=0. Le masque de la Lemma 10.1 satisfait donc bien son hypothèse à exposant fixe 26. Le passage n'utilise pas l'exposant ni la hauteur eighth de Theorem 10.2.

L'endpoint exact doit rester écrit :

```
W(N-p,p)=W_K(R)+log(R/p) A_K(R).
```

Ici |log(R/p)|<=u, car 1<=R<p. Avec le D fixé de la Lemma 10.1, les deux erreurs logarithmiques après cette multiplication sont O_D(u^(2-D)). Le coût exponentiel est au plus O((1+u)exp(-u/52+c sqrt(2u+log2))). Un choix fixé D>2 suffit donc pour o(1), uniformément sur les p concernés. Les constantes implicites ne sont pas évaluées ici. On obtient W(N-p,p)=-S(K)+o(1) avec l'endpoint payé, pas supprimé.

### Taille du produit singulier et signe des grands premiers

Le masque réel K<N^2 permet S(K)=O(ell). Dans son produit, la partie p<=u est O(log u) par le produit ordinaire de Mertens et une correction quadratique convergente. Pour p>u, il existe au plus 2u/ell premiers distincts divisant K ; pour u assez grand, log((p-1)/(p-2))<=2/p<=2/u. Leur produit est donc au plus exp(4/ell). Cette preuve est uniforme en K.

Pour p>alpha, D(p)=-log p exactement : seul k=1 est actif. Pour p>=N^(1/3), log p>=u/3, et S(K)+o(1)<=u/12 éventuellement. Ainsi D(p)-W(N-p,p)<=-u/4. Comme Lambda(n)-log n<=0 pour n>1, F_N(p)>=0 pour tous ces grands premiers unitaires ; les points non unitaires sont déjà nuls.

### Comptage positif au module fixe 3

Prenons p dans [N/3,N/2] et p congru à N modulo 3. Les deux classes possibles sont réduites puisque 3∤N. Alors n=N-p est divisible par 3 et n>=N/2. Il n'est pas premier pour N grand. S'il est une puissance première, sa base est 3 ; dans tous les cas Lambda(n)<=log3. Donc log n-Lambda(n)>=u-log6>=u/2 éventuellement, et F_N(p)>=u^2/8 sur les points unitaires.

Le PNT aux classes fixes modulo 3 donne, pour chacune des deux classes, un comptage asymptotique N/(12u) dans cet intervalle. Cela suit par différence des deux fonctions de comptage ; c'est plus fort que la seule infinitude ou la densité de Dirichlet. Une source primaire pédagogique de l'énoncé utilisé est [Kedlaya, PNT en progressions, théorème 4.12](https://kskedlaya.org/ant/chap-primes-in-ap.html). Prendre le maximum des deux seuils couvre la classe dépendant de N.

Pour rendre la marge numérique explicite dans cette dérivation qualitative, choisir éventuellement au moins N/(16u) premiers avant les exclusions. Un premier diviseur de N dans [N/3,N/2] ne peut être que N/3 ou N/2 ; le premier est exclu par 3∤N. Retirer au plus un point laisse au moins N/(24u) dès que N/(48u)>=1. En fait, le possible endpoint N/2 ne satisfait pas la congruence choisie pour cette sous-famille ; la perte d'un point est donc une marge conservatrice valide. La contribution positive retenue est au moins (N/(24u))(u^2/8)=Nu/192.

### Petit secteur et constante finale

Les p<N^(1/3) peuvent coûter au plus N^(1/3)sup|F_N|. L'enveloppe uniforme réelle de la boucle 6 donne

```
N^(1/3)sup|F_N|
 <= u^2[2N^(5/6)+3N^(1/3)(1+u)] = o(Nu).
```

Cette quantité est <=Nu/384 éventuellement. Tous les autres grands premiers sont non négatifs. On obtient donc C1>=Nu/192-Nu/384=Nu/384. Le rapport au budget cible est >=(2/3)u^2 ell, qui diverge.

Ce minorant possède un seuil qualitatif **non évalué ici**. Aucune effectivité du seuil n'est revendiquée dans cet audit, et aucune validité dès u=1024 ou à N=10^8 n'en découle. Cela ne signifie pas que le PNT au module fixé 3 serait intrinsèquement inefficace ; aucun lower sieve à seuil inefficace n'est nécessaire à cette dérivation. Son seuil global doit encore intégrer les constantes de Lemma 10.1, le signe du noyau, les deux marges PNT et la petite queue. Le résultat reste mathématique écrit et non certifié Lean.

## 5. Portée du rejet et contrat du prochain regroupement signé

La couverture complète L1/L2 est acceptée. Le paiement L5 de la queue de Mellin est accepté. Le raccourci « le secteur l=1 est une petite erreur absolue » est rejeté éventuellement sur la sous-famille N pair, 3∤N, car C1 est alors positif et d'ordre au moins Nu. Ce rejet ne concerne pas toute couverture complète, ni une compensation future de C1 par S_rest.

Les préfixes acquis de mu(l)chi(l) avec masque multiplicatif fixe ne majorent pas automatiquement le coefficient réel fII(N-pl)[D(pl)-W(N-pl,pl)]. Ce coefficient garde son couplage additif, ses unités et ses fronts mobiles. Au point l=1, aucune somme de Möbius n'existe à laquelle appliquer un gain de préfixe. Une estimation absolue indépendante de ce point est trop coûteuse ; sa compensation doit venir d'une information signée.

Un futur candidat admissible doit donc produire un regroupement exact et **une estimation arithmétique indépendante** de la différence C1-S_rest, tout en conservant les premiers longs, p∤l, les puissances propres du premier axe, les fronts, les raccords HH/raw et le terme 2max(e,0). La condition de fermeture reste

```
C1-S_rest+2max(e,0) <= N/(256u ell).
```

Il serait circulaire de l'introduire comme hypothèse du prochain théorème, ou d'introduire une hypothèse de corrélation équivalente. La nouvelle identité doit expliquer et prouver la compensation utile, pas simplement recombiner les mêmes termes sous un autre nom. Dans la formulation de Mellin, si H_T=-integral_0^T A et E_T=-integral_T^infinity A, le budget de queue laisse l'obligation suffisante -H_T+2max(e,0)<=3N/(1024u ell). Elle doit elle aussi être démontrée indépendamment.

La condition de victoire n'est donc pas atteinte par la compilation éventuelle de la convolution standard seule. Les étapes requises pour une soumission gagnante restent : un mécanisme réel sur la contribution r>alpha, ses estimations signées avec constantes et domaine exacts, puis une preuve Lean sans balise d'admission ni nouvel axiome analytique postulant ce gain.

## 6. Traçabilité

Empreintes relevées pendant le contrôle final disponible de ces entrées :

```
agent1_complete_coverage.md 309195a841c1da3dfeebde518def34c07cc781df240eea9f5a797be02d001b00
logarithmic_checks.py       eb122b2c44e52a053c38d09ad6e3b7c3abe2167bed2c6c23fbc78b62baba789a
logarithmic.json            00f7d0faf027e3b8f31844e4af9042cc2983eaf34aff91994f85af56dbba40d9
```

Le registre round7, chargé explicitement par son chemin pour éviter toute confusion avec un module homonyme de round6, confirme les **190 artefacts antérieurs inchangés** ; empreinte du registre 900367574d957bfe8e48341ca532022fc0e742d5a001099e3d402863e467de61. Le présent rôle ajoute seulement ce rapport. Le Juge doit auditer les versions finales des reçus indépendamment ; aucun résultat numérique n'est assimilé à une preuve Lean, et le compte de théorèmes Lean ne doit pas augmenter avec cet audit.
