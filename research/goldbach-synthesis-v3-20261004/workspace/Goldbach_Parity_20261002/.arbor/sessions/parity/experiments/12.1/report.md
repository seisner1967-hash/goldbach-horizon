# Agent 4 — audit du Gram pondéré et du paiement des propres puissances

Boucle 9, 2 octobre 2026. Le rapport 2 final `agent2_weighted_operator.md` est gelé, SHA-256 `43bd75aa25f7ef905936ee10405e05442fbeb48283cf6576cb273c9f8b8c3d8a`. `PROBE_BLOCK.md`, le verdict 8 et son audit R1–R16 ont été relus. Le rôle 6 final a été confirmé par root avant la lecture de son script et de ses reçus définitifs. Seul le présent fichier est écrit ; les 307 artefacts antérieurs, les autres rôles et Arbor restent inchangés.

**Verdict : paiement écrit arithmétique indépendant W12 validé dans son domaine, moment premier W13 non estimé, victoire fausse.** W1–W7 sont des identités standard exactes du bracket entier. W8–W12 donnent réellement `|B_pp|<=N/(1024*u*ell)` dès `u=log N>=65536`, sans constante inconnue ni petite énergie postulée. Ce paiement porte les propres puissances du **premier axe n**, pas une suppression de celles-ci. Il demeure une déduction mathématique écrite, non une certification Lean. Compiler seulement l'identité d'énergie ou une conséquence d'un W11 supposé ne certifierait pas ce paiement arithmétique complet et ne satisferait pas la victoire.

## 1. Objet exact, domaines et deux fronts

N est un entier pair ; dans le domaine W12, N>256, u>1 et ell=log u>0. On conserve les mêmes alpha=ceil(N^(1/4)), Q=floor((N-1)/alpha), H=floor(N^(3/8)) et `J={2<=k<=Q:gcd(k,N)=1}`. Tous les nombres dans log et les puissances réelles sont leurs valeurs réelles positives. Pour N>=256, N^(1/8)>=2, donc `floor(N^(3/8))>=ceil(N^(1/4))` ; H>=alpha est légitime à l'onset étudié. Au banc N=10^8, H=1000 et alpha=100 sont **distincts**.

Le bracket de R16 est `B=P_tail^{>=2}-M^{>=2}`. Le physique seul est coupé à r>H ; **le modèle k>=2 reste entier au front alpha**, jusqu'à Q. Le retrait conjoint de k=1, P1=M1, est déjà réalisé avant R16 ; il n'est pas refait sur chaque morceau. Les seuils BV de tête restent non évalués. Le pont global garde I et `2max(e,0)`.

Avec `n=N-m`, `1<=m<=N-2`, et `L_N(n)=Lambda(n)1_(n>1)1_(gcd(n,N)=1)`, W1 conserve

`t_k=1_(k|m,H*k<m)`,
`h_k=1_(alpha*k<m,gcd(k,n*N)=1)/phi(k)`,
`a_k=log(m/k)*(t_k-h_k)`, `K_H=sum_(k in J)mu(k)*a_k`.

Sur un front actif, m/k>alpha>=1 ou m/k>H, et `0<log(m/k)<=u`. Sur un front inactif, le coefficient correspondant est zéro ; un log signé hors front n'ajoute aucun terme. Phi(k)>0 pour k>=2. Le domaine m<=N-2 impose n>=2 ; n=1 et ses faux prolongements ne sont pas introduits.

## 2. W2 précède le masque carré-libre du Gram

La bascule acquise est exacte pour tous k,r positifs :

`mu(k*r)*mu(k)=mu(k)^2*mu(r)*1_(gcd(k,r)=1)`.

Sur L_N(n) non nul, m=N-n est unité à N. Si k|m, k et r=m/k sont unités à N ; k est aussi unité à n. Le détecteur H*k<m devient exactement r>H. Avec les caps et les unités conservés, on obtient W2 :

`B=sum_(m=1..N-2)mu(m)*L_N(N-m)*K_H(m)`.

Cette réécriture concerne le **bracket entier après le raccord acquis**, pas directement le profil fII raw ni une tête coupée en b. Le modèle a déjà mu(m) dans cette expression ; m non carré-libre annule conjointement ses coefficients. Aucun mu(n)² n'est ajouté. Le point m=311 distingue justement le raw F_N actif et le nouveau poids Lambda_N nul.

W3 est l'identité de fronts exacte

`t-h = 1_(H*k<m)[1_(k|m)-1_unit/phi(k)]`
`      -1_(alpha*k<m<=H*k)*1_unit/phi(k)`.

H>=alpha justifie cette partition ; l'égalité m=H*k appartient à la bande de modèle, l'égalité m=alpha*k n'est pas active. Remplacer le front du modèle par H abandonnerait la seconde ligne. Les colonnes du modèle jusqu'à Q restent, même quand elles n'ont aucun physique long.

## 3. W4–W7 : mesure positive, diagonales et quatre composantes

**Après** W2 seulement, poser `w_m=L_N(N-m)*mu(m)^2`, A_N=sum w_m et `Gamma_(k,k')=sum w_m*a_k*a_k'`. Ces poids sont positifs. Puisque mu(m) appartient à {-1,0,1}, mu(m)^3=mu(m), donc

`B=sum w_m*mu(m)*K_H(m)`,
`mu^T Gamma mu=sum w_m*K_H(m)^2`,
`|B|²<=A_N*(mu^T Gamma mu)`.

La norme du vecteur interne dans Cauchy est bien A_N : `sum w_m*mu(m)^2=sum L_N*mu(m)^4=A_N`. Les vecteurs extérieurs restent les **vraies** valeurs mu(k). Les indices k non carrés-libres peuvent avoir une colonne modèle, mais leur coefficient mu(k) est nul ; aucune fausse identité de colonne n'est nécessaire.

W6 conserve `DD-DM-MD+MM`, avec les deux logarithmes et les poids réels dans chaque terme. DD requiert m multiple de lcm(k,k'), non du produit si les modules ont un facteur commun ; il conserve les deux fronts H. DM et MD gardent chacun H et alpha ; MM garde les deux fronts alpha et les deux facteurs phi. Les diagonales k=k' valent `sum w_m*a_k²`, généralement positives ; elles ne disparaissent pas par orthogonalité. Ni DD-MM ni une lecture de DD comme signe du premier moment n'est autorisée.

Dans HH, les quatre Möbius, les deux copies de leurs vrais coefficients, les produits issus de factorisations distinctes, le CRT a*r, les unités et les faces doivent encore être conservés. W4–W6 ne sont pas une diagonalisation de ce développement ni une identification avec D00, Da ou Dk. Les phases natives q|k restent égales à1 sur le physique. Le modèle indépendant ne se remplace pas par une énergie positive.

La partition W7 est exacte : Lambda(n) est non nulle seulement sur n=p^j, base p première. Les n premiers j=1 et propres puissances j>=2 forment deux ensembles disjoints, avec les mêmes unités. Cela donne B=B_prime+B_pp, Gamma=Gamma_prime+Gamma_pp, A_N=A_prime+A_pp. Le paiement de B_pp porte le **premier moment** ; il n'est pas une hypothèse de petite taille de Gamma_prime ou une certification du signé par positivité.

## 4. W8 : moment harmonique avec constante 3

L'identité

`1/phi(k)=1/k*sum_(d|k)mu(d)^2/phi(d)`

vient du produit local `1+1/(p-1)=p/(p-1)`. En échangeant les deux sommes finies pour Q>=1, le nombre harmonique intérieur est au plus 1+log Q. La somme restante est majorée par le produit **fini** sur p<=Q,

`product_(p<=Q)(1+1/[p(p-1)])`.

Les termes carrés-libres d<=Q constituent une sous-somme positive de ce produit, même lorsque ses produits de premiers dépassent Q. Puisque `1+x<=exp(x)` et

`sum_p 1/[p(p-1)] <= sum_(j>=2)1/[j(j-1)] = 1`,

le produit est au plus e<3. Q<=N donne donc

`sum_(k<=Q)1/phi(k) <= e*(1+log Q) <3*(1+u)`.

Ce passage peut être effectué entièrement avec des produits finis ; il n'exige pas une formule d'Euler infinie supplémentaire. Les +1 sont ceux du majorant harmonique, pas une erreur de progression oubliée.

## 5. W9 : constante divisorielle universelle vérifiée

Pour z>=1, factoriser z en produit des p^a. Si p>=256, l'inégalité entière `a+1<=2^a` vaut pour a>=0 et `2^a<=p^(a/8)` ; aucun facteur constant n'est payé.

Pour 2<=p<256, le facteur normalisé vérifie

`(a+1)*p^(-a/8) <= sum_(j>=0)(j+1)*p^(-j/8)`
`=(1-p^(-1/8))^(-2)<256`.

La série est convergente puisque p>1. La constante est contrôlée en entiers : `15^8=2562890625 >2147483648=2^31`, donc `2^(-1/8)<15/16`. Ainsi `p^(-1/8)<=2^(-1/8)<15/16` et l'inverse carré est <256, uniformément en a. Il existe au plus 255 petits premiers distincts sous 256, en les majorant même par les entiers possibles ; cette borne est volontairement grossière mais sûre. Le produit des constantes est au plus

`256^255=2^2040`.

La formule produit pour tau(z) donne donc **tau(z)<=2^2040*z^(1/8)**, y compris z=1. Les exposants a ne sont pas artificiellement limités. Il n'y a ni C_epsilon caché ni majorant polylogarithmique uniforme erroné.

## 6. W10–W11 : paiement positif du premier axe properpower

Si n=p^j<N et j>=2, p>=2 impose `j<u/log2`, donc le nombre d'exposants autorisés est au plus u/log2. Pour chaque j, le nombre de bases entières, et a fortiori de bases premières, est au plus sqrt(N). Chaque Lambda(p^j)=log p<=u. Par comptage positif,

`sum_(n<N,n=p^j,j>=2)Lambda(n) <=sqrt(N)*u²/log2`.

Les unités et le domaine n<=N-1 ne font que réduire ce compte. Une éventuelle duplication du comptage serait une surmajoration positive ; les représentations à base première sont en fait uniques. Aucun théorème de distribution de primes n'est utilisé.

Pour un tel n admis, m=N-n>=1. Le physique long comporte au plus tau(m) diviseurs k ; `|mu(m)mu(k)|<=1` et tout log actif est <=u. Sa masse absolue est au plus `u*tau(m)*Lambda(n)`. Le modèle **entier**, avec son front alpha, a masse au plus `u*Lambda(n)*sum_(k<=Q)1/phi(k)`. Ses unités et fronts sont abandonnés seulement dans cette majoration positive.

Puis m<=N et W9 donnent W11 :

`|B_pp| <=sqrt(N)*u³/log2*[2^2040*N^(1/8)+3*(1+u)]`.

Ce bound concerne la différence réelle physique-modèle en payant les deux masses ; aucune petite énergie n'est invoquée. Le grand facteur divisoriel porte **m**, le second axe, tandis que le poste compté porte les propres puissances de **n**, le premier axe. Les deux objets ne sont pas intervertis.

## 7. W12 : audit indépendant de chaque constante du seuil

Supposer u>=65536. Tous les dénominateurs sont positifs. On utilise

`log2>=1/2`, `log2<1`, `ell=log u<=u`, `1+u<=2u`,
`log u<=u/4096`, `2040<=u/32`.

Le rapport log(u)/u est décroissant pour u>=65536, car sa dérivée est `(1-log u)/u²<0`. À 65536=2^16, `log(65536)=16log2<16=65536/4096` ; la borne log u<=u/4096 suit pour toute cette demi-droite. L'inégalité 2040<=u/32 est vraie puisque 65536/32=2048. Les logarithmes des constantes 2048 et 12288 sont tous deux <16, car ces deux entiers sont <65536.

Diviser W11 par le budget positif N/(1024u ell), utiliser ell<=u et 1/log2<=2, puis 1+u<=2u, donne exactement

`2048*u^5*2^2040*exp(-3u/8)`
`+12288*u^6*exp(-u/2)`.

Puis `2^2040=exp(2040log2)<=exp(u/32)`. Le logarithme du premier terme est majoré par

`(1+5+128-1536)*u/4096 = -1402*u/4096`.

Celui du second est majoré par

`(1+6-2048)*u/4096 = -2041*u/4096`.

Ces deux exposants sont <=-u/4. Leur somme exponentielle est donc <=2exp(-u/4)<1 : u/4>=16384, en particulier u/4>=1, et e>2 suffit. La constante 1024, les puissances de u et les deux exposants affichés sont corrects. On obtient bien

**`|B_pp|<=N/(1024*u*ell)` dès u>=65536.**

Le seuil source u>=10^24 implique ce seuil sans une calibration BV ni une constante de densité supplémentaire. N=10^8 ne le satisfait pas ; les essais finis ne certifient pas ce paiement asymptotique. Le minorant qualitatif de tête ou une borne classique BV garde son propre seuil, distinct de cette déduction élémentaire.

## 8. Témoins et portée exacte du reçu numérique final

Le script gelé `new_contract_checks.py` a SHA-256 `e0b8fb5a56757b7773d8be30365d78af36aa7ab7aa6b999735923dfc0bc79b1c` ; son JSON final a SHA-256 `ac5bad36c2527886c6f3ac10150aa44c8f20550d683ef5a0eedab5160a60271d`, confirmés par lecture locale après le signal final de root.

Pour W1–W7, la sélection est précisément m={303,311,323,658911,112211}, J={3,7,11,13}, alpha=100 et H=1000. Les logarithmes restent des polynômes symboliques à coefficients rationnels. Le script compare B à sa mesure pondérée, la contraction de Gamma à la somme des carrés et DD-DM-MD+MM à cette même énergie. Il conserve les diagonales et n'assume ni rang un ni petite énergie.

* **m=311** : n=113*199*4447 est composite ; Lambda_N(n)=0. Son raw peut être actif, mais pas ce poids Mangoldt. La fausse suggestion première est conservée comme falsificateur distinct.
* **m=323=17*19** : mu(m)=1 et n=99999677 premier. Pour k=3, alpha*k<m<=H*k et gcd(3,n*N)=1 ; t3=0, h3=1/2. La diagonale `log(n)*log(323/3)^2/4` est strictement positive. Supprimer la bande de modèle W3 perd ce point.
* **m=658911=3*11*41*487** : mu(m)=1, n=9967² est admis, Lambda_N(n)=log9967 et mu(n)²=0. Le poste properpower et Gamma_pp conservent ce poids ; un nouveau filtre sur n le détruirait. Le k=3 physique actif conserve sa phase native 1.
* **m=112211=11*101²** : mu(m)=0 tandis que n=99887789 est premier. W2 et w_m sont nuls. Cette origine du masque m est légitime après W2 ; elle ne supprime pas les termes non nuls de la tête coupée et de sa queue antérieures.

Le reçu couvre aussi l'autre piste de nouvelle face : son V1 sans unité de k est falsifié au n=2, r=161, k=621118 ; la correction V2 conserve Lambda_N ou l'unité de k. Ce défaut de support n'est pas dans W1–W15, qui conserve J et L_N. Les deux statuts d'identités corrigées ne remplacent pas ces deux falsificateurs initiaux. Les contrats analytiques W8–W12 sont explicitement **non testés** par le banc. Le registre et son rejeu isolé relèvent du rôle 6 puis du Juge ; aucune compilation Lean n'y est appelée.

## 9. Contrat Lean admissible et moment restant W13–W15

Un vrai certificat auxiliaire W12 devrait définir le bracket properpower avec les valeurs arithmétiques mu, Lambda, phi, les caps alpha,Q,H, les unités et les deux fronts exacts, puis prouver les majorants W8–W10 et leur insertion W11–W12. Un théorème qui suppose la masse W11, ou une énergie assez petite, ne certifierait pas tout ce paiement. Le présent rôle conserve donc la déduction écrite auditée sans produire un Lean générique de substitution. Aucun sorry, axiome neuf ni erreur de compilateur fictive n'est introduit. W12 est un progrès auxiliaire véritable ; il ne constitue pas un mécanisme de parité gagnant.

Le moment non estimé reste exactement

`B_prime=sum_(N-m premier)mu(m)*log(N-m)*1_(gcd(N-m,N)=1)*K_H(m)`

avec les domaines m=1..N-2 et J originaux, les deux fronts et le modèle entier. Son énergie W14 reste la somme positive réellement pondérée, sans hypothèse de petite taille. Les diagonal et mixed moments, les modules lcm au-delà d'un niveau BV, les colonnes modèle jusqu'à Q, les coefficients de Möbius et les quatre signes HH ne sont pas contrôlés par l'identité de Cauchy. Les préfixes multiplicatifs acquis à masque fixe ne deviennent pas gratuitement des estimations de mu(r)Lambda(N-k*r).

Le raccord final W15 conserve

`D_N=P_head^{>=2}+B_prime+B_pp+I+2max(e,0)`.

W12 paie un seul poste, sans doubler I ni retirer le bridge. Le gain de tête garde sa calibration, B_prime garde sa compensation physique-modèle manquante et 2max(e,0) garde son budget. Classification : **`ANALYTICAL_PARTIAL_PROPERPOWER_PAYMENT`**, avec **`GLOBAL_SIGNED_BOUND_NOT_OBTAINED`**, **`LEAN_CERTIFICATION_NOT_PRODUCED`** et **`VICTORY_FALSE`**. Les identités d'énergie seules ne sont pas soumises comme candidature gagnante.
