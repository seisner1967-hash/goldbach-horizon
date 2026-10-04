# Boucle 9 — Gram réellement pondéré et poste properpower effectif

Agent 2, 2 octobre 2026. Seul ce rapport est écrit. `round9/PROBE_BLOCK.md`, le retour final de boucle 8, les contraintes courantes et ses audits ont été lus. Les acquis, fichiers antérieurs et Arbor restent inchangés.

**Trois niveaux distincts.** Le Gram physique-modèle fusionné ci-dessous est une identité exacte standard, sans gain déduit de sa positivité. Une information arithmétique indépendante paie effectivement les propres puissances premières du PREMIER axe : au seuil source u>=10^24, leur contribution au bracket R16 vaut au plus N/(1024u ell). Le moment restant sur le premier axe PREMIER est encore non estimé. Aucun mécanisme complet de victoire, nouvel axiome analytique ou fichier Lean de substitution n'est proposé.

## 1. Premiers principes et quatre lignes

L'oscillation réellement restante est mu(r) dans le physique long, ou mu(m) après réécriture entière du bracket. Lambda(N-kr) est un poids arithmétique mobile ; aucun préfixe de Möbius fixe ne le remplace. La phase native vaut 1 sur les fibres q|k et ne crée aucune oscillation indépendante. OldPq, les facteurs locaux principaux et les diagonales acquis à la boucle 8 sont conservés, non reprouvés.

La compensation physique-modèle doit être réalisée avec les mêmes points avant une norme. Ici le physique est coupé à r>H, mais le modèle M^{>=2} demeure ENTIER avec le front alpha. Retirer ce décalage de fronts déplacerait le reste dans un défaut invisible. Le nœud de tête de la boucle 8 est déjà payé qualitativement ; cette piste n'en refait pas la bascule.

Le contre-exemple dépassé est la séparation factice du profil couplé : le vrai mineur L2 h=3,13 est non nul, et le Gram nu ne s'applique pas. On garde donc le poids prime/Mangoldt dans le Gram même, et toutes ses quatre composantes DD,DM,MD,MM. Les exemples de la coupe b de R7 restent acquis : mu(m)^2 ne peut pas être introduit dans une tête coupée. Il sera justifié ici seulement APRÈS réécriture du bracket entier avec mu(m).

Mechanism: Fusion du physique long et du modèle entier dans un Gram réellement pondéré, avec retrait indépendant des propres puissances premières du premier axe.
Hypothesis: Le bracket R16 admet un noyau exact commun après sa réécriture entière avec mu(m) ; le poste properpower est payé par tau(n)<=2^2040*n^(1/8), mais la projection signée sur l'axe premier reste à estimer.
Observable: Identité DD-DM-MD+MM avec fronts H/alpha distincts et diagonales conservées ; paiement <=N/(1024u ell) effectif dès u>=65536, donc au seuil source10^24 ; témoins m323 modèle-seul et m658911 premier-axe9967².
Conflicts: Aucun transfert du Gram natif nu au poids couplé, aucun mu(m)^2 ajouté à la coupe b de R7, modèle k>=2 entier conservé ; la petitesse de l'énergie première n'est pas postulée et aucune victoire n'est revendiquée.

## 2. Raccord entier du bracket R16 avant l'énergie

On conserve N pair, u=log N, ell=log u, alpha=ceil(N^(1/4)), Q=floor((N-1)/alpha), H=floor(N^(3/8)), avec H>=alpha sur le domaine considéré. Posons n=N-m et

L_N(n)=Lambda(n)*1_(n>1)*1_(gcd(n,N)=1).

R16, déjà acquis, est

D_N=P_head^{>=2}+[P_tail^{>=2}-M^{>=2}]+I+2max(e,0).

Les seuils de tête BV demeurent non évalués ; le paiement source de I garde u>=10^24. Le présent rôle porte sur le bracket B=P_tail^{>=2}-M^{>=2}, pas sur une tête raw ni sur une nouvelle version du pont.

Pour k dans J={2<=k<=Q : gcd(k,N)=1} et 1<=m<=N-2, définir

t_k(m)=1_(k|m)*1_(H*k<m),
h_k(m)=1_(alpha*k<m)*1_(gcd(k,n*N)=1)/phi(k),
a_k(m)=log(m/k)*[t_k(m)-h_k(m)],
K_H(m)=sum_(k in J)mu(k)*a_k(m).                       (W1)

Les fronts sont stricts. Les logarithmes apparaissent seulement avec un front actif : alors m/k>alpha>=1 ou m/k>H, et ils sont positifs. Un front inactif donne zéro. Les n=1 ou n nonunitaires sont nuls dans L_N, mais les puissances premières propres à base unitaire ne le sont pas.

La bascule acquise, appliquée point par point à m=k*r, donne pour TOUS les k,r

mu(m)mu(k)=mu(k)^2mu(r)*1_(gcd(k,r)=1).

Sur le support unitaire à N, un k divisant m est également unitaire à n*N. Le front H*k<m est exactement r>H. Ainsi le bracket entier se réécrit

B=sum_(1<=m<=N-2)mu(m)*L_N(N-m)*K_H(m).                (W2)

Les m non carrés-libres sont annulés par mu(m), conformément au physique complet et au modèle complet. Cette preuve n'applique pas un nouveau filtre à une coupe b ; aucun coefficient de cette coupe n'est employé dans W2. Le retrait de k=1 reste l'annulation conjointe acquise P1=M1 ; ce rapport ne le retire pas une deuxième fois.

Il est parfois utile d'écrire W1 comme le centré long plus un défaut de modèle :

a_k=log(m/k)*[
 1_(H*k<m)*(1_(k|m)-1_(gcd(k,nN)=1)/phi(k))
 -1_(alpha*k<m<=H*k)*1_(gcd(k,nN)=1)/phi(k)].           (W3)

La seconde ligne est indispensable. Elle conserve toute la bande de modèle dont le physique long a été amputé. Un candidat qui remplace h_k par le front H travaille sur un autre bracket.

## 3. Gram pondéré exact avec quatre composantes

APRÈS W2, on peut prendre la mesure positive réelle

w_m=L_N(N-m)*mu(m)^2,
A_N=sum_m w_m,
Gamma_(k,k')=sum_m w_m*a_k(m)*a_k'(m).                 (W4)

Le masque carré-libre porte le SECOND axe m, et vient seulement de mu(m) déjà présent dans W2. Il ne porte jamais n. Comme mu(m)^3=mu(m),

B=sum_m w_m*mu(m)*K_H(m),
mu^T Gamma mu=sum_m w_m*K_H(m)^2,
|B|^2<=A_N*(mu^T Gamma mu).                            (W5)

Les vecteurs extérieurs sont les vraies valeurs mu(k) ; la direction interne est la vraie mu(m). W5 n'est pas un remplacement par des coefficients arbitraires, et sa positivité ne donne aucun signe à B. Le Gram est pondéré par les premières valeurs de Mangoldt réelles, les unités et le support Möbius réel, contrairement au Gram natif nu de la boucle 8.

Ses quatre termes sont exactement

Gamma_(k,k')=sum_m w_m*log(m/k)*log(m/k')*
 [t_k t_k' - t_k h_k' - h_k t_k' + h_k h_k'].           (W6)

DD conserve m multiple de lcm(k,k'), les deux fronts H et les masques originaux. Les deux mixtes gardent un front H et un front alpha, différents. MM garde les deux fronts alpha et les deux facteurs phi. Les diagonales k=k' sont présentes : leur coefficient est (t_k-h_k)^2, non zéro par orthogonalité. Il est illicite de remplacer DD-DM-MD+MM par DD-MM, ou de considérer séparément DD comme un signe pour la combinaison linéaire.

Pour une composante HH, tous les indices restent a=u*v*x,r=s*t*zeta avec les quatre mu(u)mu(v)mu(s)mu(t), les faces, les détecteurs prescrits et le CRT ar. Le Gram d'une telle composante doit garder ses coefficients dans chacune des deux copies ; les produits égaux peuvent provenir de factorisations distinctes. W4–W6, qui portent le raw R16, ne prouvent aucune diagonalisation des quatre signes HH ni aucune identification avec Da,Dk,D00. Aucun caractère auxiliaire ne remplace ce CRT.

Les paramètres de la mesure et des colonnes n'ont pas disparu : le physique long a k<=(N-2)/H, alors que les colonnes du modèle continuent jusqu'à Q, avec des fronts mobiles. Les colonnes sans physique peuvent avoir un modèle non nul. Les +1 des fibres et endpoints restent dans W1 ; une estimation future de Gamma devra les payer.

## 4. Partition exacte du PREMIER axe

Scindons L_N(n) entre n premier et n=p^j,j>=2,p premier, avec les mêmes unités. Cela définit exactement

B=B_prime+B_pp,
Gamma=Gamma_prime+Gamma_pp,
A_N=A_prime+A_pp.                                     (W7)

Cette partition ne supprime aucune puissance. Il s'agit d'un poste à majorer indépendamment ; mu(n)^2 n'est pas utilisé. Les sous-matrices Gamma_prime et Gamma_pp restent positives puisque les mesures le sont, mais B_pp reste signé avant son paiement.

Le progrès indépendant concerne |B_pp|. Pour un n properpower admis, m=N-n. Dans le physique long, il existe au plus tau(m) diviseurs k ; chaque logarithme est <=u et les coefficients mu(k)^2mu(r) sont de module <=1. Ainsi sa contribution absolue par n est au plus

u*tau(m)*Lambda(n).

Dans le modèle entier, le majorant positif par n est

u*Lambda(n)*sum_(k<=Q)1/phi(k).

Les unités et fronts ne peuvent qu'abaisser ces majorants. En particulier le retrait du front H dans le modèle n'est pas requis pour les obtenir.

## 5. Deux bornes effectives élémentaires

### Moment harmonique réel

L'identité multiplicative finie

1/phi(k)=1/k*sum_(d|k)mu(d)^2/phi(d)

donne

sum_(k<=Q)1/phi(k)
 <=(1+log Q)*sum_(d>=1)mu(d)^2/[d*phi(d)]
 <=(1+log Q)*prod_p(1+1/[p(p-1)])
 <=e*(1+log Q)<3*(1+u).                               (W8)

La dernière borne utilise sum_(p)1/[p(p-1)]<=sum_(j>=2)1/[j(j-1)]=1. On peut procéder par produits finis puis monotonie ; aucun +1 arbitraire de classe de progression n'est absorbé.

### Diviseur maximal avec constante universelle explicite

Pour tout entier z>=1,

tau(z)<=2^2040*z^(1/8).                               (W9)

Preuve effective : si p>=256 et a>=0, a+1<=2^a<=p^(a/8). Pour p<256,

(a+1)*p^(-a/8)
 <=sum_(j>=0)(j+1)*p^(-j/8)
 =(1-p^(-1/8))^(-2)<256.

En effet 2^(-1/8)<15/16, ce qui se vérifie par 15^8>2^31 ; donc 1-p^(-1/8)>1/16. Il y a au plus 255 premiers distincts sous 256, en majorant même par tous les entiers possibles. Multiplier une fois ce facteur par petit premier donne 256^255=2^2040. Le nombre d'exposants a n'est pas borné artificiellement : le majorant géométrique est uniforme pour tous les a. Les grands premiers sont payés par z^(1/8). Il n'y a ainsi ni C_epsilon inconnu, ni fausse borne uniforme tau(z)<=log^C(z).

## 6. Paiement effectif du poste properpower

Pour chaque j>=2, il existe au plus sqrt(N) bases premières p avec p^j<N. Le nombre d'exposants est au plus u/log2, et Lambda(p^j)=log p<=u. Par comptage positif,

sum_(n<N,n=p^j,j>=2)Lambda(n)
 <=sqrt(N)*u^2/log2.                                 (W10)

Ce majorant grossier ne suppose aucun PNT ni hypothèse de Goldbach. Les duplications éventuelles seraient seulement une surmajoration positive ; en réalité la base d'une puissance première est unique. Les properpowers à base non unitaire sont conservées dans le compte majorant même lorsqu'elles valent zéro dans L_N.

W8–W10 et le majorant physique donnent

|B_pp|<=sqrt(N)*u^3/log2*
             [2^2040*N^(1/8)+3*(1+u)].                (W11)

Cette borne conserve les puissances du premier axe et paie leur différence physique-modèle par la somme des deux masses positives. Elle ne requiert pas la petite énergie de Gamma.

Pour u>=65536, les inégalités suivantes sont effectives : log2>=1/2, ell=log u<=u, log u<=u/4096, et 2040<=u/32. La troisième vient de la décroissance de log(u)/u et de log(65536)=16log2<16. Le rapport de W11 à N/(1024u ell) est au plus

2048*u^5*2^2040*exp(-3u/8)
 +12288*u^6*exp(-u/2).

Comme log2048<16<=u/4096, log12288<16<=u/4096 et 2^2040<=exp(u/32), les deux termes sont respectivement au plus

exp(-1402u/4096), exp(-2041u/4096).

Leur somme est <=2exp(-u/4)<1. On a donc démontré par ces majorants explicites

|B_pp|<=N/(1024u ell) pour u>=65536.                  (W12)

Le domaine source u>=10^24 satisfait ce seuil. Aucun seuil BV supplémentaire ni constante implicite ne rentre dans ce paiement : contrairement au poste de tête de la boucle 8, W12 n'utilise que les bornes élémentaires affichées. N=10^8 n'est pas dans ce domaine ; les calculs finis ne prétendent pas valider W12 à cette échelle.

Le paiement est une preuve mathématique écrite indépendante du gain recherché. Il n'est pas encore une certification Lean, et ne ferme pas R16 puisque B_prime et 2max(e,0) restent.

## 7. Le vrai moment premier encore ouvert

Le moment non payé est précisément

B_prime=sum_(1<=m<=N-2,N-m premier)
 mu(m)*log(N-m)*1_(gcd(N-m,N)=1)*K_H(m),               (W13)

avec K_H de W1 et ses deux fronts différents. Son énergie réelle est

E_prime=sum_(N-m premier)log(N-m)*mu(m)^2
                   *1_(gcd(N-m,N)=1)*K_H(m)^2.         (W14)

W13 garde le modèle entier, les secteurs divisibles, les masses principales induites, les nonunités et tous les coefficients. W14 n'est pas une hypothèse de petite taille. Écrire une borne ciblée de W13 ou une énergie assez petite pour Cauchy comme axiome déplacerait la demande. Aucune telle estimation indépendante n'a été obtenue.

Le paiement des diagonales par une seule densité de primes en AP ne traite pas les termes mixtes/les coefficients de Möbius du modèle. Les entrées DD de Gamma concernent n congru à N modulo lcm(k,k') avec un second axe carré-libre, tandis que DM et MM imposent d'autres fenêtres et poids. BV ordinaire, le Gram natif nu ou le préfixe mu(r)chi(r) à masque fixe ne couvrent pas leur combinaison pondérée. Les modules peuvent dépasser le niveau BV ; le front modèle comporte encore des colonnes jusqu'à Q. Les coefficients HH à quatre signes ne peuvent être absorbés dans une norme puis crédités comme annulés.

Les préfixes acquis au §12.6 gardent log K<=2u, conducteurs retenus, longueurs et onset source. Ils ne sont pas une estimation de mu(r)Lambda(N-kr) ou de W13. Une rugosité mobile n'est pas un masque fixe autorisé. La petitesse d'une projection exceptionnelle du Gram nu n'est pas non plus la petitesse de Gamma_prime.

Une information réellement nouvelle sur W13 pourrait provenir d'une estimation de sa dispersion pondérée avec les vrais quatre coefficients, ou d'une compensation physique-modèle aux mêmes points. Ce rapport ne postule ni l'une ni l'autre. Le fait que la positivité ne les fournisse pas n'est pas une impossibilité globale des méthodes d'opérateurs.

Après W7, le raccord exact reste

D_N=P_head^{>=2}+B_prime+B_pp+I+2max(e,0).              (W15)

W12 paie un poste à l'onset source ; la tête conserve son seuil BV propre non évalué. Aucune victoire conditionnelle complète n'est revendiquée.

## 8. Contrat concret aux formalistes et au rôle numérique

Le contrat exact W1–W7 vaut pour un sous-ensemble fini J de k et un sous-ensemble fini des m, avec leurs weights réels, si on présente son résultat comme cette sélection. Le bracket complet requiert TOUS les k de J source et TOUS les m. Les logarithmes sont symboliques, les coefficients rationnels et les fronts testés en entiers. Aucun sous-domaine numérique ne remplace le support complet.

Le rôle6, au handle réaffecté par root, a reçu W1–W7 et les témoins à N=100000000, alpha=100,Q=999999,H=1000 :

* **Modèle seul réel : m=323=17*19, mu(m)=+1 ; n=99999677 premier.** Pour k=3, 300<323<=3000 et gcd(3,nN)=1. Ainsi t3=0, h3=1/2, a3=-log(323/3)/2 et Gamma33=log(n)*a3²>0. Supprimer la bande de modèle W3 change la somme.
* **Properpower actif : m=658911=3*11*41*487, mu(m)=+1 ; n=9967².** Lambda_N(n)=log9967 reste dans W4 et B_pp. Ajouter mu(n)^2 détruirait ce point.
* **Second axe non carré-libre : m=112211=11*101², mu(m)=0 ; n=99887789 premier.** W2 et W4 donnent zéro ; cela n'autorise pas à supprimer les queues de la coupe b antérieure.
* **Correction de faux témoin : m=311, n=99999689=113*199*4447.** Le raw F_N(311) est actif, mais Lambda_N(n)=0 dans le nouveau bracket. Une suggestion initiale de l'idéateur avait confondu ces observables ; le rôle6 l'a corrigée avant ce rapport. m311 est conservé comme test d'annulation, pas comme énergie modèle non nulle.

Comparer la somme complète DD-DM-MD+MM aux carrés directs, conserver les diagonales, les deux fronts et les unités, puis comparer W2 à la bascule de P_tail-M sur les mêmes points. Les k de test peuvent être {3,7,11,13}, et les m inclure les témoins ci-dessus ; le reçu doit déclarer cette sélection exacte. La borne W12 se vérifie par sa preuve effective, pas par une extrapolation de ces points.

Les formalistes peuvent auditer le contrat et les bornes sans nouvelle hypothèse analytique. Une compilation des seules identités d'énergie standard ne serait pas une candidature de victoire ; elle n'est pas demandée. La seule progression indépendante soumise est le poste W12, tandis que W13 reste le moment arithmétique manquant. Aucun nouveau lemme portant la cible n'est fourni comme axiome.
