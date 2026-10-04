# Boucle 3 — Agent 2 : projection multiplicative de la vraie direction HH

Sources internes : monographie §§6, 12.3–12.10 ; sprint15/agents/genuine_smooth_hh_factor_fixed_modulus_pressure_test.txt ; one_sided_actual_scalar_round3.txt. Les acquis et la frontière littérale ne sont pas modifiés. L'objectif est de conserver la direction signée réelle avant une norme, puis d'auditer ce que les entrées primitives contrôlent effectivement.

## 1. Candidat exact : regrouper le quotient, pas seulement les valeurs absolues

Partons d'une cellule favorable de la complétion des seuls facteurs réellement non pondérés z,k du développement r=s*t*z. Sur les unités modulo N, la note antérieure obtient le noyau S(h,eta*b*l;N), eta=-a/(s*t), équivalent à S(eta*h*b,l;N) lorsque h est une unité. Ce modulus N est celui de cette complétion exacte de congruence ; il ne remplace pas le CRT original ar dans la route aux racines.

Soient A(a), U(s), V(t) des poids à support FINI sur des entiers unités modulo N. Dans une cellule séparée, les poids réels sont par exemple A(a)=H_y(a) fois son poids de cellule, U(s)=mu(s) fois son poids, V(t)=mu(t) fois son poids. Définissons sur G=(Z/NZ)^×

v(eta)=sum_{a,s,t} A(a) U(s) V(t) 1_{eta=-a/(s*t) modulo N}.        (P1)

Pour tout caractère chi de G, posons A_chi=sum_a A(a)chi(a), et de même U_chi,V_chi. La vraie projection signée est EXACTEMENT

v_chi := sum_eta v(eta)chi(eta)
       = chi(-1) A_chi U_bar(chi) V_bar(chi).                    (P2)

C'est une convolution finie sur le groupe des unités, avec inversion sur les deux dernières variables. Aucune norme d'opérateur ne remplace la direction v. Les unités en a,s,t et le modulus composite N sont explicites ; on ne suppose jamais N premier dans P1–P2.

Pour e_N(x)=exp(2*pi*i*x/N), définissons

S(A,B;N)=sum_{x in G} e_N(A*x+B/x),
tau(chi)=sum_{x in G} chi(x)e_N(x).

Lorsque h,b,l sont tous unités modulo N, la transformée du noyau vaut

sum_{eta in G} bar(chi)(eta) S(eta*h*b,l;N)
 = tau(bar(chi))^2 chi(h*b*l).                                  (P3)

Preuve : fixer x et poser u=eta*h*b*x dans la somme en eta donne chi(h*b*x) tau(bar(chi)). Puis poser v=x^{-1} dans la somme restante donne chi(l)tau(bar(chi)). Ces substitutions exigent les trois conditions d'unité affichées.

Si B(b),F(l) sont les autres poids séparés sur les unités, l'inversion des caractères produit donc le scalaire exact

T_unit(h) = (1/phi(N)) sum_{chi mod N}
  chi(-1) A_chi U_bar(chi) V_bar(chi)
  tau(bar(chi))^2 chi(h) B_chi F_chi.                            (P4)

Cela fournit un objet projeté concret à mesurer : des produits de véritables moments de Möbius, pas des vecteurs arbitraires. P4 concerne chaque cellule séparée et sa complétion ; le facteur Z*K/N^2 de la note reste à multiplier, puis les h et données extérieures à sommer.

## 2. Deux restes obligatoires pour le support complet

Le développement réel contient des masques non séparés : squarefreeness des produits, coprimalités entre facteurs, caps, stricte face r>alpha, et les faces distinguant n+m=N d'une congruence multiple de N. Écrivons ce sélecteur entier M(a,s,t,b,l,h,...) littéralement.

La projection complète existe toujours :

v_chi^{actual} = sum_{a,s,t} A(a)U(s)V(t) M(...) chi(-a/(s*t)).     (P5)

Elle ne factorise en P2 que si M se sépare dans les variables pertinentes. Si M0 est un sélecteur séparé choisi pour une cellule, le reste

R_sep,chi=sum A(a)U(s)V(t)[M-M0]chi(-a/(s*t))                     (P6)

est conservé exactement. On n'affirme aucune petitesse de R_sep. Une séparation de Mellin/Fourier ou une expansion de coprimalité peut rendre ce reste nul dans une somme de cellules exactes, mais il faut alors payer les normes des poids et tous les paramètres de cette séparation.

De même, l original contient des fréquences nonunitaires. La partition exacte est

T_actual = T_{gcd(h*b*l,N)=1} + T_nonunit.                        (P7)

T_nonunit retient les formules de Kloosterman originales et tous les masques. P3 n'y est pas invoquée. Un tri en classes de gcd et un abaissement de modulus demanderait une autre identité complète, avec ses poids de Gauss/Ramanujan ; ce n'est pas implicite dans P4.

La fréquence additive h=0 est aussi dans T_nonunit. Le caractère multiplicatif principal de P4 n'est pas cette fréquence additive zéro : leurs termes principaux ne peuvent pas être confondus ou payés deux fois.

## 3. Estimation véritablement déduite de l'entrée existante

La primitive all-prefix de §12.5 porte sur psi(y,chi), donc sur Lambda, pas sur mu. Elle ne devient pas une borne pour un moment U_chi par orthogonalité.

En revanche, §12.6 donne une borne indépendante pour le vrai préfixe mu(n)chi(n)1_{(n,K)=1}, pour les caractères primitifs retenus de conductor q<=u^8, masque log K<=2u et arguments x>=N^(1/8), à l'onset spécifié. En prenant K=N, le caractère induit modulo N garde exactement ce masque. Pour

U(s)=mu(s)1_{X<s<=2X}1_{(s,N)=1},
max(y,N^(1/8))<=X, 2X<=N,

les deux préfixes autorisés donnent rigoureusement

|U_chi| < 3X/u^4.                                               (P8)

La sélection Page de §12.6 reste celle de la source, notamment son unique exclusion lorsque le conductor sélectionné est au-delà de u*ell^4. Si V possède le même support avec longueur Y dans ce domaine, |V_chi|<3Y/u^4 également. Pour l'ensemble L de caractères induits ayant des conductors retenus, on en déduit, sans supposer de contrôle du reste,

|T_L(h)| <= (9XY/u^8)(1/phi(N))
  sum_{chi in L} |tau(bar(chi))|^2 |A_chi B_chi F_chi|.            (P9)

Cette estimation est valide pour les seuls poids et intervalles affichés ; des poids lisses ajoutent leurs variations d'Abel. Elle économise une fraction logarithmique d'une projection basse, mais n'est pas encore une estimation complète de HH. Les cellules avec X ou Y plus courts n'ont pas P8 sous cette forme.

## 4. Pourquoi le regroupement par conductor ne clôt pas le moment

P4 somme les caractères modulo N. Les conductors sont des diviseurs de N et peuvent être de taille comparable à N. Les petits conductors q<=u^8 ne représentent pas toutes ces directions. L'all-prefix prime de §§12.4–12.5 concerne aussi un tout autre objet : des progressions à poids Lambda, avec les moments de w_B(q) prouvés et les modules q<=Y. Ni ces moments ni ce support ne se transportent gratuitement vers les coefficients de P4 ou P5.

Pour un modulus premier p, les caractères nonprincipaux ont conductor p. La taille |tau(chi)|^2=p se démontre directement : développer la valeur absolue au carré et poser x=t*y ; la somme en y vaut p-1 si t=1 et -1 sinon. Comme sum_t chi(t)=0, il reste p. La transformation multiplie donc ces directions par une amplitude p ; elle ne les élimine pas. Pour N=2p, les directions induites de conductor p restent également des grandes directions. Aucun petit-conductor input ne suffit à les contrôler.

Après le projecteur orthogonal P_L, le complément vérifie exactement

||P_high v||_2^2=(1/phi(N))sum_{chi notin L}|v_chi|^2.             (P10)

Estimer P10 avec la vraie direction requiert des corrélations de Möbius issues du carré de P5. La monographie ne fournit pas ce moment. Le remplacer par la norme complète perd précisément l'information de projection recherchée. Le nouveau lemme nécessaire est une borne de cette projection haute et de son couplage au noyau, plus P6–P7. Aucune assertion quantitativement équivalente au budget final n'est ajoutée comme hypothèse de victoire.

## 5. Falsifiers exacts pour l'Agent 6

(a) À N=100000000, calculer deux fois le histogramme entier P1 pour des supports finis déclarés d'entiers unités : une fois en tuples directs, une fois par convolution quotient. Avec A=H_y réel et U,V=mu, les histogrammes doivent coïncider exactement. Pas de logarithmes flottants ni de caractères complexes nécessaires.

(b) Refaire avec un sélecteur couplé 1_{a<s}. P5 conserve ce sélecteur ; le produit factorisé P2 sans P6 doit être réfuté. Un exemple minimal prend N=100000000, A support {3}, U support {3,7}, V support {7}, les trois poids égaux à 1. Le sélecteur conserve seulement s=7, tandis que P2 sans le sélecteur conserve aussi s=3. Tous ces entiers sont des unités.

(c) Pour p=11 et le caractère quadratique, h=b=l=1, le histogramme signé des phases eta*x+x^{-1} dans P3 est

[-10,1,1,1,1,1,1,1,1,1,1].

Il donne exactement -11 en utilisant 1+zeta+...+zeta^10=0. Cela confirme P3 et réfute une contraction automatique du mode de conductor 11. Ce histogramme a été calculé en entiers dans cette recherche.

(d) La non-disparition structurelle concerne aussi de vrais coefficients. Le tuple a=15,s=7,t=11,z=1,b=13,k=19 donne N=1658=2*829, n=195,m=1463, unités et produits carrés-libres, y=2. H_y(a)H_y(r)=4. Une masse ponctuelle sur eta=-15/77 modulo N possède une projection nonnulle sur chaque caractère, y compris ceux de conductor 829. Ceci est un diagnostic fini, pas une affirmation sur les seuils analytiques u^8 de la monographie.

## 6. Contrôle de la piste Banks–Shparlinski

Source primaire consultée : Banks–Shparlinski, Multiple sums with the Möbius function, https://arxiv.org/html/2506.08787v1, théorème 2.1 et setup 1.3.

Leur somme impose f(n1)+g(n2)+wp(n3)=M, le poids de Möbius du produit des trois variables et des poids indépendants seulement sur les deux premières. Le quotient impose a+eta*s*t=0 modulo N : sa différence croisée en s,t est eta*(s'-s)*(t'-t), généralement non nulle. Ce n'est pas une somme de trois fonctions indépendantes. Fixer t rend le problème binaire. Grouper s*t conserve une multiplicité et supprime plutôt la troisième variable indépendante. La variable lisse z porte poids 1 ; introduire mu(z)^2 sur son support carré-libre laisse un second mu(z) dans un poids de la troisième variable. Les faces couplées restent à payer. Aucune identification exacte de l'objet HH au théorème 2.1 n'est obtenue. Le théorème n'est donc pas utilisé comme estimation de HH.

## 7. Verdict et raccord terminal

P1–P4 sont des identités exactes intéressantes pour inspecter la vraie direction et tester ses projections. P8–P9 donnent une borne limitée réellement issue du préfixe mu autorisé, avec ses hypothèses. Le regroupement par conductor ne contrôle ni la projection haute P10, ni les restes de support/nonunit P6–P7. Aucun signe favorable de HH ou contraction globale n'en découle.

Le scalaire original reste celui de §6 : D_N=-Sfull+2 max(e,0). Sa cible n'est pas déduite des seules petites projections ou d'une énergie positive. Statut : mécanisme spectral exact sur cellules séparées, filtre numérique recommandé, obligation quantitative haute explicitement non obtenue. Aucune victoire.

## 8. Filtre numérique reçu

L'Agent 6 rapporte un PASS de P1 en entier à N=10^8 : histogramme direct égal à convolution quotient, 2214 résidus non nuls. Le masque couplé a<s réfute la factorisation sans P6 : au résidu eta=122399, coefficient factorisé -4 contre coefficient réel -2. Les phases quadratiques donnent exactement -11 pour q=11 et +829 pour q=829. Le point HH N=1658 a une projection non nulle sur la direction de conductor 829. Reçu annoncé : round3/multifibre.json. Ces tests valident l'identité et falsifient les simplifications non autorisées ; ils ne prouvent aucun contrôle asymptotique.
