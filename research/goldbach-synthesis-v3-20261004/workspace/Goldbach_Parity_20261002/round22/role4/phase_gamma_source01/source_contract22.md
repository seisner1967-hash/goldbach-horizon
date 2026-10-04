# Γ pour phases complexes — SOURCE 01

Statut : deux modules SOURCE, 26+25 déclarations avec51 #print axioms écrits. Aucune compilation, aucun audit réel d'axiomes et aucun calcul numérique. Les preuves s'appuient directement sur Γ, sa vraie réflexion, sa conjugaison et sa récurrence dans mathlib4.15. Pas de hGammaImproved, de constante finale libre, d'identité zêta ou de trace finale en prémisse.

Écrire C=sqrt(2π). La vraie identité Γ(z)Γ(1−z)=π/sin(πz), appliquée à z=1/2+it, avec 1−z=conjugate(z) et sin(πz)=cosh(πt), donne |Γ(1/2+it)|²=π/cosh(πt). Comme exp(π|t|)≤2cosh(πt), le module construit |Γ(1/2+it)|≤C exp(−π|t|/2). Deux vraies récurrences donnent Γ(5/2+it)=(3/2+it)(1/2+it)Γ(1/2+it), puis la borne C(|t|+2)² exp(−π|t|/2). Ces faits valent pour tout t réel.

Pour a>0, theta réel, w=a−i theta, on travaille avec le logarithme principal dans le demi-plan droit. Re(w)=a>0 paie w≠0, son appartenance au plan coupé et |Arg(w)|<π/2. Pour tout c réel, la norme exacte est |w^(−(c+it))|=|w|^(−c)exp(t Arg(w)). Le facteur Arg n'est pas supprimé. Poser delta=π/2−|Arg(w)|>0.

Les produits effectivement définis sont
L(t)=w^(−(−1/2+it))Γ(1/2+it),
R(t)=w^(−(3/2+it))Γ(5/2+it).
Ils satisfont |L(t)|≤C|w|^(1/2)e^(−delta|t|) et |R(t)|≤C|w|^(−3/2)(|t|+2)²e^(−delta|t|).

Pour T≥0, chacune des deux queues signées t↦L(±t) ou R(±t) sur (T,+∞) est réellement intégrable dans la SOURCE. La continuité de Γ sur la demi-droite positive est dérivée de sa différentiabilité hors des entiers négatifs ; la continuité du pouvoir principal à base w≠0 est construite. Des majorants réels intégrables paient ensuite l'intégrabilité des vrais produits complexes.

Les enveloppes d'intégrale par signe sont fermées :
E_L=C|w|^(1/2)e^(−delta T)/delta,
E_R=C|w|^(−3/2)e^(−delta T)[(T+2)²/delta+2(T+2)/delta²+2/delta³].
Le module ne postule pas ces intégrales : primitives −e^(−delta t)/delta et −e^(−delta t)[(t+2)²/delta+2(t+2)/delta²+2/delta³], dérivées positives, limites0 par décroissance polynomiale-exponentielle, puis FTC sur Ioi. Les expressions E_L/E_R sont continues conjointement en (a,theta), sur a>0, pour T fixé. Le domaine de continuité de la formule fermée accepte T réel ; la comparaison aux queues signées exige T≥0. Une queue à deux signes s'obtient sur papier en additionnant les deux rayons, sans crédit formel supplémentaire.

La constante delta ne dispose d'aucune minoration globale indépendante de a et theta. Sur papier, si theta≠0, delta=atan(a/|theta|) ; à theta=0, delta=π/2. Elle tend vers0 quand a/|theta| tend vers0. Les facteurs delta^-1/delta^-2/delta^-3 rendent ce coût explicite. Même avec une fenêtre représentative |theta|≤π et a=1/N, une coupure verticale adaptée peut croître fortement avec N. Pour la queue gauche, tout budget tau>0 exige au moins le contrôle effectif C|w|^(1/2)e^(−delta T)/delta≤tau ; la queue droite exige son inégalité entière avec son polynôme. Aucune valeur de T, durée ou précision n'est mesurée ou promise ici.

Charge non fermée : ces deux produits utilisent Γ(s+1), comme le noyau thermique dérivé H(w)=ΣΛ(n) w n exp(−wn). La trace de projection T(w)=ΣΛ(n)exp(−wn) demande Γ(s) ou une récupération effective par intégration du poids dérivé. Aucune de ces identités globales n'est assumée ou démontrée par ce paquet. Le produit avec les vrais ζ'/ζ ou χ'/χ, ses domaines, son intégrabilité uniforme, sa vraie représentation de Mellin et sa périodicité en theta restent des preuves supplémentaires. Une borne Γ seule ne ferme pas les queues de ces produits : les moments/polynômes supplémentaires devront être dérivés avec leurs vrais facteurs.

Les branches, normes et domaines de la couche Γ sont concrets. La couche spectrale zêta uniforme, les boîtes numériques nodales, la projection dans le banc, les corrections canoniques de puissances premières, la frontière et D_N restent ouverts. Aucun WIN et aucune absorption de l'obstruction de parité ne sont revendiqués. La voie de rotationGammaRe2 explorée par ROLE3 peut fournir un domaine complémentaire ; ce paquet ne lui attribue aucun verdict.
