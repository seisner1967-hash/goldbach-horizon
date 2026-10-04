# Annexe réelle de Weil — identité exacte et sous-banc local falsifiable proposé

Statut : dérivation papier auditée précontractuellement par ROLE6, sans test, source Lean, producteur ou compilation. Le test porte sur une trace continue à échelle Y=√N, avec N fixé à10^8 et Y=10000. Il ne calcule pas R_Λ(N), n’extrait aucun coefficient individuel et ne justifie pas un contour complexe entier. La limitation sharp NON_INFORMATIVE_BOUND reste entière.

## Identité indépendante des deux évaluations

Pour Y≥1 réel, définissons f_Y(x)=(x/Y)exp(−x/Y) sur x>0, f_Y*(x)=f_Y(1/x)/x. Cette fonction appartient au domaine W de la vraie formule explicite : f_Y(x)=O(x) à0, décroissance exponentielle à∞, aucune discontinuité. Son transformé Mellin est

    Mf_Y(s)=Y^s Γ(s+1), Re(s)>−1 ; Mf_Y(0)=1, Mf_Y(1)=Y.

La forme complète, avant toute suppression de mode, donne exactement

    H_Y = Σ_{n≥2}Λ(n)[(n/Y)e^(−n/Y)+(1/(Yn²))e^(−1/(Yn))]
        =1+Y−Σ_{ρ∈Z}Y^ρ Γ(ρ+1)−(log(4π)+γ_E)f_Y(1)−Arch_Y,       (H1)
    Arch_Y=∫_1^∞[f_Y(x)+f_Y(1/x)/x−2f_Y(1)/x] dx/(x−x^−1).

Les deux pôles en0/1, le mode f(1), la suite duale f*, l’intégrale archimédienne et tous les vrais zéros avec multiplicité sont présents. Les zéros triviaux ne sont pas ajoutés une seconde fois : ils sont regroupés dans le terme archimédien de cette formule complète. Toutes les puissances premières restent dans Λ. (H1) est une spécialisation dérivée de la [formule primaire de Bombieri, p.8](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf), pas une définition spectrale par H_Y.

Au point x=1, le quotient de l’intégrande possède la limite f_Y(1)/2 : le numérateur s’annule et sa dérivée vaut f_Y(1), le dénominateur a dérivée2. Cette valeur est incluse dans la définition continue de l’intégrande, puis prouvée. Aucune singularité non contrôlée ni omission d’endpoint n’est permise.

## Décroissance Gamma uniforme et queue exacte majorée

La représentation de Laplace complexe Γ(ν)z^−ν=∫_0^∞exp(−zr)r^(ν−1)dr, Reν>0 et Rez>0, avec puissances principales, est [DLMF5.9.1](https://dlmf.nist.gov/5.9.E1). Prendre z=exp(iπ/4) pour Imν≥0, et son conjugué sinon, puis prendre les valeurs absolues donne

    |Γ(β+1+iγ)|≤exp(−π|γ|/4) Γ(β+1)/(cos(π/4))^(β+1)
                 ≤2exp(−π|γ|/4), 0≤β≤1.                          (H2)

La dernière borne utilise la log-convexité de Γ sur les réels positifs, Γ(1)=Γ(2)=1, donc Γ(β+1)≤1. Elle se démontre directement par Hölder dans son intégrale réelle ; [DLMF5.5(iv)](https://dlmf.nist.gov/5.5.iv) donne le cadre de log-convexité. Ce contrôle est uniforme sur toute la bande critique et n’importe ni RH ni simplicité.

Avec a=π/4 et le compte inconditionnel N_+(t)≤t logt pour t≥10 de la section3 du rapport principal, Stieltjes donne

    |Σ_{ρ:|Imρ|>T}Y^ρΓ(ρ+1)|≤E_heat(Y,T),
    E_heat(Y,T)=4Y exp(−aT)[TlogT+(logT+1)/a+1/(a²T)], T≥10.        (H3)

La preuve majore Σ_{γ>T}exp(−aγ) par a∫_T^∞N_+(t)exp(−at)dt et utilise

    tlogt ≤ TlogT+(logT+1)(t−T)+(t−T)²/(2T), t≥T.

Les deux demi-plans et le facteur2 de (H2) sont compris dans4Y. Le résultat est fermé et continu en Y≥1,T≥10. Il s’applique au paramètre réel Y seulement ; aucun remplacement Y par une variable dont l’argument s’approche de π/2 n’est autorisé.

## Coupures arithmétiques et archimédiennes

Pour X≥max(3,3Y) entier, la fonction (x/Y)logx exp(−x/Y) est décroissante au-delà de X. Avec 0≤Λ(n)≤logn et concavité du logarithme,

    Σ_{n>X}Λ(n)(n/Y)e^(−n/Y)
       ≤E_prim(Y,X)=e^(−X/Y)[(X+Y)logX+Y+2Y²/X].                  (H4)

Pour Q≥3 entier, logx/x² est décroissante et

    Σ_{n>Q}Λ(n)/(Yn²)e^(−1/(Yn)) ≤E_dual(Y,Q)=(logQ+1)/(YQ).     (H5)

Pour R≥2 réel, 1/(x−x^−1)≤4/(3x) et f_Y(1)≤1/Y entraînent

    |∫_R^∞ integrand Arch_Y dx|
       ≤E_arch(Y,R)=(4/3)[e^(−R/Y)+1/(2YR²)+2/(YR)].              (H6)

Ces quatre queues, plus les erreurs d’évaluation certifiées, forment le budget fermé. Aucune queue n’est choisie après observation d’un résidu. Les expressions exponentielles/logarithmiques sont ensuite encadrées vers l’extérieur, pas remplacées par des flottants non bornés.

## Paramètres, coût et falsification proposés

N=100000000, Y=10000, T=100, X=Q=R=1000000. Tolérance initiale τ=1/100 ; un producteur peut viser une précision plus fine, à contractualiser avant son invocation. Il faut une seule reconstruction primes/puis puissances jusqu’à10^6, une seule liste complète des vrais zéros jusqu’à100, des Γ dans leurs boîtes et une intégrale réelle régulière sur[1,10^6]. Aucune complexité quadratique en couples de zéros n’est nécessaire pour ce sous-banc. ROLE6 a confirmé sur papier les modes, f*, le signe et l’endpoint archimédien, H2/H3 et les queues conservatrices H4–H6. Cela ne remplace pas des boîtes/Turing complets ni une quadrature certifiée.

Contrat : conserver séparément somme arithmétique directe, somme duale, toutes puissances propres, deux pôles, mode f(1), Arch, somme de zéros et chaque queue. Les valeurs doivent provenir d’évaluateurs indépendants avec intervalles rationnels dirigés. Le spectre doit être certifié complet avec multiplicité et contours sans zéro ; aucune liste critical-line seule n’est admise. Réussite locale = intersection des intervalles des deux côtés et totalerror≤τ, avec contrôles négatifs.

Contrôle négatif obligatoire : retirer le mode Mf(1)=Y, puis les deux modes1+Y dans une copie du résultat. Une toléranceτ et des erreurs certifiées beaucoup plus petites que1 doivent rendre chaque identité mutée fausse par intervalles disjoints. Une liste sans puissances premières est un autre contrôle à documenter, sans présupposer sa taille. À l’inverse, le sharp K_N ne doit pas recevoir un PASS de falsifiabilité si l’omission de A(K_N) passe encore son enveloppe géante. Publier exactement ce contraste de pouvoir discriminant, sans transformer la trace réelle en résultat sur le coefficientN.

Contrat Lean : prouver appartenance W de f_Y, intégrale Mellin réelle et complexe, H2 par la formule de Laplace complexe et Hölder, H3 par le vrai compte global, H4/H5 par comparaison somme/intégrale, H6 par intégrabilité et bornes. H1 exige toujours une formule explicite globale réellement formalisée, qui ne peut être donnée comme axiome ou prémisse du théorème final. Les modules de queues peuvent être séparés comme auxiliaires ; leur compilation ne serait ni H1 certifié ni victoire D_N.

Statuts futurs séparés : `REAL_TRACE_LOCAL_CERTIFIED` si tous critères remplis ; `SHARP_COEFFICIENT_NON_INFORMATIVE_BOUND` pour le majorant actuel ; `D_N_UNPAID` tant que le raccord et l’estimation quantitative du bilan manquent. Tous sont encore des projets. Aucune donnée, test, invocation Lean ou PASS nouveau n’existe dans cette phase ROLE1.
