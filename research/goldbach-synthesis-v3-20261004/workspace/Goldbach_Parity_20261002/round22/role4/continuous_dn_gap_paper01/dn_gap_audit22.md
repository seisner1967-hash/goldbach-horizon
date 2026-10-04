# Audit ciblé du raccord spectral à D_N — PAPER/SOURCE 01

Portée : note de dérivation, environ trois pages ; aucun nouveau théorème Lean, calcul, import, compilation ou programme exécuté. Les acquis sont conservés. BUILD_ONLY03 est gelé séparément ; ses contrôles et les identités auxiliaires ne donnent pas un contrôle du résidu. Le test N=10^8 reste distinct du seuil source u=log N≥10^24. Les nouvelles recherches n'utilisent aucune forme bilinéaire arithmétique, crible, inversion de Möbius, Vaughan ou estimation de restes AP.

## 1. Ce qui est payé, et le raccord exact qui reste

Le contrat v04 et l'identité indépendante du lot13 donnent, pour a_th>0,

\[
 T(\theta)=\sum_{n\ge0}\Lambda(n)e^{-a_{\rm th}n}e^{in\theta},\qquad
 C_N=\frac{e^{a_{\rm th}N}}{2\pi}\int_{-\pi}^{\pi}T(\theta)^2e^{-iN\theta}\,d\theta
     =\sum_{n=0}^N\Lambda(n)\Lambda(N-n).
\]

La conjugaison de T(-θ) donne T(θ), et non sa conjugaison à la même phase. Remplacer T² par |T|² changerait la projection additive en une projection de différences de fréquences. Une positivité de norme ou d'opérateur n'est donc pas une minoration du coefficient voulu.

Définir directement P(n)=log n si n est premier, zéro sinon, et U(n)=Λ(n)−P(n). U porte exactement les puissances p^k, k≥2. Sans nouvelle inversion arithmétique,

\[
 R_{\rm sf}=\sum_{n=0}^NP(n)P(N-n),\qquad
 Q_N=C_N-R_{\rm sf}
 =\sum_{n=0}^N\{2P(n)U(N-n)+U(n)U(N-n)\}\ge0. \tag{PP}
\]

Chaque terme est conservé. Pour N≥2 et u=log N, les bases des puissances propres sont ≤√N ; leur poids total est ≤√N u, car chaque base contribue au plus u. Avec Λ(n)≤u sur 1≤n≤N, le majorant papier concret Q_N≤2√N u² suit de la partition « au moins un axe est une puissance propre ». Q_N n'est pas le seul P_retained du bilan : celui-ci garde ses propres restrictions. Cette borne n'autorise aucune double charge ni suppression de Q_N au test fini.

Dans la convention couverte de la monographie, le pont conservé, avec ses conditions et le même support, est

\[
 D_N+\varepsilon_{\rm tr}=R_{\rm ref}-R_{\rm sf}+2\max(e,0),
 \quad R_{\rm ref}=\mathfrak S(N)(N-F_N).
\]

Il implique exactement D_N=R_ref−C_N+Q_N+2max(e,0)−ε_tr. Nous ne redéveloppons pas F_N par l'ancienne route interdite. La définition du résidu, la référence acquise et les conditions du pont sont gardées telles quelles. Le ledger complet conserve B_prime^(a_cut), B_pp^(a_cut), P_band_ge2, Z_face_ge2, I_α et 2max(e,0), chacun une fois ; α=ceil N^(1/4), Q=floor((N−1)/α), a_cut=ceil N^(7/16), M_cut=ceil N^(3/4). Le paramètre thermique a_th est distinct de ces coupures.

Ainsi une enclosure de C_N seule ne contrôle ni l'excès couvert e, ni ses fronts/coins/unités, ni le défaut signé R_ref−C_N. Supposer une borne sur ce défaut qui reproduit la cible serait simplement remettre D_N en prémisse.

## 2. Candidat concret continu : garder le noyau angulaire avant d'estimer

Poser w=a_th−iθ, θ∈[−π,π], Log principal, L(s)=−ζ′(s)/ζ(s) pour la vraie ζ. Re w>0 évite zéro et la coupure. Le contrat phase SOURCE propose

\[
 T(\theta)=\frac1{2\pi}\int_{\mathbb R}\Gamma(2+it)L(2+it)w^{-2-it}\,dt. \tag{M}
\]

M reste une charge de preuve : inversion de Fourier/Mellin réelle, échange dominé avec la vraie série Λ, puis holomorphie et prolongement sur Re w>0. La rotation générale de Γ est indépendante PASS ; les nouveaux G2/DOM/TAIL et la chaîne quantitative L sont SOURCE, sans crédit de compilation. Une identité abstraite de trace ne remplace pas M.

Définir I_H par la même intégrale sur [−H,H], H≥0, et

\[
 J_{a,N}(q)=\frac1{2\pi}\int_{-\pi}^{\pi}(a-i\theta)^{-q}e^{-iN\theta}\,d\theta,
\quad
 C_N^H=\frac{e^{aN}}{(2\pi)^2}\int_{[-H,H]^2}
 \Gamma(2+it)\Gamma(2+iv)L(2+it)L(2+iv)J_{a,N}(4+i(t+v))\,dt\,dv.
 \tag{SC}
\]

Ici a=a_th. SC est la corrélation de deux traces spectrales continues ; elle n'est pas une estimation de formes bilinéaires arithmétiques. Son égalité avec la projection de I_H² exige seulement le Fubini concret sur le compact et les branches indiquées. La relation au vrai C_N exige M. Garder J avant une norme absolue est le seul emplacement proposé pour chercher une annulation globale nouvelle.

Le premier lemme autonome utile est payé sur papier par d/dθ(w^(−q))=iq w^(−q−1). Pour l'entier N≥1, l'intégration par parties donne exactement

\[
 J_{a,N}(q)=\frac{i(-1)^N}{2\pi N}
 [(a-i\pi)^{-q}-(a+i\pi)^{-q}]+\frac qN J_{a,N}(q+1). \tag{BORD}
\]

Les deux valeurs du logarithme sont différentes ; le terme de bord ne s'annule pas point par point. La périodicité de T complet vient de sa série, après intégration verticale. Postuler la périodicité de chaque intégrande Mellin tronqué ferait perdre cette charge. BORD est falsifiable et formalisable sans une hypothèse d'annulation ; il ne donne pas un signe de SC.

## 3. Restes explicites et critère de falsification

La rotation β(t)=atan(t/2), Γ(2)=1 et |t|atan(2/|t|)≤2 donnent la borne papier G2, |Γ(2+it)|≤(t²+4)e^(2−π|t|/2)/4. La série directe Λ≤log, si son raccord réel à L est prouvé, donne |L(2+it)|≤4. Avec ρ=|w| et δ=π/2−|Arg w|>0, le vrai intégrande est alors dominé par e²ρ^(−2)(t²+4)e^(−δ|t|). Sa queue est

\[
 E(w,H)=\frac{e^2}{\pi\rho^2}e^{-\delta H}
 [(H^2+4)/\delta+2H/\delta^2+2/\delta^3].
\]

Pour d(a)=atan(a/π), remplacer ρ par a et δ par d donne E_u(a,H), uniforme en θ. Cette expression et A(a)=e^(−a)/(1−e^(−a))² sont fermées, continues pour a>0,H≥0. Dès que M et DOM sont réellement payés, |T|≤A et |T−I_H|≤E_u donnent

\[
 |C_N-C_N^H|\le e^{aN}E_u(a,H)[2A(a)+E_u(a,H)]. \tag{ERR}
\]

Ce reste est un paiement de troncature ; il n'est pas une preuve d'annulation. À a=1/N, d=atan(1/(πN)) ; la hauteur garantie croît symboliquement comme N(log N+log(1/budget)). Le coût du voisinage du bord est explicite, aucune durée mesurée n'est déduite.

Pour fermer sur papier une quadrature angulaire au milieu de K cellules, poser

\[
 U_H(a)=\frac{e^2}{\pi a^2}(2/d(a)^3+4/d(a)),\qquad
 V_H(a)=U_H(a)^2[N+2(H+2)/a].
\]

Le symbole U_H désigne ici un majorant uniforme, indépendant de H. DOM donne |I_H|≤U_H et |I_H′|≤(H+2)U_H/a, car la dérivée en θ multiplie l'intégrande par i(2+it)/w. Donc |(I_H²e^(−iNθ))′|≤V_H. L'intégrale de la distance au milieu d'une cellule de largeur 2π/K vaut (2π/K)²/4. La projection angulaire possède ainsi l'erreur fermée

\[
 E_\theta(a,H,K)=e^{aN}\pi V_H(a)/(2K),\quad K\ge1. \tag{ANG}
\]

Un futur test N=10^8 comparerait cette quadrature de SC à I_A/S² du constructeur canonique A32, S=2^58. La borne arithmétique indépendante est E_q=(N+1)(64/S+1/S²). Pour la quadrature verticale, le contrat phase donne Q=Σ_j M_j h_j²/(4π), M_j=48e³max(ρ^(−3/2),ρ^(−5/2))(1+u_j/3)³e^(−δr_j), u_j=|x_j|+h_j/2+1/2, r_j=max(|x_j|−h_j/2−1/2,0). Si ε est le maximum des rayons nodaux réellement produits — Q plus les contributions dirigées de toutes les primitives, positions et poids — l'erreur totale de comparaison est

\[
 E_q+\operatorname{ERR}+E_\theta+e^{aN}(2U_H+\varepsilon)\varepsilon. \tag{TEST}
\]

ε n'est pas une entrée libre : Γ,ζ,ζ′,Log,exp, les divisions et chaque position/poids doivent avoir leurs enclosures calculées et vérifiées. Une séparation effective de zéro est exigée avant la division par ζ. Toute pièce absente force NOT_PREPARED, pas PASS. ERR et ANG sont continues pour a>0,H≥0 à N,K fixés. À a=1/N et hauteur garantie croissante, ANG est très coûteuse : son majorant grossier a un ordre symbolique a^(−12)log(a^(−1))/K pour budget fixé. Aucun choix pratique K ni durée mesurée n'est annoncé. Le producteur SC global n'existe pas encore et les restes nouveaux restent PAPER/SOURCE.

Échec précis de la proposition comme contournement : même après M, SC, BORD et ERR, aucune invariance exacte ni estimation signée de la vraie densité spectrale projetée, avec la référence et tous les fronts canoniques, n'est démontrée. Les majorants absolus payent la convergence et l'erreur ; ils ne produisent pas la minoration. Il manque une nouvelle annulation globale issue de la vraie ζ et de ses phases, transportée explicitement au ledger. Un opérateur dont la trace contient C_N, RH, une modularité postulée ou une positivité supposée ne paie pas ce manque. Aucun candidat quantitatif suffisant n'est retenu ici comme résultat ; D_N≤N/(256u log u) et WIN restent ouverts.
