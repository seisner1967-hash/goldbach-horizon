# Positivité réelle de D et reconstruction des blocs conservés — PAPER01

**Résultat borné.** Le mécanisme testé est l'extraction des atomes par moyennes triangulaires positives de Fejér, suivie de leur insertion dans les blocs canoniques. Une telle moyenne de la vraie donnée verticale D reconstruit chaque amplitude avec une fuite explicite O(T⁻²). Elle reste une reconstruction classique ; la positivité qui la fonde ne donne aucun minorant strict uniforme du canal additif. Aucun mécanisme suffisant pour D_N ni nouveauté mathématique n'est revendiqué. Note PAPER uniquement : zéro Lean, Python/math, probe, préparation, gate ou évaluation numérique ; aucun ancien fichier modifié.

## 1. Donnée acquise et positivité indépendante de la cible

Poser c_n=Λ(n)/n² pour n≥2, avec toutes les puissances premières, et c_0=c_1=0. Le lot35 réellement PASS30 paie Q=Σc_n≤6, la continuité de

\[
D(t)=\sum_{n\ge2}c_ne^{-it\log n},\quad t\in\mathbb R,
\qquad
P(w)=\frac1{2\pi}\int_{\mathbb R}D(t)\Gamma(2+it)w^{-2-it}\,dt,
\quad\Re w>0,
\]

avec le logarithme principal. Le statut officiel 88 modules / 1488 déclarations est celui transmis par ROOT ; l'adjudication35 et son reçu de clôture sont relus ici, pas le journal brut ni l'observation ROOT. Les statuts SOURCE/FAIL historiques des notes relues ne sont pas actualisés rétroactivement.

La non-négativité réelle de c_n donne, pour r fini, t_j réels et z_j complexes,

\[
\sum_{j,k=1}^{r}\overline{z_j}z_kD(t_k-t_j)
=\sum_{n\ge2}c_n\left|\sum_{k=1}^{r}z_ke^{-it_k\log n}\right|^2\ge0.\tag{PD}
\]

L'échange est payé par Q≤6 et la somme finie. Ainsi D est de type positif sur la variable continue t ; PD porte la vraie mesure Σc_nδ_(log n), indépendamment de N et de Goldbach. Il s'agit d'une dérivation directe, sans invoquer un théorème spécialisé de Bochner ni une positivité des zéros équivalente à RH.

## 2. Identité de reconstruction positive et rayon spectral fermé

Pour T>0 et m entier≥1, définir

\[
A_T(m)=\frac1T\int_{-T}^{T}\left(1-\frac{|t|}{T}\right)D(t)e^{it\log m}\,dt.
\]

L'intégrande est continu par morceaux et absolument intégrable sur ce compact. La sommabilité Q permet son échange avec la vraie série. L'intégrale d'une exponentielle contre le triangle donne exactement

\[
A_T(m)=\sum_{n\ge2}c_n\,\operatorname{sinc}^2\!\left(\frac T2\log\frac mn\right),
\qquad \operatorname{sinc}(x)=\begin{cases}\sin x/x&x\ne0,\\1&x=0.\end{cases}\tag{TRI}
\]

En effet le triangle est l'autocorrélation de 1_[−T/2,T/2], divisée par T. TRI est réelle et positive, malgré les phases complexes de D. Pour m≥2, le terme n=m vaut exactement c_m ; pour m=1, il est absent et c_1=0. Pour n≠m, l'écart entre logarithmes d'entiers satisfait

\[
\left|\log(m/n)\right|\ge\delta_m:=\log(1+1/m)>0.
\]

Pour n>m, cela suit de n≥m+1 ; pour n<m, m≥2 et m/(m−1)>(m+1)/m. Pour m=1, tous les supports n≥2 vérifient directement l'écart≥log2=δ_1 et c_1=0. Avec |sinc x|≤1/|x| et Q≤6,

\[
0\le A_T(m)-c_m\le b_m(T):=\frac{24}{T^2\delta_m^2},\qquad
\max(0,A_T(m)-b_m(T))\le c_m\le A_T(m).\tag{ATOM}
\]

Le rayon est fermé, continu pour T>0 et tend vers zéro à m fixé. ATOM n'offre aucune masse positive : lorsque c_m=0, la fuite positive peut subsister et la borne inférieure demeure zéro. Aucun terme de puissance première n'est retiré, aucune équation fonctionnelle ou formule explicite de zéros n'est nécessaire à cette identité.

## 3. Action à l'intérieur des paires d'énergie

Garder E_N, e_n, R_N et A_N de la note ROLE4, avec N entier≥6 et a>0. Soit B_Ne_n=(n−N/2)e_n et S_(N,a)=exp(aB_N), opérateur positif inversible sur cet espace fini. On a R_NS_(N,a)R_N=S_(N,a)⁻¹, donc S_(N,a)R_NS_(N,a)=R_N. L'état thermique acquis v_(N,a) devient

\[
u_{N,a}=S_{N,a}v_{N,a}
=e^{-aN/2}\sum_{n=0}^{N}\Lambda(n)e_n,
\qquad
\langle u_{N,a},R_Nu_{N,a}\rangle
=\langle v_{N,a},R_Nv_{N,a}\rangle=e^{-aN}C_N.\tag{BAL}
\]

Ce changement non unitaire conserve exactement le canal, sans supprimer un résidu. Pour n<N−n, le bloc d'énergie (n−N/2)² de |u⟩⟨u| est

\[
e^{-aN}\begin{pmatrix}\Lambda(n)^2&\Lambda(n)\Lambda(N-n)\\
\Lambda(n)\Lambda(N-n)&\Lambda(N-n)^2\end{pmatrix}.\tag{BLOCK}
\]

Son déterminant vaut zéro et son entrée croisée est la racine **non négative** du produit des diagonales. Ce signe est un fait de la vraie Λ ; la seule positivité d'une densité arbitraire ne l'impliquerait pas. Le bloc singleton central, s'il existe, contribue e^(−aN)Λ(N/2)². ATOM permet d'encadrer chaque amplitude de BLOCK depuis D, donc agit sur les blocs que le commutateur heat conservait. Il ne fabrique pas de masse commune aux deux axes d'une paire.

Un contrat auxiliaire falsifiable existe. Pour 2≤m≤N−2, poser ℓ_m=m²max(0,A_T(m)−b_m(T)), h_m=m²A_T(m), et mettre leurs amplitudes0 aux indices0,1,N−1,N. Dans E_N, écrire ℓ=Σℓ_me_m, h=Σh_me_m et q_N=Σ_(m=2)^(N−2)Λ(m)e_m. Les termes omis de q_N ont un partenaire0 ou1 de Λ nulle : ⟨q_N,R_Nq_N⟩=C_N exactement. Alors, par ordre des entrées non négatives de BLOCK,

\[
\langle\ell,R_N\ell\rangle\le C_N\le\langle h,R_Nh\rangle.\tag{ENC}
\]

C'est une reconstruction opérateur, pas une estimation de formes bilinéaires arithmétiques. Avec V_N=√(N+1)log N et

\[
\eta_N(T)=\left[\sum_{m=2}^{N-2}(m^2b_m(T))^2\right]^{1/2}
\le\frac{24N^4\sqrt{N+1}}{T^2},
\]

chaque extrémité de ENC est à distance≤η_N(T)(2V_N+η_N(T)) de C_N. Cela suit de la norme1 de R_N et des erreurs coordonnées≤m²b_m. Le majorant grossier utilise δ_m≥1/(m+1). Ce rayon concerne les intégrales exactes A_T et n'inclut aucune erreur d'évaluation de D ou de quadrature. Il montre le coût en N, sans durée de calcul ni faisabilité annoncée.

Pour un futur test N=100000000, ENC exige des intervalles **produits** [A_m⁻,A_m⁺] contenant les vraies intégrales. Remplacer ℓ_m par m²max(0,A_m⁻−b_m) et h_m par m²max(0,A_m⁺) reste valide. Positions, évaluations de D, exponentielles, quadrature, logarithmes et arrondis doivent payer ces intervalles ; aucun rayon libre n'est accepté. Le présent paquet ne fournit ni ces valeurs ni leur producteur. Un intervalle incompatible avec les amplitudes canoniques réfuterait l'évaluateur ou son contrat, pas TRI. Il n'y a aucun PREP/PASS numérique.

La dette d'évaluation de D est concrète : un catalogue exact des vraies Λ(n) jusqu'à M entier≥3, des enclosures de log n et exp(−it log n), et la queue uniforme

\[
\left|D(t)-\sum_{n=2}^{M}c_ne^{-it\log n}\right|
\le\sum_{n>M}\frac{\log n}{n^2}
\le\int_M^\infty\frac{\log x}{x^2}\,dx
=\frac{\log M+1}{M}.\tag{DTAIL}
\]

Le dernier passage utilise la décroissance de log x/x² sur x≥3. Cette queue absolue de la vraie série spectrale n'est aucun reste de progression arithmétique et ne donne aucun signe à C_N. Une route d'évaluation via −ζ′/ζ exigerait en plus son raccord exact à D et la séparation effective du dénominateur ; ceux-ci ne sont pas attribués au seul PASS35. Aucun catalogue ni évaluateur n'est construit ici.

## 4. Pourquoi cette positivité ne paie pas la minoration

La positivité considérée est déjà portée par le seul secteur véritable p=2 :

\[
D_2(t)=(\log2)\sum_{k\ge1}2^{-k(2+it)},
\qquad P_2(w)=(\log2)\sum_{k\ge1}e^{-2^kw}.
\]

Ce sous-secteur a une masse log2/3<6, vérifie PD/TRI/ATOM et l'inversion Mellin par le même échange absolument convergent. Il est même le logarithme dérivé négatif du facteur eulérien (1−2^(−s))⁻¹ pour Re s>0. Pourtant sa projection réfléchie à N=14 est exactement nulle : les seuls supports pertinents sont2,4,8, et leurs partenaires12,10,6 sont absents ; le singleton7 est absent. Aucun calcul numérique n'est utilisé.

Une positivité de moments strictement plus forte ne remédie pas à cela. Pour a>0 et k≥0, (−1)^kP^(k)(a)=ΣΛ(n)n^ke^(−an). La matrice H_ij=(−1)^(i+j)P^(i+j)(a), 0≤i,j≤r, est strictement définie positive : sa forme est ΣΛ(n)e^(−an)|p(n)|² pour un polynôme p non nul ; déjà les supports infinis2^k empêchent p de s'annuler partout. Le même argument vaut pour P_2. Les dérivées terme à terme sont payées uniformément sur a≥a_0>0 par Σ(log n)n^ke^(−a_0n)<∞. Ainsi les moments thermiques stricts et la phase réelle positive peuvent coexister avec un bloc réfléchi sans masse commune.

Ce contre-modèle ne remplace pas la vraie ζ, et ne possède pas sa donnée complète de zéros ni sa fonctionnelle complétée. Il réfute uniquement l'inférence depuis PD, les moments positifs et la reconstruction positive vers un minorant strict uniforme. Il ne réfute aucune propriété supplémentaire de la vraie ζ ni toutes les méthodes spectrales. La recherche d'une identité spécifique à cette donnée complète reste ouverte.

## 5. Dette exacte et handoff

Le ledger demeure D_N=R_ref−C_N+Q_N+2max(e,0)−ε_tr, dans son régime canonique et avec ses fronts. ATOM/ENC paient une lecture possible de C_N, pas la comparaison à R_ref ni les corrections PP/front/excès. Poser directement un minorant d'affinité des blocs qui suffise au ledger importerait l'estimation manquante en prémisse. Aucune telle hypothèse n'est retenue. L'équation fonctionnelle et les symétries d'orbites déjà analysées ne sont pas rebaptisées comme nouvelle annulation.

Handoff : revue indépendante PAPER des identités TRI/ATOM/BAL/BLOCK/ENC et de la portée du contre-modèle ; éventuelle formalisation séparée de ces seuls auxiliaires ; ensuite seulement, si demandée, construction d'un évaluateur. Aucune propriété indépendante suffisante pour le signe global n'a été identifiée. D_N et WIN restent OPEN.

Provenance : les quatre notes exigées sont lues FULL (chunks c0f2b1/bede31/57d353/6f06d4), ainsi que la directive utilisateur, les reçus/handoff de la note canonique, l'ancien contrat Λ–Mellin02 et l'adjudication/clôture35. Lectures et SHA exacts sont dans read_receipts22.json. Les identités sont des dérivations PAPER de ce paquet, sans revendication de nouveauté mathématique ni de nouvel acquis Lean. Aucun fait externe spécialisé n'est utilisé ; aucune source externe n'a été consultée.
