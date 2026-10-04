# Canal canonique de réflexion : test d'une annulation par commutateur — PAPER

**Verdict borné.** Le contrat coefficient34 paie sur SOURCE le passage d'une erreur uniforme de trace à une erreur de coefficient ; il ne donne aucun signe au défaut canonique. La construction exacte ci-dessous teste une piste opérateur de type Ward. Elle montre pourquoi le commutateur naturel ne retire pas le canal recherché et pourquoi sa version « reste nul » est incompatible avec la vraie Λ pour un fond constant. Aucun mécanisme supplémentaire justifié n'est retenu comme contournement. Note PAPER uniquement, sans Lean, probe, préparation, import de candidat, calcul numérique ou binaire ; tous les anciens paquets restent gelés.

## 1. Ce que le rayon du coefficient paie

Pour a>0, H≥0 et N naturel, les objets sont exactement P(w)=ΣΛ(n)e^{-nw}, D(t)=ΣΛ(n)n^{-2-it} et K(w,t)=Γ(2+it)w^{-2-it}, avec toutes les puissances premières et le cpow principal. Le paquet coefficient34 écrit

\[
C_N=\frac{e^{aN}}{2\pi}\int_{-\pi}^{\pi}P(a-i\theta)^2e^{-iN\theta}d\theta,
\qquad
|C_N-C_{N,H}(a)|\le\mathcal E_N(a,H),
\]
\[
\mathcal E_N=e^{aN}(2U\varepsilon+\varepsilon^2),\quad
U=\frac{e^{-a}}{(1-e^{-a})^2},\quad
\varepsilon=\frac{24e^{-dH}}{\pi a^2d},\quad d=\tfrac12\arctan(a/\pi).
\]

La vraie série P est périodique ; P_H et son cpow ne le sont pas postulés. La continuité de P_H à H fixé et les deux intégrabilités sont construites. Ce paquet reste SOURCE, dépendant du mainΛ/EΛ/Geometry prospectifs à son gel ; la revue indépendante est une revue SOURCE, pas une compilation. Le rayon paie uniquement la coupure Mellin, sans quadrature, arrondi ni évaluateur complet.

Le ledger conservé est

\[
D_N=R_{\rm ref}-C_N+Q_N+2\max(e,0)-\varepsilon_{\rm tr}.
\]

Ainsi diminuer \(\mathcal E_N\) permet de mesurer un coefficient. Cela ne contrôle ni le défaut signé R_ref−C_N, ni Q_N, ni l'excès couvert et ses fronts. Les conditions et le régime de la monographie restent ceux des acquis.

## 2. Opérateur concret sur un espace continu

Fixer N≥6 et prendre L² du cercle, de mesure dθ/(2π). Écrire e_n(θ)=exp(inθ), et E_N=span{e_0,…,e_N}. C'est une compression de l'espace continu, avec ses vrais caractères. Définir

\[
v_{N,a}(\theta)=\sum_{n=0}^N\Lambda(n)e^{-an}e_n(\theta),\qquad
(R_Nf)(\theta)=e^{iN\theta}f(-\theta).
\]

R_N est une involution unitaire autoadjointe sur E_N, car R_Ne_n=e_{N-n}. La densité de rang1 ρ_v=|v⟩⟨v| est positive. L'orthogonalité finie et les poids réels donnent exactement

\[
\operatorname{Tr}(\rho_vR_N)=\langle v,R_Nv\rangle=e^{-aN}C_N.\tag{R}
\]

Cette égalité sert à identifier le canal ; elle n'est pas annoncée comme une nouvelle minoration. La covariance positive ρ_v contient sa position relative à R_N : oublier celle-ci ne permet pas de récupérer son signe.

Pour rendre le fond concret, poser b_n=κ pour 2≤n≤N−2 et b_n=0 sinon, puis b(θ)=Σb_ne^{-an}e_n(θ), σ=|b⟩⟨b|, Δ=ρ_v−σ. Pour tout κ≥0,

\[
\operatorname{Tr}(\Delta R_N)=e^{-aN}\bigl(C_N-\kappa^2(N-3)\bigr).\tag{REF}
\]

Dans un régime où la condition indépendante R_ref≥0 est satisfaite, κ=√(R_ref/(N−3)) branche positivement définie identifie le second terme à la référence fixée. Sinon garder κ quelconque et conserver séparément R_ref−κ²(N−3). Ce fond ne remplace aucun front : mettre la référence dans σ est une définition, pas une estimation de Δ.

## 3. Identité Ward exacte, et canal qui lui échappe

Sur E_N définir le vrai générateur géométrique

\[
A_N=(-i\partial_\theta-N/2)^2,\qquad
Q_\tau=e^{-\tau A_N},\quad\tau>0.
\]

Ses valeurs propres sont d_n=(n−N/2)² ; les espaces propres sont précisément les paires {n,N−n}, et le singleton N/2 lorsque N est pair. Noter Π_d leurs projecteurs orthogonaux et λ_d=e^{-τd}. R_N commute avec chacun de ces projecteurs et avec Q_τ.

Tout opérateur Δ de ce même espace fini possède la décomposition **construite**, sans prémisse d'annulation,

\[
F=\sum_d\Pi_d\Delta\Pi_d,\qquad
X=\sum_{d\ne d'}\frac{\Pi_d\Delta\Pi_{d'}}{\lambda_d-\lambda_{d'}},
\qquad
\Delta=[Q_\tau,X]+F.\tag{W}
\]

Les sommes sont finies et λ_d≠λ_d′ pour d≠d′. Le prix de l'inversion est visible : d≤N²/4 et deux énergies distinctes diffèrent d'au moins1, donc

\[
|\lambda_d-\lambda_{d'}|^{-1}
\le g_N(\tau):=\frac{e^{\tau N^2/4}}{e^\tau-1},\qquad
\|X\|_{\rm HS}\le g_N(\tau)\|\Delta\|_{\rm HS}.
\]

Les blocs orthogonaux paient la dernière inégalité. Cette constante fermée est continue pour τ>0 ; ce n'est pas un budget de signe ni une durée de calcul.

La cyclicité de la trace finie donne Tr([Q_τ,X]R_N)=0. Mais, exactement,

\[
\Pi_dF\Pi_d=\Pi_d\Delta\Pi_d,
\qquad
\operatorname{Tr}(FR_N)=\operatorname{Tr}(\Delta R_N).\tag{LOCK}
\]

Le commutateur a retiré seulement les blocs entre énergies différentes. Le coefficient additif est tout entier dans les blocs dégénérés **conservés**. Une covariance ou une invariance qui agit uniquement sur ces blocs hors diagonale ne fournit donc aucune annulation du défaut canonique.

La version candidate « Δ est un pur commutateur, F=0 » est falsifiable bloc par bloc. Pour la vraie Λ et le fond constant ci-dessus, elle est même impossible : ses entrées diagonales imposeraient simultanément Λ(2)²=κ² et Λ(3)²=κ². Or Λ(2)=log2, Λ(3)=log3, et 0<log2<log3. Les facteurs e^{-2an}>0 ne changent pas cette contradiction. Aucune asymptotique, RH, crible ou estimation de reste arithmétique n'intervient.

Cette réfutation concerne ce générateur et ce fond explicites ; elle ne réfute pas une propriété supplémentaire de la véritable ζ, ni la densité canonique, ni la cible. Choisir σ=ρ_v supprimerait Δ mais importerait alors le coefficient voulu dans la référence : ce serait circulaire.

## 4. Charge suivante et critère de falsification honnête

Une nouvelle annulation opérateur utile doit agir **à l'intérieur** des paires d'énergie n,N−n et doit venir d'une propriété réellement démontrée de la trace canonique ou de la vraie ζ. Les symétries des orbites ne la donnent pas : elles conservent les deux phases cos(γlog(x/y)) et cos(γlog(xy)), ainsi que les couplages entre orbites. Aucune positivité modulaire, adélique ou de Connes n'est postulée.

Le prochain sous-contrat recevable serait une construction indépendante explicite d'un terme signé F et d'une identité telle que W, avec une estimation de ses blocs conservés déduite d'une propriété analytique de ζ et une queue calculable. Il doit préciser la formule explicite, les multiplicités, les branches, l'intégrabilité et le reste. Aucun tel mécanisme n'est aujourd'hui justifié. Offrir simplement \(\|F\|_1\le\eta\) avec η choisi pour D_N serait une nouvelle prémisse cachant la lacune, car \(|\operatorname{Tr}(FR_N)|\le\|F\|_1\) porte déjà le défaut recherché.

Pour falsifier une future égalité de signe proposée sur cette même référence, une enclosure réellement produite de C_NH et son rayon total suffirait à réfuter C_N=κ²(N−3) si la distance au fond dépasse ce rayon. Pour le présent contrat, seul \(\mathcal E_N\) paie la troncature H ; il faut encore toutes les erreurs de D, quadrature, positions/poids et arrondi avant ce test. Aucun point ni test à N=10^8 n'a été exécuté ici.

**Résultat retenu :** W/LOCK identifient précisément le canal manquant, sans le majorer. L'annulation signée canonique, les corrections PP/front et D_N restent ouverts ; aucun candidat de victoire n'est annoncé.

Provenance : coefficient34 SOURCE bf9b8257 (contrat b6904088, handoff e55aa804) et ses lectures FULL précédentes ; dn_gap_audit22/operator_phase_obstacle22 relus FULL e4d7de ; orbites ROLE1 et revue ROLE4 relues FULL512a40. Les identités opérateur et le prix g_N sont des dérivations PAPER nouvelles, pas de nouveaux acquis Lean. Aucune source, banque ou archive ancienne n'est modifiée.
