# ROLE1 — corrélation de Weil sur un noyau compact, boucle 22

Statut : PROPOSITION PAPIER, avant sélection root. Zéro calcul expérimental, zéro nouveau producteur, zéro invocation Lean ou probe d’élaboration. Les fichiers de la boucle 21 sont arrêtés et conservés. Le noyau exact au coefficient N a une borne NON_INFORMATIVE_BOUND au budget étudié sur papier. L’annexe `role1/real_trace_annex.md` propose séparément une vraie trace continue testable, avec queue exponentielle et tous modes présents. Elle ne remplace pas le coefficient N et ne paie pas D_N. Aucune compilation ou victoire n’est revendiquée.

La famille proposée utilise la dualité globale premiers–zéros et une corrélation continue des distributions de Weil. Le noyau dépend uniquement de N et de paramètres géométriques rationnels. La somme sur les zéros, ses deux contributions mixtes, les puissances premières et la queue sont développées explicitement. Il n’y a ni décomposition en facteurs locaux, ni crible, ni inversion de Möbius, ni estimation scalaire de restes AP. Le terme spectral n’est pas défini comme la somme arithmétique à retrouver.

## 1. Formule exacte, normalisation et modes

Soit Z le multiensemble des zéros non triviaux de la vraie fonction ζ, avec leurs multiplicités, dans 0<Re(ρ)<1. Les deux demi-plans Im(ρ)>0 et Im(ρ)<0 sont conservés. Aucun zéro n’est placé sur Re=1/2 par hypothèse ; aucune simplicité n’est postulée. Le logarithme de x>0 est réel et x^(ρ−1)=exp((ρ−1)log x).

Pour f∈C_c^12((1,∞)), posons Mf(s)=∫_1^∞ f(x)x^(s−1)dx et a(x)=1−1/[x(x²−1)]. La spécialisation de la formule explicite de Weil donne

    Σ_{n≥2} Λ(n)f(n) = ∫_1^∞ f(x)a(x)dx − Σ_{ρ∈Z} Mf(ρ).                 (W1)

La normalisation de départ est celle de [Bombieri, section V, formule explicite, p.8](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf). Le domaine W y comprend les fonctions compactes C^12 utilisées ici. Notre spécialisation au support strictement supérieur à 1 est une dérivation : les modes f(1) et f(1/n) disparaissent ; Mf(0)−∫ f(x)/(x−x^−1)dx = −∫f(x)/[x(x²−1)]dx. Le mode du pôle en 1 donne ∫f. Les zéros triviaux et le terme archimédien sont donc conservés exactement dans a, et non dans une erreur non spécifiée. La constante de ψ ne contribue pas à cette distribution testée loin de 1. Les sommes de zéros sont absolument convergentes grâce aux bornes de la section 3.

Soit K∈C_c^12((1,∞)²), avec dérivées mixtes jusqu’à l’ordre total 12. Définissons

    M_K(s,t) = ∫∫ K(x,y)x^(s−1)y^(t−1) dxdy,
    U_x(s)   = ∫∫ K(x,y)x^(s−1)a(y) dxdy,
    U_y(t)   = ∫∫ K(x,y)a(x)y^(t−1) dxdy,
    A(K)     = ∫∫ K(x,y)a(x)a(y) dxdy.

Deux applications de (W1), justifiées par convergence absolue uniforme et Fubini, conduisent à l’identité proposée

    Σ_{n,m≥2} Λ(n)Λ(m)K(n,m)
      = A(K) − Σ_ρ U_x(ρ) − Σ_σ U_y(σ) + Σ_{ρ,σ} M_K(ρ,σ).             (W2)

Toutes les intégrales portent sur (1,∞)². Le noyau peut être non séparable ; (W2) ne se réduit pas à définir un opérateur dont la trace recopierait la réponse. L’information développée est le couplage entre les vrais zéros, avec termes de pôles et corrections exactes. L’identité proposée est une conséquence de la formule classique, pas une revendication de nouveauté de cette dernière ou de contournement de parité déjà obtenu.

## 2. Noyau isolant exactement un entier

Paramètres figés proposés : N entier ≥5, δ=1/4, J=12, ordre k=3. Le test fini demandé est N=100000000. Définissons le smoothstep rationnel

    C = 25!/(12!)²,
    S(t)=0 si t≤0 ; S(t)=1 si t≥1 ;
    S(t)=C Σ_{i=0}^{12} (−1)^i binom(12,i)t^(13+i)/(13+i) si 0<t<1.

Il satisfait S′(t)=C t^12(1−t)^12 sur (0,1), 0≤S≤1 et S∈C^12. Posons

    χ_N(x)=S(2x−3) S(2N−3−2x),
    b(t)=(1−t²)^13 si |t|<1, et 0 sinon,
    K_N(x,y)=χ_N(x)χ_N(y)b((x+y−N)/δ).

Le support de χ_N est [3/2,N−3/2], χ_N=1 sur [2,N−2]. Le noyau appartient à C_c^12((1,∞)²), même aux coutures où toutes les dérivées nécessaires s’annulent. Aux entiers n,m≥2, il vaut exactement 1 lorsque n+m=N et 0 sinon. Il n’y a aucune approximation de coefficient et aucune extraction sur un contour seulement réel.

Ainsi le membre arithmétique de (W2) est exactement

    R_Λ(N)=Σ_{2≤n≤N−2} Λ(n)Λ(N−n).                                  (W3)

Pour revenir aux deux premiers, soit

    R_θ(N)=Σ_{p+q=N, p et q premiers} log p log q,
    PP_N=Σ_{2≤n≤N−2, n ou N−n est une puissance première propre}
                     Λ(n)Λ(N−n).

Alors R_Λ(N)=R_θ(N)+PP_N. Le retrait porte sur l’union des deux axes ; les couples où les deux axes sont des puissances propres sont comptés une fois. Λ(1)=0 ; les endpoints 2 et N−2, et les couples p=q, restent présents dans la somme ordonnée. Aucun masque μ(n)² n’est introduit pour les traiter.

## 3. Queue spectrale et enveloppe continue construite

Écrivons E_x=x∂_x, E_y=y∂_y et L_x=(2−E_x)^6, L_y=(2−E_y)^6. L’adjoint Mellin exact est

    M_{L_xK}(s,t)=(2+s)^6 M_K(s,t),
    M_{L_yK}(s,t)=(2+t)^6 M_K(s,t).

Sur le support, x,y≥3/2 et 0≤Re(s),Re(t)≤1. Par conséquent x^(Re(s)−1), y^(Re(t)−1)≤1 et |2+s|^6≥(1+Im(s)²)^3. Posons

    B_x=∫∫|L_x K_N| dxdy, B_y=∫∫|L_y K_N| dxdy,
    B_K=∫∫|L_x L_y K_N| dxdy, w(t)=(1+t²)^−3.

Comme 0≤a≤1 pour x≥3/2,

    |U_x(ρ)|≤B_x w(Imρ), |U_y(σ)|≤B_y w(Imσ),
    |M_K(ρ,σ)|≤B_K w(Imρ)w(Imσ).                                    (W4)

Le choix de L évite une hypothèse cachée sur les zéros de petite hauteur : utiliser sans justification (1−E²)^3 et remplacer son multiplicateur par (1+γ²)^3 serait incorrect. Cette réparation vient de l’audit papier ROLE6 ; elle n’est pas un échec Lean, aucune invocation n’ayant eu lieu.

Un corollaire conservateur du [Corollaire 1 de Trudgian, version arXiv v2, p.2](https://arxiv.org/pdf/1208.5846) est N_+(t)≤t log t pour t≥10, où N_+ compte tous les zéros à hauteur positive avec multiplicité. En effet son erreur est ≤0.111log t+0.275loglog t+2.450+0.02 ; ajouter 7/8, majorer loglog t≤log t et le terme principal par (t/2)log t donne une borne strictement inférieure à t log t dès t≥10. La borne aux hauteurs de zéros s’obtient par limite à droite si nécessaire ; on ne perd aucune multiplicité.

Intégration de Stieltjes de w et suppression d’un terme de bord négatif donnent, pour T≥10,

    Σ_{ρ:|Imρ|>T} w(Imρ) ≤ E_Z(T),
    E_Z(T)=12 T^−5 (log T/5+1/25),
    Σ_{ρ∈Z} w(Imρ) ≤ Zbar=20log10+E_Z(10).                           (W5)

Les deux signes des hauteurs expliquent le facteur 12. La dérivation utilise −w′(t)=6t(1+t²)^−4≤6t^−7, puis ∫_T^∞t^−6log t dt=T^−5(log T/5+1/25). Aucun zéro non trivial n’est réel ; le compte couvre donc Z par conjugaison. La borne pour les hauteurs ≤10 utilise N_+(10)≤10log10, sans supposer ce domaine vide.

Avec Z_T={ρ∈Z:|Imρ|≤T}, notons

    S_T(K)=A(K)−Σ_{ρ∈Z_T}U_x(ρ)−Σ_{σ∈Z_T}U_y(σ)
                         +Σ_{ρ,σ∈Z_T}M_K(ρ,σ).

La queue hors du carré est majorée en séparant les deux axes, et toutes les contributions mixtes sont conservées. On obtient

    |R_Λ(N)−S_T(K_N)| ≤ (B_x+B_y+2B_K Zbar)E_Z(T).                  (W6)

Le membre droit est continu en T≥10, contrairement à un budget dépendant du nombre exact de zéros déjà listés. Il est aussi continu en N réel≥5 et en δ>0 dans les expressions de majoration ci-dessous. Cette majoration ne présuppose aucune annulation spectrale favorable.

### Majorants fermés, sans norme libre

Toutes les constantes suivantes sont des sommes finies explicites de rationnels lorsque N et δ sont rationnels. Pour 1≤r≤12, définissons

    C_0=1,
    C_r=C Σ_{i=0}^{12} binom(12,i)/(13+i) · (13+i)!/(13+i−r)!,
    M_r=2^r Σ_{h=0}^{r}binom(r,h) C_h C_{r−h}, avec M_0=1.

Elles majorent les dérivées ordinaires de χ_N. Pour 1≤d≤12,

    D_0=1,
    D_d=Σ_{0≤i≤13, 2i≥d}binom(13,i) (2i)!/(2i−d)!.

Elles majorent celles de b sur chaque pièce et aux coutures. Pour r+s≤12, posons

    P_rs=Σ_{a=0}^{r}Σ_{b=0}^{s}binom(r,a)binom(s,b)
                     M_{r−a}M_{s−b} δ^(−a−b)D_{a+b}.

Alors |∂_x^r∂_y^sK_N|≤P_rs. Écrivons {j r} les nombres de Stirling de deuxième espèce, avec {0 0}=1. L’identité d’opérateurs E^j=Σ_{r=0}^{j}{j r}x^r∂^r et le volume du support ≤2δN donnent

    Ibar_jl=2δN Σ_{r=0}^{j}Σ_{s=0}^{l}{j r}{l s}N^(r+s) P_rs

pour 0≤j,l≤6. Il majore ∫∫|E_x^jE_y^lK_N|. Avec c_j=binom(6,j)2^(6−j), définissons

    Bbar_x=Σ_{j=0}^{6}c_j Ibar_j0,
    Bbar_y=Σ_{l=0}^{6}c_l Ibar_0l,
    Bbar_K=Σ_{j,l=0}^{6}c_jc_l Ibar_jl,
    C_N=Bbar_x+Bbar_y+2Bbar_K Zbar,
    E_N(T)=C_N ·12T^−5(log T/5+1/25).                               (W7)

La borne finale complètement fermée est |R_Λ(N)−S_T(K_N)|≤E_N(T). Il n’y a aucun champ « B petit », aucun oracle pour une norme et aucune erreur O(·) dont la constante serait masquée. Les majorants peuvent être améliorés par intégrales rationnelles exactes des pièces ; le contrat initial utilise les expressions affichées, pas un ajustement à la différence observée.

À δ fixé, ce majorant a une croissance dominante en N^13 et une décroissance en T^−5log T. Il peut être très pessimiste. Une vraie identité avec enveloppe finie n’est pas une preuve de précision utile : le rôle6 doit publier le coût et la largeur d’intervalle obtenus avant toute exécution autorisée. Le double calcul naïf demande O(N_+(T)²) intégrales ; aucun coût faible n’est annoncé.

Le préaudit ROLE6 rend cette limite explicite : le seul terme j=l=r=s=6 donne Bbar_K≥2^23 N^13 lorsque δ=1/4. Zbar>20 et E_Z(T)≥(12/25)T^−5 impliquent E_N(T)≥(96/5)·2^23·N^13/T^5. À N=10^8 et T≤3·10^12, cette enveloppe dépasse10^49 ; pour exiger E_N(T)≤1/100, ce majorant impose T>10^22. Ces inégalités concernent le majorant choisi, jamais l’erreur réelle. Ce sont des constatations papier, pas un test exécuté. L’omission de A(K) aurait une amplitude ≥(25/36)(3/4)^13 δ(N−6)>1024, tout en restant invisible à une tolérance10^49. Le contrat sharp est donc actuellement non discriminant et ne doit pas être lancé comme test de réussite. L’annexe de trace réelle ajoute un autre sous-banc, de portée explicitement locale.

## 4. Axe modulaire exact et combinaison examinée

La theta de réseau θ(τ)=Σ_{n∈Z}exp(πin²τ), Imτ>0, satisfait θ(−1/τ)=(-iτ)^(1/2)θ(τ) et θ(τ+2)=θ(τ). Le choix de racine est celui continu sur le demi-plan avec valeur positive à τ=i. La preuve vient de Poisson ; [Gangl, propositions 7.4–7.5, normalisation 2π, p.3–5](https://www.maths.dur.ac.uk/users/herbert.gangl/MF-2014/MFLecture7-easyreading.pdf) donne la version de niveau4 équivalente. Les déclarations correspondantes sont présentes dans le cache mathlib local lu : `jacobiTheta_S_smul`, `jacobiTheta_T_sq_smul`, `norm_jacobiTheta_sub_one_le`.

Cette structure appartient au réseau entier. Elle ne transfère pas automatiquement sa transformation à une série où les coefficients sont Λ(n) ou un détecteur de primalité. Je ne postule aucune modularité d’une série de premiers, ni aucune positivité par analogie avec la géométrie sur corps finis.

Une combinaison admissible utilise la theta uniquement comme noyau géométrique indépendant des premiers. Pour L=4N, t>0 et s réel, posons

    H_L,t(s)=Σ_{j∈Z}exp(−πt(s+jL)²),
    H_L,t(s)=(L√t)^−1 Σ_{k∈Z}exp(−πk²/(tL²))exp(2πiks/L),           (M1)
    K_heat(x,y)=χ_N(x)χ_N(y) H_L,t(x+y−N)/H_L,t(0).

Poisson rend (M1) exact, avec mode zéro (L√t)^−1 conservé. Appliquer (W2) à ce noyau compact donne une trace spectrale exacte et une invariance du noyau de chaleur sous changement de représentation. Aux entiers, la diagonale additive vaut1 ; les autres termes ne disparaissent pas. Leur somme positive Leak_N,t est conservée par

    R_Λ(N)=TraceWeil(K_heat)−Leak_N,t.

Pour |s|≤N et entier non nul, H_L,t(s)/H_L,t(0)≤q_N(t), où

    q_N(t)=exp(−πt)+2exp(−9πtN²)/(1−exp(−16πtN²)).

Donc 0≤Leak_N,t≤N²(logN)²q_N(t), enveloppe fermée continue pour t>0. Elle découle de |s+jL|≥jL−N et (jL−N)²≥9N²+(j−1)L². Les queues géométriques et les dérivées du noyau theta devraient être traitées séparément des queues des zéros. Cette combinaison développe une véritable information spectrale via (W2) ; (M1) seul resterait une réécriture Fourier et ne satisferait pas le contrat utilisateur.

Le candidat compact est préféré pour cette sélection proposée : il évite entièrement la fuite aux entiers et ne requiert pas un second budget infini theta. La variante mixte reste un candidat différent, pas un gain établi. Le rôle2 explore indépendamment la vraie diffusion de la surface modulaire ; je ne prolonge pas ni ne revendique son travail.

## 5. Contrat de formalisation et relation au D_N

Le contrat détaillé est `role1/lean_contract.md` ; le protocole sharp sans exécution est `role1/numeric_contract.md`, désormais déclaré non discriminant. Le sous-banc falsifiable proposé est l’annexe `role1/real_trace_annex.md`, échelle Y=√N, et non le coefficient R_Λ(N). Les objets sont les vrais ζ, Λ, multiplicité analytique des zéros, intégrales et noyau affiché. Une hypothèse libre « Weil est vrai » ou une liste arbitraire de nombres nommés zéros ne peut être promue au théorème final. La formule explicite globale et la borne de compte demeurent à formaliser si aucune dépendance vérifiée du cache ne les fournit. Le fait que des modules auxiliaires de queue ou theta puissent compiler ne constitue pas cette preuve globale.

La recherche ciblée en lecture seule a identifié `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` dans `Mathlib.NumberTheory.LSeries.Dirichlet`, sous Re(s)>1 ; elle n’a pas identifié de formule explicite Weil ni de compte global des zéros dans les répertoires recherchés. C’est un constat ciblé et non une preuve d’absence dans tout le monde Lean. Zéro probe/compilation a été effectué.

R_θ(N) est une vraie contribution globale de deux premiers. Son identité n’est pas une nouvelle définition de D_N et ne paie pas automatiquement le bilan fixé

    D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0).

Toute application au bilan devra donner un raccord explicite aux poids, domaines, signes et charges de ce bilan, en conservant les fronts et puissances premières. Aucun raccord de cette force n’est prétendu ici. Il reste à obtenir une information quantitative favorable sur la trace couplée et à justifier son transfert au résidu. Le seuil source u=logN≥10^24 reste celui des acquis ; le test fini N=10^8 ne satisfait pas ce seuil et ne peut valider l’application asymptotique.

## 6. Décision proposée et traçabilité

Les cinq déclarations, les quatre mouvements, le probe et le self-check sont dans `role1/ideation_probe_candidates.md`. Root choisit et ajoute seul un nœud. Cette proposition distingue : identité mathématique papier dérivée, contrat de troncature effectif, résultats numériques futurs, preuve Lean future et victoire globale absente.

Sources primaires lues de façon ciblée : Bombieri/Clay, Trudgian arXiv v2, Gangl, Connes–Consani–Marcolli et Cantarini. Les deux dernières éclairent respectivement la lecture de trace et l’existence de formules sur des moyennes de Goldbach ; elles n’ajoutent aucune hypothèse de positivité ou de RH. Aucun PDF n’est déclaré lu intégralement à partir de quelques pages. Les essais web refusés et recherches sans hit sont dans les reçus. Les SHA et scopes des fichiers locaux sont consignés dans `role1/read_receipts.json` et `role1/manifest.json`.

Le préaudit papier ROLE6 a confirmé la forme de E_Z(T), demandé un compte complet/Turing pour les zéros effectivement utilisés, et corrigé le choix d’opérateur Mellin. Aucun FAIL de compilateur ou résultat de test n’est inventé à partir de ces échanges. Les prochaines portes restent fermées jusqu’à décision root.
