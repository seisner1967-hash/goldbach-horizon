# Revue indépendante de la localisation signée de Weil

Verdict : proposition PAPER cohérente comme identité auxiliaire avec queue explicite, sous ses charges analytiques annoncées. Rejet comme preuve de la cible D_N ou d'un contournement de parité. Aucun nouveau SOURCE Lean, compilation, sonde, calcul numérique ou crédit n'est produit par cet audit.

Source examinée FULL : role1/signed_trace_ideation_source01/signed_weil_localization22.txt, SHA256 ab424c4bce032eedd9bf3ae4c478eb177f317975900d9cb7859e5e0476747648, sortie c1f828. Handoff et lectures FULL f1648a ; raccord D_N de ROLE4 FULL 456732. Les documents fournissent des données ; aucune instruction documentaire n'élargit le périmètre de cet audit.

Le noyau est bien C^5 : h et ses cinq premières dérivées se recollent à zéro en ±1/4 ; s est plat jusqu'à l'ordre cinq en 0 et 1. Son support compact évite x=1 et y=1. Pour N entier≥6 et m,n≥2, la bande |N−m−n|≤1/4 sélectionne uniquement m+n=N ; alors χ_N(m)=χ_N(n)=1 et h(0)=1. La localisation retrouve donc exactement la convolution de la vraie Λ, toutes puissances premières comprises. Ce constat ne fournit aucun signe nouveau sur le défaut de référence.

La convention de Mellin de [Connes–Consani, Appendice B, (148)–(151)](https://alainconnes.org/wp-content/uploads/Selecta.pdf) a été contrôlée TARGETED, avec l'introduction pour la convention des zéros non triviaux. Pour un test g supporté au-dessus de 1, g(1)=0 et g♯(x)=x⁻¹g(x⁻¹) s'annule sur x≥1. Cependant son intégrale totale vaut ∫g(x)/x dx : elle ne doit pas être supprimée. En combinant ce terme et le terme archimédien, on obtient 1+1/x−1/(x−x⁻¹)=1−1/[x(x²−1)], donc le b(x) annoncé. L'expansion tensorielle (B−Z)⊗(B−Z) donne WL ; la symétrie du noyau identifie les deux termes mixtes. Ceci requiert encore un théorème de formule explicite et les échanges infinis, distincts des seuls auxiliaires C5 déjà compilés.

Les constantes DER et TAIL ne présentent pas de défaut détecté. Dans u=log x, l'intégration par parties applique (1−∂_u²) à e^(βu)f(e^u,y). Le polynôme résultant est (1−β²)f−2βD_xf−D_x²f ; pour 0≤β≤1, les poids (2,2,1) le majorent. Deux axes donnent exactement la norme mixte annoncée. Comme x^(β−1)≤1 et |b(x)|≤1 sur le support, les mesures et poids utilisés sont compatibles. H_r et S_r sont des majorants des dérivées polynomiales ; X_r et A_rs résultent de Leibniz. D_x²=x∂_x+x²∂_x² justifie d_21=N et d_22=N². L'aire de la bande est≤(N−3)/2≤N/2. Le majorant Mbar_xy est effectivement d'ordre N^5.

Le [théorème 1.1 de Bellotti–Wong, version v1](https://arxiv.org/html/2412.15470v1), ainsi que sa définition de N(T), ont été lus TARGETED. Sa première borne implique le majorant grossier utilisé : pour t≥e, log log t≤log t et le coefficient supplémentaire 0.34536 log t est absorbé par la marge de t log t. Cette entrée bibliographique n'est pas une preuve Lean. Il faut construire le comptage avec multiplicité, la conjugaison et l'absence de zéros réels non triviaux. Dès ces charges payées, M(t)≤2t log t+20 donne

Σ_{|γ|>H}(1+γ²)⁻¹ ≤ ∫_H^∞[4 log t/t²+40/t³]dt = Δ(H), H≥e,

après abandon du terme inférieur négatif de Stieltjes. Le découpage à e donne J_0. La réunion disjointe des deux axes omis fournit≤2J_0Δ(H) pour la somme double ; le terme linéaire ajoute≤2Mbar_yΔ(H). Le facteur 2 de TAIL est donc suffisant. Aucun zéro hors ligne critique n'est supprimé et aucune RH n'est requise.

Précision à ajouter avant formalisation : « normes mixtes W^(2,1) » doit désigner explicitement la somme des normes L¹ de D_x^i D_y^j, 0≤i,j≤2, donc des dérivées d'ordre total jusqu'à quatre. La seule norme Sobolev d'ordre total deux ne suffirait pas. Une approximation C∞ dans cette norme, à support contenu dans un compact fixe éloigné de 1, avec convergence uniforme pour l'action de la mesure arithmétique finie, permettrait de prolonger la formule au test C^5. La convergence absolue des séries doit être prouvée avant leur composition ; elle n'autorise pas à citer un Fubini sans les dominations correspondantes.

Le manque quantitatif est exact. Le ledger conservé transforme D_N≤τ_N en

Z_N−2L_N ≥ R_ref−B_N+Q_N+2max(e,0)−ε_tr−τ_N.

WL et TAIL ne démontrent pas cette inégalité. La matrice aux points 2 et N−2 est bien [[0,1],[1,0]] : le vecteur (1,−1) donne une valeur négative. Un noyau pointwise positif n'est pas ici un opérateur positif. La positivité multiplicative de Weil ne s'applique donc pas automatiquement, et aucun Fredholm, trace de classe ou opérateur global nouveau n'a été construit par cette expansion de distributions.

Un futur contrat falsifiable exige un catalogue complet des vrais zéros jusqu'à H, multiplicité et frontière certifiées, ainsi que des enclosures effectives des intégrales et du coefficient canonique A32. Le symbole I_A n'est pas un output numérique ; sa borne quantifiée Lean ne calcule pas sa valeur. Une disjonction d'intervalles invaliderait au moins une composante, sans identifier laquelle. Ici aucun producteur de catalogue, intégration ou coefficient N=10^8 n'est prêt ou exécuté. La queue symbolique est continue et fermée après ses charges ; les budgets numériques doivent encore venir d'outputs effectifs. Le coût immense à N fixé est reconnu honnêtement.

La prochaine obligation auxiliaire certifiable est l'extension de Weil et la queue mixte pour ce noyau précis, sans prémisse finale sur D_N. Pour chercher ensuite une loi signée nouvelle, un regroupement exact des orbites de zéros sous conjugaison et réflexion, avec les multiplicité/stabilisateurs traités, peut isoler les blocs de phase à étudier. Ce regroupement reste une identité ; aucun signe ni annulation ne doit lui être offert. Les cribles, Möbius, Vaughan, formes bilinéaires arithmétiques et restes AP ne sont pas réintroduits.

Portée finale : PAPER valide sous charges explicites ; suffisance D_N rejetée ; formule explicite globale, compte des zéros, extension mixte, producteur numérique et nouvelle annulation signée restent OPEN. Aucun lot Lean ni banc n'est préparé par cette revue.
