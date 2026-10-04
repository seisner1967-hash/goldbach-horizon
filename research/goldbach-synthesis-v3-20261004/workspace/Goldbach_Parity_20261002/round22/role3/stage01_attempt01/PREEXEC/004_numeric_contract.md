# ROLE2/22 — contrat numérique proposé

Statut : **PAPER_ONLY / NOT_EXECUTED / OPEN_CERTIFIED_PRODUCER**. Les formules ont été auditées sur papier parROLE6, pas évaluées. Trois bancs distincts évitent de présenter un test auxiliaire comme une extractionN ou une victoireD_N. N=100000000 est fixé ; aucune donnée historique, fenêtre, masque, ancienne banque ni logPASS n'est réutilisé. La préparation source-only parROLE6 doit figer ses propres sources et recevoir un nouveau gate avant toute invocation math.

## G0 — EPSTEIN_UNFOLDING_AUX, premier banc géométrique

Objet continu neuf : poury>0,m≠0,Q>|m|,

I_Q(m,y)=∫_0^1Σ_(n=−Q)^Q y^(3/2)[(mx+n)²+(my)²]^(-3/2)dx.

24cas proposés, avant toute réduction :

- 18cas y∈{1/2,1,2},m∈{−7,−2,−1,1,2,7},Q=4096 ;
- 6cas y=√N=10000,m∈{−7,−2,−1,1,2,7},Q=2^20.

Paramètres de certificats suggérés : p=96 bits pour racines par bornes rationnelles, tolérances1/10^5 pour le banc, à confirmer par dérivation du budget et root. Le banc haut a une queue strictement<10^−6 : y^(3/2)=10^6 etQ−|m|>10^6. Ces inégalités doivent recevoir des preuves rationnelles et non des arrondis flottants de confiance.

Primitive : q=|m|,a=q y,H_a(u)=u/sqrt(u²+a²), H'_a=a²(u²+a²)^−3/2. Par substitution signée et télescope,

I_Q(m,y)=y^(3/2)/(q a²) [Σ_(u=Q+1)^(Q+q)H_a(u)−Σ_(u=−Q)^(−Q+q−1)H_a(u)].

Pourm<0, prouver la bijectionn↦−n sur la fenêtre entière avant de remplacer m parq. Le producteur de basse échelle doit former la fenêtre entière−4096..4096 et comparer sa somme de différences de primitives à l'expression indépendante des2q extrémités. Les6cas hauts représentent explicitement2Q+1 termes entiers mais calculent seulement2q extrémités après le télescope exact ; ils ne prétendent pas avoir évalué chaque terme du réseau. La forme d'origine avec signes est préservée dans les métadonnées de cas.

Valeur continue complète : I_∞=2/(q²sqrt(y)). Queue réelle dérivée :

0≤I_∞−I_Q≤R_Q=y^(3/2)/(Q−q)².

Chaque cas émet les bornes rationnelles des racines, avec certificats `lo²≤u²+a²≤hi²`,0≤lo≤hi ; il propage des intervalles exacts avec inversions gardées, puis produit [loI,hiI] et un intervalle pourI_∞. Comparer une intersection ou un écart nu ne suffit pas : vérifier les preuves du télescope, la borneR_Q et que le rayon d'arrondi entre dans la tolérance du cas. Toute division parq,a,lo exige une garde positive. Lesu=0 éventuels sont conservés. Pas de specialcase de signe qui supprime un cas entier.

Sanity tests falsifiables : injecter un facteur1/q omis, un facteur2 omis, un signe d'extrémité inversé et la plageQ..Q+q−1 erronée ; chaque mutation devra être détectée par des cas pertinents et un budget donnant séparation. Ces tests ne sont pas des valeurs déjà exécutées. Conserver également le casm=0 comme **branche séparée**, pas comme évaluation du noyau ci-dessus : ce mode contient n≠0, la sommeζ(3)y^(3/2) et le facteur1/2 du réseau. La preuve globale réunissantm=0 et±m reste un livrable formel, pas un résultat numérique deG0.

G0 vérifie un déroulement géométrique à une valeur réelle des, sans Gamma complexe, zéros, RH, caractérisation du vrai scattering ni primalité. Sa dépendanceN apparaît uniquement par l'échelle cusp√N. Verdict possible : EPSTEIN_UNFOLDING_AUX_PASS/FAIL. **Jamais COEFFICIENT_N_PASS ou D_N_PASS.** Le banc ne remplit pas à lui seul le contrat arithmétique strict sur1..N.

## H0 — HEAT_AUX, signal global réel avec référence entièreN

Objet : F(t)=ΣΛ(n)e^(−nt) reconstruit par le télescope de diffusion. Paramètres papier : t=64logN/N,K=64,h=1/32,J=4096,8193 nœuds Mellin, environ524352 appels deφ/ψ si évalués directement. Iciδ=π/2, car t est réel positif ; ceδ ne peut être transporté au contourC0.

Référence stricte : tous les entiers1≤n≤N, avant masque, avec producteur neuf de certificats premier/composite, puissance première propre, exposant etbase. Λ(1)=0 et les entrées0/nonunités sont traitées par domaine réel, pas supprimées pour améliorer un score. Les entiers non premiers, puissances répétées et valeurs deΛ doivent être représentés sans réutiliser un crible/banque antérieur. Des certificats directs d'algorithmes de primalité/composité sont permis ; un booléen non certifié ne remplace pas le poids exact. Conservation des indices entiers et comptage indépendant requis.

Queue de référence : avec r=e^−t,

R_N=r^(N+1)[(N+1)−Nr]/(1−r)².

Le protocole devra certifier AVANT exécution que

R_N+C(64)+A_Mellin(t,1/32)+E_J(t,1/32,4096)+ε_eval+ε_ref≤10^−8.

C,A_Mellin,E_J sont les fonctions fermées de uniform_formula. ε_eval etε_ref sont de vrais rayons de producteurs dirigés pourζ,ζ',Γ,ψ,exp,log,pouvoirs/sommes et certificats entiers. Aucun petit rayon n'est une entrée libre. L'expressionφ à base deζ est un test de l'identité analytique, pas une vérification indépendante du PDE. Une référence géométrique indépendante appartient àG0/O1 et ne sera pas confondue avec ce test.

État actuel : aucune bibliothèque Gamma/ζ complexe à arrondi certifié n'est présumée disponible. Construire un producteur d'intervalles avec queues dérivées (intégrale Gamma, Euler–Maclaurinζ, dérivées, branches) est une obligation source-only avant le gate math. Le recours à une bibliothèque devra lire son contrat et certifier ses sorties ; mpmath à haute précision seul n'est pas un certificat. Verdict possible H0 : HEAT_AUX_PASS/FAIL, distinct deC0 etD_N.

## C0 — COEFFICIENT_N, contour complet et enveloppe fermée

Paramètres exacts papier : N=10^8,η=8logN/N,M=N+1=100000001,K=512,h=1/128,J=1280000000000. Domaines0<η≤1,h>0,K≥2,(J+1)h≥1,a=2π/h≥log2,ηe^a≥4a à prouver ; aucune garde sourceu≥10^24 n'est invoquée. Exécuter tous lesj extérieurs0..M−1,θ_j=2πj/M sur le cercle, tous les nœuds intérieurs−J..J et tous les rangs0..K−1 si une accélération n'a pas été démontrée. Une symétrie complexconjugate utilisée pour réduire des évaluations exige sa preuve et les endpoints réels.

Poserδ=π/2−arctan(π/η),q=e^(−2π/h),b=e^(−δh),j0=J+1. Les fonctions fermées sont

C(σ)=log2·2^−σ+2^(1−σ)[log2/(σ−1)+1/(σ−1)²],

A_Mellin=2η^(−3/2)q^(1/2)/(1−q^(1/2))+2η^−1q/(1−q)+4q²/(1−q²),

E_J=(6C(2)/π)η^−2h³b^j0[j0²/(1−b)+2j0b/(1−b)²+b(1+b)/(1−b)³],

ε_F=C(K)+A_Mellin+E_J+ε_eval.

LesΓ,ψ,φ'/φ,t^−w sont évalués sur le domaine complet avec des branches explicites. Les rayons seront propagés simultanément avec la taille absolueB_F=e^−η/(1−e^−η)². L'analyse Schwartz de Poisson, toutes ses dérivées et les séries sur les deux signes d'alias constituent des preuves nécessaires, pas des diagnostics sur un petitT.

G_N=Σ_(1≤n<N)Λ(n)Λ(N−n). L'estimateur de cercle donne l'alias exactΣ_(l≥1)G_(N+lM)e^(−ηlM) ; il n'y a pas de termes négatifs parce queM>N. Poserx=e^(−ηM) ; payer

A_circle=(1/6)[N³x/(1−x)+3N²Mx/(1−x)²+3NM²x(1+x)/(1−x)³+M³x(1+4x+x²)/(1−x)^4].

Enveloppe complète : |G_N−G_hat|≤e^(ηN)(2B_Fε_F+ε_F²)+A_circle+ε_outer_round. Tout ε_eval devra être dérivé du budget final ; par exemple une cibleτ ne peut pas être atteinte en donnantε_F≤τ lorsque e^(ηN)=N^8=10^64. Il faut une répartition positive démontrée deτ, dontε_F≤τ/(4N^8B_F) plus un paiement séparé deε_F², des alias et rayons. La tolérance finale choisie doit être annoncée et certifiée avant le banc.

Coût déclaré :100000001 signaux ×2560000000001 nœuds intérieurs ×jusqu'à512 rangs. Le contrat d'erreur est mathématiquement fermé et continu sous ses gardes, mais ce plan direct est astronomique et **NON_PRATICABLE_COMME_BANC_ACTUEL**. Aucune annoncePREPARED/mathPASS. Une accélération ou un autre contour exige une nouvelle preuve et un nouveau budget de toutes les erreurs. Les producteurs certifiés et leur allocation effective de rayons restent **OPEN**.

## Charges conservées et conditions d'exécution

Dans H0/C0, la pleine référenceΛ inclut les puissances premières propresQ. Le tableau des charges garde les produitsprime·prime,Q·prime,prime·Q,Q·Q, lespaires orientées et leurs intersections une fois par expansion exacte ; aucune erreur de troncature n'absorbe ces termes. Un compteur de représentations non pondéré ne découle pas gratuitement du coefficient pondéré. RaccordG_N→D_N et ledgerphysique/modèle **OPEN**.

Avant toute invocation : gel sources/contrat, lectureFULLroot, conservation des3089archives, gate nouveau daté, capturesPREEXEC, commande exacte, log/exit et reçu. Un échec réel doit conserver sa source et ses données avant correction. Aucun vieuxPASS rejoué ; aucun FAIL inventé à partir d'une critique papier. Juge indépendant pour Lean. Les invariants sourceu≥10^24, Q,k=1,unités,wholeU_a,fronts etPP restent fixés. RH/Hilbert–Pólya, positivité/cancel libre outrace définie pour recopier la réponse sont exclus.
