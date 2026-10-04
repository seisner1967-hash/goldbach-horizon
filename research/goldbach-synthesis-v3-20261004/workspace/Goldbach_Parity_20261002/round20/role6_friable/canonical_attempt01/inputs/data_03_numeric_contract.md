# Contrat numérique20 ROLE2 — neuf, avant sélection et exécution

Ce fichier est un contrat d'idéation, pas un script exécuté ni un résultat. Exécution uniquement par ROLE6 après nouvelle sélection et gate root. N=100000000. Fenêtre fermée **tous les1001 q** de1800100 à1801100 ; aucune sélection préalable de q premiers. Paramètres entiers exacts alpha100, Q999999, a3163, M1000000, Z100, p0=3, D10000. Le seuilsource Y=floor(exp(u/(128logu))) vaut1 ici ; le certifier avec intervalles rationnels de log/exp. Stocker u>=10^24=false, ell>=6=false, logY>=4=false et sigma_source undefined. **Ytest=4096 est distinct**, ne pas l'insérer dans F4source.

## Fenêtre complète et supports

Pour chaque q, factoriser exactement N-q et N-p0q avec multiplicité ; conserver la liste triée complète, Omega, terminalPrime, cofactor, SF, mu, tau, primalité, unités à N et au point complémentaire. Ces identités utilisent les entiers effectivement calculés. Les nonpremiers q et axes hors H ne sont pas retirés du tableau.

Pour chaque q, énumérer tous les e de1 àfloor((N-Q-1)/q) avec valeurs SF/unité, n_e=N-eq, cap, e>p0 et toutes les composantes de StructuralSupport19. **Le filtre n_e premier ou properpower ne participe pas au support structurel.** Stocker d'abord tous les labels entiers, puis H déclaré, F1/F0/F0-inter-F1/F0-minus-F1 et complément. e1 et ep0, e nonSF/mu0, n_e composites, axes theta0/raw0, incidences vides conservent leurs labels et raison d'exclusion. Utiliser le véritable SS=minFac<=Z ET quotientPrime, composite ResourceCell, pas un rang substitué.

Les trois strates de19 sont évaluées sur chaque cellule H et reconstruites à partir des constantes originales ; union disjointe exhaustive, sans coût long effacé. Les canaux D/P et terminal/cofactor peuvent être stockés par calcul neuf ; aucune banque19 n'est exécutée ou reparsée pour recalculer ses valeurs. Aucun rang, p² ou gcd cofactor/terminal n'est supposé favorable.

## Préfixes et classes

Pour chacune des deux ressources de tous les1001 q, si n>=D et P+(n)<=Ytest, multiplier sa vraie liste avec répétitions jusqu'au premier préfixe d>=D. Certifier avec entiers : produit de liste=n, d|n, D<=d<D*Ytest, tous les facteurs<=Ytest ; précédent<D. La garde de taille est stockée séparément et dérivée par le cap seulement sur H. Si n<D, conserver le cas hors certificat ; si nonfriable, ne produire aucun faux préfixe.

Former l'ensemble fini des **d observés**, dédupliquer uniquement pour des annexes AP ; ce n'est pas B_D complet. Pour chaque e et d observé, compter exactement dans la fenêtre intersectée avec J_e les deux congruences q≡N mod d et p0q≡N mod d. Stocker L/cardinal et endpoints ; vérifier cardinal<=(L-1)/d+1 si nonvide, ainsi que <=N/(e*d)+1. Pour classe0, gcd(p0,d)|N est la solvabilité exacte ; p0|d impose0. Dans la sous-famille q unitaire, gcd(d,N)>1 impose0. Inclure les d nonunitaires observés même s'ils proviennent d'un q nonunitaire hors H.

Afin que l'annexe ne dépende pas de la chance d'observer un d nonunitaire, ajouter explicitement d de{2,3,4,5,6,8,9,10,12,15,25,30,10000}, avec mêmes comptages exacts. Ils sont des tests de classes, **pas des témoins du préfixe ni des éléments prétendus de B_D**. Les intervalles vides de e>cap sont testés avec e=cap+1 et comptage0. Comparer l'union exacte des q satisfaisant un témoin à la somme des cardinalités réelles et de leurs deux masses sum1/d et card ; chaque +1 reste literal, sans gain implicite au principal.

## Vrais kernels nouveaux et ressources uniques

Construire à neuf les fonctions source : D physique sur les vrais diviseurs avec Q/a*k<m et gcd(k,n*N)=1 ; W sur **tous les1..Q** avec les mêmes strictfront/unités, mu/log(k/m)/phi(k), wholeQ et k1 présents. Optimiser uniquement par des préfixes arithmétiques exactement équivalents : le test de référence doit démontrer la conservation de chaque coefficient, pas utiliser Wmodel/S(bN) à la place du vrai W. Préserver log(k/m) avec son signe.

Pour tous les vertices actifs de H filtré F0 ou F1 sous Ytest, évaluer les coefficients logarithmiques exacts de C, thetaBracket et rawBracket ; les axes theta0 et raw0 sont nuls par leur **vraie définition**, sans évaluer inutilement un kernel ensuite multiplié par0. Lorsque raw est nonnul et theta nul, garder le properpower et son logp réel ; jamais mu(n)^2 au premier axe. Vérifier la nouvelle identité cofacteur lorsque e<=a<q et e<=Q, et les majorations génériques fondées sur TK (pas les exposants de F4source, faux à N fini).

Former Q_F1 par image des labels, puis les m1=N-q **une fois**. Évaluer le sourceBracket réel q,m1 avec ses diviseurs et W ; mu(m1)=0 donne le zéro réel mais ne supprime pas son entrée/poids tau de la table. Conserver les m1 SF composés et leur signe effectivement certifié. m0=N-p0q doit avoir theta/raw premier axe0 par produit de deux premiers distincts sur H. Les m1 attachés à F0-minus-F1 sont **stockés comme non payés**, même s'ils peuvent être évalués pour contrôle ; ne pas les joindre à U_F1. L'union physique de demandes/réciproques garde les intersections et consomme chaque vertex une fois.

Les logs sont d'abord réduits à une combinaison exacte sum c_p log p sur des premiers effectivement factorisés, c_p Fractions. Zéros identiques prouvés par tous les coefficients0. Pour les autres signes/bornes, intervalles rationnels avec réduction d'argument et série atan h : logx=2sum t^(2j+1)/(2j+1), reste positif borné explicitement, aucun math.log/float/approximation non certifiée. Raffiner tout intervalle ambigu jusqu'à séparation ; un intervalle contenant0 sans preuve algébrique n'accorde aucun PASS.

## Annexe Euler et Rankin finie exhaustive

Annexe indépendante, explicitement **Y_E=7, D_E=16, U_E=64, K_E=6, sigma_E=1/4**, aucun changement du banc principal. P_E={2,3,5,7}. Énumérer toutes les7^4=2401 tuples d'exposants de0 à6. Chaque tuple définit m=product p^k et tau(m)=product(k+1). Vérifier unicité des m, factorisations avec répétitions, y compris puissances et1. Construire symboliquement l'identité exacte de polynômes multivariés

    sum_tuples product t_p^k = product_p sum_(k=0..6)t_p^k,
    sum_tuples tau(m)*product t_p^k
       =product_p sum_(k=0..6)(k+1)t_p^k.

Le contrôle combinatoire par dictionnaire des exposants est exact, pas un test d'égalité de nombres arrondis. Puis prendre t_p=p^(-3/4). Enclore chaque quatrième-racine de p^3 par rationnels via entiers : pour échelle2^b, trouver z tel que z^4<=p^3*2^(4b)<(z+1)^4 ; réciproques donnent t_p. Pour les produits et sommes, opérations d'intervalles rationnels dirigées, b adaptatif. Certifier les deux sommes tronquées <=product(1-t_p)^-1 et <=product(1-t_p)^-2 par les queues géométriques positives, jamais égalité au produit infini tronqué.

Énumérer **tous les entiers1..64** et former B_E={m :16<=m<=64,P+(m)<=7}. Les exposants y sont<=6, donc tous les m de B_E figurent dans l'annexe exhaustive. Vérifier

    sum_(m in B_E)1/m <=D_E^(-sigma_E)*Eplus_E,
    card B_E<=U_E*sum_(m in B_E)1/m,
    sum_(16<=m<=64,smooth)tau(m)
      <=64*16^(-sigma_E)*Eplus_E^2.

Ici B_E est un ensemble fini **tronqué à64**, pas le B_D de source à D*Y=112. Ne pas nommer son cardinal cardB_Dsource. Ajouter la version complète B'_E={m :16<=m<=112,smooth<=7}, via l'énumération entière1..112 ; certains exposants<=6 encore, puisque2^7=128>112. Vérifier son tail et card<=112*S. Les deux annexes distinguent leur borne supérieure. Aucune constante asymptotique27/37/33/39 n'est validée par ce banc.

## Annexe totient finie et rapports obligatoires

Sur tous les n=1..4096, vérifier exactement n/phi(n)=sum_(d|n,SF)1/phi(d), échange des sommes phi/harmonic et majorant SF Euler positif. Le télescopage sum_(j=2..X)1/(j(j-1))=1-1/X est Fractions exact. La borne3(1+logX) utilise logX rationnel certifié. Cette annexe teste le raccord TK ; elle ne démontre pas TK uniforme en X à la place de Lean.

Conserver source/config/commande/log réel/exit/certificats avant/après exécution, comptes complets par masks/F/strates/rangs, éventuelles familles vides et m1 non payés, intervalles stricts et champs0float/0unresolved. Toute identité fausse arrête la gate avant Lean et garde le contre-exemple exact. Le rapport distingue **NoCounterexampleInWindow** et garde-source-false, sans Win. Aucune condition de signe ou cardinal nonnul n'est prescrite avant le test.
