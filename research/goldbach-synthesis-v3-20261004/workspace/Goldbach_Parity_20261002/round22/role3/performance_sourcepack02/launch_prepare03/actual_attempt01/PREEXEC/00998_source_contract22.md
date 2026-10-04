# SOURCEPACK02 — candidat distinct, sans exécution

Ce paquet conserve le contrat thermique global de `source_manifest22.json` ROLE4 (SHA e1caa3d115dd492cfa6d91478240b0e8418614b6faf8798f48e15312dfe11a51). Il contient neuf copies locales de sources Python : cinq sont modifiées pour réduire le travail de représentation, quatre sont identiques octet par octet. Les neuf alias restent distincts et un futur chargeur devra les résoudre exclusivement vers les neuf fichiers de ce dossier. Aucun fichier du banc actuel, de ses captures ou des anciens lots n'est modifié.

Statut : SOURCE_REVIEW_READY, revue indépendante nouvelle requise. Zéro import, parseur Python, calcul, compilation, test de performance ou nouveau lancement. Il n'existe ici ni launcher, ni préparation exécutable, ni autorisation ROOT. Le banc actuellement autorisé continue sous ses propres sources immuables. Sa clôture et une nouvelle gate ROOT sont requises avant toute invocation future de ce candidat.

## Contrat mathématique inchangé

Paramètres fixes : N=100000000, Y=10000, T=100, X=Q=R=1000000, tau=1/1000000. Y²=N est désormais aussi une garde effective du producteur. On compare les sommes thermiques primal et dual avec l'identité H1 existante :

Σ Λ(n)[(n/Y)exp(-n/Y)+exp(-1/(Yn))/(Yn²)]
=1+Y−J∞−(log(4π)+γ_E)exp(-1/Y)/Y−Arch.

Les sommes numériques s'arrêtent à X et Q, et les queues explicites restent ajoutées séparément. G(s)=Y^s Γ(s+1) et F(s)=1/(s−1)+ζ′(s)/ζ(s) restent les véritables objets évalués. Les formules de primitive, Euler–Maclaurin M128/K64, Stirling avec décalage64/ordre32, leurs restes, la réduction d'exponentielle par k log2 et les domaines sont conservés. L'identité H1 globale n'est pas formalisée par ce paquet.

Catalogue vertical : a∈{3/2,−1/2}, j=0..127, k=0..799,
s=a+(3/16)ω_j+i(−799/8+k/4), soit204800 nœuds. Les32768 graines comprennent32512 graines EM et256 graines Y ; chacun des128 pas partagés est construit par de nouvelles primitives dans le futur interpréteur. Les26181632 transitions transportent les127 puissances n^−s et Y^s. Les graines restent issues de `new_power(n,s0)` et `exp_complex(s0*log10000)`, avec U=128 et U=100000000, et avec la garde effective rayon≤2^−200.

Catalogue Arch :128 cellules et96 racines par cellule, soit12288 nœuds. La largeur réelle logR/128, les positions calculées à partir du milieu de logR, leur incertitude et les poids restent payés. Le facteur16 du majorant de quadrature utilise logR<16 ; il ne remplace pas les largeurs des poids. Le catalogue arithmétique visite chaque n=2..1000000 avant le masque et écrit999999 certificats exacts. Primal, dual et toutes les puissances premières sont conservés. Le mutant primal4 soustrait seulement la contribution primale de n=4 ; la contribution duale reste inchangée.

Les quatre budgets fonction, position, poids et accumulation restent calculés depuis les enclosures et les produits réels. Les queues E_vert, E_quad, E_prim, E_dual, E_arch et E_quad_arch sont celles de `envelopes_source22.py`, copie inchangée. Les gardes de largeur et E_total<10^−8 restent identiques. Aucun reste n'est fixé à partir du résidu observé. Les domaines supplémentaires de la revue sont conservés : Y≥1 pour W et Cauchy8W ; X entier≥2 et X/Y≥1+1/logX pour la queue primale ; Q entier≥2 et R≥2. Les valeurs fixes satisfont ces gardes.

## Modifications concrètes

`dyadic_r01` remplace quatre opérations de conversion ou arrondi rationnel par leurs formules d'entiers exactes. Les intervalles résultants ont les mêmes extrémités. `analytic_r01` construit une seule fois, dans le nouvel interpréteur, les extrémités de log(2π)/2 et f(1)=exp(-1/Y)/Y ; chaque utilisation reçoit une nouvelle Box. Gamma calcule la première projection de la même formule de Stirling sans construire une dérivée inutilisée. La voie psi/γ_E conserve sa dérivée concrète.

`transport_catalogue_source22` représente le rayon sur la grille d'entiers S=2^512. La récurrence, l'arrondi dirigé, l'erreur du produit et l'enveloppe fermée sont algébriquement les mêmes. `advance()` retourne désormais None ; les seuls appelants du producteur ignorent sa valeur de retour puis appellent `box()` au nœud suivant. Les transitions de la séquence primale restent la copie originale `UnitBoundTransport`, à laquelle s'appliquent les primitives dyadiques équivalentes.

Le producteur ajoute trois compteurs effectifs : une construction de log(2π)/2, une construction de f(1),204800 évaluations Gamma par la projection valeur seule. Le checker exige ces compteurs et l'étiquette de transport. Son pliage rationnel, les certificats arithmétiques, les normalisations1/(2π),1/Y,1+Y, les gardes et les trois mutants restent identiques.

Les commentaires SHA de `unit_transport_source22.py` décrivent sa provenance historique. Le manifeste de ce candidat lie explicitement sa dépendance `dyadic_r01` à la nouvelle copie locale ; aucun ancien alias ou chemin historique n'est une entrée d'exécution. Son constructeur EM historique est inutilisé, seule `primal_heat_sequence()` est importée par la source arithmétique.

## Portée d'une future évaluation

Niveau proposé : PAPER_AUDITED_DIRECTED_INTERVAL_PRODUCER_WITH_INDEPENDENT_STRUCTURAL_CHECKER, sous réserve de la nouvelle revue des cinq modifications. Les anciennes revues sont de la provenance, sans autorisation héritée. Le checker structurel ne réévalue pas ζ, ζ′, Γ ni les primitives : `primitives_recomputed=false`, `analytic_remainders_formalized=false`, `structural_PASS_is_enclosure_PASS=false`. Une réussite structurelle seule ne constitue donc pas une nouvelle certification des primitives.

Le volet horizontal reste UNIMPLEMENTED. H1 formel, C5/Fubini global, coefficient additif N et borne D_N restent ouverts. Aucune victoire n'est revendiquée. Aucun calcul ancien, sortie partielle ou résultat R01 n'entre dans les nouvelles primitives ou les caches. Les caches proposés sont vides dans un nouvel interpréteur et reçoivent uniquement les primitives de cette invocation.

La limite proposée reste celle du banc actuel :3600s mur enfant et2147483648 octets d'artefacts. Aucun gain de temps mesuré, aucune garantie d'achèvement et aucun changement de ces limites ne sont acquis. Le rapport d'équivalence donne uniquement des comptes d'opérations retirées et les checkpoints réellement observés du banc actuel.
