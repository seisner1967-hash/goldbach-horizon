# Contrat global thermique neuf — SOURCE REVIEW READY, aucun run

Les cinq modules ROLE4 forment un producteur concret et un vérificateur structurel à relire. Aucun import, compilation Python, appel Lean, calcul ou reprise d'ancien banc n'a été effectué. Aucun launcher/gate n'est fourni par ce paquet. Il ne reçoit pas H1 comme prémisse et ne construit pas sa référence depuis le résidu observé.

Paramètres conservés : N=100000000, Y=10000, T=100, X=Q=R=1000000, tau=10^-6. Les deux droites sont c=3/2 et d=-1/2. La comparaison proposée est exactement

    sum_(n>=2) Lambda(n)[(n/Y)exp(-n/Y)+exp(-1/(Yn))/(Yn²)]
       = 1+Y-J_infty-(log(4pi)+gamma_E)exp(-1/Y)/Y-Arch.
    J_infty=(1/(2pi))*int_R [Y^(c+it)Gamma(c+1+it)F(c+it)
                            -Y^(d+it)Gamma(d+1+it)F(d+it)]dt,
    F=A'/A=1/(s-1)+zeta'/zeta, A=(s-1)zeta(s) prolongé en1.

La vraie identité C3 doit encore être prouvée sous Lean. Le test calcule le mode thermique à Y=sqrtN ; il ne calcule pas le coefficient additif N et ne paie pas D_N.

## Sources et corrections strictes

`transport_catalogue_source22.py` construit les points a+(3/16)omega_j+i(-799/8+k/4), deux côtés, j=0..127, k=0..799. Il remplace la phase non raccordée +(1/16+j/8) de l'ancien constructeur EM, qui reste intact et n'est jamais appelé. Graines nouvelles par(a,j,n), pas exp(-i log(n)/4), majorant vrai U=128 pour n^-s et U=Y² pour Y^s. Les127 étapes EM et l'étape Y sont évaluées nouvellement puis partagées dans la même invocation. La récurrence construite paie produit et arrondi du rayon ; sa borne est 2e0+1600(Ueq+3EPS), EPS=2^-512. Les gardes e0,eq<=2^-200 sont vérifiées sur les enclosures produites.

`arithmetic_catalogue_source22.py` est une copie distincte de l'ancien source arithmétique, avec dual Taylor16, reste suivant a^17/17!, et champs primal4/dual4 séparés. Le module readonly `unit_transport_source22` n'est utilisé que pour exp(-n/Y), n=2..1000000. Chaque entier possède un certificat neuf n=p^e*r, p premier, p ne divise pas r ; aucun crible, inversion de Möbius ou tableau précédent. Toutes les puissances propres restent dans le total. Le flux complet est contrôlé après sa création, puis par le checker indépendant. Mutant fixé : **PRIMAL_N4_ONLY**.

`producer_source22.py` utilise les sources readonly dyadic_r01, analytic_r01 et kernel_r01, sans leur producteur, checker ou résultat fermé. Route gauche fixée : EM direct de la vraie zeta et de sa dérivée, avec séparation effective du diviseur ; une enclosure contenant0 déclenche une erreur d'évaluateur. Le reste EM et le reste Cauchy dérivé sont inclus dans les valeurs. Gamma emploie Stirling32/shift64, exp réduit par klog2 et ses64 facteurs, avec le reste logGamma conservé. gamma_E=-psi(1) est nouvellement évalué. Les identités EM/Stirling/branches restent des obligations analytiques à certifier ; elles ne sont pas des champs de tolérance libres.

## Quadratures et quatre budgets construits

Vertical : 1600 cellules de largeur1/4,128 nœuds/cercle Rc=3/16, degré64 et grand disque R0=3/8. Tous les204800 nœuds sont réellement parcourus par la future source. Les poids incluent i^k et la normalisation1/(2pi), avec signe droite moins gauche. Le rayon de position est ceil_grid(8W*rho_cercle), W=1024Y²+32T+2560.

Arch :128 cellules,96 nœuds/cercle Rc=1/8, degré32 et grand disque1/4. Les12288 nœuds sont tous parcourus. Les points sont évalués au milieu rationnel de l'enclosure du vrai logR ; l'incertitude des centres est payée par ceil_grid(16Warch[rho_cercle+(2k+1)rho_logR/256]). L'incertitude de la **vraie largeur** est payée dans chaque poids par ceil_grid(r_weight+rho_logR/(96*96)), car |dw_j/dlogR|<=1/(96m), m=96. L'endpoint n'est pas déplacé : ces poids et positions encadrent la quadrature à logR exact. Warch=128Y+32/Y+32. L'extension holomorphe amovible de B en0 et ses majorants restent à prouver.

Pour un point p, un poids w et leurs rayons construits rf,rp,rw, le fold paie séparément

    E_function+=(|w|_1+rw)rf,
    E_position+=(|w|_1+rw)rp,
    E_weights+=|p|_1*rw,
    E_accumulation+=erreur exacte du produit dyadique arrondi.

Les gardes rf,rp<=2^-81, E_weights,E_accumulation<=2^-72, largeur des sommes et constantes<=2^-50 sont contrôlées **après construction**. Un échec lève une erreur, sans changer de précision, T ou catalogue. Le flux des nœuds conserve les boîtes d'évaluation ; les catalogues conservent les boîtes des racines et des poids. Le checker redérive rf depuis la boîte d'évaluation, rp/rw depuis ces catalogues et logR, puis chaque produit/arrondi et les quatre sommes : aucune garde ne remplace un rayon effectif.

## Enveloppe fermée continue et spécialisation rationnelle

Les fonctions continues proposées restent celles du précontrat ROLE1, pour Y>0,T>=0,X,Q,R>1 :

    Evert=e^(-pi*T/4)/pi *
      [32Y^(3/2)((T+2)*4/pi+16/pi²)
        +8Y^(-1/2)((T+8)*4/pi+16/pi²)],
    Eprim=e^(-X/Y)[(X+Y)logX+Y+2Y²/X],
    Edual=(logQ+1)/(YQ),
    Earch=(4/3)[e^(-R/Y)+1/(2YR²)+2/(YR)].

Les restes de quadrature sont le degré65/alias128 vertical et le degré33/alias96 Arch du même précontrat. `envelopes_source22.py` les spécialise par pi>3, log(10^6)<16 et exp(-1)<3/8 ; il ne dépend d'aucune sortie observée. Les erreurs effectives des quatre folds, des sommes, des constantes et un supplément8EPS de finalisation sont additionnés. La garde finale E_total<10^-8 doit être effectivement vérifiée ; aucune valeur de E_total n'est annoncée ici comme mesurée. Les queues primale/duale sont unilatérales positives ; les queues verticale/Arch sont signées.

La continuité des fonctions originales et la justification de ces majorants doivent encore être formalisées. Les lemmas Gamma auxiliaires jugés ne prouvent ni ce domaine entier, ni C3/C5/C6.

## Vérification et décisions falsifiables

`structural_checker_source22.py` importe seulement la bibliothèque standard. Il vérifie les217088 clés ordonnées, le fold exact de chaque nœud, les999999 certificats arithmétiques, les formules fermées et leurs gardes, les signes/modes de la comparaison, et les trois mutants (omissionY, omission1, retrait primal4). Il recalcule toutes les décisions d'intersection et de disjonction depuis les intervalles. Il ne réévalue pas les primitives transcendantes ni les valeurs ζ/Γ à partir de leur source : **un structural_checker_PASS seul ne certifie pas leurs enclosures**. Une revue indépendante concrète des sources et des restes est nécessaire avant préparation d'un banc ; Lean garde sa gate séparée.

Si les enclosures construites se chevauchent, le résidu est de norme<=tau et les trois mutants sont disjoints, la future décision est THERMAL_TRACE_NUMERIC_AGREEMENT. Si les enclosures sont disjointes ou la partie imaginaire exclut0, ENCLOSURE_CONFLICT signifie une erreur possible d'identité, de preuve ou d'évaluateur ; ce n'est pas une réfutation automatique de Goldbach. NON_DISCRIMINATING conserve les autres cas. Aucun statut fictif PASS n'est produit pendant cette préparation.

## Complétude et coût non mesuré

La boucle thermique est concrète :32512 graines EM,256 graines Y,128 étapes transcendantes partagées ;32768 tracks de800 valeurs ;26181632 avances ;204800 évaluations EM/Γ ;12288 évaluations Arch ;deux sommes sur999999 entiers. Les tests par division directe et les contrôles indépendants visitent les domaines complets. Aucun temps, consommation mémoire ou volume réel de sorties n'a été mesuré. Les flux de nœuds/certificats peuvent être volumineux ; ils sont lus en streaming, sans promesse d'efficience pratique.

Travail restant avant exécution : revue indépendante FULL de ces sources et des dépendances ; traitement de tout défaut ; résolution exacte des noms/imports et byte-binding dans un nouveau launcher ; manifeste PREEXEC/START/POST/reçus et gate ROOT propres ; choix explicite du niveau de certification numérique après revue analytique. Aucun launcher n'existe dans ce paquet. Aucun script n'a été parsé ou importé par Python ; l'élaboration/syntaxe reste à contrôler selon la future gate.

Le volet horizontal512 cellules n'est pas implémenté ici et reçoit UNIMPLEMENTED. C7/C9/résidus et la vraie trace de zéros sont OPEN. H1_FORMAL, COEFFICIENT_N, D_N et WIN restent ouverts. Les sources sont stabilisées pour revue ; le paquet est SOURCE_REVIEW_READY_THERMAL_C3_ONLY, jamais NUMERIC_PREPARED/PASS.
