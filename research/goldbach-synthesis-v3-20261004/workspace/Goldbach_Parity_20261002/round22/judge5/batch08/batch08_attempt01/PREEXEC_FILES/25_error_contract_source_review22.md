# Revue indépendante des enveloppes — PAPER / SOURCE uniquement

ROLE5, 2026-10-03. Aucune exécution Python, import, banque numérique, invocation
Lean, nouvelle preuve ou préparation de manifeste. Sources des autres rôles
inchangées. Le bilan officiel reste 66 modules / 1109 auxiliaires ; aucun WIN.

Base exacte : `B=D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002`.
Lectures intégrales non tronquées, sans audit complet de leurs dépendances :

| Fichier sous B/round22 | SHA256 | FULL |
|---|---|---|
| role1_bridge/contour_formula22.md | 42faea33cdcd56c08f6fb593dbd42c5c293b8e72beb9c823db68e9576ac1edb7 | 10a697 |
| role1_bridge/numeric_precontract22.md | 02cba2d0b3478b5fe3bddb46c1df0862a7c6287452f19892b7cec8ba100db05b | 96e2d9 |
| role4/h1_global_numeric/source_contract22.md | cea359055df1966ece11887305856bed46c24bb6de62f1a052d2e54c0e7d6cec | 6f9aa1 |
| role4/h1_global_numeric/envelopes_source22.py | f988d3edbcd28ce40698515f2e608d67a2615ab6bf777e4daf42f0820e8d5e67 | cf6f1e |

SHA et tailles contrôlés par metadata715e48. Le module Python a été lu comme
texte uniquement : même ses fonctions rationnelles n'ont pas été appelées.
Les autres modules producteur/checker/catalogues relèvent de la revue ROLE3 ;
leurs propriétés annoncées dans ce contrat ne sont pas ici certifiées.

## Résultat et domaine

Aux paramètres fixés Y=10000, T=100, X=Q=R=1000000, les cinq enveloppes
de queue et les deux formules de quadrature sont cohérentes sur papier.
Je n'identifie pas de constante insuffisante à cette spécialisation. La lacune
importante est le domaine : continuité et validité d'un majorant ne sont pas
la même assertion. Les champs « Y>0,T>=0,X,Q,R>1 » décrivent la continuité,
pas un domaine uniforme déjà démontré pour toutes les estimations.

- **C6 Evert :** la preuve sur les deux droites exactes utilise les facteurs
  Y^(3/2) et Y^(-1/2) sans comparaison d'exposants. Son enveloppe peut donc
  être valable pour Y>0, T>=0 si cette preuve est acquittée séparément.
- **W vertical et C8 Ehoriz :** les comparaisons Y^σ<=Y² sur les disques de
  droite, Y^σ<=1 à gauche et Y^σ<=Y^(3/2) sur le rectangle exigent Y>=1.
  Les réutiliser pour tout Y>0 serait incorrect. Pour Y<1, le facteur gauche
  Y^(-1/2) devient notamment non borné lorsque Y tend vers zéro ; W n'en
  tient pas compte. Un changement de domaine ou de majorant serait requis.
- **Eprim :** pour la preuve par comparaison d'une somme à l'intégrale,
  une garde suffisante est X entier>=2 et X/Y>=1+1/logX. Elle rend
  x log(x)exp(-x/Y) décroissante sur [X,infty). Le X fixé satisfait largement
  cette garde ; X>1 seul ne justifie pas cette étape.
- **Edual :** Q entier>=2 assure la décroissance de log(x)/x².
- **Earch :** R>=2 justifie x-x^(-1)>=(3/4)x ; R>1 seul ne suffit pas à
  utiliser le facteur constant4/3 par cette preuve.
- **Quadrature Arch spécialisée :** R=10^6 et logR<16 sont utilisés.
  Pour une formule générale avec128 cellules, il faut conserver logR et
  vérifier logR/256<=1/16 pour les rapports affichés. T et les nombres de
  cellules verticaux sont également fixés ici, pas variables silencieux.
- **C7/C8 :** le rectangle non dégénéré demande T>0. La borne |A'|<2^27
  est proposée pour les disques autour des horizontales à T=100 ; sa
  continuité comme paramètre ne la démontre pas pour tout T>0.

## Contrôle des queues et de la normalisation

Evert provient des bornes source
|Gamma(5/2+it)|<=2(t+2)exp(-at), |Gamma(1/2+it)|<=4exp(-at),
|F(c+it)|<16 et |F(d+it)|<=2(t+8), a=pi/4.
Les deux demi-queues et 1/(2pi) donnent exactement le facteur1/pi de C6.
L'intégrale de (t+b)exp(-at) donne
exp(-aT)[(T+b)/a+1/a²]. Les coefficients32 et8 sont donc cohérents.
Sur la droite gauche |cot(pi*s/2)|=1 et la série Psi utilisée a Re>=1 ;
la preuve de ces bornes reste à formaliser, pas à remplacer par un max mesuré.

Pour Eprim, l'intégrale majorante est
exp(-X/Y)[(X+Y)logX+Y]+Y*int_X^infty exp(-x/Y)/x dx.
Le dernier terme est <=Y²exp(-X/Y)/X ; le coefficient2 du précontrat est
conservateur. Edual domine exp(-1/(Yn)) par1 et utilise
int_Q^infty log(x)/x² dx=(logQ+1)/Q. Pour Earch, la majoration absolue des
trois termes donne respectivement exp(-R/Y), 1/(2YR²) et2/(YR), puis4/3.
Les sommes doivent garder tous les entiers et les puissances propres ;
aucune borne ne paie une omission de catalogue.

La paramétrisation verticale ds=i dt paie le passage de 1/(2pi*i) à1/(2pi).
La droite gauche a le signe moins. Le contour positivement orienté de C7
conserve les deux horizontales avec leur contribution signée. Avec la vraie
non-annulation du bord et les résidus, Z_T=J_T+H_horiz ; H_horiz ne vaut pas0.
C8 exige une séparation effective delta et une preuve de |A'|, puis la
longueur totale4/(2pi)<1. Le pôle1 doit être réellement supprimé dans A.

Le volet horizontal512 cellules, largeur1/256, couvre exactement le segment
de longueur2. Chaque boîte doit certifier A sur toute la cellule, pas sur
son milieu. Le bord inférieur nécessite la vraie conjugaison ou une évaluation
distincte. Aucune liste partielle, RH ou simplicité ne remplace le certificat.
Le nouveau paquet déclare ce volet UNIMPLEMENTED : il ne peut donc recevoir
ni CONTOUR_BOUNDARY_CERTIFIED ni FINITE_ZERO_TRACE_CERTIFIED.

## Deux quadratures : disques, alias et catalogues

Les disques verticaux R0=3/8 centrés à c=3/2 et d=-1/2 restent respectivement
dans Re(s)>1 et -1<Re(s)<0. Leur distance réelle au bord est au moins1/8 ;
Gamma(s+1) est aussi sans pôle. La non-annulation de zeta et A doit venir des
vraies identités Euler/réflexion. Une boîte numérique de diviseur contenant0
doit malgré cela être rejetée ; un point analytiquement non nul ne fournit
pas automatiquement une division d'intervalles sûre.

Les majorants4 et16 pour Gamma peuvent se déduire de son intégrale sur ces
bandes. Pour la série Lambda sur Re>=9/8, la comparaison avec
int_1^infty(logx+log2)x^(-9/8)dx donne une borne<72 ; la contribution du
pôle est<=8 à droite. Les constantes256 et2T+160 sont donc plausibles et
conservatrices sur les disques fixés. Il faut encore payer exactement les
bornes de cotangente/Psi à gauche. W=1024Y²+32T+2560 suit sous Y>=1.

Avec r=1/8, Rc=3/16, R0=3/8, le reste Taylor de degré64 est
W(r/R0)^65/(1-r/R0). Les alias DFT de128 nœuds sont bornés par
W(Rc/R0)^128/[(1-(Rc/R0)^128)(1-r/R0)]. L'erreur effective d'un nœud
est amplifiée d'au plus1/(1-r/Rc)=3. Le facteur total4T/(2pi) est correct.
Les positions, racines, poids et erreurs complexes doivent être enclos avec
une norme compatible. Les polynômes verticaux incluent i^k.

Le catalogue annoncé 1600*128=204800 conserve chaque cercle des deux
segments [-100,100]. Les centres -799/8+k/4 sont cohérents avec les cellules.
Une vérification de clés ne prouve cependant pas les valeurs Gamma/zeta des
nœuds ; EM, Stirling, branche holomorphe de logGamma, récurrences et chaque
rayon propagé restent des obligations. Les restes analytiques sont distincts
des erreurs de primitives/sommation et doivent tous deux être additionnés.

Pour Arch, B(u) reçoit en0 la valeur amovible f(1)/2, à dériver, et ses
disques R0=1/4 évitent les autres zéros de sinh. Les bornes affichées de
numérateur/dérivée et |2sinh u|>=|u| peuvent soutenir Warch ; elles ne sont
pas ici compilées. Rc=1/8, degré32,96 nœuds donnent les restes de degré33
et d'alias96. Avec L=logR<16, r=L/256<1/16, donc r/R0<1/4 et r/Rc<1/2.
Le facteur16 dans `arch_quad=16*W_ARCH*(...)` majore la **longueur totale L**,
après sommation des128 cellules ; il est correct et conservateur. Il ne
remplace ni L/128 dans les poids ni les vrais centres.

L'incertitude de logR doit payer centres et largeur. Le contrat source
annonce ces deux charges séparées. Sa garde |dw_j/dL|<=1/(96m), m=96,
est cohérente avec (1/(128m))*sum_(k even)(r/Rc)^k<=1/(96m).
Les facteurs de position8W et16Warch nécessitent en outre que les rayons
construits restent à l'intérieur des grands disques. Les12288 nœuds Arch
doivent être parcourus ; au total les deux catalogues ont217088 nœuds.
La garde de rayon ne prouve pas cette complétude sans outputs effectifs.

## Budgets effectifs et niveau de preuve

Les quatre budgets de E_total, **E_quad, E_quad_arch, E_arithmetic_round et
E_constants_round**, doivent combiner les restes analytiques justifiés avec
les rayons réellement produits. Ils ne peuvent être simplement remplis avec
les plafonds2^-44,2^-37 ou2^-50. L'erreur par nœud<=2^-80, les largeurs
des deux sommes, gamma_E, log(4pi), f(1) et les produits correspondants
doivent aussi provenir d'enclosures construites.

Dans chaque quadrature, les quatre postes annoncés E_function, E_position,
E_weights et E_accumulation doivent être redérivés à partir des boîtes de
valeurs, catalogues, logR et erreurs dyadiques effectives. Les gardes rf/rp,
e0/eq et largeur sont des critères d'acceptation après cette construction,
jamais des preuves du rayon. La spécialisation rationnelle des queues de
`envelopes_source22.py` est indépendante du résidu, mais n'acquitte pas ces
postes. Un structural_checker_PASS seul ne certifie pas les primitives ni
les enclosures analytiques ; le contrat le reconnaît explicitement.

La dérivation C3–C5 est une preuve proposée sur papier, avec inversion Mellin,
Fubini, Arch et constantes encore à formaliser. Les restes EM/Stirling et
les majorants de quadrature sont aussi des dettes analytiques. P1 et les
auxiliaires Gamma déjà jugés ne certifient pas ce contrat global. La revue
C5 indépendante antérieure relève ΓContour244f20 réellement FAIL, pas une
dépendance acquise. Aucun des fichiers lus ici n'est une preuve Lean compilée.

Les mutations omissionY/omission1/primal4 sont discriminantes sur papier
aux paramètres fixés : pour primal4 la minoration utilise Y>8, satisfaite
ici. Leur disjonction doit toutefois être redécidée sur les outputs réels.
L'affirmation papier E_total<10^-8<tau ne vaut ni mesure ni PASS numérique.
C9 ajouterait Ehoriz après son certificat effectif ; aucune trace de zéros,
coefficient N, borne D_N ou victoire n'est promue. La revue est close.
