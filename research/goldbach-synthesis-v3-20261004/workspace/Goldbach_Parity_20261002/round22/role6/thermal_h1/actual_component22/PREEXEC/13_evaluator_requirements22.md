# Plan retenu pour une production H1 neuve : DFT avec récurrences certifiées

SOURCE ONLY. Le plan conserve le catalogue ROLE1 : 1600cellules verticales,
128points par cercle,204800nœuds fonctionnels ;128cellules Arch,96points,
12288nœuds ;512cellules horizontales ; tous les entiers2..1000000 sur
les deux axes arithmétiques. Il n'emprunte aucun ancien résultat ou banc.
La préparation de source est autorisée ; l'exécution reste fermée avant
source gelée, revue FULL et gate distincte. Ce texte n'est pas un résultat
numérique ni un producteur PREPARED.

## Choix entre jets et DFT

Le choix initial est **DFT optimisée avec récurrences exactes le long des
centres verticaux**, et non un évaluateur élémentaire répété26009600fois.
Les jets holomorphes locaux restent une variante ultérieure distincte,
avec une nouvelle sélection, un nouveau contrat et une preuve des mêmes
restes Cauchy. Ils ne changent pas silencieusement la source ou le budget
d'une tentative gelée.

Pour un côté a dans{3/2,-1/2}, un index de cercle j et une base entière
n dans2..128, le point exact est

    s_(a,k,j)=a+Rc*omega_j+i(t0+k*h),
    Rc=3/16,h=1/4,t0=-799/8=-99.875,omega_j=exp(2pi i j/128).

La puissance vérifie exactement

    n^-s_(a,k+1,j)=n^-s_(a,k,j)*q_n,
    q_n=exp(-i*h*log n), |q_n|=1.

Les deux côtés emploient la même étape q_n. Chaque couple(a,j,n) possède
une graine neuve ; les800valeurs sont transportées par multiplication
certifiée. Cela réduit les appels transcendants pour ces puissances à
2*128*127graines et127étapes, tout en construisant effectivement chaque
nouveau nœud. Les puissances M^(1-s-2k) partagent M^-s avec les facteurs
réels exacts M^(1-2k). zeta' partage les mêmes puissances, multiplie par
-log n et dérive le vrai polynôme EM. Aucun terme de série n'est supprimé.

Le facteur Y^s suit de même q_Y=exp(i*h*logY). Son module vrai est
majoré par Y^2 ; les graines et étapes sont nouvelles. Gamma et psi
sont encore évaluées aux204800nœuds avec leur nouvelle source Stirling.
La distinction nœuds fonctionnels / graines transcendantes / opérations
de transport doit figurer dans le reçu final.

## Le transport n'est pas une rotation de rectangles naïve

Un rectangle propagé800fois peut croître par une norme de matrice >1,
même si la phase vraie a module1. Le producteur doit employer un centre
dyadique complexe p_k et un rayon rationnel euclidien majoré, ou une
preuve équivalente. Avec q_c approchant la vraie q, rayons e_q,e_k,
module vrai initial<=U et erreur d'arrondi complexe<=2*epsilon_grid,

    e_(k+1)<=(1+e_q)e_k+U*e_q+2*epsilon_grid.

Le rayon fermé est la somme géométrique FINIE de cette récurrence. Il
ne nécessite pas une division par e_q si e_q=0. Gardes fixées pour la
future source : e_0,e_q<=2^-200 ; epsilon_grid=2^-512 ; k<=799.
Comme (1+e_q)^800<=2, un majorant est

    e_k<=2e_0+1600(Ue_q+2epsilon_grid).

Pour les puissances2..128, U=128 suffit ; pour Y^s, U=Y^2=100000000
suffit. Les gardes portent sur les rayons CONSTRUITS des graines et
étapes ; elles ne sont pas des prémisses libres. Si elles échouent,
le statut est EVALUATOR_UNRESOLVED et aucune précision ne change sous
la gate consommée.

La source peut évaluer le centre rationnel m_(a,k,j) du rectangle du
point exact. Sa position réelle est ensuite transportée avec Cauchy :
rho_j est le rayon certifié de la racine de l'unité et de la construction
du point ; rho_j<=2^-200 est une garde fixée. Les points restent dans
le grand disque de rayonR0=3/8 ; |H'|<=8W convient pour cette petite
perturbation, car R0-Rc-rho_j>1/8. Le futur code n'utilise jamais H(m)
comme H(s_exact) sans le rayon8W*rho_j.

## Quatre budgets séparés, construits et contrôlés

Chaque valeur d'un nœud porte un centre dyadique p, r_function et
r_position. Son poids d'intégration porte un centre dyadique w et
r_weight. Le produit a les rayons suivants :

    E_function_product<=(|w|+r_weight)*r_function,
    E_position_product<=(|w|+r_weight)*r_position,
    E_weight_product<=|p|*r_weight,
    E_accumulation_product<=2*epsilon_grid.

Les produits croisés sont ainsi payés une fois dans les deux premières
classes. |p| et |w| ont des majorants rationnels dirigés, éventuellement
la norme L1 de leurs coordonnées ; aucune racine flottante n'est nécessaire.
L'addition de centres sur la même grille est exacte. Les autres arrondis
de multiplication/scaling et la finalisation des intervalles sont payés
explicitement dans la quatrième classe. Les rayons internes aux
évaluateurs sont dans la première ; ils ne disparaissent pas au passage
à un centre. Les positions restent dans la deuxième.

Gardes proposées avant gate : r_function<=2^-81 et r_position<=2^-81
par nœud, donc somme<=2^-80. Les rayons r_function comprennent EM et
sa dérivée, Stirling et sa dérivée, logs, exp, trig, quotients et tous
les arrondis internes. Pour chaque intégrale complète, E_weights et
E_accumulation doivent être construits puis <=2^-72. La contribution
des erreurs nodales est majorée par le noyau d'intégration, <3fois la
longueur totale normalisée. Ces deux petits budgets supplémentaires
ne compromettent pas l'enveloppe E_total<1e-8 ; leur ajout est enregistré
au lieu de leur attribuer une valeur libre dans epsilon_node.

Les poids verticaux peuvent être construits une seule fois, nouvellement,
car la largeur est commune :

    w_j=1/(2pi*128) *
          sum_(k even<=64) (-1)^(k/2)*2r^(k+1)/(k+1)*Rc^-k*omega_j^-k.

Les signes droite moins gauche restent à part. L'intégration directe
de sum_j w_j H(s_j) remplace le recalcul de65coefficients DFT par cellule
sans changer le polynôme mathématique. Le reste de degré64 et l'alias128
demeurent payés par la formule ROLE1. Les poids emploient les vraies
racines exactes via leurs enclosures ; leur erreur effective est conservée.

## Primitives propres et reconstruction Gamma

Profil proposé : centres entiers sur grille2^-512, rayons rationnels,
aucun float, aucune API Gamma/zeta, aucune importation d'ancien producteur.
La source de règles dyadiques historique pourra être citée en READONLY
avec son SHA et revue FULL ; les nouveaux modules adaptent les règles
et évaluent leurs propres données. Aucun ancien log/PASS/certificat n'est
une entrée du banc.

Un log réel positif peut réduire x=2^k*m avec m dans[1/2,2], puis utiliser
2atanh((m-1)/(m+1)) avec256termes et reste géométrique explicite,
|(m-1)/(m+1)|<=1/3. Tous les log(n),logY,logR,log2 etlog(2pi) sont calculés
à nouveau. La réduction d'une boîte doit garantir ses bornes, pas seulement
la réduction de son milieu.

Pour w=z+64 aux nœuds Gamma, Re(w)>64 et |Im(w)|<101, donc le Log
complexe est

    Log(w)=1/2*log((Re w)^2+(Im w)^2)+i*atan(Im(w)/Re(w)).

Il ne nécessite pas sqrt. Pour |r|<=1/2, la série atan a son reste
alterné explicite ; pour1/2<=r<=2, atan(r)=pi/4+atan((r-1)/(r+1)),
avec argument dans[-1/3,1/3], et le signe négatif se traite par imparité.
Des boîtes coupant un seuil doivent être couvertes par des domaines
élargis prouvés ou des sous-boîtes complètes, sans perte de portion.
Choix fixé : atan Taylor512, avec domaine direct |r|<=5/8 et son reste
2*(5/8)^1025/1025 ; sinon, branche signée r>=1/2 ou r<=-1/2 et transformation
vers[-1/3,1/3]. Un intervalle ne certifiant aucune de ces couvertures
retourne UNRESOLVED. Le log réel utilise256termes. Ce texte ne donne
pas déjà un crédit numérique aux primitives.

Gamma ne peut pas appeler inchangé un exp_box dont le domaine positif
s'arrête à16 sur logGamma(w), qui dépasse16. Deux routes admissibles :

1. exp(logGamma(z)) après L32(w)-sum_(j=0..63)Log(z+j), avec identité
   de branches démontrée sur Re(z)>0 ; cette route multiplie le coût des logs.
2. Route retenue en préparation : choisir un entier k de réduction et
   calculer exp(L32(w)-k*log2)*2^k/product_(j=0..63)(z+j).

Dans la deuxième, k est un choix de représentation, pas une modification
de la fonction. Le calcul inclut le reste logGamma avant exp. Exiger que
la partie réelle de l'argument réduit soit dans[-2,2], puis employer
les primitives à domaine borné. Les phases sont encadrées entièrement.
Le facteur2^k est exact. Chaque facteur du produit a Re>0 aux nœuds ;
une séparation de0 de son enclosure et de tout diviseur est vérifiée.
L'erreur logGamma passe via exp(R)-1, puis les divisions. La norme
gigantesque d'un intermédiaire n'est pas soumise à une ancienne garde
d'efficience absolue conçue pour exp<=exp16. Le rayon final de la vraie
Gamma doit satisfaire le budget nodal après toute reconstruction.

psi utilise la dérivée explicite de L32 et le reste Cauchy, puis la
récurrence64. F sur le côté gauche peut être évalué par l'équation
fonctionnelle avec zeta(1-s),cotangent etpsi(1-s), plutôt qu'une division
fragile par une approximation de zeta gauche. La route doit être fixée.
Elle emploie les mêmes vrais objets et paie tous les restes. Sur les
disques droits, le produit Euler fournit sans Möbius un minorant utile
|zeta(s)|>=1/9 ; le code contrôle en plus chaque diviseur effectivement.

Pour le cotangent complexe, la route fixée évite les hyperboliques à
exposant positif énorme. Si x=pi*Re(s)/2,y=pi*Im(s)/2,q=exp(-2|y|),
alors D=1+q^2-2q*cos(2x) et

    cot(x+i y)=2q*sin(2x)/D-i*sign(y)*(1-q^2)/D.

Le cas y=0 prend sign0=0. La formule est évaluée au centre rationnel
avec tous les intervalles de pi conservés et la séparation réelle de D
contrôlée ; sa valeur au point exact reçoit ensuite le transport Cauchy.
Le domaine de cette nouvelle exp est négatif, inclus dans[-1024,0].
Les sin/cos réels, les racines de l'unité et l'exponentielle réduite Gamma
peuvent conserver Taylor128 et Machin256 avec leurs restes explicites,
réécrits dans le nouveau profil512bits et relus avant gate.

## Arch et arithmétique : coût propre

Arch utilise128cerclesRc=1/8,96points, degré32 et intégration de poids
préconstruits avec la vraie largeur logR/128 et son enclosure. Les
positions, poids, limite supérieure et constantes sont propagés dans
leurs quatre classes. Au catalogue fixé, 12<logR<16 donne |u|>1/64
sur tous les points exacts des cercles : le premier centre est logR/256,
et les suivants sont au moins3logR/256. Les boîtes de position assez
fines conservent une marge1/128. Cela permet d'évaluer le quotient B aux
nœuds par une division contrôlée sans recevoir B(0) comme oracle.
L'extension amovible et son majorant restent nécessaires à la preuve
Cauchy sur les grands disques comprenant0.

Dans B, calculer exp(2u) comme exp(u)^2 ; ne pas appliquer un ancien
exp réel à2Re(u)>16 sans preuve de domaine. Les exponentielles emboîtées
conservent leur argument complexe, pas sa seule partie réelle. Tous les
dénominateurs sont contrôlés. La contribution R..infty reste E_arch.

Pour les999999entiers de chaque somme, les factorisations et primalités
proviennent d'une découverte neuve par divisions exactes/certificats,
sans crible de multiples. Chaque n a un certificat ; les facteurs premiers
peuvent partager un certificat neuf. Les zéros Lambda sont des valeurs
certifiées, pas un filtre omettant des entiers du domaine.

L'exponentielle primale utilise une graine neuve q=exp(-1/Y) et transport
q^n de module<=1. Le rayon global finitement construit ne doit pas croître
comme un rectangle naïf ; la même règle avec U=1 et n<=1000000 paie
chaque valeur. Un q avec rayon<=2^-200 et grille512bits laisse une marge
construite avant somme ; la garde réelle de somme<=2^-50 est vérifiée.
Le primal inclut le facteur exact n/Y. Pour la duale, seulement après le
certificat Lambda(n)=0 oulogp, une nouvelle Taylor de exp(-1/(Yn)) peut
employer son domaine minuscule et un reste fixé ; un objectif de degré16
avec reste2*(1/(2Y))^17/17! est constructible. Les coefficients logp,
1/(Yn^2) et tous les arrondis sont ajoutés. La somme contient bien tous
les n avant catégories et les queuesE_prim/E_dual sont toujours payées.

## Certificats horizontaux et contrôles négatifs

Les512cellules couvrent le segment complet, sans masque. La méthode
peut évaluer A au centre et transporter avec une borne locale d'A'
construite par EM sur toute la cellule ; le grossier2^27 n'est pas un
transport utile pour une cellule1/256 mais reste utilisable pour C8.
Un intervalle contenant0 retourne UNRESOLVED. Une autre grille, un autre
T ou une subdivision supplémentaire demande un nouveau contrat avant
exécution, jamais une reprise silencieuse de la tentative.

Contre-tests de source à préparer, avec référence indépendante :
- Quadrature de1 ; de(s-s0) ; de(s-s0)^2, dont la moyenne verticale est
  négative et détecte l'oubli de i^k ; monôme de degré128 pour l'alias DFT.
- EM aux valeurs zeta(0)=-1/2,zeta(-1)=-1/12,zeta(2)=pi^2/6 ; cas du
  pôle retiréA(1)=1 au moyen d'une véritable extension et non division0/0.
- Nouvelle route Stirling aux valeurs Gamma élémentaires et à des
  paramètres complexes nouveaux, par réflexion/récurrence ou une nouvelle
  quadrature indépendante ; aucun ancien résultat Gamma ne sert d'oracle.
- Mutants H1 obligatoires : omissionY, omission1, retrait de4 primal
  explicitement défini. Les autres changements de signe sont diagnostiques.

Ces contrôles ne sont pas exécutés ici. Le futur résultat garde les
statuts thermiques, boundary, résidus, H1formel,coefficientN,D_N etWIN
distincts. Si les quatre budgets sont construits mais trop larges,
NON_INFORMATIVE_BOUND est permis ; si la source échoue, SOURCE_ERROR ;
si le temps/coût empêche la production complète, COST_UNRESOLVED. Aucun
de ces statuts ne réfute une identité analytique par une intersection.

## Contrat d'exécution restant à construire

Avant toute invocation, figer nouveaux arithmetics, logs/EM/Stirling,
catalogue, kernels intégrés, arithmeticcertificates, producteur et
launcher ; lier runtime connu -B-Xutf8, sources/documentation/paramètres,
fourbudgets et formules de restes. PREEXEC précède START réel. Un seul
acteur, une seule tentative et un log de progression ; conserver sortie,
certificats, exit, receipt et POSTEXEC. La gate doit nommer ce nouveau
THERMAL_H1_NUMERIC volet et son SHA. Aucune gate G0/Gamma ne l'autorise.
Le Juge Lean possède une autre gate ; la vraie finale H1 doit dériver C3.
