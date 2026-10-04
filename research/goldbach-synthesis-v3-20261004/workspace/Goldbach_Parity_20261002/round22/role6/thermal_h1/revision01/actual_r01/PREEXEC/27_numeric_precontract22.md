# Précontrat neuf — trace globale thermique / contour, SOURCE ONLY

Ni producteur ni gate n'existent ici. Aucun calcul n'est autorisé par ce texte.
Il propose UNE expérience discriminante au ROLE6, après préparation, relecture,
gel et autorisation ROOT. Aucun ancien résultat G0/Gamma ne sert d'oracle.

## Paramètres avant observation

N=100000000 ; Y=sqrt(N)=10000 ; T=100 ; X=Q=R=1000000 ;
tau=1/1000000. Le test porte sur H_Y, somme sur TOUS les n>=2,
tronquée à X et Q avec queues construites. Il ne calcule pas le coefficient N.
delta_horizontal=2^-24. Évaluations complexes nouvelles avec intervalles
rationnels dirigés ; objectif d'erreur absolue par nœud 2^-80, à vérifier.
Le nombre de bits interne, par exemple768, ne constitue pas une preuve
d'enclosure ou d'efficience.

## ζ et sa dérivée, sans oracle de zéros

Pour M=128,K=64, l'Euler–Maclaurin paire emploie

    Z_MK(s)=sum_(n=1..M-1)n^-s+M^(1-s)/(s-1)+(1/2)M^-s
       +sum_(k=1..K) [B_(2k)/(2k)!](s)_(2k-1)M^(1-s-2k).
    zeta(s)-Z_MK(s)=-(s)_(2K)/(2K)! *
                        int_M^infty Btilde_(2K)(x)x^(-s-2K)dx.

Les coefficients B sont calculés exactement par leur récurrence rationnelle.
La Fourier des Bernoulli périodiques donne |Btilde_(2K)| <=
4(2K)!/6^(2K). Par conséquent, pour sigma+2K>1,

    E_zeta(s)=4|(s)_(2K)| /
           [6^(2K)(sigma+2K-1)M^(sigma+2K-1)].

Sur -1<=Re(s)<=2, |Im(s)|<=101, chaque facteur du produit est <230,
sigma+127>=126, et donc

    E_zeta <= [4*128^2/126]*(230/768)^128 <2^-182.

La dérivée du reste est <=16*2^-182=2^-178 sur les nœuds utiles,
par Cauchy avec disque1/16 contenu dans ce domaine. Ce sont des restes
analytiques ; les largeurs des primitives et de la somme sont ajoutées.
La représentation analytique de A multiplie par(s-1) après avoir supprimé
explicitement son pôle ; ses évaluations au bord T ne rencontrent pas s=1.
Les phases n^-s utilisent log(n) réel et sont évaluées nouvellement.
Source de normalisation : [Euler–Maclaurin NIST](https://dlmf.nist.gov/25.2.E9),
et [Fourier Bernoulli NIST](https://dlmf.nist.gov/24.8.E1), lectures ciblées.
Le reste pair affiché est dérivé par intégration par parties.

## Γ et ψ par formule à reste, pas par approximation flottante

Pour z=s+1 aux nœuds, Re(z)>0. Décaler w=z+64 et utiliser

    L_32(w)=(w-1/2)Log(w)-w+(1/2)log(2pi)
          +sum_(k=1..32)B_(2k)/[2k(2k-1)w^(2k-1)],
    logGamma(w)-L_32(w)
          =-(1/64)int_0^infty Btilde_64(x)/(x+w)^64 dx.

logGamma est la branche HOLOMORPHE sur Re(w)>0, réelle sur les réels
positifs ; on ne la remplace pas par le Log principal de Gamma(w).
Sur Re(w)>=64, le reste est <=4/(63*6^64)<2^-128.
Puis Gamma(z)=exp(logGamma(w))/product_(j=0..63)(z+j).
Le rayon multiplicatif exp(R)-1 et chaque division sont propagés.
ψ s'évalue en différentiant cette source, avec le reste dérivé par Cauchy,
et ψ(z)=ψ(z+64)-sum_(j=0..63)1/(z+j). La même route à z=1
donne gamma_E=-ψ(1), sans constante décimale importée.
La provenance exacte du reste découle de
[Johansson, équations21–23](https://arxiv.org/pdf/2109.08392), lecture ciblée :
son reste à somme jusqu'à31 devient le reste périodique ci-dessus après
inclusion du terme32. Il faut prouver cette formule, pas utiliser une
asymptotique sans constante.

## Quadrature verticale fermée

Deux segments de longueur200, 800cellules par segment, largeur h=1/4.
Leur disque holomorphe de rayon R0=3/8 reste dans Re(s)>1 à droite et
Re(s)<0 à gauche. À gauche l'équation fonctionnelle transporte le
logarithme dérivé vers Re(1-s)>1. Les zéros et le pôle1 sont hors de ces
disques. La Gamma a Re(s+1)>=1/8. Le majorant dérivé est

    W(Y,T)=1024Y^2+32T+2560 ; W(10000,100)<2^40.

En effet à droite |F|<256 et |Gamma(s+1)|<4 ; à gauche |F|<=2T+160
et |Gamma(s+1)|<16. Ces bornes proviennent de la série absolue Lambda,
de l'intégrale Gamma et de la série ψ, pas d'un max numérique supposé.

Dans chaque cellule, évaluer H(s)=G(s)F(s) aux128 points du cercle de
rayon Rc=3/16. Extraire les coefficients0..64 par DFT certifiée ; intégrer
exactement leur polynôme sur la cellule verticale. Conserver les orientations
droite moins gauche. Pour r=h/2=1/8, les rapports sont r/R0=1/3,
Rc/R0=1/2 et r/Rc=2/3. Le vrai reste, incluant alias de coefficients,
est majoré par

    E_quad <= (4T/(2pi))*W *
       [ (1/3)^65/(1-1/3)
         +(1/2)^128/((1-(1/2)^128)(1-1/3)) ]
       +(4T/(2pi))*3*epsilon_node.

Avec epsilon_node<=2^-80, E_quad<2^-44 sur papier. Le dernier rayon
inclut les racines de l'unité, l'incertitude des positions, EM, Stirling,
les produits, divisions, DFT et accumulation ; il n'est pas un champ libre.
Un vérificateur rejette tout nœud dont son certificat construit dépasse
la garde. Comptage fixé :1600*128=204800 nouveaux nœuds complexes.
La source pourrait être coûteuse (environ26millions de termes de ζ avant
optimisation prouvée) ; aucune durée mesurée ni faisabilité pratique sur ce
PC n'est annoncée avant la précritique ROLE6.

## Certificat horizontal et interprétation des zéros

512cellules réelles, largeur1/256, couvrent [-1/2,3/2]+100i.
EM sur des boîtes complexes et les primitives certifiées produisent une
enclosure de A sur CHAQUE cellule. Exiger distance à0 >=2^-24.
Le segment inférieur découle de la conjugaison de la vraie zeta, ou doit
être évalué séparément si cette propriété n'est pas disponible formellement.
Il n'y a ni zéro préchargé ni compteur critical-line présumé complet.

Sur le disque1/8 autour de chaque point horizontal, la somme EM et sa
queue donnent |ζ|<2^16 ; Cauchy donne |ζ'|<=2^19, donc |A'|<2^27.
La preuve de cette majoration doit garder les termes, le pôle éloigné de
la zone |Im(s)|>=99 et le reste. La non-annulation observée est un
CERTIFICAT EFFECTIF à vérifier sous Lean, pas une nouvelle prémisse analytique.
Si elle échoue, aucune interprétation en trace complète de zéros n'est
accordée ; le test thermique des deux droites peut néanmoins rester évalué.
La contribution horizontale est conservée avec E_horiz de C8, pas déclarée0.

## Arithmétique et terme archimédien indépendants

Évaluer les DEUX sommes de H_Y sur les domaines complets 2..X et2..Q.
Λ(n) provient de certificats neufs : primalité exacte / factorisation
exacte / vérification d'une puissance d'un seul premier. Pas de crible,
Möbius, masque ou banque précédente ; aucun facteur local ne sert
d'estimateur de la trace. Garder les contributions des puissances propres
dans un champ séparé sans les retirer du total. La borne Λ<=log se
prouve directement par sa définition PrimePow.

Les queues fixes de FINAL1 sont

    E_prim=exp(-X/Y)[(X+Y)logX+Y+2Y^2/X],
    E_dual=(logQ+1)/(YQ),
    E_arch=(4/3)[exp(-R/Y)+1/(2YR^2)+2/(YR)].

Elles ne sont pas ajustées au résidu. À nos paramètres E_dual<2e-9,
E_arch<3e-10 et E_prim<2^-112, par comparaisons rationnelles papier.
La largeur totale certifiée des deux sommes doit être <=2^-50.

Pour Arch, x=exp(u), 0<=u<=logR. L'intégrande devient

    B(u)=[exp(2u)exp(-exp(u)/Y)/Y
          +exp(-u)exp(-exp(-u)/Y)/Y-2f(1)]/[2sinh(u)].

La valeur amovible B(0)=f(1)/2 est dérivée. Sur les disques de rayon1/4
autour de cet intervalle, un majorant est W_arch=128Y+32/Y+32.
Il vient de |2sinh u|>=|u| pour |Im u|<=1/4, du numérateur borné
par16Y+4/Y lorsque |u|>=1/8, et de sa dérivée près de0.
Utiliser128cellules de largeur(logR)/128<1/8,96points de cercle
rayon1/8, degré32. La même quadrature Cauchy/DFT, avec rapports1/4
et1/2, donne E_quad_arch<2^-37 à nos paramètres, avec erreurs des
nœuds<=2^-80 et de logR réellement propagées. Il faut environ12288
nœuds supplémentaires. Aucune intégration d'une singularité tronquée.

## Enveloppe totale et falsification

Comparer les intervalles de
H_(X,Q) et 1+Y-J_T-(log4pi+gamma_E)f(1)-Arch_[1,R].

    E_total=E_vert+E_quad+E_prim+E_dual+E_arch
            +E_quad_arch+E_arithmetic_round+E_constants_round.

Toutes les fonctions affichées sont continues sur leurs domaines gardés.
Fixer E_arithmetic_round,E_constants_round<=2^-50 uniquement comme
gardes d'efficience contrôlées APRÈS construction des enclosures ; la
preuve d'enclosure n'est jamais remplacée par la garde. Les autres
constantes ne dépendent pas du résidu observé. Sur papier E_total<1e-8<tau.
Ajouter E_horiz si le résultat est exprimé en vraie trace de zéros Z_T.
Il reste inférieur à tau. Ces inégalités ne sont ni une mesure ni un PASS.

Contrôles négatifs obligatoires, faits dans une copie de l'estimateur :
omission deY ; omission de1 ; retrait du terme propre n=4 du côté arithmétique.
Ce dernier déplace le côté direct d'au moins1/Y=1e-4 : log2>1/2 et
exp(-4/Y)>1-4/Y. Les trois mutations dépassent strictement les enveloppes
proposées et doivent être disjointes ; sinon statut NON_DISCRIMINATING.
Autres mutations d'orientation peuvent être testées mais ne reçoivent pas
de détection promise sans borne préalable.

Statuts distincts : THERMAL_TRACE_INTERVALS_CERTIFIED ;
CONTOUR_BOUNDARY_CERTIFIED ou UNRESOLVED ;
FINITE_ZERO_TRACE_CERTIFIED seulement après résidus/formalisation ;
H1_FORMAL_OPEN tant que le compilateur ne valide pas la preuve ;
COEFFICIENT_N_OPEN ; D_N_UNPAID ; NO_WIN. Un écart d'intervalles
sur une vraie identité peut révéler une erreur de source, de certificat ou
de preuve ; il ne réfute pas automatiquement la conjecture de Goldbach.
