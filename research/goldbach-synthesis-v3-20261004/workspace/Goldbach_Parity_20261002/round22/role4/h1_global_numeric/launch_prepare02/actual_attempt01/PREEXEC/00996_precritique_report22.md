# Précritique indépendante ROLE6 de 15.3 — papier uniquement

Verdict : **C3–C9 sont cohérents sur papier**, avec les distinctions de
portée ci-dessous. Le budget analytique proposé est informatif à Y=10000.
Il n'existe encore ni évaluateur neuf gelé, ni certificat horizontal, ni
résultat numérique H1, ni preuve Lean globale. Le statut de mise en œuvre
est **SOURCE_REQUIRED / COST_HIGH_UNMEASURED**, pas PREPARED et pas PASS.
La taille d'un intervalle futur ne permet pas de déclarer une identité
fausse avant construction et contrôle des enclosures.

Cet audit ne modifie aucun fichier ROLE1, G0, Gamma ou archive. Il ne
réexécute aucun banc. Invocations nouvelles mathématiques : 0 ; Lean : 0 ;
probe de runtime : 0 ; installations : 0. Le prompt de sélection15.3 est
lié par son hash réel dans les reçus ; ses instructions génériques
d'évaluation ne sont pas une gate et n'annulent pas SOURCE/PAPER ONLY.
Baseline du prompt :0 ; score nouveau : NON_MESURE ; victoire :false.

## Fichiers réellement contrôlés

Le manifeste ROLE1 `paper_manifest22.json` est FULL et son SHA réel est
`812bad4eb69d612208eae8380d8bdc1dd8ab4fb2605d39eaa790f0479f2b37e3`.
Les six fichiers liés sont FULL : contour, précontrat numérique, probe,
charges Lean, rapport et reçus. Les six hashes et tailles annoncés sont
conformes. Les huit inputs historiques ont leurs hashes vérifiés ; leurs
tailles réelles sont lues, sans inventer de tailles attendues absentes du
manifeste. Directive et PROBE22 sont aussi relus FULL. Aucune relecture
FULL des six autres inputs historiques n'est revendiquée par cet audit.
Le prompt15.3 est FULL, SHA
`0ac337ada01aed929b00f2ff94a7f740409df18350d62433a58edd74fe371958`.

Une première commande metadata a eu un ParserError PowerShell (`6e4d78`).
Elle n'est pas créditée. Sa correction, pure lecture de hashes, est
`7de010`, exit0, avec les14bindings conformes. Aucun calcul mathématique
ou réservation de tentative n'a été effectué par ces commandes.

## C3, C4 et C5 : signes et charge globale

Avec c=3/2,d=-1/2, écrire F=1/(s-1)+zeta'/zeta. Les trois identités
intermédiaires signées sont

    int_c G zeta'/zeta /(2pi i) = -S_primal,
    int_d G zeta'/zeta(1-s) /(2pi i) = -S_dual,
    (int_c-int_d)G/(s-1)/(2pi i) = G(1)=Y.

Dans la deuxième, w=1-s renverse le sens vertical et ds=-dw le compense.
Comme zeta'/zeta(s)=chi'/chi(s)-zeta'/zeta(1-s), la contribution totale
de la droite gauche est I_chi+S_dual. On retrouve exactement

    J_infty=Y-S_primal-S_dual-I_chi.                         [C4]

L'inversion Mellin du dual utilise G(1-w) avec Re(1-w)=-1/2>-1 : son
domaine est correct. Les deux séries conservent tous les Lambda(n),
donc toutes les puissances premières. La [réflexion NIST25.4.2](https://dlmf.nist.gov/25.4.E2)
confirme la normalisation de chi utilisée. Le logarithme dérivé Euler
doit être dérivé de la convergence locale du vrai produit, sans série
Möbius. Ce sont des obligations de preuve et de provenance, pas des
hypothèses libres d'une finale H1.

La récurrence psi transforme son argument s/2 en 1+s/2 et fournit le
terme **+1/s**. Sur d, les deux autres arguments ont Re=3/4. Le terme
G/s sur cette droite vaut -int_0^1 f(x)/x dx. La
[représentation de psi NIST5.9.16](https://dlmf.nist.gov/5.9.E16) a le signe
e^-u-e^-zu, tel qu'écrit dans ROLE1.

Après u=2v, la dernière intégrale L du papier satisfait

    Arch-L=int_1^infty f(x)/x dx-2log2*f(1).

Les deux intégrales de f/x sont 1-exp(-1/Y) et exp(-1/Y), dont la somme
est1. Donc I_chi=(log(4pi)+gamma_E)f(1)+Arch-1. Le **-1** de C5 et
le mode **+1** de C3 sont corrects. Le pôle de zeta retiré dans A n'est
pas compté comme un zéro ; le modeY ne doit pas être retiré une deuxième
fois dans la somme de résidus.

Les échanges psi/Mellin doivent porter sur les différences groupées
près de u=0. Les termes séparés e^-u/(1-e^-u) y divergent. Un dominateur
construit, par exemple de croissance O(1+|t|) après annulation en u,
puis la décroissance Gamma en t, est nécessaire à Fubini. La preuve du
pôle amovible A(1)=1, de A(0)=1/2 et de l'inversion Mellin ne peut être
remplacée par une définition contenant H_Y.

## C6 : queue verticale

Sur c, la série absolue Lambda est<7 et |1/(s-1)|<=2, donc |F|<9<16.
Sur d, |cot(pi s/2)|=1 ; la
[série psi NIST5.7.6](https://dlmf.nist.gov/5.7.E6) donne
|psi(3/2-it)|<=1+2|1/2-it|<=2t+2 pour t>=0. Ajouter log(2pi),
le cotangent, la série Lambda réfléchie et1/(s-1) donne bien la marge
2(t+8). Les récurrences Gamma fournissent les facteurs2(t+2) et4 du
papier. Les deux signes de t et la normalisation1/(2pi) produisent
**32Y^(3/2)** et **8Y^(-1/2)** dans C6, avec1/pi devant l'intégrale.

C6 est fermée et continue en Y>0,T>=0. La comparaison annoncée
E_vert(10000,100)<2^-69 est conservatrice : pi>3, exp(-1)<3/8 et un
majorant rationnel du facteur polynomial suffisent. Aucun compte de
zéros, Turing, RH ou simplicité n'est requis par ce contrôle. Les bornes
|gamma_E|<=1 et log(2pi)<2 doivent néanmoins avoir leurs propres preuves.

## C7–C9 : ce que certifie un rectangle

Le rectangle est positivement orienté : droite vers le haut, gauche
vers le bas. G est holomorphe dans Re(s)>-1. A est holomorphe après sa
suppression réelle en1. Sur le bord, A'/A est défini si toutes les
enclosures horizontales sont strictement séparées de0 et si les deux
droites sont analytiquement sans zéro. Alors le résidu en un zéro rho
est mult(rho)*G(rho), sans hypothèse de simplicité. C7 est correct :

    Z_T=J_T+H_horiz,
    H_Y=1+Y-Z_T-C*f(1)-Arch+H_horiz-(J_infty-J_T).           [C9]

La preuve analytique exclut les zéros hors du strip dans ce rectangle
par Euler/équation fonctionnelle ; A(0) non nul est traité explicitement.
Les zéros triviaux -2,-4,... sont hors du rectangle. Des zéros éventuels
sur Re=0 ou1 n'ont pas besoin d'être exclus pour la somme sur le strip
fermé. Une absence de zéro au bord T est un vrai certificat à construire,
jamais le résultat d'une liste de zéros partielle.

Le majorant Gamma horizontal16*exp(-pi T/4) peut être obtenu par rotation
et bornes réelles sur sigma dans[1/2,5/2] ; il ne doit pas être déduit
de H2 sur[1,2] sans cette extension. C8 utilise bien la longueur totale4,
|A'|/delta et4/(2pi)<1. Aux paramètres annoncés, le majorant
(3/4)^75<2^-28 est valide ; la comparaison élémentaire
(3/4)^5<1/4 donne même une marge2^-30. Le signe du terme horizontal
reste **+H_horiz dans C9**. Si Z_T est seulement encadré depuis J_T,
il faut garder la corrélation des termes ou payer les deux enclosures
de H_horiz conservativement ; ne pas l'effacer deux fois.

**Distinction essentielle :** C7 certifie une vraie somme finie intérieure.
C3 utilise J_infty, un objet indépendant défini par les deux droites.
Identifier J_infty à une somme de tous les zéros sur une hauteur infinie
demande encore une preuve de passage à la limite des contours. C6 seule
ne garantit pas le contrôle d'A'/A sur une suite de bords horizontaux
passant arbitrairement près de zéros. Cette identification infinie n'est
pas nécessaire au test thermique C3 ni à C7/C9 au T certifié. Elle reste
un volet séparé, et n'est pas promue par le certificat512cellules.

## Euler–Maclaurin et sa dérivée

La somme1..M-1 et le terme **+1/2 M^-s** sont cohérents avec la forme
1..M et **-1/2 M^-s** de
[NIST25.2.9](https://dlmf.nist.gov/25.2.E9). Le reste pair du papier suit
de l'arrêt à B_(2K) ; il n'est pas une copie textuelle du reste impair de
cette page. Son signe moins, produit(s)_(2K), factorielle et exposant
x^(-s-2K) sont corrects. Les intégrations par parties conservent la
valeur Bernoulli à l'endpoint entierM.

[Fourier Bernoulli NIST24.8.1](https://dlmf.nist.gov/24.8.E1), pi>3 et
sum n^-128<2 donnent bien |Btilde128|<=4*128!/6^128. Sur le domaine
annoncé, sigma+127>=126 et chaque |s+j|<230. Le majorant

    4*128^2/126*(230/768)^128

est valide et plus fin que la marge2^-182 affichée. Le reste est une
fonction holomorphe après annulation du pôle commun ; Cauchy de rayon
1/16 donne la marge dérivée2^-178. Les nœuds utiles, y compris les
disques supplémentaires, restent dans -1<=Re(s)<=2, |Im(s)|<=101.

Le futur code doit produire zeta ET zeta' avec les deux restes. La
dérivée des produits peut utiliser P_next=(s+j)P et
P'_next=P+(s+j)P', sans divisions artificielles par s+j. Il faut inclure
les dérivées des puissances M^-s et du terme1/(s-1). Un EM seulement
ponctuel, suivi d'une différence finie non certifiée, ne paie pas zeta'.

## Stirling, psi et branches

[Johansson, équations21–23, p.11](https://arxiv.org/pdf/2109.08392) écrit
31termes avec R32 comportant B64-Btilde64. L'intégrale de la constante
B64 est exactement le terme32. Après son inclusion dans L32, le reste
est donc celui du papier, -1/64*int Btilde64/(x+w)^64. Aucune constante
B64 n'est perdue. Son majorant explicite est d'abord

    4*63! / [63*6^64*(Re w)^63],

puis <=4/(63*6^64) pour Re w>=64. L'inégalité63!<=64^63 explique la
factorielle apparemment disparue. La marge2^-128 est conservatrice.
Les nœuds Gamma ont Re(w)>64 avec une marge suffisante pour un disque
1/16 ; un reste dérivé <=16*2^-128 peut donc être déclaré explicitement
pour psi. Cela reste à ajouter à la propagation numérique.

La branche logGamma est holomorphe sur Re(w)>0 et normalisée sur les
réels. Log(w) y est principal ; Log(Gamma(w)) n'est pas interchangeable.
Les64facteurs z+j ne rencontrent pas0 aux nœuds. Toutes les divisions
requièrent une séparation effective de leurs enclosures. L'erreur de
l'exponentielle de logGamma est multiplicative, via exp(R)-1<=2R pour
0<=R<=1/2, puis transportée aux produits et divisions. gamma_E=-psi(1)
peut être évaluée avec cette nouvelle source et son reste ; aucune
constante décimale non certifiée n'est nécessaire.

## Quadrature DFT et positions

Soit H(s0+u)=sum a_k u^k, |H|<=W sur le disqueR0. Les128échantillons
au cercleRc fournissent b_k=a_k+sum_(l>=1)a_(k+128l)Rc^(128l).
Ainsi l'alias est <=W/R0^k * (Rc/R0)^128/[1-(Rc/R0)^128]. Après
intégration, sa somme est bien majorée par le deuxième terme géométrique
du précontrat. Le reste de degré64 commence à65. La stabilité aux erreurs
de nœuds est <=sum_(k=0..64)(r/Rc)^k<3. Les trois rapports1/3,1/2,2/3
sont corrects ; les majorants annoncés E_quad<2^-44 sont conservateurs.

L'intégration verticale doit inclure les puissances de i :

    int_(tau=-r..r) H(s0+i tau)dtau
       =sum_(k even<=64) a_k*(-1)^(k/2)*2r^(k+1)/(k+1).

Omettre ce facteur change la formule dès k=2. Les racines de l'unité
et les positions du cercle sont irrationnelles : leurs enclosures et
leur propagation sont obligatoires. Un évaluateur au centre d'un petit
rectangle n'est pas la valeur au point exact sans transport certifié.
Un choix possible est rho_position<=2^-128 ; Cauchy sur le grand disque
donne alors un transport fermé, par exemple8W*rho_position, avant les
autres erreurs. Il faut également payer les poids DFT, l'intégration
du polynôme et l'accumulation. La phrase epsilon_node inclut tout ne
doit pas devenir un champ libre. Les certificats devraient séparer
E_function, E_position, E_weights et E_accumulation.

Sur les grands disques, les arguments Gamma parcourent[1/8,7/8] et
[17/8,23/8]. Les normes16 et4 se dérivent de l'intégrale Gamma réelle
et de la log-convexité, pas du seul banc21cas. La série Lambda réfléchie
est bornée uniformément pour Re>=9/8. Le petit élargissement de t par
R0 doit figurer dans la preuve des majorants locaux. Le W global affiché
possède assez de marge pour cet élargissement à Y>=1 ; ne pas justifier
chaque summand par un T qui ne contient pas son disque.

## Arch : transformation, endpoint et disques

La transformation x=exp(u) donne exactement le B(u) écrit dans ROLE1.
B(0)=f(1)/2 : le numérateur s'annule et sa dérivée vaut f(1), tandis
que le dénominateur a dérivée2. Cette extension est holomorphe près de0.
Les autres zéros de sinh sont hors de |Im(u)|<=1/4. Sur cette bande,
|2sinh u|>=|u| se justifie par sinh(Re u) et sin(Im u), pas par une
division d'intervalles contenant0.

Avec cos(Im u)>=1/2 et t=exp(Re u)/Y, t^2 exp(-t/2)<=8 donne la
borne16Y+4/Y du numérateur. Pour |u|>=1/8, la division donne
128Y+32/Y. Pour |u|<=1/8, on peut majorer la dérivée du numérateur
par10/Y+12/Y^2<=22 et utiliser l'annulation en0 : |B|<=22. Le W_arch
annoncé128Y+32/Y+32 est donc constructible, sans max empirique.

La cellule a r=log(R)/256<1/16 ; R0=1/4 etRc=1/8 donnent les rapports
de somme majorés par1/4 et1/2. Degré32 et96points paient le reste33 et
l'alias96, donc E_quad_arch<2^-37 est conservateur. La source doit
évaluer le quotient amovible par une série ou un transport prouvé dans
les cellules contenant0. La borne au voisinage de0 n'est pas un oracle
pour ses valeurs. L'incertitude de logR se propage aux centres, largeurs,
poids et borne d'intégration ; elle doit être enregistrée explicitement.

## Lambda, budget total et mutations

Les deux domaines2..1000000 sont complets avant toute distinction
prime/power/composite. Des factorisations entières neuves avec facteurs
premiers certifiés déterminent Lambda exactement ; aucun crible, masque
de multiples ou ancienne table n'est requis. Les certificats peuvent
être dédupliqués, mais chaque entier doit avoir une justification. Les
puissances propres sont un sous-total diagnostique conservé dans H_Y,
et non un retrait du total. Le terme4 a Lambda(4)=log2.

Les queues E_prim, E_dual et E_arch sont celles de la vraie formule
globale, pas de simples comparaisons sur l'échantillon. Leurs bornes
papier annoncées sont conservatrices ; exp(-100)<(3/8)^100 et
log(1000000)<16 suffisent à les contrôler. E_total<1e-8 àtau=1e-6 est
cohérent avec les gardes de somme et constantes effectivement vérifiées.
Les queues primal/dual peuvent être payées en intervalles unilatéraux
[0,E] ; la queue Arch reste signée. Les erreurs des deux côtés doivent
être additionnées, pas attribuées seulement au contour.

OmissionY et omission1 déplacent respectivement10000 et1. Retirer la
contribution primale4 seule déplace déjà plus que1/Y=1e-4, car log2>1/2
et exp(-4/Y)>1-4/Y. Retirer les deux contributions4 est encore plus
grand ; le mutant doit préciser laquelle est retirée. Ces trois écarts
sont discriminants si les vrais rayons et la tolérance annoncés sont
payés. Des intervalles chevauchants déclenchent NON_DISCRIMINATING ou
UNRESOLVED, jamais une falsification proclamée.

## Coût et politique des volets

Le plan fixe204800nœuds complexes et12288nœuds Arch, plus512cellules
horizontales et deux sommes de999999termes avant catégories. Avec les
bases2..128 de l'EM, il représente **26009600 puissances complexes**,
même en partageant les termes entre zeta et zeta'. Il faut encore les
128facteurs de Pochhammer, les64corrections, Gamma/psi, produits et DFT.
La DFT directe0..64 ajoute1600*65*128 produits de poids complexes.

Réutiliser la forme Taylor128 de primitives, sans optimisation, ferait
3303219200itérations Horner pour sin/cos et3329228800 pour exp, seulement
sur les puissances EM. Il ne s'agit pas d'une durée mesurée ; aucune
conclusion d'impossibilité mathématique n'en découle. Cela rend la voie
Python768bits naïve coûteuse et interdit de présenter PREPARED/praticable
avant un vrai plan neuf de primitives. Le détail correctif figure dans
`evaluator_requirements22.md` : précomputation neuve de constants/logs,
accumulation intégrée de DFT, ou jets analytiques locaux avec la même
preuve Cauchy, tous à sélectionner et geler avant exécution.

Le banc thermique C3 est un volet autonome ; il n'a pas besoin de la
certification horizontale pour ses deux droites. Un échec de512cellules
ne falsifie pas C3 et ne retire pas un éventuel résultat thermique payé,
mais laisse CONTOUR_BOUNDARY_UNRESOLVED et la trace finie non certifiée.
C7/C9 requièrent le vrai checker complet et le vrai théorème des résidus.
La compilation H1 doit démontrer Mellin/Euler/FE/psi/Fubini, pas recevoir
C3 en prémisse. Une future preuve Gamma-prime/Box reste un auxiliaire
distinct ; le contour présent exige un domaine plus large que[1,2].

Recommandation : autoriser maintenant seulement la préparation de sources
neuves et des certificats de coût/domaines, avec une relecture complète.
La prochaine gate numérique doit nommer le volet, les fichiers, paramètres,
captures, tentative unique et erreurs. Aucun score de ce papier ne vaut
H1_FORMAL, FINITE_ZERO_TRACE, COEFFICIENT_N ou D_N. L'inversion additive,
les puissances propres physiques, les charges du bilan et le seuilsource
u>=10^24 demeurent séparés. Le présent N=1e8 via Y=sqrtN ne les paie pas.
