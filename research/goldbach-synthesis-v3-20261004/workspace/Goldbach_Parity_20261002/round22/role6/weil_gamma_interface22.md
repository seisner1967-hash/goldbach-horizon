# Interface Gamma-prime vers l'annexe Weil 15.2

Statut : dérivation papier et précontrat SOURCE ONLY. Aucun nouveau
producteur n'est exécuté, aucun zéro n'est calculé et aucune compilation
Lean n'est invoquée. Les bancs G0 et Gamma sont clos et non rejouables.
Le PASS fini Gamma ne fournit ni une liste de zéros, ni sa complétude.

## Objet à encadrer

Pour Y=10000, N=100000000 et un vrai zéro rho=beta+i gamma de zeta,
le terme de l'annexe est

    H_Y(rho) = Y^rho Gamma(rho+1),
    Y^rho = exp(rho log Y), avec log Y réel.

Le domaine général est 0<=beta<=1. Pour les boîtes positives,
0<gamma_lo<=gamma<=gamma_hi<=100. Aucune égalité beta=1/2, simplicité
ou RH n'est présupposée. Les boîtes négatives sont traitées par conjugaison
après justification ; leurs multiplicités sont conservées.

La représentation complexe utilisée est la Laplace avec branche
principale, Re(s)>0 et Re(c)>0 ; elle est recensée dans
[DLMF 5.9.1](https://dlmf.nist.gov/5.9.E1). Pour c=exp(i theta),
theta=pi/4 et Im(s)>=0, sa forme est

    Gamma(s)=c^s int_0^infty exp(-c x)x^(s-1) dx.

Ici log c=i theta. Sur x>0, log x est réel ; dans le changement x=exp(v),
l'intégrande entière en v n'utilise pas une nouvelle branche de puissance.

## Majorant fermé de Gamma-prime

Sur 1<=sigma=Re(s)<=2, gamma=Im(s)>=0, la dérivation en paramètre s donne

    Gamma'(s)=i theta Gamma(s)
       + c^s int_0^infty exp(-c x)x^(s-1)log x dx.

Cette formule requiert une preuve de domination locale et de dérivation
sous l'intégrale. Elle n'est pas encore un théorème Lean compilé. Elle
s'audite avec un dominateur intégrable sur tout segment compact du strip.

Après multiplication par exp(pi gamma/4), |c^s| devient 1. Sur (0,1),
x^(sigma-1)<=1 et le module de l'amortissement est <=1, donc le moment
absolu logarithmique est <=int_0^1 -log x dx=1. Sur [1,infty),
x^(sigma-1)log x<=x^2 et cos(theta)>=1/2, donc le moment est <=
int_0^infty x^2 exp(-x/2)dx=16. Avec H2, le module normalisé de Gamma
est <=2 et |theta|<1. Ainsi

    |Gamma'(sigma+i gamma)| <= 19 exp(-pi gamma/4).          (Gprime)

La constante 19 est construite par 1+16+2 ; elle n'est pas une erreur
d'évaluation ajustée après observation. ROLE4 a audité cette dérivation
sur papier. La domination en paramètre et l'identité dérivée restent des
obligations de preuve distinctes du contrôle fini Gamma effectué.

## Transport d'une boîte de zéro

Soit une boîte rectangulaire B centrée en rho0, de demi-largeurs rationnelles
delta_beta et delta_gamma, contenue dans le domaine ci-dessus. Le segment
de rho0 à tout rho dans B reste dans le strip et au-dessus de gamma_lo.
Comme |rho-rho0|<=delta_beta+delta_gamma, (Gprime) donne

    |Gamma(rho+1)-Gamma(rho0+1)|
      <= 19 exp(-pi gamma_lo/4)(delta_beta+delta_gamma).

Pour le terme complet H_Y, la dérivée est

    H_Y'(rho)=Y^rho [log Y Gamma(rho+1)+Gamma'(rho+1)].

Avec |Y^rho|=Y^beta<=Y et H2, le rayon de localisation est donc

    R_box(Y,B)=Y exp(-pi gamma_lo/4)(19+2 log Y)
                         (delta_beta+delta_gamma).          (Rbox)

Une évaluation ponctuelle certifiée de H_Y(rho0) doit être élargie par
R_box. Le rayon de localisation ne remplace ni l'erreur du calcul au
centre, ni l'incertitude de log Y, ni les erreurs de la phase et des
produits. Chaque boîte est sommée avec sa multiplicité ; une paire
conjuguée contribue 2 Re(H_Y(rho)) et paie deux fois le rayon de module.
Une intersection d'intervalles large signifie UNRESOLVED, pas FALSE.

## Paramètres proposés avant toute future gate

Le compte inconditionnel N_+(t)<=t log t employé dans le contrat ROLE1,
à t=100, donne N_+(100)<500 car log100<5. Sa preuve reste une obligation
mathématique et Lean visible. Aucun nombre de zéros effectivement isolés
n'est inventé ici. En comptant les deux signes avec multiplicité, un
budget conservateur est 1000 termes.

Proposition de précision des boîtes : les deux demi-largeurs <=2^-80.
Comme log10000<10, la somme de tous les rayons de localisation est

    sum R_box <=1000*10000*39*2*2^-80
              =780000000/2^80 <2^-50.

Les inégalités de logarithmes peuvent être établies sans flottant par
exp(1)>=8/3 et des comparaisons entières. Les valeurs décimales de zéros
arrondies non certifiées ne satisfont pas ce précontrat.

Le futur module Gamma général pourra adapter, avec dépendance READONLY
hashée et nouvelle revue complète, l'arithmétique dyadique actuelle. Il
devra évaluer les vrais centres rationnels de toutes les boîtes, au lieu
de copier les sorties des 21 cas du banc clos. La quadrature tournée
[-32,6], h=1/256, degré12, garde |Im(s)|<=100, possède sur papier les
budgets uniformes déjà audités :

    E_quad=19/2216615441596416,
    E_left=(3/8)^32,
    E_right=516/2^128,
    E=E_quad+E_left+E_right.

Il faut encadrer chaque primitive et vérifier la largeur réelle après
reconstruction complexe de Gamma. Un objectif explicite est un rayon
complexe au centre <=4(E+2^-80), en conservant la preuve d'enclosure et
la garde d'efficience séparées. Sous cette garde réellement vérifiée,
la contribution conservatrice de ces erreurs Gamma, avant les autres
erreurs du produit Y^rho, est <=40000000(E+2^-80)<1/100000. Ce budget
est un critère fixé à implémenter et vérifier, pas une mesure nouvelle
ni un PASS général du strip.

L'exponentielle réelle beta logY est dans [0,10] ; la phase gamma logY
est dans [-1000,1000] pour les deux signes. Ces domaines sont inclus
dans les domaines des primitives gelées. Pour logY, une nouvelle source
peut utiliser log10000=4(3 log2+log(5/4)) et

    log u=2 sum_(j=0..J-1) z^(2j+1)/(2j+1)+reste,
    z=(u-1)/(u+1),
    0<=reste<=2 z^(2J+1)/[(2J+1)(1-z^2)], z in {1/3,1/9}.

J=256 est proposé avant gate ; cette source, ses restes et leur
propagation n'ont pas encore été exécutés ni gelés. Le produit final
paie l'incertitude de logY une seule fois à chaque dépendance effectivement
utilisée, avec les enclosures complètes plutôt qu'une phase centrale.

## Certificat de complétude requis

Une entrée exploitable contient pour chaque boîte ses bornes rationnelles,
sa multiplicité certifiée, sa provenance, son certificat d'existence et
un certificat que la frontière ne contient pas de zéro. Le certificat
global doit justifier que l'union de ces boîtes couvre tous les zéros du
strip avec 0<Im(rho)<=100, avec le traitement explicite du bord T=100.
Un compte par argument principle ou une variante de Turing certifiée
peut fournir cette seconde couche. Un changement de signe sur la seule
ligne critique ne suffit pas sans comparaison au compte global.

[Platt et Trudgian, section2](https://arxiv.org/pdf/2004.09765) séparent
le compte complet par Turing et l'isolation de haute précision ; leur
théorème de hauteur ne fournit pas à lui seul les boîtes numériques
nécessaires à cette somme. [Platt, Isolating some non-trivial zeros of
zeta](https://research-information.bris.ac.uk/ws/portalfiles/portal/78836669/platt_zeta_submitted.pdf)
décrit une isolation rigoureuse à haute précision. Ces références sont
des sources primaires lues en ciblé, pas des artefacts de données locaux
avec hash inventé. Aucun certificat externe ni boîte de ce travail n'a
été importé ou vérifié ici.

Le format futur doit rejeter une liste vide, une couverture partielle,
un doublon de multiplicité, une boîte chevauchant le bord sans traitement,
une précision insuffisante et un certificat de contour manquant. Les
statuts attendus séparent `ZERO_BOXES_CERTIFIED`, `ZERO_COMPLETENESS_OPEN`,
`GAMMA_BOX_ENCLOSURES_CERTIFIED` et `REAL_TRACE_UNRESOLVED`.

## État et livrables nécessaires

IDENTITE_PAPIER : Gprime et Rbox ont une dérivation fermée auditée.
SOURCE_ONLY : paramètres, budgets et schéma d'interface ci-dessus.
OPEN : preuve dérivée sous l'intégrale, formalisation de Gprime/Rbox,
source du log avec propagation, module Gamma général, certificat complet
des zéros et évaluation de toutes leurs boîtes. Les queues, l'intégrale
archimédienne avec sa valeur amovible à1, les constantes et la somme
arithmétique de la vraie annexe restent des couches supplémentaires.

Aucun fichier `.lean` nouveau n'est produit par ROLE6. ROLE4 possède la
source H2 séparée ; sa compilation appartient au Juge et à une gate
distincte. Cette interface n'est pas un producteur PREPARED et n'autorise
aucun calcul. Elle ne change aucun binding G0/Gamma, n'utilise aucun ancien
résultat comme oracle et n'offre aucun crédit coefficientN, D_N ou WIN.
