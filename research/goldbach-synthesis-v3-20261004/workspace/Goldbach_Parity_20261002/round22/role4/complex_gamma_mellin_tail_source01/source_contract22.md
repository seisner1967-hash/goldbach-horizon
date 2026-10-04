# Queue Mellin de la vraie Gamma — contrat SOURCE22

Statut : un module SOURCE gelé pour revue indépendante, non compilé par
auteur ou juge, non PREPARED. Le mot DRAFT du commentaire Lean conserve
cette qualification. 22 déclarations : 18 théorèmes,4 définitions et22
prints axioms qualifiés. Aucune prémisse de rayon, de majorant final ou
d'intégrabilité finale n'est offerte.

Objet réel : pour Re(w)>0 et t réel,
K(w,t)=Complex.Gamma(2+it) * w^(-2-it), cpow principal. Le domaine est
explicitement dans Complex.slitPlane et w≠0 via Local26. Avec
eta(w)=(pi/2+|Arg(w)|)/2, delta(w)=eta(w)-|Arg(w)|>0 et
C(w)=||w||^(-2) sec(eta(w))^2, la domination déjà prouvée dans Local26 est
||K(w,t)||≤C(w) exp(-delta(w)|t|). Elle provient de la vraie rotation de
Gamma, pas d'une Gamma abstraite ou d'un rayon postulé.

Pour H≥0, le module définit les deux vraies intégrales sur (H,+infini),
K(w,t) et K(w,-t), puis leur somme normalisée par1/(2pi). Il prouve leur
intégrabilité depuis le véritable Laplace réel et intègre la domination :
chaque norme≤C exp(-delta H)/delta. L'erreur des deux rayons est donc

 R(w,H)=C(w) exp(-delta(w) H)/(pi delta(w)).

Le transport Lebesgue t↦-t et le découpage de l'intégrale L1 sur[-H,H]
payent l'identité exacte entre cette queue et
complexGammaInverse(w)-complexGammaTruncated(w,H). L'erreur de troncature
de cette vraie intégrale Mellin est≤R(w,H). Les intégrales utilisent volume;
le découpage intégral+complément fixe explicitement la mesure.

R est positif pour Re(w)>0 et tout H réel, continu conjointement sur le
demi-plan×R, et décroît en H. Pour chaque centre w du demi-plan et H≥0,
la continuité construit une vraie boule ouverte epsilon>0 telle que pour
z dans cette boule et T≥H, Re(z)>0 et ||queue(z,T)||≤2R(w,H). Epsilon est
obtenu du voisinage de Re>0 et de R(z,H)<2R(w,H), sans hypothèse de rayon.
C'est une uniformité locale à coupure fixée. Le module ne prouve pas encore
la continuité conjointe de la queue complexe elle-même, ni un théorème
formalisé R(w,H)→0/localement uniforme quand H→infini. La borne explicite
exponentielle permet le contrat papier correspondant, mais aucun crédit
Lean de ce prolongement n'est annoncé ici.

Le domaine H≥0 est requis pour les rayons disjoints et l'erreur effective.
L'évaluation auxiliaire de l'intégrale exponentielle accepte tout H réel.
La continuité/positivité/monotonie de R accepte H réel. La constante contient
sec(eta)^2 et1/delta : le coût près de Re(w)=0 est visible et aucune
uniformité jusqu'au bord n'est postulée.

Dépendance locale unique : ComplexGammaMellinLocal22 source et olean du
vrai PASS22 indépendant26, conservé malgré le reçu global26 FAILED dû au
second module. ROOT a observé sa conservation et l'a crédité. Sourcee54cac...
olean364ac79...,reçu53201e...,observation9b7697... sont liés avec SHA
complets au handoff. Les dépendances transitives GammaPrerequisites22
(batch02 indépendant) et ThermalGammaMellinInverse22 (batch20 indépendant)
restent readonly ; une future préparation doit fermer leurs imports et
les bytes/cache exacts, sans les recompiler. Aucun import du module
Holomorphy02 échoué ni de la réparation03 n'est utilisé ici.

Le remplacement de complexGammaInverse par exp(-w) est un raccord aval à
l'identité analytique de Holomorphy27, pas une prémisse de ce module.
Aucun calcul de primitives, quadrature finie, produit zeta'/zeta, échange
Lambda, trace globale, annulation de bords, PP/frontière,D_N ou WIN n'est
prouvé par cette queue auxiliaire. Toute compilation future requiert sa
revue et une gate distincte ROOT. Zéro auteur Lean/probe/runtime/math ici.
