# Revue indépendante du producteur thermique H1 — SOURCE/PAPIER

Verdict : les règles d'enclosure et l'enveloppe sont fermées et cohérentes
sur papier pour les paramètres fixés, après l'addendum de domaines distinct.
Aucun défaut de terme, signe ou facteur n'a été identifié dans les neuf
modules runtime lus FULL. Cette revue ne mesure ni précision effectivement
obtenue, ni résultat, ni durée. Aucun import, parser Python, banc, Lean ou
probe n'a été invoqué. Les14bindings ROLE4 restent inchangés.

Niveau admissible d'un futur run : producteur d'intervalles audité sur papier,
avec contrôle structurel indépendant et décisions numériques falsifiables.
Le checker seul ne fournit aucun certificat d'enclosure transcendant.
Un éventuel THERMAL_TRACE_NUMERIC_AGREEMENT devra rester distinct d'un
théorème Lean, d'un certificat formel des primitives et de la trace de zéros.
Le statut de cette revue est SOURCE_REVIEW_NUMERICAL_ENCLOSURES_CLOSED,
au sens SOURCE/PAPIER explicite ci-dessous, sans budget effectivement PASS.

## Primitives et exactitude des restes

Les endpoints sont entiers sur grille2^-512. Produits, quotients, scalings
et carrés utilisent floor/ceil dirigés. Un quotient réel refuse0 dans le
diviseur ; le quotient complexe paie |z|² et exige son minorant positif.
Les racines isqrt vérifient les deux inégalités carrées. Point.from_box
utilise la somme des deux erreurs coordonnées, qui majore la norme réelle
complexe. La multiplication de points paie exactement ses deux arrondis.

Machin256 utilise pi=16atan(1/5)-4atan(1/239), avec la prochaine erreur
alternée1/(513q^513). Sin/cos réduisent par une période entière en conservant
toute la boîte pi. Leur polynôme et le rayon2*4^257/256! couvrent les deux
queues sur [-4,4]. Exp128 réduit au voisinage0 et ajoute2/8^129 avant les
carrés successifs ; tous les arrondis de carrés restent dans les boîtes.
Log utilise256 termes atanh et la queue2/(513*3^513)/(1-1/9).
Atan512 traite les domaines direct et transformé avec leur reste.
Les branches et les domaines complets des boîtes sont gardés ; un échec
produit une erreur, jamais une précision libre attribuée aux primitives.

EM conserve126 puissances2..127, le terme1, et la puissance128 multipliée
par128/(s-1)+1/2 et les64 corrections. La récurrence du Pochhammer normalisé
par128^length donne exactement M^(1-s-2k), sans facteur M manquant.
Sa dérivée inclut le terme1/128, la dérivée du pôle et -log128.
Le reste pair exact provient d'EM avec Bernoulli périodique128.
La borne4*128²/126*(230/768)^128 est<2^-182 : le préfacteur est<2^10,
230/768<1/3 et3^128>2^192. Le reste holomorphe a donc dérivée<2^-178
par Cauchy de rayon1/16. L'addendum ferme le domaine de ce disque.

Stirling utilise32 termes, la branche holomorphe logGamma sur Re w>0 et
le reste -(1/64)*int Btilde64(x)/(x+w)^64 dx. Son rayon est au plus
4*63!/[63*6^64*(Re w)^63]≤4/(63*6^64), puisque63!≤64^63.
La dérivée reçoit16fois ce rayon. Le code conserve le reste AVANT exp,
réduit par un entier klog2, multiplie exactement par2^k et divise par les
64facteurs de récurrence. Psi dérive la même source et soustrait les64
inverses. gamma_E=-psi(1) est neuf, sans constante décimale/oracle.

Ces identités et inégalités sont vérifiées ici par dérivation papier,
avec leurs domaines ; elles restent à formaliser sous Lean. En particulier
la formule EM paire, le reste périodique Stirling/sa branche, Cauchy, les
identités de primitives et leurs arrondis ne sont pas promus en axiomes.
La vraie identité globale C3 est un objectif distinct encore ouvert.

## Catalogue, unités et quadratures

Les points sont a+(3/16)omega_j+i(-799/8+k/4). Les32768tracks ont chacun
800 valeurs :32512graines EM,256graines Y,127étapes EM et1étape Y.
La phase est -ilog(n)/4 pour n^-s et+ilogY/4 pour Y^s.
Les majorants vrais U128 etY² et la récurrence e_next≤(1+eq)e+Ueq+3EPS
paient les erreurs ; les gardes des graines/étapes sont construites.
L'ancien constructeur EM incompatible n'est pas appelé.

La garde de la graine Y est payée aussi àj=0, sur le côté droit.
La série positive de exp(7/3) jusqu'au degré6 vaut5358205/524880>10,
donc log10000<28/3. Avec Re(s0)≤27/16+EPS,
Re(s0*logY)<63/4+une erreur dyadique explicitement bornée<16.
La réduction réelle Exp128 utilise au plus8carrés ; sa queue2^-386
est amplifiée de moins de2^34. Les arrondis du log atanh256 donnent
une largeur<2^-400 (borne grossière2^20EPS et queue géométrique).
La phase a module<1010, dans le domaine trig ; le reste trig≤2^-381,
car256!≥128^128. Les gardes primitives de largeur donnent chacune
<2^-299, avec les incertitudes d'argument/log/pi conservées.
L'amplitude vraie<exp16<2^24, donc les deux produits de coordonnées
et Point.from_box donnent rayon<2^-270<2^-200. Il n'y a pas de
manque de marge identifié pour thermal_y_track. Aucun succès effectif
de cette garde n'est annoncé avant un run ; aucune source n'est changée.

Le disque vertical3/8 reste dans Re s>1 ou Re s<0. La série Lambda
réfléchie sur Re≥9/8, Lambda≤log et la comparaison intégrale donnent
un majorant<80. À droite, |F|<256 et Gamma≤4 ; à gauche la récurrence
psi et le cotangent donnent |F|≤2T+160 et Gamma≤16. Par exemple
|psi(1-s)|≤1+2|s|≤2T+7/2 et |cot(pi*s/2)|<6 sur ce disque.
L'intégrale Gamma et la convexité réelle paient ses normes jusqu'à Re1/8.
Ainsi W=1024Y²+32T+2560 majore le vrai H sur les grands disques.
La marge entre3/16 et3/8 donne le transport Cauchy8W*rho.

Les poids verticaux contiennent i^k,1/(2pi), droite moins gauche.
Degré64/alias128 avec rapports1/3 et1/2 donnent la queue affichée.
Les erreurs nodales sont payées dans les quatre folds, pas ajoutées sous
forme d'un epsilon libre au reste analytique.

Arch évalue le vrai quotient B(u) avec u=logx ; exp(2u)=exp(u)² et les
exponentielles emboîtées gardent leurs parties imaginaires.
La numérateur s'annule en0 et sa dérivée vaut f1 ; sinh a dérivée1.
L'extension est donc B(0)=f1/2. Sur la bande|Im u|≤1/4,
|2sinh u|≥|u|. Loin0 le numérateur≤16Y+4/Y ; près0 sa dérivée≤22
pourY≥1. Cela construit Warch=128Y+32/Y+32, sans max observé.

Les128cellules Arch gardent la vraie longueur logR, demi-largeur logR/256,
96points et degré32. La marge des disques paie16Warch pour les positions.
La dérivée de chaque poids par logR est≤(1/(128m))*sum_even(1/2)^k
≤1/(96m) ; le supplémentrho_logR/(96²) est correct.
La queue16Warch utilise logR<16 et inclut le degré33 et l'alias96.
Les nœuds sont à distance>1/64 de0, puis la garde de boîte est1/128.

## Arithmétique, quatre budgets et falsification

Tous les999999entiers sont visités avant classification. Le certificat
n=p^e*r, p premier et p ne divisant pas r, est contrôlé deux fois en
streaming. Si r>1, n ne peut être une puissance d'un seul premier.
Lambda vaut donc exactementlogp pourr=1, sinon0. Aucun crible ou table.
Les termes sont(logp)(n/Y)exp(-n/Y) et(logp)exp(-1/(Yn))/(Yn²).
La Taylor duale16 soustrait le terme suivant a^17/17! et arrondit dehors.
Toutes les puissances propres restent dans les deux sommes.

Pour p,w et rayons rf,rp,rw, les produits croisés sont payés par
(|w|_1+rw)(rf+rp)+|p|_1rw+erreur_produit. L'addition des points est
exacte. RF vient des vraies boîtes évaluées, RP du transport, RW des
poids, et les arrondis exacts forment la quatrième classe.
Les rayons de positions/poids sont arrondis dehors sur la grille.
Les quatre sums ont donc dénominateur divisant2^1024 ; les guards
d'export ne réintroduisent pas l'ancien dénominateur Fraction géant.

Les queues originales, leurs spécialisation rationnelles et les erreurs
effectives sont additionnées. Les queues primale/duale sont positives,
verticale/Arch signées. Les gardes nodales2^-81, poids/accumulation2^-72,
sommes/constantes2^-50 et total<10^-8 sont testées APRÈS construction.
La continuité des expressions ne dispense pas des domaines de l'addendum.

Le mutant retire uniquement le terme primal4 ; dual4 reste dans le total.
Log2>1/2 et exp(-4/Y)>1-4/Y>1/2 àY=10000 donnent un déplacement>1/Y.
Les modes1 etY sont chacun conservés une fois puis omis dans leur mutant.
Les intersections, le résidu≤tau et les disjonctions restent des décisions
futures à recalculer ; aucune n'a été observée ici.

## Limite exacte du checker et coût

Le checker ne reconstruit PAS evaluation_box depuis ζ/Γ, circle_box depuis
les racines, weight_box depuis le noyau, ni finite_arithmetic/primal_four
depuis les valeurs log/exp. Il contrôle les certificats entiers, les clés,
les rayons dérivés de ces boîtes, les folds, queues et décisions.
Un résultat structurel positif seul ne certifie donc pas une boîte
transcendante ni une somme arbitraire. La provenance future doit lier les
neuf sources auditées, tous les inputs/output et le niveau papier explicite.

Coût exact des catalogues :217088nœuds ;26181632avances EM/Y ;999998
avances primales supplémentaires ;13107200facteurs de reconstruction Gamma.
Il reste26009600étapes normalisées Pochhammer et les sommes EM.
Les fonctions Gamma/Arch et les contrôles de primalité restent coûteux.
Aucune durée/mémoire/taille de flux n'est mesurée. Un arrêt de coût ou
une garde non satisfaite ne constitue pas un contre-exemple mathématique.

Aucun blocker source identifié ; obligations formelles ouvertes : primitives,
EM/Stirling, W/Cauchy/Arch, queues/continuité, C3/C5 et résidus.
Horizontal512cellules UNIMPLEMENTED ; H1_FORMAL/COEFFICIENT_N OPEN,
D_N UNPAID ; NO_WIN. Cette revue ne valide aucun ancien banc comme oracle.

## Lectures réelles

Manifest FULL834877 SHAe1caa3… ; contrat/reçus FULL3cc8ce SHAcea359…/b54727… .
Runtime : transport FULL0b349d (2fd293…), envelopes FULL117862 (f988d3…),
arithmétique FULLd0dc11 (ce60c6…), producteur FULLd95321 (e47dfc…),
checker FULL3e2d8d (b2e9e3…), analytic FULLc90264 (a00fc6…),
kernel FULLdff316 (03a557…), unit FULL7f025a (c44fc2…),
dyadic FULLbbd377 (290d0e…). Les deux dernières lectures précèdent le
handoff mais portent exactement sur les mêmes bytes.
Contrats : numeric FULL43322e, précritique FULL31fa14, requirements FULL5b15eb,
contour C1–C9 FULL406857. Une lecture envelopes n'avait pas créé son processus
(erreur technique ACL helper), corrigée117862 sans faux crédit FULL.
Les recherches/inventaires n'ont pas de crédit de lecture mathématique FULL.
