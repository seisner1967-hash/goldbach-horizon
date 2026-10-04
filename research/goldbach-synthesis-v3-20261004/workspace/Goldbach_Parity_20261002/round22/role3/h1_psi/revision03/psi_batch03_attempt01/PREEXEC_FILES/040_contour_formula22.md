# ROLE1 — raccord global par deux droites et contour certifié

Statut : DÉRIVATION PAPIER / SOURCE ONLY. Aucune invocation Lean, aucun calcul
numérique, aucun producteur exécuté. La proposition attaque la vraie couche H1,
pas seulement une estimation Gamma. Les bancs G0 et Gamma sont clos et ne sont
pas rejoués. Les 59 modules / 993 déclarations auxiliaires du bilan courant ne
certifient pas cette identité. Aucun gain sur le coefficient N ou sur D_N n'est
revendiqué.

## 1. Objet analytique indépendant

Pour Y >= 1, poser f(x)=(x/Y)exp(-x/Y), G(s)=Y^s Gamma(s+1),
A(s)=(s-1) zeta(s), avec A(1)=1 par suppression réelle du pôle.
Toutes les puissances Y^s utilisent le logarithme réel de Y. A est une fonction
analytique construite à partir de la vraie zeta, non à partir de H_Y.

Poser c=3/2, d=-1/2 et F(s)=A'(s)/A(s) sur les deux droites. Ces droites
sont sans zéro : à droite, produit d'Euler absolument convergent ; à gauche,
équation fonctionnelle, Gamma sans zéro et sinus sans zéro sur cette droite.
Aucune RH, simplicité ou liste de zéros n'intervient. La preuve analytique du
produit d'Euler et de son logarithme dérivé est autorisée ici ; elle n'utilise
ni inversion de Möbius, ni crible, ni décomposition de Vaughan, ni reste AP.
La dépendance mathlib historique qui procède via Möbius ne sera pas utilisée
comme nouvelle preuve de cette étape.

Définir l'intégrale réelle complexe convergente

    J_infty(Y)=(1/(2 pi)) int_(t in R)
                   [G(c+it)F(c+it)-G(d+it)F(d+it)] dt.          (C1)

Le terme archimédien est celui fixé dans FINAL1 :

    Arch_Y=int_1^infty
      [f(x)+f(1/x)/x-2f(1)/x]/(x-x^(-1)) dx.                  (C2)

Le quotient reçoit en x=1 sa valeur amovible f(1)/2, à prouver.
L'identité arithmétique globale proposée est

    H_Y=sum_(n>=2) Lambda(n)[f(n)+f(1/n)/n]
       =1+Y-J_infty(Y)-(log(4 pi)+gamma_E)f(1)-Arch_Y.          (C3)

H_Y conserve TOUS les entiers et toutes les puissances premières sur les deux
axes. Les termes 1, Y, f(1), l'intégrale archimédienne et les deux orientations
de contour sont explicites. J n'est pas défini par cette égalité.

## 2. Dérivation complète de C3

La preuve proposée procède par Mellin, équation fonctionnelle et intégrale de
psi ; elle ne prend pas « Weil est vrai » comme prémisse. Les identités
classiques nécessaires doivent être démontrées dans Lean si elles ne sont pas
déjà disponibles avec provenance admissible.

L'inversion Mellin donne f(x)=(2 pi i)^(-1) int_Re(s)=b G(s)x^(-s)ds,
pour tout b>-1. La décroissance Gamma justifie l'intégration absolue. Le
logarithme dérivé du produit d'Euler donne, pour Re(s)>1,

    zeta'(s)/zeta(s)=-sum_(n>=2) Lambda(n)n^(-s).

Il se prouve en dérivant le produit absolument convergent, puis en développant
chaque facteur géométrique et en identifiant les puissances premières. Aucune
série de 1/zeta, aucune somme Möbius et aucun masque de carrés-libres.
Fubini sur c=3/2 est payé par la série absolue et la décroissance de Gamma.
Ainsi l'intégrale du morceau zeta'/zeta à droite vaut -sum Lambda(n)f(n).

Écrire zeta(s)=chi(s)zeta(1-s), où
chi(s)=2(2 pi)^(s-1)sin(pi s/2)Gamma(1-s). Son logarithme dérivé est

    zeta'/zeta(s)=chi'/chi(s)-zeta'/zeta(1-s).

Le changement w=1-s transporte la droite d sur c, avec l'orientation
exactement compensée par ds=-dw. Le morceau zeta'/zeta(1-s) donne
-sum Lambda(n)f(1/n)/n, car Mellin(f*)(w)=G(1-w).

Le pôle artificiellement supprimé dans A fournit

    (2 pi i)^(-1)(int_c-int_d) G(s)/(s-1) ds=G(1)=Y.

Les segments horizontaux de CE contour sans zeta tendent vers zéro par Gamma.
On obtient donc déjà

    J_infty=Y-H_Y-I_chi,
    I_chi=(2 pi i)^(-1) int_d G(s)chi'(s)/chi(s) ds.            (C4)

Voici le calcul du terme archimédien, qui constitue la dette globale essentielle
à formaliser et dont les constantes ne sont pas laissées libres.
La version symétrique de chi et la récurrence psi donnent sur d

    chi'/chi(s)=log pi+1/s
        -(1/2)psi((1-s)/2)-(1/2)psi(1+s/2).

Les deux arguments de psi ont partie réelle 3/4. Employer

    psi(z)=-gamma_E+int_0^infty
                 [exp(-u)-exp(-zu)]/(1-exp(-u)) du,
    Re(z)>0.

Après u=2v, garder les différences dans un seul intégrande au voisinage de 0.
Mellin et Fubini donnent

    I_chi=(log pi+gamma_E)f(1)-int_0^1 f(x)/x dx
       +int_0^infty
        [exp(-v)f(exp(-v))+exp(-2v)f(exp(v))
                              -2exp(-2v)f(1)]/(1-exp(-2v)) dv.

La différence entre Arch_Y (C2) et la dernière intégrale est

    int_1^infty f(x)/x dx-2 log(2)f(1).

En effet x=exp(v) et int_0^infty exp(-v)/(1+exp(-v))dv=log2.
Pour notre f, les deux intégrales de f/x sont respectivement
1-exp(-1/Y) et exp(-1/Y). Ainsi

    I_chi=(log(4 pi)+gamma_E)f(1)+Arch_Y-1.                    (C5)

C4 et C5 prouvent C3. Les termes amovibles, échanges d'intégrales et inversion
Mellin sont de vraies obligations de preuve ; leur dérivation affichée ne vaut
pas compilation. Ce calcul est un raccord substantif au global, absent des
auxiliaires Kernel/Finite/Gamma actuels.

## 3. Queue verticale fermée sans compte global des zéros

Poser a=pi/4. La borne Gamma sur la bande [1,2], suivie de la récurrence, donne
pour t>=0

    |Gamma(5/2+it)|<=2(t+2)exp(-at),
    |Gamma(1/2+it)|<=4exp(-at).

La borne absolue de la série Lambda sur Re(s)=3/2 est <7. Elle se déduit de
Lambda(n)<=log n et de la comparaison intégrale décroissante de
log(x)x^(-3/2) sur x>=2. Donc |F(c+it)|<9<16.
Sur d, |cot(pi(d+it)/2)|=1. La série psi sur Re(z)>=1 donne
|psi(3/2-it)|<=1+2|1/2-it|<=2t+2, en utilisant |gamma_E|<=1
et sum_(n>=1)n^(-2)<=2. Avec log(2pi)<2,

    |F(d+it)|<=2(t+8).

Par conséquent la troncature J_T de C1 à [-T,T] vérifie, pour T>=0,

    |J_infty-J_T|<=E_vert(Y,T),
    E_vert=exp(-aT)/pi *
       [32Y^(3/2)((T+2)/a+1/a^2)
                         +8Y^(-1/2)((T+8)/a+1/a^2)].         (C6)

Cette fonction est fermée et continue en Y>0,T>=0. Elle ne nécessite ni N(t),
ni Turing, ni boîtes de zéros. À Y=10000,T=100, des comparaisons rationnelles
avec pi>3 et exp(-1)<3/8 donnent E_vert<2^(-69), sur papier.
Cela est une borne précontractuelle, aucun résultat de calcul.

## 4. Vraie trace finie des zéros par certificat de contour

Pour donner une interprétation spectrale finie authentique, prendre le rectangle
R_T=[-1/2,3/2]+i[-T,T], orienté positivement. Sur les segments horizontaux,
exiger un certificat numérique vérifiable de |A(s)|>=delta>0.
Les bords verticaux sont sans zéro par les propriétés analytiques précédentes.
G est holomorphe sur tout le rectangle, car Re(s)>-1. Le théorème des résidus
pondéré donne EXACTEMENT

    Z_T=sum_(rho dans R_T) mult(rho)G(rho)
       =(2 pi i)^(-1) int_boundary(R_T) G(s)A'(s)/A(s)ds
       =J_T+H_horiz.                                         (C7)

Tous les zéros de la vraie zeta à |Im rho|<T et 0<=Re rho<=1 sont inclus,
avec multiplicité analytique. Le pôle en 1 a été réellement retiré dans A et
n'ajoute pas un faux zéro ; A(0)=1/2 n'ajoute pas de zéro ; les zéros triviaux
-2,-4,... sont hors du rectangle. Aucune RH, simplicité ou liste externe.
La non-annulation au bord T est vérifiée, pas postulée. Si le certificat échoue,
le statut est CONTOUR_BOUNDARY_UNRESOLVED ; aucune liste partielle n'est promue.

Pour T=100, la proposition de certificat est delta=2^(-24).
La majoration Euler–Maclaurin de la section numérique fournit |A'|<=2^27
sur les deux segments horizontaux. La rotation Laplace donne uniformément
|Gamma(s+1)|<=16exp(-aT), -1/2<=Re(s)<=3/2. D'où

    |H_horiz|<=E_horiz(Y,T,delta)
      =16Y^(3/2)(2^27/delta)exp(-aT),                         (C8)

la longueur totale étant 4 et 4/(2pi)<1. Cette enveloppe est fermée et continue
dans ses paramètres positifs. À Y=10000,T=100,delta=2^(-24),
E_horiz<(3/4)^75<2^(-28). Le segment n'est PAS effacé : il est conservé avec
son intervalle signé centré en zéro et son rayon C8.

La formule finie complète est alors

    H_Y=1+Y-Z_T-(log(4pi)+gamma_E)f(1)-Arch_Y
                               +H_horiz-(J_infty-J_T).       (C9)

C9 contourne la dette d'un compte global des zéros pour CE test pondéré. Elle
ne suppose pas la convergence d'une somme spectrale non pondérée. Le certificat
du rectangle prouve la complétude intérieure par résidus, sans isoler chaque
zéro. Les queues C6/C8 ferment la contribution extérieure pondérée.

## 5. Sources et portée

La formule explicite complète de [Bombieri, p.8](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf)
fixe les modes conservés dans FINAL1. C3–C9 sont notre dérivation par deux
droites et contour, avec budget nouveau ; leur preuve n'est pas admise par
cette référence. Les normalisations analytiques employées sont celles de
[DLMF 25.2](https://dlmf.nist.gov/25.2) et de la
[réflexion 25.4.2](https://dlmf.nist.gov/25.4.E2), lectures ciblées.

La vraie formule analytique C3 et son certificat fini représentent H_Y global.
H_Y est une trace à échelle Y, PAS R_Lambda(N), ni D_N. Une famille de traces
réelles peut déterminer un signal analytique par unicité sans fournir un
inverse numériquement stable ni un gain de signe. L'extraction à N garderait
l'amplification du contour, les alias et les puissances propres décrits dans
FINAL2. Aucune méthode ici ne paie encore le ledger fixé D_N.
