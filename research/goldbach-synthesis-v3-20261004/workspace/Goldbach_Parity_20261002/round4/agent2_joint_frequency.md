# Boucle 4 — Agent 2 : sommer les fréquences avant leur valeur absolue

Source interne : boucle 3/P1–P10 et genuine_smooth_hh_factor_fixed_modulus_pressure_test.txt. Cette piste conserve h avec sa longueur dépendant de C=s*t et les phases de Gauss. Elle met en évidence un retour exact à l'échelle physique N ; elle ne produit pas encore le gain logarithmique du budget terminal.

## 1. L'identité jointe et la dépendance de C

Pour une cellule séparée, le spectre de la boucle 3 devient, lorsqu'un poids de h est effectivement séparé,

T_unit = pref/phi(N) sum_{chi mod N} chi(-1) tau(bar chi)^2
 A_chi U_bar(chi) V_bar(chi) B_chi F_chi H_chi.                   (J1)

Les variables sont a,s,t,b,l,h, avec les vrais poids H_y(a),mu(s),mu(t) et les facteurs lisses du transport. Le spectre garde sa phase tau^2 ; aucune indépendance statistique des six moments n'est supposée. Les nonunités et les masques couplés restent les restes P6–P7 de la boucle 3.

Dans le modèle d'exposants, C=s*t, Z(C)=N^(3/4)/C et la longueur de h est N/Z(C)=N^(1/4)C. Le poids réellement présent est, par exemple,

(1/(N*C)) Ftilde(h/(N^(1/4)C)).                                 (J2)

On ne peut donc pas remplacer H_chi(C) par un moment fixe sans prix. Deux procédures exactes existent : garder F_C et H_chi(C) indexés par le produit C ; ou séparer ce poids par Mellin. Pour h>0 et un poids lisse W, l'inversion de Mellin écrit

W(h/(N^(1/4)s*t))=(1/(2*pi*i))int M_W(z)
 (h/N^(1/4))^(-z) s^z t^z dz.                                 (J3)

Avec Re z>1, les sommes de h sont absolument convergentes après la décroissance du poids et les facteurs sont bien définis. Les h<0 utilisent W(-x), h=0 reste à part. Les coûts sont l'intégrale absolue de M_W, les moments des poids s^(Re z-1),t^(Re z-1), et la série de h. Choisir Re z=1+1/u peut limiter les facteurs de taille sur un bloc polynomial mais introduit une série harmonique de taille O(u). Les autres masques ou un cap brusque de C exigent leurs propres séparations. J3 fournit une identité, pas une économie gratuite.

## 2. Énergie multiplicative exacte, modulus composite

Pour trois supports finis avec poids x1,x2,x3, posons

g(n)=sum_{n1*n2*n3=n} x1(n1)x2(n2)x3(n3),
E_q(g)=sum_{r in (Z/qZ)^×}|sum_{n≡r modq}g(n)|^2.

L'orthogonalité multiplicative donne exactement

E_q(g)=(1/phi(q))sum_{chi modq}|X1_chi X2_chi X3_chi|^2.          (J4)

La diagonale entière est sum_n |g(n)|^2. Elle comprend TOUTES les factorisations ayant le même produit n, pas seulement n1=n1',n2=n2',n3=n3'. Les autres termes sont n-n'=j*q, j non nul. Tous leurs poids signés demeurent dans J4. Cela ne soustrait pas automatiquement les diagonales Da ou Dk de l'énergie antérieure à quatre signes : il s'agit d'un autre regroupement et leurs interfaces ne sont pas identifiées.

Si le produit est au plus P, Cauchy dans chaque classe donne

E_q(g) <= (1+P/q) sum_{n<=P}|g(n)|^2.                            (J5)

Pour des poids bornés par des fonctions diviseurs fixes, le dernier moment est <= P (1+log P)^K pour un K fixe, obtenu par les moments diviseurs élémentaires. Cela est valable pour tout modulus composite q. Ni un grand crible sur modules premiers ni une uniformité des collisions ne sont nécessaires.

Un autre fait élémentaire valable pour q composite est |tau(chi)|^2<=q : Parseval additif donne sum_{j modq}|sum_{x unit}chi(x)e_q(jx)|^2=q*phi(q), tandis que les phi(q) indices j unités ont tous la même valeur absolue |tau(chi)|. Il suffit de garder ces termes positifs.

## 3. Le surplus explicite après une Cauchy jointe duale

Groupons (a,b,h) et (s,t,l) dans J1. La borne |tau|^2<=N et J4 donnent

|T_unit| <= pref*N*sqrt(E_N(g_ABH) E_N(g_STL)).                  (J6)

Aux axes A=N^(3/4), B=N^(1/4), ST=N^nu, L=N^(3/4), H=N^(1/4+nu), on a P=ABH=N^(5/4+nu), Q=STL=N^(3/4+nu) et pref=N^(-1-nu). Avec J5,

|T_unit| <= N^{max(1+nu,9/8+nu/2)+o(1)}.                        (J7)

Calcul : E_P a l'exposant 3/2+2nu ; E_Q a l'exposant max(3/4+nu,1/2+2nu). La racine puis pref*N=N^(-nu) donnent J7. Cette borne jointe économise une puissance par rapport à la sommation absolue de h de la note précédente, mais son exposant dépasse toujours 1. Ce n'est pas une borne inférieure sur l'objet : seulement le coût d'une majoration valide.

Retirer le caractère principal conserve exactement

E_q(g)-|sum_n g(n)|^2/phi(q).                                   (J8)

Cette soustraction peut être utile lorsque le véritable moment principal est connu ; elle ne transforme pas J5 en une borne purement diagonale. Affirmer ensuite E_nonprincipal<=P polylog pour la vraie direction demanderait un contrôle des collisions signées n-n'=j*q, pas un principe d'indépendance des moments.

## 4. La phase de Gauss peut être annulée exactement avec les deux Fourier poids

Voici une identité plus précise, qui explique ce qui est disponible sans nouveau théorème. Utilisons d'abord le modèle cyclique fini, avec q quelconque composite et des fonctions F,G sur Z/qZ :

Fhat(h)=sum_z F(z)e_q(-h*z),
g_chi(h)=sum_{x unit}bar(chi)(x)e_q(h*x),
H_chi=sum_{h unit}Fhat(h)chi(h),
F_bar(chi)=sum_{z unit}F(z)bar(chi)(z),
E_F,chi=sum_{h nonunit}Fhat(h)g_chi(h).

Parce que g_chi(h)=chi(h)tau(bar chi) pour h unité, et parce que la somme additive complète détecte z=x, on a, SANS hypothèse de primitivité,

tau(bar chi) H_chi = q F_bar(chi) - E_F,chi.                    (J9)

La même identité pour G donne

(tau(bar chi)^2/q^2) H_chi L_chi
 = (F_bar(chi)-E_F,chi/q)(G_bar(chi)-E_G,chi/q).                  (J10)

Les caractères primitifs modulo q ont g_chi(h)=0 aux fréquences nonunitaires, donc E_F=E_G=0. Pour eux, les deux facteurs tau de J1 sont annulés exactement par les deux poids Fourier sommés. Dans la version Poisson réelle, le facteur q/Z et q/K remplace q, et le préfacteur ZK/q^2 s'annule de la même manière. Les longueurs redeviennent celles des facteurs physiques z et k.

Pour les caractères induits, J9–J10 gardent explicitement les contributions nonunitaires. Si tau=0, on ne divise pas par tau : J9 reste valide et q F_bar=E_F. Oublier ces corrections ferait disparaître des lignes arithmétiques réelles.

L'identité qui conserve toutes les fréquences est encore plus directe :

(1/q^2)sum_{h,l modq} Fhat(h)Ghat(l) S(eta*h*b,l;q)
 =sum_{z,k units}F(z)G(k)1_{z*k=eta*b modq}.                    (J11)

Elle vaut pour eta,b unités et tout q. Elle garde h=0,l=0 et tous les nonunits. Pour chaque C=s*t, on applique J11 avec F_C ; rien n'exige que F_C soit indépendant de C. Un masque couplé z,k se traite par sa transformée Fourier à deux variables, avec son coût et son support réels.

Ainsi la sommation jointe peut restituer les variables physiques sans le surplus en puissance de J7. C'est une inversion de la complétion, pas un théorème d'annulation neuf.

## 5. Échelle physique retrouvée, logarithmes toujours impayés

Après J11, les produits sont n=a*b et m=s*t*z*k, avec 0<n,m<N sur le support littéral. Une collision modulo N entre deux de ces produits est une égalité entière : il n'y a plus les translations j*N non nulles de J5. Les multiplicitées de factorisation, elles, restent présentes.

Pour une cellule séparée, les deux histogrammes de produits alpha_n,beta_m donnent par Cauchy

|sum_{n+m=N}alpha_n beta_m|
 <= (sum_n|alpha_n|^2)^(1/2)(sum_m|beta_m|^2)^(1/2).             (J12)

En conservant les vrais logarithmes (<=u) et en prenant les coefficients absolus pour un masque |chi|<=1, les multiplicités sont au plus d4(n),d4(m). Le moment élémentaire sum_{n<N}d4(n)^2<=N(1+log N)^15 donne, par exemple, le majorant brut N*u^2*(1+log N)^15. L'injection des marges de matrices 4x4 dans leurs répartitions de facteurs prouve d4(n)^2<=d16(n), et le moment de d16 donne cette borne.

Ce majorant brutal est inférieur en échelle de puissance à J7, mais il est bien moins bon en logarithmes que les enveloppes déjà établies dans le corpus, notamment les déductions utilisant Rosser. Le retour à l'échelle N ne doit donc pas être annoncé comme un gain nouveau sur ces acquis. Rien dans J11–J12 ne donne le contrôle signé N/(256u ell), et la positivité des énergies n'est pas un signe de Sfull.

## 6. Deux sources primaires auditées, sans import indu

Korolev–Shparlinski, Sums of Kloosterman sums Twisted by Arithmetic Functions, théorème 2.1 : https://arxiv.org/html/1804.01337v1 . Ils contrôlent la somme de mu(n) fois un Kloosterman normalisé pour un modulus premier p et une longueur supérieure à p^(1/2+epsilon), avec économie loglog(p)/log(p). H_y n'est pas ce coefficient ; les moduli composites ne sont pas couverts par cet énoncé. Fixer les autres facteurs pourrait donner un secteur à une vraie variable mu suffisamment longue, mais exige les poids et les sélecteurs correspondants.

Korolev, On Kloosterman sums with multiplicative coefficients, théorème 1 : https://arxiv.org/html/1610.09171v1 . Le modulus peut être composite ; la fonction f doit être multiplicative et bornée par 1. La phase est a/n+b*n avec a unité et la longueur dépasse q^(1/2+epsilon). La borne donnée est 562*x*loglog(q)/(epsilon*log(q)), à partir d'un onset dépendant de epsilon. Un facteur mu(s) long peut correspondre à cette phase après ouverture de Kloosterman ; l'intervalle, les masks et les sommes extérieures doivent encore être payés.

H_y ne satisfait pas ces hypothèses : pour y=2, H_y(3)=H_y(5)=0 mais H_y(15)=2, et H_y(1)=0. Il n'est pas une fonction multiplicative bornée par 1. Dans le régime équilibré s,t de tailles N^(nu/2), nu<3/4, les deux longueurs sont inférieures à N^(3/8), hors de la portée >N^(1/2+epsilon). Aucun des deux théorèmes n'est importé pour cette cellule. Même une économie logarithmique sur un secteur long ne paie pas automatiquement le surplus en puissance J7 ni tous les logarithmes des amplitudes connues.

## 7. Tests exacts transmis à l'Agent 6

J9–J10 sur q=11,15,100 et fonctions ponctuelles F=G=delta_1. Pour q=11 et le caractère quadratique primitif : E_F=0. Pour q=15, le caractère quadratique modulo 3 induit : tau^2=-3, tau*H=3, q F_bar=15, E_F=12. Le membre dual unit-only de J10 vaut 1/25, alors que F_bar*G_bar vaut 1 ; cela falsifie la suppression du reste composite.

À N=100000000, le caractère quadratique modulo 5 induit a tau=0. La translation x -> x+N/5 partage les unités en orbites de longueur 5, conserve leur caractère et multiplie la phase par une racine cinquième ; les cinq phases somment zéro. Pour F=delta_1, J9 impose donc E_F=N. Ce test peut être certifié par orbites et identité cyclotomique, sans énumérer 40 millions d'unités.

Test du C couplé : q=100, R=70,K=3, F_C(z)=1_{1<=z<=floor(R/C),(z,q)=1}, G(k)=1_{1<=k<=K,(k,q)=1}. Choisir C=21=3*7 et C=33=3*11, eta=-a/C, a,b unités. Vérifier J11, puis réfuter une version gelant F_C à F_21 lorsque C=33. Ce banc vérifie la congruence cyclique ; il ne prétend pas couvrir les faces de l'équation entière HH.

## 8. Verdict

La sommation conjointe de h,l avec leur phase conserve une identité exacte pertinente. Elle supprime les coûts artificiels de complétion lorsqu'on revient aux facteurs physiques, avec des corrections nonunitaires indispensables au modulus composite. L'inégalité jointe duale J7 laisse un surplus en puissance ; l'inversion exacte J11 retrouve une amplitude N polylog déjà compatible avec les acquis, sans gain signé nouveau.

Aucun contrôle indépendant des grandes projections signées, aucun paiement du résidu couvert et aucune borne nouvelle de D_N ne sont obtenus. Statut : identité/test de retour physique et diagnostic quantitatif ; résultat partiel, pas victoire.
