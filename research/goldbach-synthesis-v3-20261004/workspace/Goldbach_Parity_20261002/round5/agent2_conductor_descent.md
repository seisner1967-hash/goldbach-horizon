# Boucle 5 — Agent 2 : descente exacte des fréquences induites

Nœud Arbor 8. Sources internes lues : contraintes de l'Idea Tree, rapport round4/agent4_composite_completion.md et identités J9–J11. Aucun acquis ni reçu antérieur n'est modifié. Le domaine conserve le vrai profil F_C, tous les sélecteurs d'unité et les fréquences nonunitaires.

## 1. Identité de descente avec conductor et modulus distincts

Soit N>=2. Soit chi_N un caractère modulo N induit par un caractère primitif chi_r de conductor r|N. Pour chaque h modulo N, posons d=gcd(h,N), q=N/d, et écrivons h=d*u, u unité modulo q. Pour h=0, q=1 ; lorsque r>1, ce stratum est nul. On définit

g_N,chi(h)=sum_{x unit modN}bar(chi_N)(x)e_N(h*x).

La réduction du groupe des unités modulo N vers celui modulo q est surjective, avec fibres de cardinal phi(N)/phi(q). La somme du caractère sur une fibre est nulle si r ne divise pas q ; s'il le divise, le caractère y est constant. Il vient exactement

g_N,chi(h)=0                                  si r ne divise pas q,
g_N,chi(h)=[phi(N)/phi(q)] chi_r(u) tau_q(bar(chi_q)) sinon,     (C1)

avec chi_q le caractère modulo q induit par chi_r. En posant c=q/r,

tau_q(bar(chi_q))=mu(c)bar(chi_r)(c)tau_r(bar(chi_r)).            (C2)

Donc le support non nul est exactement

q=r*c, q|N, c carré-libre, gcd(c,r)=1.                          (C3)

Le conductor multiplicatif est r ; le modulus ADDITIF de la phase réduite est q. C1 ne les identifie pas.

Source primaire vérifiée : Montgomery–Vaughan, Multiplicative Number Theory I, chapitre 9, théorèmes 9.10 et 9.12, pp.289–291, sur le site de l'auteur :
https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/13.0_pp_282_325_Primitive_characters_and_Gauss_sums.pdf . Ces deux théorèmes donnent respectivement l'induction de Gauss et la phase générale. Le même chapitre établit la somme des fibres et le module sqrt(r) de la somme primitive. Les barres de conjugaison mal rendues dans l'extraction PDF ont été raccordées à notre convention par le changement de variable sur les unités.

## 2. Preuve des normalisations et de la partition

La phase e_N(h*x)=e_q(u*x) ne dépend que de x modulo q. Une fibre de réduction a phi(N)/phi(q) unités. Si r ne divise pas q, chi_N n'est pas constant sur le noyau ; multiplier la fibre par une unité du noyau où le caractère est non trivial fait annuler sa somme. Si r|q, la somme de fibre donne bar(chi_r)(x)phi(N)/phi(q). Le changement x->u*x dans le groupe modulo q prouve alors C1.

Pour C2, on peut aussi développer l'indicateur d'unité des premiers supplémentaires par inclusion-exclusion. Les contributions de divisors e coprimes à r sont des sommes d'un caractère de période r sur un modulus q/e. La somme de phases est nulle sauf q/e=r. Il reste e=c, avec coefficient mu(c)bar(chi_r)(c). Cela conserve la condition de carré-liberté et les primes communs, qui rendent le coefficient nul.

Les classes q=N/gcd(h,N) partitionnent toutes les fréquences. Aucune fréquence n'est supprimée parce qu'elle est non unité modulo N ; elle appartient à son groupe modulo q avec sa multiplicité phi(N)/phi(q).

## 3. Le cas obligatoire N=10^8

N=2^8*5^8, r=5, chi_r quadratique. C3 autorise seulement c=1,2, donc q=5,10. Les fréquences actives sont exactement

h=20000000*u pour u=1,2,3,4,
h=10000000*u pour u=1,3,7,9.

Toutes sont nonunitaires modulo N. Le facteur de fibre est 40000000/4=10000000 dans chaque stratum. Le Gauss au modulus N est nul ; ceci ne retire aucune masse physique. Cette descente à deux petits moduli est vraie pour ce N particulier, grâce à ses puissances premières et au conductor 5.

Elle n'est pas une propriété universelle du conductor 5. Prenons le N pair carré-libre 70630=2*5*7*1009. Les q actifs sont 5,10,35,70,5045,10090,35315,70630. Le q=35315=N/2 appartient au reste nonunitaire, par exemple à h=2, et sa somme de Gauss n'est pas nulle. Le conductor est toujours 5. Un modulus additif presque aussi grand que N est donc compatible avec un petit conductor multiplicatif.

## 4. Masse exacte d'un stratum sur un profil physique d'unités

Supposons maintenant F(z)=0 si z n'est pas unité modulo N. Ce support est celui du facteur physique dans le problème original ; il n'est pas une affirmation de lissité ni de séparabilité de ses autres masques. Posons

Fhat(h)=sum_{z modN}F(z)e_N(-h*z),
M_F=sum_{z unit modN}F(z)bar(chi_N)(z),
E_q(F)=sum_{N/gcd(h,N)=q}Fhat(h)g_N,chi(h).

Pour un q actif de C3, substituer C1 et développer Fhat donnent

E_q(F)=[r*phi(N)/phi(q)] M_F.                                 (C4)

En effet, z unité modulo N est aussi unité modulo q. La somme en u vaut bar(chi_r)(-z)tau_q(chi_q). Le produit tau_q(bar chi_q)tau_q(chi_q) vaut chi_r(-1)*r lorsque C3 est satisfait. Les signes chi_r(-1) se neutralisent. Les coefficients de C4 sont positifs réels ; M_F, lui, est un moment COMPLEXE signé et n'est pas positif.

En notant A(N,r) l'ensemble actif,

sum_{q in A(N,r)} r*phi(N)/phi(q)=N.                           (C5)

Preuve Euler finie : phi(rc)=phi(r)phi(c), puis

sum_{c squarefree|N/r,(c,r)=1}1/phi(c)
 =prod_{p|N,p ne divisant pas r}(1+1/(p-1)).

Les facteurs locaux annulent exactement ceux de phi(N) et phi(r). C5 montre le coût total, sans perte de triangle :

sum_q |E_q(F)|=N |M_F|.                                      (C6)

La descente ne donne aucune annulation entre ces strata : ils portent le même moment avec des coefficients positifs. Leur faible cardinal ne réduit pas le facteur N.

Pour N=10^8 et r=5, chacun des deux coefficients vaut 50000000. Avec F=delta_1, M_F=1 : E_5=50000000 et E_10=50000000, donc E_nonunit=N. Les petits moduli portent la totalité de la masse, pas une petite erreur.

## 5. Énoncé court destiné à la formalisation après filtre

On peut prouver l'obligation critique sans formaliser préalablement toute la théorie des conductors. Pour q quelconque non nul, chi:DirichletCharacter C q et F:ZMod q->C, supposons seulement

forall z, not IsUnit(z) -> F(z)=0.

Avec les définitions déjà prouvées dans round4/lean/CompositeCompletion.lean,

Hmoment(F,chi)=chi^(-1)(-1) tau(chi) Fmoment(F,chi).              (C7)

Preuve : échanger les deux sommes ; pour z unité, la somme intérieure sum_{h unit}chi(h)e_q(-h*z) est g_{chi^(-1)}(-z). Le changement multiplicatif de variable déjà certifié dans round4 donne chi^(-1)(-z)tau(chi). Les z nonunitaires ont coefficient F(z)=0.

Posons le coefficient arithmétique réellement défini

kappa_chi=chi^(-1)(-1)tau(chi^(-1))tau(chi).

Alors, sans supposer son signe,

tau(chi^(-1))Hmoment(F,chi)=kappa_chi Fmoment(F,chi),
E_nonunit(F,chi)=(q-kappa_chi)Fmoment(F,chi).                   (C8)

La conjugaison de la somme de Gauss, prouvée par x->-x, donne

tau(chi^(-1))=chi(-1) conj(tau(chi)),
chi(-1)^2=1,
kappa_chi=normSq(tau(chi)).                                    (C9)

Kappa est donc réellement non négatif, sans hypothèse de positivité ajoutée. Il multiplie cependant le moment complexe Fmoment, dont aucun signe n'est acquis. Avec deux profils physiques d'unités,

(tau(chi^(-1))^2/q^2) Hmoment(F,chi)Hmoment(G,chi)
 =(kappa_chi/q)^2 Fmoment(F,chi)Fmoment(G,chi).                  (C10)

Les conductors ne sont nécessaires que pour évaluer kappa : pour chi induite de conductor r, kappa est soit 0 soit r, selon C3 au q=N. L'essentiel C7–C10 est une identité de vrais Gauss et Fourier, pas un scalar coefficient libre choisi pour imposer la conclusion.

Aucun tau n'est inversé. Ces énoncés restent valides si tau=0. Le coefficient exact d'E est alors q ; E=qF est conservé.

## 6. Ce que les acquis de petits conductors contrôlent effectivement

L'indicateur d'unité croissant est déjà acquis dans la monographie §12.6. Pour chi primitive retenue r<=u^8, tout K avec log K<=2u et les arguments/onset prescrits, le vrai préfixe mu(n)chi(n)1_{(n,K)=1} est contrôlé. Cela peut borner M_F lorsque F possède LITTÉRALEMENT ce coefficient mu avec un poids de variation payé. K=N ou, sur un produit physique fixé, K=N*s*t*k<=N^2 répond au contrat. Aucun nouveau blocage de masque n'est inventé ici.

C8 transporte alors exactement cette même borne vers E, avec facteur q-kappa. Il ne fournit pas un gain indépendant : après la normalisation de complétion, c'est la borne physique existante. Dans le facteur zeta genuinely unweighted, F n'a pas automatiquement un coefficient mu ; les masks rugueux/carrés-libres de l'autre axe peuvent dépendre de zeta. On ne remplace donc pas son moment par un préfixe mu sans identité supplémentaire.

Le contrôle de la petite projection reste distinct de tous les grands conductors, des directions signées de H_y, des masques couplés et des interfaces Da/Dk. La partition en fréquences n'altère pas les sommes physiques ni leurs diagonales.

## 7. Un levier différent examiné : préfixe carré-libre tordu

Après l'échec du gain gratuit de conductor, un lemme élémentaire indépendant peut contrôler CERTAINS moments physiques sans réintroduire un signe mu non présent. Pour un caractère primitif nonprincipal chi_r et un masque K, définir

P(x)=sum_{n<=x}mu(n)^2 chi_r(n)1_{(n,K)=1}.

L'expansion mu(n)^2=sum_{d^2|n}mu(d), puis l'inclusion-exclusion des primes de K, et la périodicité du caractère donnent exactement la borne

|P(x)|<= r * 2^{omega(K)} * floor(sqrt(x)).                    (C11)

La somme complète d'un caractère nonprincipal sur une période est nulle ; chaque préfixe a donc module au plus r. Les 2^{omega(K)} termes d'inclusion-exclusion et les d<=sqrt(x) donnent C11. La borne est explicite ; pour des poids, leur variation d'Abel est payée. Ce mécanisme concerne une vraie variable carrée-libre et un twist périodique, et n'utilise pas une hypothèse de corrélation additive souhaitée.

Il est pertinent seulement lorsqu'après fixation des autres données le profil F contient précisément mu(zeta)^2 et le masque multiplicatif fixe K. Le facteur I_W(N-s*t*k*zeta), le détecteur carré-libre de N-s*t*k*zeta et les autres sélecteurs originaux ne sont pas ces poids indépendants. Les inclure dans F peut détruire la borne de variation nécessaire. C11 n'est donc pas importé comme une estimation globale de HH. Il fournit un secteur testable, pas une clôture de la partie complète.

## 8. Tests transmis avant Lean et verdict

Agent 6 reçoit C1–C5 et le candidat court C7–C10 avant toute compilation centrale. Banc obligatoire N=10^8/r5, q5 et10, GaussN zéro, masse delta_1 totale E=N. Banc composite q=385/r5 : coefficients exacts des q=5,35,55,385 égaux à 300,50,30,5 ; total385 et reste nonunit380. L'exemple N70630/r5 vérifie un modulus nonunit q=N/2 malgré le petit conductor. Les mêmes profils F_C et leurs masques restent dans chaque formule.

La descente est exacte et les défauts sont arithmétiques ; les petits q ne rendent pas petit E. Les coûts C5–C6 et le contre-exemple delta_1 réfutent cette étape. C11 est un levier indépendant limité à des profils physiques séparés, sans aucun gain signé global établi.

Statut : résultat partiel de descente/projection avec obstruction à la suppression des défauts. Le raccord D_N=-Sfull+2max(e,0) et la cible N/(256u ell) ne sont pas prouvés. Aucune victoire.
