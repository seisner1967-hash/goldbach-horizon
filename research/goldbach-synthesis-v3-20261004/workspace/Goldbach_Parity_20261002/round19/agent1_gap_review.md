# Revue mathématique indépendante19 — coefficient réel et compensation de Gamma

Résultat : le principal négatif annoncé par FINAL1 est correct sur papier, avec les unités effectives et les fronts indiqués. Il ne constitue pas encore une estimation du résidu physique corrigé. Cette revue ne modifie aucun acquis, aucun FINAL antérieur et aucune source Lean ; elle n'exécute ni compilateur ni producteur. Statut auxiliaire, score0, noWin.

Lectures : FINAL1 `agent1_weighted_aggregate.md`, FINAL6rank `agent6_rank.md`, PROBE19 `PROBE_BLOCK.md`, les six sources `RankCalibration*.lean` de ROLE3. Les sources sont des objets à examiner ; aucun statut de compilation n'est déduit de cette lecture. Les valeurs finies ci-dessous sont celles publiées dans FINAL6, sans recomptage ni recalcul des prix.

## 1. Coefficient Euler effectif, y compris les recouvrements avec N

Poser d=cr avec deux premiers distincts, (d,N)=1 ; h=39 ; H0=Nh ; delta_N=phi(N)/N et delta0=phi(Nh)/(Nh). Le coefficient pertinent est

    a0(d)=sum_{k|rad(h), (k,N)=1} mu(k)/phi(dk).

Les k non unitaires à N ne portent aucun principal X/phi(dk). Ils sont absents de `effectiveDivisors`. Leur vraie somme theta vaut zéro : si k|b et un premier p|gcd(k,N), alors p|N-db ; un candidat unitaire à N ne peut être premier de poids theta non nul. Le front db<=N prévient la soustraction naturelle tronquée. FINAL1 a déjà retiré ces facteurs en définissant e0=rad(h)/gcd(rad(h),N). Aucune garde supplémentaire gcd(N,39)=1 n'est nécessaire à K14.

La factorisation écrite complète est

    a0(d)=1/phi(d)
          * product_{p|h, p∤N, p|d}(1-1/p)
          * product_{p|h, p∤N, p∤d}(1-1/(p-1)),

donc

    a0(d)/delta0
      =1/(phi(d)*delta_N)
       * product_{p|h, p∤N, p∤d} p(p-2)/(p-1)^2.       (R1)

Explication des trois cas : si p=3 ou13 divise d mais pas N, phi(dp)=p phi(d), et le facteur (1-1/p) est exactement compensé par la densité entière. Si p divise N, il n'apparaît pas dans l'IE première et sa densité appartient déjà à delta_N. Si p ne divise ni d ni N, il reste le facteur p(p-2)/(p-1)^2. Les facteurs ne sont jamais traités comme disjoints par défaut.

Pour ds, produit des facteurs de d<=R, ajouter un p|ds qui n'est pas déjà dans h multiplie as(d) et delta_s par le même (1-1/p). Ajouter un p déjà dans h ne change ni l'ensemble effectif ni la densité. Ainsi

    as(d)/delta_s=a0(d)/delta0.                         (R2)

C'est une dérivation arithmétique indépendante de toute incidence première masquée et de toute hypothèse de petites erreurs AP. Elle n'annule pas le prix unitaire mesuré.

## 2. Positivité de la masse réelle et signe du principal

Tous les facteurs de R1 sont strictement positifs : les seuls premiers de h sont3 et13. Avec L=#I>0 et le vrai front X=d(L-1)+1>0,

    Md=A_d X a0(d)/(L delta0)>=0,
    Md>0 si et seulement si A_d>0.                     (R3)

Une fibre A=0 a Md=0 ; elle ne reçoit aucun gain strict. Si L>=2, X>=dL/2. Comme delta_N<=1 et les deux facteurs défavorables possibles valent3/4 et143/144,

    a0/delta0>=143/(192 phi(d)),
    Md>=143 A_d d/(384 phi(d))>=143 A_d/384.             (R4)

La garde L>=2 est indispensable à cette borne uniforme : la positivité R3 seule reste vraie pour L=1, mais ne justifie pas R4.

Pour t=P_d=P/gcd(P,d)>1, avec P=1771 et (P,Nh)=1,

    g(t)=(1-1/phi(t))/(1-1/t)=1-chi(t),
    chi(t)=(t-phi(t))/(phi(t)(t-1))>0.

Les masses principales des références initiale et hors face sont respectivement Md et Md*g(t). Leur différence vaut donc exactement -Md*chi(t). Le minimum sur les sept t possibles est451/2336400=41/212400. R4 donne le coefficient C*=64493/897177600=5863/81561600. Les fractions réduites de FINAL6 ne changent aucun coefficient.

Cette conclusion porte sur le principal identifié. Le prix réel peut recevoir les erreurs AP, les erreurs de densité, les fronts et les grandes unités ; il faut les payer avant d'affirmer son signe source.

## 3. Le point précis où le crédit est compensé

Écrire T_beta=sum_d kappa_c sum_{b in I_d} beta_d(b) theta_N(N-db), et M0/Mrank les masses premières réelles des références. Alors

    Gamma0=T_beta-M0,
    Gamma_rank=T_beta-Mrank,
    Pi=Mrank-M0,
    Gamma0=Gamma_rank+Pi.

Au niveau des principaux, M0=sum kappa Md et Mrank=sum kappa Md*(1-chi). La nouvelle référence a une moyenne première plus basse. Par conséquent, le résidu corrigé augmente précisément du montant dont Pi est négatif. Ce n'est pas un défaut de signe de K16 : c'est la conservation de l'incidence physique T_beta.

Si K18 était intégralement établi au source, il fournirait

    Gamma0<=Gamma_rank-sum kappa Md chi+B_price.

Il manque donc une majoration indépendante de Gamma_rank permettant de dépasser cette compensation, avec un reste réellement inférieur au budget disponible. En termes d'incidences, il faut contrôler T_beta relativement à la masse initiale sum kappa Md, et pas simplement remplacer M0 par Mrank. Le prix favorable n'est pas une minoration de capacité parent, ni une disponibilité gratuite de candidats premiers.

La seule positivité d'une énergie ne suffit pas : le moment centré conserve DD, DM, MD, MM et les interactions avec le prix. Le passage à theta ou raw conserve leurs incidences effectives. Aucun signe de leur covariance ne découle de R1–R4.

## 4. Une voie non circulaire à examiner, sans la présenter comme acquise

L'objet nouveau à estimer est très concret. Pour c,r,s physiques fixés, t=crs, le dernier facteur q est premier et le candidat est N-tq. Le numérateur contient donc simultanément les deux conditions premières sur q et N-tq ; l'AP non masquée utilisée pour les références ne contrôle pas cette incidence.

Une branche possible peut attaquer une majoration unilatérale de ce numérateur par un majorant positif sur la seconde forme, tout en gardant q réellement premier. Il faut d'abord décider si son principal est assez petit ; une identité de poids seule ne serait aucun progrès de parité.

Sur papier, pour z inférieur à tous les candidats de la tranche, lambda1=1 et des lambda_k réels supportés sur k<=z,

    theta_N(N-tq)<=u*(sum_{k|N-tq, k<=z} lambda_k)^2.

Pour un candidat premier>z, la somme vaut1 ; pour les autres candidats theta est0 et le carré est positif. Développer donne des vraies sommes sur q premier avec lcm(k,l)|N-tq. Les classes impossibles quand lcm(k,l) partage tN doivent rester nulles, et les exceptions petites doivent être explicitement gardées. Pour les modules compatibles, il s'agit de progressions ordinaires en q, avec tous les endpoints de la vraie tranche de q et le poids inverse-logarithme si l'on convertit un compte premier en theta.

Le test analytique décisif serait de comparer, après sommation sur tous c,r,s et paiement de chaque reste, le principal de ce majorant avec sum kappa Md. Il faut prouver le niveau des modules, la multiplicité complète, l'effet des coefficients lambda et les restes cumulés ; aucun résultat BV sur beta ou sur deux incidences premières ne doit être supposé. Si le principal dépasse cette masse, le signe du prix de rang ne répare pas l'écart : la branche doit être rejetée ou utiliser un véritable switching avec son complément payé.

Cette proposition isole une estimation extérieure identifiable sans poser la borne désirée de Gamma comme hypothèse. Elle ne prétend ni que les constantes fonctionnent, ni qu'un théorème existant fournit les restes, ni qu'un upper-bound sieve crée une capacité lower-bound. Aucun nouveau node ou choix de branche n'est rédigé ici ; la décision doit suivre les contraintes fraîches et le verdict du Juge.

## 5. Obligations formelles, source et ledger conservées

Les sources ROLE3 lues construisent l'IE effective, les remainders AP littéraux et l'estimateur exact. `rank_price_principal_nonpositive/negative` reçoit encore la non-négativité/positivité d'un réel M générique. `rankMainMass` utilise un X réel arbitraire ; la source lue ne dérive pas R1–R4 pour le coefficient effectif à h39 et X=d(L-1)+1. Une compilation de ces identités ne certifie donc pas encore K14/K17 ni le principal source complet. La borne32 d'une seule expansion n'est pas le registre combiné T0+Ts+TFs à40/64.

K18 demande encore les gardes L delta_s>=4eta_s et L delta0>=4eta0, leurs preuves source, les fronts exacts, le passage des remainders définis aux AP ordinaires cumulatives, les trois expansions combinées, les exceptions N, les grandes unités et les constantes/onset BV. Son coût est littéral :256u sum E_theta +48N^(1/2)u²+8N^(31/32)u³+160N^(7/16)u². Le niveau15/32 ne fixe à lui seul ni constante ni onset au seul u>=10^24.

La face explicite P=1771 exige (P,N)=1 ; les N partageant7,11 ou23 restent hors de ce raccord quantitatif. Une face dépendant de N nécessiterait ses propres gardes, coefficients et plafonds ; elle n'est pas fabriquée ici. K14, lui, permet les recouvrements de39 avec N.

FINAL6 publie Gamma0/Gamma_rank theta/raw négatifs et Pi négatif sur son banc complet N=10^8. Il conserve les485 fibres A=0, les puissances propres et les prix non nuls. Ces signes finis ne donnent pas une estimation uniforme au source. Le prix PP doit rester séparé : sa négativité agrégée finie ne permet ni de l'effacer au source ni d'ajouter un second paiement au Bpp acquis.

Enfin cet agrégat canonique n'est pas la totalité du ledger. Les parents et W, les familles extérieures, les cofacteurs longs/faces/nonbulk, les ressources nonSS/T_A, les capacités uniques et les gaps d'onset restent à raccorder. Le ledger D_N=Bprime^a+Bpp^a+Pband>=2+Zface>=2+Ialpha+2max(e,0), Iglobal acquis, whole U_a, Q/k1, les vrais S(bN), le principal -S(N)N et les singleton/fronts sont inchangés. Chaque coût ne doit être payé qu'une fois.

Verdict de cette sous-revue : coefficient principal validé sur papier avec ses gardes effectives ; compensation de normalisation identifiée exactement ; aucune borne nouvelle de Gamma_rank, aucune clôture du ledger et aucune victoire. Aucune exécution mathématique ou Lean n'a eu lieu dans ce rôle. Les deux chemins initialement devinés pour PROBE et Euler n'existaient pas ; rg a retrouvé les noms exacts avant lecture. Ces incidents de lecture n'affectent aucun objet mathématique.
