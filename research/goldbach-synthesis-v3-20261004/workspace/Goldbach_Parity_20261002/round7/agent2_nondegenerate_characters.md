# Boucle 7 — caractères non dégénérés et reconstruction de HH

Agent 2, nœud Arbor 10.1, 2 octobre 2026. `round6/agent4_contract_audit.md`, `round6/agent5.md`, le reçu indépendant et l'arbre courant ont été relus. **Toute la boucle 6 reste figée.** Son corrigendum, et non son ancien S3, est utilisé ci-dessous.

**Verdict proposé : rejet du transfert « moyenne de Jacobi petite ⇒ résidu HH petit ».** Il existe une insertion exacte dans le porteur arithmétique HH. Elle conserve un secteur non unitaire et sa projection principale ; éliminer cette dernière algébriquement reconstruit sa masse par l'ensemble des caractères nonprincipaux. Si le conducteur provient du vrai module divisoriel k ou du CRT a*r, le twist à deux unités supprime précisément des secteurs originaux, dont la ligne divisible. La moyenne non dégénérée ne produit donc pas un gain indépendant. Aucune nouvelle identité générique n'est proposée à Lean, aucune cible n'est supposée, aucune victoire n'est annoncée.

## 1. Probe et hypothèse réellement auditée

PROBE BLOCK

Q1 First principles : wrong credit assignment. Le reçu de boucle 6 certifie à la fois le compensateur constant pour q|N et une fibre vraie à un point malgré un intervalle brut long ; un facteur oscillant isolé n'est pas le coefficient HH complet. Le corrigendum S3' montre également qu'un inverse sans compatibilité change le contrat.

Q2 Hidden assumption : introduire un caractère nonprincipal copremier à N suffirait à contrôler la somme qui n'en contient pas. En abandonnant cette hypothèse, on doit reconstruire exactement la projection principale et toutes les exceptions q-unitaires.

Q3 Elephant : le signé complet avec mu(u)mu(v)mu(s)mu(t), tous les fronts, les masques mobiles et les secteurs courts. Une moyenne complète non pondérée ne paie pas ce moment.

Q4 Hamming : oui ; un gain sur sa reconstruction physique aurait un intérêt direct, tandis que la seule formule de Jacobi n'en a pas.

Les quatre mouvements sont : inversion de q|N vers une corrélation non dégénérée à p∤N ; raisonnement arrière depuis une insertion exacte et ses exceptions ; transfert de la résolution spectrale au ratio physique n/m ; rétroanalyse du tuple actif n=273 et de la vraie progression mince de boucle 6.

Candidat examiné, cinq champs :

1. Hypothèse contestée : un twist artificiel hérite automatiquement de l'objet principal.
2. Classe : résolution spectrale finie du ratio physique, avec reconstruction et secteur exceptionnel explicites.
3. Chaîne : une corrélation de Jacobi pourrait être pertinente si sa reconstruction exacte et son cumul extérieur gagnent au coût terminal ; le test décisif est ce cumul, pas le seul module de Jacobi.
4. Orthogonalité : q est copremier à N ; le compensateur n'est donc plus constant sur la fibre, contrairement au nœud 10. Cette différence exige une nouvelle insertion physique, pas un remplacement du module original.
5. Conflits : le nœud 10 interdit le transfert du twist isolé ; le nœud 5.1 conserve les compensateurs/nonunités ; ils sont conservés ici. Le candidat est rejeté si le principal est présumé petit ou si le cumul des caractères est supprimé.

## 2. Somme originale et partition exacte

Soit Omega l'ensemble fini des tuples HH ORIGINAUX de la continuation :

a=u v x, r=s t zeta, n=a b, m=r k=N-n,
u,v,s,t>y, x,zeta,b,k>0.

Il conserve I_W(n), les détecteurs carrés-libres réellement prescrits à cette composante HH, gcd(n,N)=1, k<=Q, r>alpha, le core a,b<=m, les fenêtres et chaque face originale. Aucun détecteur mu(n)^2 n'est ajouté au profil brut distinct de la boucle 6. Le poids du tuple est

c(omega)=mu(u)mu(v)mu(s)mu(t) theta(omega) log(b)log(r),

avec tous les sélecteurs réels dans theta. Si la composante exacte porte une autre normalisation, elle est gardée dans c ; l'identité suivante vaut linéairement pour ce poids réel sans le modifier. On note S_HH=sum_Omega c(omega).

**Portée exacte de ce symbole :** S_HH désigne ici le porteur arithmétique du compte HH, dont les tuples physiques satisfont n+m=N et m=r*k. Il n'est pas automatiquement le résidu centré E_HH=C_HH-M_HH. La ligne de modèle M_HH et les corrections W ne portent pas nécessairement ces mêmes tuples ; elles doivent être gardées et traitées séparément. Si C_HH est le porteur désigné par S_HH, le transfert au centré reste exactement E_HH=R_p-sum_(chi!=chi0)conj(chi(-1))T_chi-M_HH, avec toutes les autres corrections originales. Rien ici n'est une insertion gratuite dans M_HH.

Choisissons un premier impair p tel que p∤N. Les caractères de cette section sont modulo p ; cela ne change ni le module CRT original a*r, ni le profil alpha,Q, ni le module additif N.

Omega_p={omega in Omega : p∤n m},
R_p=sum_(Omega minus Omega_p)c(omega).

Pour TOUS les caractères modulo p, principal compris, posons

T_chi=sum_(omega in Omega_p)c(omega) chi(n)conj(chi(m)). (N1)

Sur Omega_p, le développement du caractère complet est

chi(b)chi(u)chi(v)chi(x)
 conj(chi(k))conj(chi(s))conj(chi(t))conj(chi(zeta)).     (N2)

Ainsi les quatre vrais signes de Möbius, les facteurs x et zeta et tous les caractères des facteurs restent présents. N1 n'est pas un profil inventé pour porter chi. La décomposition physique initiale est exactement

S_HH=R_p+T_chi0.                                      (N3)

Les secteurs p|n et p|m sont disjoints puisque p∤N. Aucune annulation de R_p n'est acquise. Le tuple n=273,m=99999727, a=21,b=13,r=7951*12577,k=1, y=W=2, donne H_y(a)H_y(r)=4 et un poids positif. Pour p=13, chi(n)=0 : N1 perd ce tuple, qui reste dans R_p. Ce témoin est fini, sous l'onset analytique ; il ne prétend pas être un profil asymptotique W presque-puissance.

Lorsque p<=W dans un profil asymptotique, I_W(n) impose p∤n et seul p|m reste dans R_p. Cela ne le rend pas nul. Il peut provenir d'un facteur de C=k s t ou de zeta, et la frontière r>alpha ne l'exclut pas. Si p>W, les deux secteurs doivent être conservés. Aucun acquis n'est utilisé pour les supposer petits.

## 3. Reconstruction exacte de la projection principale

Sur Omega_p, le ratio t=n/m modulo p est une unité et t≠-1, car n+m=N et p∤N. L'orthogonalité des caractères donne

sum_(chi != chi0)conj(chi(-1))chi(t)=-1.

Il s'ensuit l'insertion exacte

T_chi0=-sum_(chi != chi0)conj(chi(-1))T_chi,
S_HH=R_p-sum_(chi != chi0)conj(chi(-1))T_chi.           (N4)

On ne suppose donc pas la projection principale petite. On la reconstruit avec p-2 caractères nonprincipaux, chacun muni d'un coefficient de norme 1. Une autre manière de voir cette obligation consiste à développer 1_(t!=-1) sur le groupe des unités : son coefficient principal est (p-2)/(p-1), et ses coefficients nonprincipaux sont -conj(chi(-1))/(p-1). Déplacer le principal au membre gauche donne exactement N4 ; ce déplacement n'économise pas les p-2 modes.

N4 utilise tous les caractères, même celui qui serait exclu d'un acquis de nonexceptionnalité. Un théorème valable seulement pour les caractères primitifs RETENUS doit payer séparément toute ligne exclue. Aucun petit poids positif g(d)/phi(d) de la monographie n'apparaît dans N4 pour payer cette ligne automatiquement.

## 3 bis. Raccord à la vraie ligne centrée : trace déjà acquis

La monographie §5 (texte extrait lignes 640–680) donne déjà la trace primitive carrée-libre

P_q(m)=prod_(ell prime,ell|q)[(ell-1)1_(ell|m)-1]

sur unit-n, unit-N. Lorsque gcd(q,m)=1, P_q(m)=mu(q), donc mu(q)P_q(m)/phi(q)=1/phi(q). Les deux facteurs ne sont pas deux oscillateurs indépendants ; cette identité antérieure reste acquise et n'est pas annoncée comme nouvelle.

Pour le vrai module k, sur gcd(n*N,k)=1, l'orthogonalité native est

1_(k|m)-1/phi(k)
 =1/phi(k) sum_(chi mod k,chi!=chi0)chi(n)conj(chi(N)).  (N10)

Le facteur conj(chi(N)) est constant. Le remplacer par conj(chi(m)) CHANGE la projection. Pour k=p premier, la ligne centrée vaut P_p(m)/(p-1). Sur p|m elle vaut (p-2)/(p-1), tandis que chi(n)conj(chi(m)) vaut zéro pour chaque caractère. Sur p∤m elle vaut -1/(p-1). La nouvelle composante de Jacobi ne couvre donc pas la ligne divisible, qui est précisément une partie de D.

Dans le porteur physique m=r*k, si p|k, alors p|m pour TOUTE la fibre. Omega_p est vide et R_p=S_HH sur cette fibre ; l'hypothèse p∤C nécessaire à N6 est fausse, puisque C=k*s*t. Aucun gain Jacobi n'y est défini.

Plus généralement, si un premier p provient du vrai CRT a*r, il divise a ou r, donc n=a*b ou m=r*k. Le twist qui demande simultanément n et m unités modulo p est zéro sur ce tuple. Si l'on choisit un q non trivial divisant a*r, les caractères modulo q prolongés par zéro perdent au moins un axe. On ne peut pas substituer ce q au module a*r pour rendre la composante artificiellement non dégénérée.

Un p auxiliaire copremier au module a*r peut avoir N6 non dégénérée. N4 décrit exactement son insertion dans le porteur, mais elle n'est pas une nouvelle projection native de N10. Elle ajoute une résolution locale et ses exceptions ; elle ne remplace ni les anciennes traces primitives ni le centré exact. Cette distinction est le rejet précis du raccord envisagé depuis le vrai module.

## 4. Vraie moyenne de Jacobi et pourquoi elle restitue la masse

Fixons les six facteurs b,u,v,k,s,t, et écrivons A=b u v, C=k s t, A x+C zeta=N. Dans Omega_p, p∤A C et p∤x zeta. Le caractère complet N2 se réécrit exactement

tau_chi(zeta)=chi(N-C zeta)conj(chi(C zeta)).            (N5)

Pour un caractère nonprincipal modulo p, p∤N C,

sum_(zeta mod p)tau_chi(zeta)=-chi(-1).                 (N6)

Les deux résidus zeta=0 et C zeta=N ont valeur zéro. Pour prouver N6, poser y=C zeta/N ; le ratio (1-y)/y parcourt les unités sauf -1 lorsque y parcourt les résidus hors 0,1. La somme de chi sur toutes les unités est nulle ; il reste -chi(-1). Il n'est pas nécessaire de diviser par une somme de Gauss ni de supposer un caractère quadratique. Si le facteur conj(chi(C)) a été omis, la somme vaut au contraire -chi(-C).

La valeur N6 a module 1 et sa moyenne sur les p résidus vaut -chi(-1)/p ; elle n'est PAS de moyenne nulle. La moyenne du caractère principal est (p-2)/p. En reconstruisant par N4 les moyennes des p-2 caractères, on obtient

-sum_(chi != chi0)conj(chi(-1))[-chi(-1)]=p-2.           (N7)

C'est exactement le nombre de résidus du secteur p-unitaire. Le petit module de chaque Jacobi complet restitue donc la contribution principale entière après l'insertion exacte. Le banc constant non pondéré sert uniquement à certifier ce calcul de coût : il ne remplace pas les vrais coefficients de Möbius de HH et ne fournit pas une borne inférieure sur le signé global.

Référence primaire pour la théorie générale des Jacobi : Montgomery–Vaughan, *Multiplicative Number Theory I*, chapitre 9, exercice 9.2.10, p.294. N6–N7 sont dérivées ici directement par la bijection du ratio ; aucune borne générale de Jacobi ne remplace leur moyenne exacte.

## 5. CRT complet : compatibilité avant inverse, unités p et vraie longueur

Dans une expansion à deux carrés, gardons le corrigendum autoritaire de boucle 6. Pour d^2|zeta, e^2|n, f|zeta dans le masque de rad(CN), ell|n dans une expansion de I_W, posons

L=lcm(d^2,f), M=lcm(A,e^2,ell), g=gcd(C L,M).

Si g∤N, la cellule est vide. Sinon

M'=M/g,
v0=(N/g)*(C L/g)^(-1) mod M',
zeta=L(v0+M'j).                                      (N8)

Pour M'=1, v0=0. On ne remplace ni L par f d^2 sans gcd(d,f)=1, ni M par A e^2 ell sans les coprimalités nécessaires. Les secteurs e partageant A et d partageant ell sont conservés par la compatibilité, avant tout inverse. Les suppressions issues des masques exacts se font avant leur développement ou après regroupement signé ; elles ne sont pas des suppressions termwise sous valeur absolue.

Sur la composante p-unitaire véritable, les cellules retenues peuvent être définies avec p∤A,C,L,M : p|A ou p|C rend la composante vide ; un d contenant p rencontre zeta unité ; e ou ell contenant p rencontre n unité ; f|rad(CN) est unité p puisque p∤CN. Ces exclusions utilisent le masque p-unitaire exact, conservé avant l'inclusion-exclusion. Alors le pas P=L M' est unité modulo p. Zeta parcourt les p résidus pendant p indices consécutifs j, et N6 s'applique exactement sur cette progression. Les cellules avec p|P, lorsqu'on considère d'autres secteurs, nécessitent leur propre traitement : la phase y est alors fixe modulo p et peut être constante. Elles ne sont pas créditées comme oscillantes.

Les fronts stricts restent ceux de la fibre originale, notamment r>alpha iff zeta>=floor(alpha/(s t))+1. Le nombre de points de J est au plus 1+length(J)/A avant les carrés, puis au plus 1+length(J)/P dans N8. Aucun +1 n'est abandonné. Dans b,k~N^.25, uv~N^sigma, st~N^nu, la longueur continue de la fibre est N^(.5-sigma-nu), et non la longueur brute N^(.75-nu) de zeta. Les fibres très courtes et zeta=1 restent présentes. Un p petit peut tenir dans certaines longues progressions, mais cela ne prouve rien pour les fibres à un point.

## 6. Somme jointe des caractères : erreur locale exacte, aucun nouveau gain

Centrons N5 par sa vraie moyenne :

rho_chi(zeta)=tau_chi(zeta)+chi(-1)/p.

En gardant la somme des caractères avant les valeurs absolues, N4 donne pointwise, y compris aux deux résidus nonunitaires,

-sum_(chi != chi0)conj(chi(-1))rho_chi(zeta)
 =1_(p∤(N-C zeta)C zeta)-(p-2)/p.                      (N9)

Sur une progression de pas unité p, le membre droit retranche deux classes modulo p à la fonction constante. Son préfixe non pondéré a module au plus 2 : sur une période il vaut zéro, et sur un morceau de longueur h<p il vaut 2h/p moins le nombre (0,1,2) de ces deux classes rencontrées. Pour un poids F de variation V, l'erreur est donc O(sup|F|+Var(F)), après paiement des morceaux.

Sommer séparément les p-2 caractères fournirait une majoration artificielle O(p^2 V). La somme jointe N9 la corrige. Mais elle ne fait que retrouver l'erreur O(1) de deux comptages en progression. Le CRT original comptait déjà des classes avec une erreur de plancher O(1). Ce résultat local exact ne réduit pas le nombre de grandes fibres, leur discrepancy sélectionnée, ni leur charge extérieure.

Dans une cellule, une moyenne de Jacobi pondérée comporte son terme -chi(-1)/p times sum F, et une erreur de variation. Le premier reconstruit (p-2)/p times sum F ; le second reconstruit le comptage des deux exclusions. La direction signée mu(u)mu(v)mu(s)mu(t) et sa somme extérieure sont encore intactes. Déclarer la première petite exigerait soit son raccord complet au MAIN continu déjà acquis, soit une estimation nouvelle ; cela ne découle pas de N6. Le MAIN acquis ne fournit pas le contrôle du vrai selected-root count moins ce MAIN, comme l'énonce `weighted_hh_root_main_raw_prefixes.txt`.

## 7. Acquis petits conducteurs et coût extérieur

La monographie §12.6 contrôle le vrai préfixe mu(t)chi(t)1_(t,K)=1 pour les caractères retenus, log K<=2 log N, les seuils et l'onset prescrits. Il demeure acquis. Dans N1–N2, on a quatre valeurs de Möbius, un x et un zeta reliés par A x+C zeta=N, un masque carré-libre du complément, la rugosité et des faces mobiles. On ne remplace pas cet objet par un préfixe unique auquel le théorème s'appliquerait directement.

En particulier, le produit chi(N-C zeta)conj(chi(zeta)) est une phase rationnelle dans zeta, pas un caractère multiplicatif fixe de cette variable. L'expansion rough I_W(n) ne peut pas être incorporée gratuitement au masque K : son primorial a log K de taille W, au-delà du contrat lorsque W est presque-puissance. Les cellules de N8 sont des progressions contraintes, pas des préfixes complets. Fixer le poids pour qu'il porte artificiellement le caractère changerait l'objet. Les caractères nonretenus ne disparaissent pas de N4.

Aux échelles équilibrées, le nombre brut des sextuples b,u,v,k,s,t est N^(.5+sigma+nu) à facteurs logarithmiques près. Quand la longueur continue L_cont=N^(.5-sigma-nu) est grande, leur produit est N. Les +1 peuvent dominer dans les sous-boîtes minces ; ils nécessitent un comptage des fibres actives supplémentaire. Le gain local attendu ne peut donc être évalué sans cette somme extérieure.

Avec D,E coupes carrées et un niveau rough D_R, la somme absolue des cellules après paiement de masques peut coûter D E D_R 2^omega(CN) par fibre. N9 paie O(V) PAR cellule ; il ne supprime pas ce facteur ni le nombre extérieur. Les queues conservent les termes sqrt(max J), sqrt(N), les multiplicités divisorielles et les +1 du corrigendum de boucle 6. Les poids réels à variation arbitraire ne deviennent pas lisses parce que p est petit. Un encadrement de Rosser conserve ses restes positifs et leur moment ; une borne de Jacobi non pondérée ne les paie pas.

Zeta=1 et tous les secteurs courts restent dans N1 et R_p. Ils n'ont aucun cycle utile. La borne d'amplitude antérieure du secteur zeta polylogarithmique n'est pas une réserve terminale. Un changement de variable conjoint x,zeta conserve la droite A x+C zeta=N et son nombre de points ; il ne produit pas une seconde direction libre.

Le mécanisme conjoint réellement nécessaire serait une estimation de la somme des ERREURS de N8/N9 contre les quatre valeurs réelles de Möbius, avec les mêmes faces, et un budget indépendant pour R_p et les queues. Aucune telle estimation n'a été dérivée ici à partir des seuls acquis. La déclarer comme hypothèse de faibles corrélations serait seulement renommer le moment manquant. Aucun candidat de ce type n'est présenté comme une nouvelle preuve.

## 8. Contrat numérique et verdict de candidature

N1–N9 ont été transmis à la racine et à l'Agent 6 AVANT toute candidature Lean. Banc N=100000000, p=3,7,11,13,17,19, p∤N :

* vérifier N6 pour des caractères quadratiques et d'ordre 4, avec le facteur conj(chi(C)) ;
* vérifier N4 sur les vrais tuples HH et garder R_p, notamment le tuple n273 au p13 ;
* vérifier N7 : les moyennes des p-2 modes reconstruisent p-2, au lieu de produire un gain ;
* vérifier N9 en rationnels exacts, tous les préfixes et les deux résidus nonunitaires ;
* conserver le CRT général N8, les inverses uniquement après g|N, e partageant A, et les cas p|pas ;
* garder les fronts stricts, zeta=1, les quatre signes et les logarithmes symboliques.

Les tests non pondérés sont des diagnostics de la normalisation ; ils ne sont pas une mesure de HH complet. Les tests de tuples sont des filtres de support finis sous l'onset, pas une preuve asymptotique.

Retour de l'Agent 6 reçu : `round7/jacobi.json` annonce PASS des identités seules, sur les six premiers p=3,7,11,13,17,19 avec tous les caractères nonprincipaux et l'ordre 4 inclus ; 44944 préfixes centrés ; cinq vrais tuples HH avec quatre mu et R_p ; la fibre A=273,C=10403,p=11 conserve ses douze cellules e=3, avec twists 0,+1,-1. Aucun PASS asymptotique ni gain quantitatif n'est crédité. Le raccord N10 et les secteurs p|k,p|a*r ont aussi été transmis pour audit ; ce rapport ne prétend pas les avoir fait rejouer par le Juge.

Le passage à p∤N évite réellement la dégénérescence de la corrélation isolée lorsque p|N. N4 montre comment l'insérer dans le porteur. N7 et N9 montrent pourquoi cette insertion, seule, ne contrôle pas le principal original : sa masse est reconstruite, ses erreurs et exceptions sont conservées. N10 montre que le vrai centré utilise chi(N) plutôt que chi(m), et que choisir p depuis k ou a*r perd précisément ses secteurs physiques. Le modèle M_HH reste explicitement dans le raccord. **Le candidat de gain par Jacobi seul est donc rejeté avant formalisation.** Aucun nouveau .lean générique n'est proposé, aucun compilateur n'est invoqué par ce rôle, et aucun gain indépendant sur D_N n'est revendiqué.

[Source primaire : Montgomery–Vaughan, sommes de Gauss et Jacobi](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/13.0_pp_282_325_Primitive_characters_and_Gauss_sums.pdf).
