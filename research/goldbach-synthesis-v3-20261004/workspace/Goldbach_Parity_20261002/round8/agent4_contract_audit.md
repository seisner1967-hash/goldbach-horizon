# Boucle 8 — audit du Gram natif et du raccord aux poids réels

Agent 4, 2 octobre 2026. Rapport proposé audité : `agent2_native_bilinear.md`, B1–B10. Code consulté : `native_gram_checks.py`, son JSON et son journal. Le corrigendum d'onset `SOURCE_ONSET_CLARIFICATION.md` est conservé ; le rendu de la page physique 32 a aussi été examiné directement. Les autres rôles et les 227 artefacts antérieurs du registre ne sont pas modifiés.

**Verdict : identités natives exactes, mais transfert quantitatif absent ; candidature rejetée avant compilation pour absence d'estimation indépendante des poids couplés et de leur cumul.** Aucun défaut de conjugaison n'a été trouvé dans B5–B9. Le Gram nu donne une borne valide pour deux vecteurs séparés ; il ne donne pas celle du signed-root discrepancy HH. Un nouveau diagnostic sur de vrais indices premiers de L2 réfute une séparation exacte de rang un du poids raw, sans réfuter une future estimation plus riche. Aucun nouveau Lean standard de remplacement n'est produit.

## 1. Identités du raw et support L2 exact

Le profil est littéralement

`F_N(m)=1_(0<m<N) 1_(N-m>1) 1_(gcd(N-m,N)=1)`
`*[Lambda(N-m)-log(N-m)]*[D(m)-W(N-m,m)]`.

Il ne comporte **aucun nouveau mu(N-m)²**. Les n non carrés-libres et les puissances premières propres restent présents. Les frontières `alpha*k<m`, `1<=k<=Q` et le préfixe `min(Q,floor((m-1)/alpha))` restent réévalués au véritable m.

Pour m>1 carré-libre, les premiers h divisant m donnent `mu(m/h)=-mu(m)` et la somme de log(h) vaut log(m). Pour m non carré-libre, tous les termes autorisés `h∤l` sont nuls par mu(l), ou sont exclus. Cela justifie B1 sur **h premier, l>=1, h*l<N, h∤l**. Le terme m=1 absent de cette couverture a F_N(1)=0 à cause de la face stricte. Ni h=1 ni un h composite n'est un indice de L2.

Sur gcd(n,N)=1 avec m=N-n, un diviseur k de m est automatiquement premier à n*N. Les lignes DIV peuvent donc être réunies aux lignes W dans B2 sans perdre de termes. B3 est alors l'orthogonalité native sur **gcd(n*N,k)=1** ; elle conserve `chi(n)*conj(chi(N))`. Pour k=1, la ligne centrée et la somme nonprincipale sont toutes deux nulles. Les k non carrés-libres ont mu(k)=0 dans B2 ; le passage au tensor carré-libre ne constitue pas une exclusion supplémentaire.

B1–B3 sont une insertion exacte dans le raw sous ces conditions. Elles gardent mu(l), mu(k), le véritable fII(N-h*l), les normalisations logarithmiques, les unités, les nonunités des caractères induits et les fronts. La primalité de h et l'exclusion h|l ne sont pas des poids séparables gratuits. Leur identité ne fournit aucune estimation signée supplémentaire.

## 2. Gram premier, conjugaisons et axes zéro

Pour q premier ne divisant pas N et chi nonprincipal, définir G sur **tous** les résidus par

`G(a,b)=chi(N-a*b)*conj(chi(N))`.

Les axes a=0 ou b=0 valent 1 ; lorsque N-a*b=0 modulo q, G vaut zéro. Avec `w_a=chi(a)` et w_0=0, les quatre cas du Gram sont :

| a,c | Somme en b de G(a,b) conj(G(c,b)) |
| --- | --- |
| a=c=0 | q |
| un seul indice nul | 0 |
| a=c non nul | q-1 |
| a,c non nuls distincts | -chi(a) conj(chi(c)) |

Dans le dernier cas, le ratio des deux formes affines parcourt F_q sauf a/c, avec un terme nul au pôle. B5 a donc exactement l'orientation

`G G* = q I - w w*`.

Comme G est symétrique, **le Gram droit est**

`G* G = q I - conj(w) conj(w)*`.

Ainsi B6 soustrait **|sum_b chi(b)*beta_b|²**, et non une somme où chi aurait été arbitrairement conjugué. Les tests d'ordre 4 détectent cette distinction. ||w||²=q-1 : la direction exceptionnelle gauche w a valeur propre 1, son orthogonal a valeur propre q. La norme complète est sqrt(q). Elle est atteinte, notamment, par la colonne b=0 qui vaut 1 ; ces axes ne peuvent être retirés de DIV-HARM.

La restriction aux unités retranche cette colonne constante :

`G_unit G_unit* = q I - 1 1* - v v*`, `v_a=chi(a)`.

Les vecteurs 1 et v sont orthogonaux et ont norme carrée q-1. Ils ont chacun valeur propre 1, les autres directions valeur propre q. Le Gram droit y conjugue v ; l'énergie devient `q||beta||²-|sum beta|²-|sum chi(b)beta_b|²`. Au q=3, l'orthogonal aux deux directions est vide et la norme unitaire vaut 1. Cette exception ne remplace pas la norme complète sqrt(3), puisqu'elle perd les axes natifs m nonunitaires.

Une petite projection de Möbius dans le terme soustrait de B6 signifie une petite soustraction, **pas** une petite énergie totale. Toute conclusion sur la direction réelle exige son insertion pondérée.

## 3. Facteurs principaux composites et caractères induits

Pour un local principal modulo p avec p∤N,

`G_0=J-P_tilde`, `P_tilde(a,b)=1_(a*b=N)`.

P_tilde est une permutation involutive sur les unités, nulle sur les axes zéro. Sur le sous-espace orthonormal engendré par delta_0 et les unités constantes normalisées, la matrice est

`[[1,sqrt(p-1)],[sqrt(p-1),p-2]]`.

Sa trace est p-1 et son déterminant -1 ; ses racines satisfont `lambda²-(p-1)lambda-1=0`. La racine positive

`rho_p=((p-1)+sqrt((p-1)²+4))/2`

domine les valeurs singulières restantes, qui valent 1 sur l'orthogonal lorsqu'il existe. On a p-1<rho_p<p. Sur les unités seules, la norme principale vaut p-2 ; le cas p=2 a un espace unitaire de dimension un et une matrice nulle. Le profil pair original exclut de toute manière p=2 des k unitaires à N.

Le CRT est un réindexage unitaire des résidus. Pour k carré-libre, gcd(k,N)=1, la matrice d'un caractère global est le tensor des matrices locales, **principales comprises**. Si son conducteur primitif est q|k, sa norme exacte est

`sqrt(q)*product_(p|k/q)rho_p <= k/sqrt(q)`.

Seul un caractère primitif à k a automatiquement norme sqrt(k). La primitive de conducteur q prolongée seulement au module q ne remplace pas le caractère induit modulo k : ses facteurs principaux à k/q assurent encore les nonunités originales. Pour q=1, la formule décrit la matrice globalement principale ; ce caractère n'est pas dans la somme nonprincipale B3, mais ses facteurs locaux peuvent apparaître dans des caractères globalement nonprincipaux.

Le banc spectral principal a N=10000² et donc deux racines de a²=N modulo chacun des premiers testés ; ses multiplicités de valeurs propres ±1 sont spécifiques à cette donnée. La formule générale rho_p ne dépend pas de ces multiplicités et reste valable pour tout N unité p.

## 4. Secteur divisible conservé : phase constante dans le porteur HH

Le raccord natif garde le témoin de boucle 7 : `k=7,n=47864203,m=52135797` donne chaque phase native égale à 1, et la ligne centrée vaut 5/6. Le twist bipolaire chi(n)conj(chi(m)) reste zéro ; le rapport proposé ne le substitue plus à la ligne native.

La portée est plus générale. Dans **tout porteur physique DIV-HH** où m=r*k, chaque conducteur q|k satisfait m=0 modulo q ; n=N modulo q. Pour A=b*u*v,C=k*s*t et A*x+C*zeta=N, on a donc

`chi(N-C*zeta)*conj(chi(N))=1`

sur toute la fibre du caractère natif modulo k, non seulement au témoin. Les facteurs locaux principaux induits valent aussi 1, puisque n=N est unité à k. La matrice complète conserve cette ligne C=0 ; elle ne produit aucune oscillation de caractère à l'intérieur de cette composante physique.

La phase peut varier dans l'objet raw DIV-HARM complet, qui comprend aussi les lignes harmoniques sur m non divisible par k. Les quatre signes HH, les détecteurs prescrits à cette composante, la rugosité, les faces, les diagonales de factorisations et le CRT a*r restent à traiter dans le porteur physique. **Le modèle reste séparé : E_HH=C_HH-M_HH.** Aucun Gram ne construit automatiquement M_HH sur les tuples m=r*k ni ne borne leur différence. L'identité de trace primitive antérieure `mu(q)P_q(m)/phi(q)=1/phi(q)` sur gcd(q,m)=1 demeure acquise et ne devient pas une innovation oscillatoire.

## 5. Borne séparable et défaut réel de couplage

B10 est valide pour deux vecteurs séparés sur des intervalles entiers. Agréger alpha et beta par classe modulo q, puis utiliser B5 et Cauchy, donne

`|sum alpha_h beta_l G(h,l)| <= sqrt(q)||A||_2||B||_2`
`<=sqrt(q)*sqrt(1+|H|/q)*sqrt(1+|L|/q)*||alpha||_2||beta||_2`.

Les +1 paient le nombre maximal de représentants d'une classe. Cette norme ne s'applique pas en remplaçant alpha_h beta_l par un coefficient W(h,l) arbitraire borné. Le falsificateur quadratique W=G donne `sum W*G=q²-q+1`, supérieur à q sqrt(q) pour q>=3. Il réfute uniquement ce contrat générique de transfert ; il ne réfute pas une future estimation spécifique de HH.

Le mineur h={1,3},l={101,311} du banc original est un diagnostic raw de rang, pas un diagnostic L2 : h=1 n'est pas premier. **Un véritable mineur L2 existe aussi**, calculé directement avec le profil exact et communiqué à l'Agent 6 :

`h={3,13}`, `l={101,311}`, `m=[[303,933],[1313,4043]]`.

Tous les h sont premiers, h∤l, h*l<N et les quatre arguments sont unités à N. Les calculs symboliques de logarithmes et leurs encadrements rationnels donnent

`F_N(933)<-52`, `F_N(1313)>2`, `F_N(4043)=0`.

La dernière égalité vient de la primalité exacte de n=99995957, donc fII(n)=0. Au m=1313, `n=99998687=23*59²*1249` est **non carré-libre** et doit rester au raw. Ajouter mu(n)² supprimerait illicitement ce témoin. Le déterminant raw est

`F_N(303)*F_N(4043)-F_N(933)*F_N(1313)>104`.

Les deux l sont premiers, donc mu(l)=-1, et log(h)/log(h*l)>0. Le déterminant des **vrais coefficients L2** `mu(l)*log(h)/log(h*l)*F_N(h*l)` est lui aussi strictement positif : le premier produit est nul, et le second est négatif. Cela réfute une séparation exacte de rang un sur ces indices admissibles. Le replay numérique de ce complément appartient à l'Agent 6 puis au Juge ; cet audit n'annonce pas encore leur reçu.

Ce mineur ne borne ni le rang global, ni une norme pondérée, ni le coût d'une séparation en plusieurs termes. Il n'est pas un témoin HH : ce dernier a ses détecteurs prescrits, qui ne sont pas ceux du raw. Les facteurs logarithmiques lisses peuvent être séparés avec leur coût, mais cela ne sépare pas Lambda(N-h*l), les unités et les fronts mobiles. Dans Cauchy avec les vrais poids, le Gram contient `W(C,zeta)conj(W(C',zeta))` et n'est plus B5. Sa diagonale comprend toutes les factorisations de même C=k*s*t ; elle n'est pas seulement la diagonale de tuples identiques. Les distinctions D00/Da/Dk acquises restent intactes.

## 6. Coût N^(13/8) : majoration optimiste et domaine

Le calcul proposé est arithmétiquement correct sous ses hypothèses simplifiées : une bande k~K avec q~k, tous les caractères concernés supposés primitifs, deux blocs P,L<=q avec P*L~N, deux vecteurs séparés de normes dont le produit est de taille sqrt(N) avant facteurs logarithmiques. B10 donne alors de l'ordre sqrt(K*N) **par caractère**. Dans une somme absolue, jusqu'à phi(k) caractères paient le facteur 1/phi(k) de B3 ; une bande de O(K) modules donne

`K*sqrt(K*N)`, donc `N^(13/8)` lorsque K~N^(3/4).

Ce nombre est le coût d'une majoration optimiste du bloc séparable, **pas** une minoration de la somme réelle, ni un coût prouvé inévitable pour un traitement joint. Il ne constitue pas non plus une borne du profil complet avec ses poids couplés et caractères induits : ces derniers exigent les normes B9, et les vrais poids/masques restent à payer. Les premiers h, mu(l), les normalisations et les autres sommes HH ne sont pas de nouveaux facteurs négligeables. Garder k et les caractères joints pourrait améliorer cette majoration, mais aucune estimation correspondante avec les vrais coefficients n'est fournie.

Le gain local N^(7/8) au q~N^(3/4), P=L~N^(1/2), vaut également seulement pour ce bloc nu. Le secteur l=1 et les fibres courtes ne sont pas couverts par une norme sur deux longs vecteurs. L'identité exacte `D_N=C1-S_rest+2max(e,0)` conserve la compensation globale requise ; le minorant qualitatif de C1 n'a pas un seuil effectif automatiquement égal à l'onset de la monographie. Les queues, défauts d'unités, secteurs constants, modèle et erreur e demeurent dans leurs lignes d'origine.

## 7. Onset, vérification et obligations ouvertes

Le rendu original de la page 32, équation 66, porte visiblement **u>=10^24**. Le corrigendum lie les pages 32, 33, 36 au PDF inchangé. Il corrige l'aplatissement de l'exposant dans l'ancienne extraction ; il ne remet aucun acquis en cause. Les préfixes retenus, exclusions exceptionnelles, log(K)<=2u et longueurs originales du §12.6 restent dans leur domaine. La phase additive de produit chi(N-h*l) n'est pas automatiquement un caractère multiplicatif de l, et les filtres mobiles/primoriaux ne sont pas un nouveau masque fixe gratuit. N=10^8 reste un falsificateur fini sous cet onset.

La version du banc consultée vérifie 9339 entrées de Gram premiers et 6120 entrées tensorielles CRT, les conjugaisons d'ordre 4, les axes zéro, les facteurs principaux et le falsificateur W=G, en phases cyclotomiques et polynômes entiers exacts. Son reçu indique `PASS_ALGEBRA_ONLY`, la conservation des 227 artefacts et aucune estimation de D_N. Aucun replay indépendant du Juge ni compilation Lean n'est attribué à ce rôle.

Pour qu'une candidature devienne éligible, il manque une estimation arithmétique indépendante d'au moins l'objet réellement pondéré : son cumul doit conserver les quatre Möbius, les fronts, les diagonales, les localement principaux et les nonunités, puis payer les modules extérieurs, C_HH-M_HH, les secteurs courts, les queues et le pont e. Poser cette petite somme signée comme hypothèse équivalente au budget terminal ne serait pas une preuve.

Le Gram fournit donc une information exacte sur le noyau natif ; **le mécanisme de contournement demandé n'est pas obtenu**. Le transfert séparable reste inapplicable sans un défaut estimé, et le secteur physique DIV est nativement constant. Classification précise : `REJECTED_BEFORE_COMPILATION_MISSING_WEIGHTED_ARITHMETIC_ESTIMATE`. Aucun nouveau .lean standard, aucun sorry, aucune fausse erreur de compilateur et aucune victoire ne sont produits.
