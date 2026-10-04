# Agent 4 — formalisation et audit indépendant, boucle 10

**TERMINÉ. U1 est compilée avec les vrais μ et Λ, le cap source, le front strict et le masque physique. U2, U5, U6, U7-sharp et U7 sont cohérentes dans les domaines déclarés. La compensation signée entière reste ouverte : aucune victoire.** Les conclusions analytiques ci-dessous sont un audit mathématique écrit, sans certification Lean de (54) ou de U7.

## 1. Entrées gelées et gate préalable

J'ai lu le PROBE de boucle 10, les rapports finaux des rôles 1 et 2 et le reçu final du rôle 6. Les empreintes ont été vérifiées avant compilation :

| Entrée | SHA-256 |
|---|---|
| agent1_prime_signed.md | e439a43eea07380643c233ca6e48442d79e0c6cd1bdff4d67adc590797791064 |
| agent2_prime_operator.md | 55b0eddd21732a6d9052f888d6df7114c4041ad41e8e59c33c6568bab261b4fa |
| paired_cofactor_checks.py | bdee7952e47419fef2a0512d8e74a7234bf3da6800e2dc9561b94f9bd34d5ef2 |
| paired_cofactors.json | 909df1b5cd38a4ed42cad65ca8930c47930d7ba8afd356148d87f4c7edcf34b2 |
| agent6.md | 3453e489eb94df5a187b107173a9081c95471116ae0369de4dd3d0d1cb7ef413 |

Le JSON donne PASS_FINITE_IDENTITIES_ONLY, dual_and_matched=PASS_IDENTITY_ONLY, N=100000000 et victory=false. Le script SHA consigné coïncide avec les octets gelés. Le rôle 6 a confirmé le gate sauvegardé puis son état TERMINÉ. Je n'ai ni rejoué un ancien banc passé, ni modifié les archives. Le rendu source54_page27.png a été examiné : l'exposant de (54) est bien −sqrt(u/60), et l'endpoint de (53) est présent. L'onset source acquis est u>=10^24.

## 2. Ce que Lean prouve réellement

Le module autonome lean/ShortDivisorComplement.lean importe mathlib en cache. Il définit

```
mu(m) = (ArithmeticFunction.moebius m : ℝ),
D(Q,a,m) = sum_(k|m) if k<=Q and a*k<m
                           then mu(k) log((k:ℝ)/(m:ℝ)) else 0,
U(a,m) = sum_(r|m) if r<=a then mu(r) log r else 0.
```

Les diviseurs de m positif sont automatiquement positifs. Aucun coefficient libre ne remplace μ, et Λ est ArithmeticFunction.vonMangoldt. Le théorème short_divisor_complement établit, pour m≠0 et m<a*(Q+1),

```
−mu(m) D(Q,a,m)
   = mu(m)^2 [−ArithmeticFunction.vonMangoldt(m) − U(a,m)].
```

Le cap n'est pas laissé implicite. source_cap prouve

```
alpha>0, alpha<=a, m<N
    => m<a*(floor((N−1)/alpha)+1).
```

Il utilise l'inégalité entière Nat.lt_mul_div_succ. Le théorème short_divisor_complement_source applique donc U1 avec le Q original floor((N−1)/alpha). Il ne suppose ni la cible ni une identité manquante. La forme alternative m<=Q*(a+1), proposée par root, serait également suffisante ; elle n'est pas nécessaire au contrat retenu.

La preuve carré-libre établit explicitement k.Coprime(m/k), à partir de k|m et du produit exact k*(m/k)=m. La multiplicativité réelle et mu(k)^2=1 donnent mu(m)*mu(k)=mu(m/k). logarithm_complement prouve log(k/m)=−log(m/k), avec les cast/divisions et leurs non-zéros. strict_front_iff établit a*k<m ↔ a<m/k. Le changement de variable est la bijection exacte Nat.sum_div_divisors, puis la partition r<=a / a<r est reliée à l'identité mathlib sum_moebius_mul_log_eq. Le cas non carré-libre annule le coefficient original entier par mu(m)=0 ; il n'efface pas U(a,m). at_one prouve séparément l'égalité en m=1 pour tous Q et a.

Le raccord physique est lui aussi certifié. physicalDivisorKernel conserve la condition k.Coprime(n*N). physical_divisor_units prouve que tout k|m la satisfait lorsque m+n=N et n.Coprime N : n est copremier à m, puis chaque diviseur de m est copremier à n et à N. physical_kernel_eq retire ce masque uniquement sur cette fibre prouvée. Le théorème physical_short_divisor_complement_source conclut U1 pour ce noyau physique, avec m≠0, m+n=N, n>0, n.Coprime N, alpha>0 et alpha<=a. La primalité de n n'est pas requise par cette identité ; elle reste une condition de la somme B_prime et des applications analytiques. Aucun masque mu(n)^2 n'a été ajouté.

Le module ne prétend pas certifier le modèle harmonique, qui reste une somme sur tous les k unitaires dans son cap, et pas seulement sur les diviseurs de m. Il ne duplique pas le module PrimeCofactorIdentity du rôle 3.

## 3. Compilation et défauts techniques conservés

La reconstruction locale utilise Lean 4.15.0 et huit bibliothèques précompilées existantes, sans installation ni construction des anciens modules. Les commandes, versions, chemins, snapshots de chaque source, SHA et sorties brutes sont dans role4_build_receipt.json et role4_build/.

| Tentative | Résultat exact |
|---|---|
| 1 | Erreur de type dans strict_front_iff : une réécriture globale de m avait aussi réécrit m dans m/k. Le quotient du but devenait (m/k)*k/k. Correction : une étape calc localise la réécriture au membre a*k<m. |
| 2 | Compilation U1, cap source et m=1 réussie. |
| 3 | Après ajout du raccord physique, simp made no progress dans physical_kernel_eq. Le lemme d'unité et les autres théorèmes étaient déjà prouvés. Correction : introduction explicite de l'unité et distinction des deux conditions de front/cap. |
| 4 | Compilation de la source finale complète réussie, code de sortie 0. |

Les sorties des tentatives en erreur mentionnent sorryAx, introduit automatiquement par Lean pour ses déclarations en erreur ; aucun sorry n'a été écrit dans les candidats. Ces candidats ne sont pas certifiés. La sortie finale des quatre #print axioms, incluant le théorème physique, contient exclusivement propext, Classical.choice et Quot.sound. La source finale ne contient ni sorry, ni admit, ni déclaration axiom. Ces défauts techniques ne sont pas des démonstrations d'un obstacle mathématique et ne sont pas utilisés comme verdict sur la parité.

| Artefact final | SHA-256 |
|---|---|
| lean/ShortDivisorComplement.lean | 25f38fcb6f84b73551bf9d4131745d5c234a3187dd3e92a8402f8e81b721b447 |
| role4_build/ShortDivisorComplement.olean | 733128e14b663152143ea15a6939437691d0d3477837f10b686def852a56cc6b |
| role4_build/attempt04.log | 88f1a49cd9ed0ee0159a87b3d7e8e3d024a8ccb4c95dfb2e5b552d541f227bf3 |
| role4_build_receipt.json | 75ba330f5d6711d3f82b98abed400a6f9d1fff82b06e6c7f6cbd2f8e31e6c0c8 |

## 4. Audit de U2 et de la partition réelle

Avec a=ceil(N^(7/16)) et m<N, trois facteurs premiers >a auraient un produit >a^3>=N^(21/16)>N. Sur le support carré-libre entier, j appartient donc à {0,1,2}. Le point m=1 est nul. Le zéro non carré-libre vient du coefficient entier, pas d'un filtre ajouté au raw.

Dans J2, les conditions sont a<p<q premiers, m=c*p*q, c carré-libre, gcd(c,pq)=1, tous les facteurs premiers de c<=a, unités avec N et premier axe n=N−m. Les conditions de coprimalité excluent les facteurs répétés. On a

```
c<=floor((N−2)/(a+1)^2)<N/a^2<=N^(1/8)<a.
```

Chaque diviseur r<=a de m est alors un diviseur de c, et tous les diviseurs de c sont <=a. Le préfixe est complet dans ce secteur : U_a(m)=−Lambda(c), Lambda(m)=0 et mu(m)=mu(c). Ainsi U2, L_a(m)=Lambda(c) et C_m=Lambda(c)+mu(c)W_a, est exacte. Pour c=1, C=W_a ; pour c premier, C=log c−W_a ; pour c composite carré-libre, Lambda(c)=0. Remplacer Lambda(c) par log c pour tous les c est faux.

Pour J1,c>a, U_a(c) demeure tronqué. Le témoin c=3183=3*1061, p=3307, m=10526181 conserve U_a(c)=−log3183 alors que Lambda(c)=0. Le témoin J0 m=1174173 conserve sa combinaison littérale de logarithmes. Le cœur c=9 de m=28629 conserve son préfixe non nul, mais L=C=0. Les témoins ne sont pas réétiquetés comme erreurs Lean.

Le retrait de k=1 est conjoint : si m>a, L reçoit mu(m)log m et mu(m)W reçoit son opposé ; sinon les deux morceaux sont inactifs. Ni un modèle k>=2 isolé, ni une complétion générale des fibres coupées n'est autorisée.

## 5. Audit de (54), du masque bulk et de U5/U6

Sur Omega_bulk, n premier et n>Q impliquent n∤k pour tout k<=Q. Le masque gcd(k,nN)=1 devient exactement gcd(k,N)=1. Cette simplification est limitée au bulk ; hors bulk, n reste dans le masque. K=N est pair et <=N^3. Le préfixe R=min(Q,floor((m−1)/a)) est entier, strictement positif et >=N^(5/16)/8>=N^(1/5) dès u>=10^6. En effet a<=2N^(7/16), m>=ceil(N^(3/4)), et les erreurs de deux planchers sont dominées par cette marge ; Q>=N^(3/4)/8 ne réduit pas la borne. N^(9/80)>=8 suffit pour la dernière comparaison.

L'endpoint de (53) vaut log(R/m)A_K(R), de module <=u|A_K(R)| puisque 1<=R<m<=N. Après division de (54) par u, on obtient

```
|W_a+S(N)| <= epsilon_W
 =4*10^8*u^4*exp(−sqrt(u)/60)+160*u*exp(−u/40).
```

L'affaiblissement est correct : sqrt(u/60)>=sqrt(u)/60. À u0=10^24, u0<2^80 ; les facteurs positifs sont <2^349 et <2^88, et chaque exponentielle est <2^(−10000). Les dérivées par rapport à log u sont 4−sqrt(u)/120 et 1−u/40, négatives ensuite. Ainsi epsilon_W<=1/4 sur le domaine source, sans hypothèse nouvelle de petitesse.

Pour la borne inférieure de U5, les produits finis des facteurs de C2, indexés par p−1 pour p impair premier, sont des sous-produits des facteurs 1−1/j^2, j>=2. Chaque facteur est dans (0,1), et le produit complet télescopique tend vers 1/2. Le passage à la limite donne C2>=1/2 ; les facteurs locaux (p−1)/(p−2) de S(N) sont >=1. Donc S(N)>=1. Le produit infini source est conservé, et aucune valeur décimale empirique n'est utilisée.

La borne S(N)<=N/phi(N) est l'input source (19). Pour N pair et u>=8, le facteur 2 est explicite dans N/phi(N). Les premiers impairs p<=u donnent

```
sum log[p/(p−1)] <= sum 1/(p−1) <=(1+log u)/2.
```

La dernière somme se majore par les dénominateurs pairs et l'harmonique correspondante. Le nombre de premiers divisant N et dépassant u est <=u/log u, car leur produit divise N. Leur somme est <=u/((u−1)log u)<=1. Donc N/phi(N)<=2*exp(3/2)*sqrt(u)<10sqrt(u). Tous les facteurs premiers de N sont couverts ; aucun seuil de distribution première n'intervient.

U6 suit alors pointwise sur le bulk. Pour m premier, log m>=3u/4 et C=−log m+S(N)−delta. Ainsi C<=−3u/4+10sqrt(u)+1/4<=−u/2 dès u>=10^24. Pour m=p*q rough carré-libre, C=W_a<=−S(N)+1/4<=−3/4. L'inégalité 10sqrt(u)+1/4<=u/4 est monotone et largement vraie à ce seuil. Une classe vide donne une contribution favorable nulle ; aucune représentation de Goldbach n'est supposée.

## 6. Un seul paiement de coins, injection et U7-sharp/U7

U est la réunion du bloc premier rough et de tout J2. Hors bulk, n<=Q ou m<M. Une seule union est comptée, avec au plus Q+M<=3N^(3/4) points, y compris l'intersection une fois seulement. Sur U, |L|<=u, |W|<=u*sum_(k<=Q)1/phi(k)<=3u(1+u), et log n<=u. Pour u>=1, chaque masse absolue est donc <=7u^3. Le coût 21N^(3/4)u^3 tient dans la marge E_corner=30N^(3/4)u^3.

Le paiement E_corner<N/(1024u ell) dès u>=65536 est effectif : le ratio est 30720u^4ell*exp(−u/4), <=30720u^5exp(−u/4). log30720<16<=u/4096 et log u<=u/4096 à partir de 65536, par décroissance de log u/u. Le logarithme du ratio est <=−1018u/4096<0. Pour la marge 10^(−12)N/(u ell) au seuil source, le facteur polynomial 30u0^4ell0 est <2^331 ; l'exponentielle est <2^(−10000). Sa dérivée logarithmique 4+1/ell−u/4 est négative ensuite. Les deux marges sont donc justifiées par des inégalités écrites, sans test numérique au seuil énorme.

L'injection J2 est canonique : le cœur c est le produit unique des facteurs premiers <=a, les deux autres facteurs sont l'unique couple p<q, et n=N−m est déterminé. Aucun facteur de multiplicité n'est introduit. Le comptage J_c contient la condition réelle que n est premier unitaire, le bulk et tous les fronts. Il n'est pas une somme de Möbius ordinaire sur c.

Ainsi B_(J2,c>=2,bulk)=H2−S(N)M2+R2, et |R2|<=N*u*epsilon_W=N*G54. Le terme c=1 est exclu de cette erreur et déjà conservé dans le bloc rough. À u0, les facteurs positifs du ratio NG54/[N/(u ell)] sont <2^515 et <2^254 ; leurs exponentielles sont <2^(−10000). Les dérivées 6+1/ell−sqrt(u)/120 et 3+1/ell−u/40 sont négatives ensuite. NG54<10^(−12)N/(u ell) est donc un paiement écrit valide sous (54).

Sur le bloc premier, le majorant exact est −R_pair+[S(N)+epsilon_W]Theta_prime. Sur le rough semipremier, il est −[S(N)−epsilon_W]Theta_2. En y joignant le J2 nonrough, l'unique paiement de coins, et les secteurs entiers B_J0 et B_J1,c>1, on obtient exactement U7-sharp. U6 donne ensuite U7. Les diagonales p=q non carré-libres restent annulées par le coefficient entier ; elles ne sont pas insérées dans le couple p<q. Aucune minoration de Theta_prime, Theta_2 ou R_pair n'est postulée.

Le raccord du rôle 2, 1<c<=a<p, appartient à J1. Il ne doit pas être ajouté comme un second secteur à B_J1,c>1. Son c=1 recoupe le bloc premier ; J2 est disjoint. L'extraction singulière S(nN)/S(N)=1+1/(n−2) exige n premier unitaire, conserve n=3, et son paiement harmonique exige les n distincts. L'injection c<=a<p assure cette distinctivité. Le noyau positif du rôle 2 a principal +S(nN), tandis que le W source du rôle 1 a principal −S(N) sur son bulk. Ces conventions sont compatibles.

## 7. Limite du résultat et verdict transmis au Juge

Le falsificateur m=30108669=3*3167*3169, n=69891331 premier, donne C=log3−W>0 : « tout J2 est favorable » est faux. Les témoins J0 et J1 incomplet sont également positifs. Les deux témoins rough sont négatifs et le non carré-libre m=30089667 est nul. Les certificats finis conservés n'établissent ni U6 asymptotique à N=10^8, ni une compensation globale.

U7 conserve précisément B_J0+B_J1,c>1+H2−S(N)M2 et les masses favorables. Le poids J_c impose simultanément p, q et N−c*p*q premiers. Une estimation signée indépendante de cette combinaison reste manquante. H2 est positif sur les c premiers et M2 n'a aucune positivité acquise. Le gain ne suit pas de la seule brièveté c<N^(1/8), d'un préfixe Mertens ordinaire ou d'une norme de Gram. Ce constat ne constitue pas une impossibilité globale des méthodes de caractères ou de poids.

La route source reste

```
D_N=B_prime^a+B_pp^a+P_band^{>=2}+Z_face^{>=2}
                       +I_alpha+2max(e,0).
```

I, le properpower et la face harmonique restent payés une fois selon leurs contrats acquis ou écrits. Le seuil BV supplémentaire de la bande physique n'est pas évalué ; le pont couvert 2max(e,0) reste à payer. Le nouveau paiement de coins et celui de R2 ne les absorbent pas. Aucun axiome de (54), de compensation principale ou de cible n'a été créé pour produire un U7 Lean.

Verdict : **COMPILED_AUXILIARY_U1_WITH_PHYSICAL_UNITS; WRITTEN_ROUGH_ONE_SIDED_REDUCTION_VALID; SIGNED_THREE_PRIME_CORE_MOMENT_OPEN; PHYSICAL_BAND_ONSET_UNEVALUATED; COVERED_E_UNPAID; VICTORY_FALSE.** Source, sorties et rapport de ce rôle sont gelés après cette clôture ; l'empreinte du présent rapport est transmise séparément. Tous les travaux écrits ont été confinés aux fichiers du rôle 4 sous round10.
