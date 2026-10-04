# Agent 4 — raccord réel P1/P2 et audit indépendant P3–P6, boucle 11

**TERMINÉ. Le raccord J2 du bracket source, P1 locale, la partition injective carré-libre avec faces et P2 sont compilés. Le paiement écrit du seul modèle conjoint P5 est valide dans son domaine source. Les célibataires, faces, entropies et le reste du ledger ne sont pas payés : aucune victoire.**

## 1. Entrées, gate et périmètre

J'ai lu PROBE11, le retour final10, round11_observe, le prompt du nœud13.1 et le rapport1 final entier. Les inputs source relus sont (44), ses constantes et son uniformité en masque, (53)/(54), et la borne S(N)<3ell au §12.7. Le seuil source reste u>=10^24 ; le seuil log z>=16 du crible et u>=10^6 de (54) sont inclus dans ce domaine, sans déplacement d'un acquis.

| Entrée gelée | SHA-256 |
|---|---|
| agent1_signed_compensation.md | 41cf2ead5d3cb8aa399bfc148e1e29f0f543135ca8b225b0d92c7fb2253ed7dd |
| paired_axes_checks.py | 5c3f5d86120bbe5950dc4670e2b4854412de5f8077a3fc006a97a6d46343d2eb |
| paired_axes.json | ff1f8526553f2861776e9aa3f492969274a664055b8e3fb6ea41bebe079c6173 |

Le rôle6 a confirmé explicitement le gate final sauvegardé et son rejeu neuf octet pour octet avant toute compilation. Le gate général est PASS_NEW_PAIR_IDENTITY_ONLY. Les deux entrées full_partitions, both_prime et one_prime_axis, portent chacune PASS_FULL_FINITE_PARTITION_AND_P2_ONLY, disjoint_partition=true et P2_formal_scalar_identity=true. Elles conservent X={1,3,7}, D={1}, 3D={3}, F={7}. Le builder vérifie ces champs et les SHA exacts ; aucun statut numérique analytique n'est adopté.

Ce rôle n'a écrit que son module, son builder, ses snapshots/logs/reçu et le présent rapport sous round11. L'unique dépendance custom est une copie inchangée de ShortDivisorComplement.lean de boucle10, liée par SHA et reconstruite dans role4_build/dependency. Aucun ancien olean de producteur n'est importé, aucune installation, aucune mutation Arbor ni ancien banc passé relancé.

## 2. Bracket, unités, cap et complétude J2 effectivement prouvés

Le fichier lean/ThreeAdicPrimePairing.lean utilise le vrai μ et le vrai Λ via U1. harmonicKernel est la somme réelle sur tous les k dans Icc(1,Q), avec totient(k), k copremier à n*N et le front strict a*k<m. Son logarithme est log(k/m), de convention négative. Il n'est jamais remplacé par une somme sur les diviseurs du cœur, ni supposé invariant entre n et n3.

primeIncidence(N,n) vaut 1 exactement pour n premier et n.Coprime N, zéro sinon ; theta est cette indicatrice multipliée par log n. sourceBracket est exactement

```
theta(N,n) * [−mu(m)(D_physical(Q,a,m,n,N)−W(Q,a,N,n,m))],
Q=floor((N−1)/alpha).
```

D_physical conserve lui aussi ses unités n*N. U1 importée prouve son cap depuis alpha>0, alpha<=a et m<N. Aucun cap agrandi ni nouveau masque mu(n)^2 n'est ajouté. Tous les k, dont k=1, restent dans ces définitions : aucun morceau k=1 n'est isolément supprimé.

short_filter_prime_pair prouve

```
{r in divisors(c*p*q) : r<=a}=divisors(c)
```

pour c>0, c<=a, a<p<q premiers. Pour un petit r, p et q ne peuvent le diviser ; les deux coprimalités permettent d'enlever ces facteurs de r|c*p*q. Réciproquement, tous les diviseurs de c sont <=c<=a. complete_short_prime_pair donne ensuite U_a(c*p*q)=−Lambda(c). La complétude n'est pas étendue à J1,c>a ni à J0.

prime_pair_arithmetic prouve ensemble que c*p*q est carré-libre, mu(c*p*q)=mu(c), et Lambda(c*p*q)=0 lorsque c est carré-libre. Les coprimalités avec p,q et entre p,q sont déduites des inégalités strictes ; les facteurs répétés sont exclus. Le zéro de Λ utilise la caractérisation carré-libre et prime-power, pas une identité supposée. Le cas non carré-libre n'est pas rajouté à J2 : sa nullité originale entière demeure acquise10.

actual_source_bracket_j2 raccorde réellement le bracket aux coefficients

```
theta(N,n)[Lambda(c)+mu(c)W(n,c*p*q)].
```

Il utilise U1, le carré de μ, le préfixe complet et le zéro de Λ(c*p*q). Si l'indicatrice n est zéro, les deux membres sont zéro sans hypothèse sur son W ; si elle est active, ses unités fournissent exactement le masque physique certifié10. Le théorème n'introduit pas une fonction A_c autonome comme substitut à ce raccord.

## 3. P1 et géométrie entière compilées

mu_three_mul prouve mu(3d)=−mu(d) depuis 3 premier et 3∤d. actual_three_adic_pair combine les deux brackets réellement raccordés, avec d carré-libre, 3d<=a, a<p<q, deux points positifs et les deux égalités de conservation. Il conserve Λ(d), Λ(3d), les deux indicatrices et les deux W différents exactement comme P1. L'entropie Λ(3)log n3 de d=1 n'est pas supprimée.

coreGrid(K,C) est Icc(1,C) filtré par Squarefree(c) et c.Coprime K ; K=N*p*q. pairedBases impose 3∤d et 3d<=C. geometricFaces impose 3∤d et C<3d. Le théorème core_grid_partition prouve la partition disjointe

```
X=D union image(d↦3d,D) union F.
```

Tout c divisible par3 dans X s'écrit 3d ; le carré-libre fournit d carré-libre et 3∤d, et les unités passent au diviseur d. Inversement, 3d est dans X depuis 3.Coprime K et d dans D. Les trois morceaux sont disjoints ; d↦3d est injectif. sum_core_grid est un helper de somme appliqué ensuite aux vrais brackets et principaux, jamais le résultat final à coefficient libre.

bulkCap est littéralement C_t=floor((N−Q−1)/(p*q)). literal_bulk_front prouve c<=C_t ⇒ Q<N−c*p*q sous Q+1<N, avec les planchers exacts. bulk_cap_le_front prouve C_t<=a depuis N<=a^3 et a<p<q. Cette prémisse entière découle du a source ; elle n'est ni une petitesse de moment ni la cible. Les paramètres source α et a restent explicites.

actual_p1_partition prouve pour chaque couple canonique p<q la somme du bracket sur X égale à la somme de P1 sur D plus les faces θ(N−d*p*q)[Λ(d)+μ(d)W] réellement raccordées. Le théorème conserve N pair, t=p*q copremier à N, 3 copremier à N, a>3, carré-libre et cœur court. three_coprime_mask déduit 3.Coprime(N*p*q) des conditions sources. Aucun cas 3|N n'entre dans cette extraction.

## 4. P2 est une identité du modèle, avec toutes ses composantes

singularSeries est défini par le produit source : 2C2 fois le produit local (p−1)/(p−2) aux premiers impairs divisant N, et zéro pour N impair. C2 est son vrai produit infini. Il n'est pas un coefficient libre. La compilation n'affirme aucune nouvelle convergence, positivité ou borne analytique de ce produit ; P2 n'en a pas besoin.

principalTerm vaut [Λ(c)−S(N)μ(c)]theta(N−c*p*q). entropyTerm conserve Λ(c)theta. commonTerm contient les deux indicatrices multipliées et log(n3/n). singletonTerm contient explicitement (1−i)j log n3−i(1−j)log n. Les arguments de log du quotient sont prouvés positifs par le front bulk ; aucune division par un n3 hors face n'est utilisée.

principal_pair_split établit la décomposition locale par expansion algébrique et log_div. actual_principal_partition applique la partition réelle à ces termes et conclut exactement

```
K2=H2+S(N)(Delta_common+Delta_single+Delta_face),
Delta_face=−sum_(d in F)mu(d)theta(N−d*p*q).
```

Les célibataires restent présents même si l'autre axe est composite, et les faces n'ont aucune incidence fictive à 3d. Le certificat est par couple canonique ; on peut sommer ces égalités sur les couples. L'injection globale nécessaire aux coûts analytiques est auditée mathématiquement ci-dessous, sans prétendre à une nouvelle estimation Lean.

P1 et P2 sont deux égalités exactes distinctes. Leur raccord quantitatif via (54) est seulement écrit : W=−S(N)+delta s'applique aux points premiers n>Q, pas aux points composites de la grille. Sur ce support, n dépasse tous les k<=Q, donc le masque de W devient celui de N. Le bulk m>=M est automatique dans J2 au seuil source car p*q>a^2>=N^(7/8), avec les marges entières. L'endpoint log(R/m)A_N(R) est conservé, et son coût est G54/u. Le total d'erreur des W de tout J2 est <=N*G54 par injection, une fois seulement. Aucun nouvel axiome de (54) n'est créé.

## 5. Audit indépendant P3 : racines, masque, CRT et constante

Dans n(3n−2N), pour N pair et 3∤N, les nombres de racines sont rho(2)=1, rho(3)=1 ; pour l>3, rho(l)=1 si l|N et 2 sinon. À 3, la seconde forme est la constante −2N non nulle ; à l>3, les racines 0 et 2N/3 coïncident précisément quand l|N. Ce sont donc exactement les racines du masque K=3N. Le produit source donne S(3N)=2S(N), sans omettre le facteur3.

Le crible fini (44) s'adapte à ces nombres de racines : pour chaque racine CRT dans un intervalle de longueur L, le compte est <=L/r+1. Le reste complet conserve rho(lcm(d,e))<=lcm(d,e)<=d*e. Avec |lambda_d|<=1 et d,e<z, le double reste est <=z^4. Le +1 n'est jamais supprimé par une règle de multiples positifs : ce sont ici des AP incomplètes.

L'uniformité en masque est explicite. Pour y=z^(1/16), la masse eulérienne positive E(y)=prod_(l<=y)(1−rho(l)/l)^(-1) porte la probabilité carré-libre g(d)/E(y). Son espérance de log d est sum rho(l)log(l)/l<=4+4log y grâce à l'input global θ(t)<=2t, indépendamment des facteurs de3N. Pour log z>=16, Markov fournit G(z)>=E(y)/2. L'identité des facteurs, y compris2, donne E(y)>=C2/S(3N) fois le carré du produit harmonique. Le minorant C2>=2541/4096 de la source et log y=(log z)/16 donnent

```
G(z)>=2541/(2097152*S(3N))*(log z)^2.
```

Avec z=N^(1/8), l'inverse de cette constante multiplie par64 : C_sieve=134217728/2541. Dans le central, les deux vrais premiers dépassent z et l'intervalle a longueur <=N. Donc P3, I_common,central<=C_sieve*S(3N)*N/u^2+sqrt(N), est valide sous le crible source. Aucune distribution de premiers en AP ou uniformité de J_c n'est supposée.

## 6. Audit P4/P5 : gains communs et marges effectives

Dans d*t<=N/6, le quotient (N−d*t)/(N−3d*t) est croissant avec d*t et <=5/3 ; log(5/3)<1. La décomposition canonique de m=N−n en petit cœur et ses deux facteurs >a, avec p<q, injecte ces incidences dans n. Aucun facteur de multiplicité en c,p,q ne multiplie le coût.

Pour μ(d)=+1, le modèle commun est négatif et conservé. Pour μ(d)=−1, le majorant positif central est

```
2*C_sieve*S(N)^2*N/u^2+S(N)*sqrt(N).
```

S(N)<3ell est ici un input acquis du §12.7, avec la version universelle2.50637 mentionnée par la source ; la borne plus faible 10sqrt(u) ne suffirait pas à ce paiement. Après normalisation par N/(u ell), P4 donne 18*C_sieve*ell^3/u+3u*ell^2*exp(−u/2). À u0=10^24, ell0<56, 18*C_sieve<10^6 ; le premier terme est <1.75616*10^(−13)<2*10^(−13). Le second est <10^(−13), par e>2 et la domination exponentielle. Les dérivées 3/ell−1 et 1+2/ell−u/2 sont négatives ensuite. P4 est donc effectif dans son domaine central.

Pour le commun entier, Q<n3<n<N et log(n/n3)<=log(N/n3). Si Q<=Y<=N, n3<=Y impose un intervalle en n de longueur <=Y/3. Ses comptes CRT sont <=Y/(3r)+1<=Y/r+1. On peut prendre z=Y^(1/8) : les deux premiers sont >Q>N^(1/8)>=z au seuil source. Le même minorant G reste uniforme dans le masque3N, même si la longueur est Y. Ainsi

```
I_common(n3<=Y)<=C_sieve*S(3N)*Y/(log Y)^2+sqrt(Y).
```

Q>=N^(3/4)/8 implique log Y>=log Q>=2u/3 au domaine retenu, et log z>=16. La formule de couches est une identité positive exacte pour une somme finie : sum log(N/n3)=integral_Q^N I_common(n3<=Y)dY/Y. Les intégrales sont <=9*C_sieve*S(3N)*N/(4u^2)+2sqrt(N). Multiplier par S(N) donne

```
E_common=(9/2)*C_sieve*S(N)^2*N/u^2+2S(N)*sqrt(N).
```

Le signe favorable −S(N)A_common,+ reste entier. Avec S(N)<3ell, le ratio de l'erreur est <=(81/2)*C_sieve*ell^3/u+6u*ell^2*exp(−u/2). (81/2)*C_sieve<3*10^6 et ell0^3<2*10^5 donnent <6*10^(−13) pour le premier terme ; le second est <10^(−13). Les mêmes décroissances donnent P5<10^(−12)N/(u ell) pour tout u>=10^24. P5 remplace P4 si l'on traite le commun entier ; les deux budgets ne s'ajoutent pas.

Ce paiement est une preuve écrite sous les inputs source. Il ne certifie pas S(N)<3ell ou le crible dans Lean et ne provient pas du banc N=10^8, où aucune base conjointe μ(d)<0 n'existe pour ces deux t.

## 7. P6, témoins et obligations restantes

K2 contient déjà H2−S(N)M2 et le crédit rough c=1. L'appairer change leur représentation, sans créer une seconde masse négative rough. P6 conserve −R_pair+[S+epsilon_W]Theta_prime, H2, S*Delta_single, S*Delta_face, −S*A_common,+, puis E_common, N*G54 et l'unique E_corner de l'union hors bulk. Le paiement de l'erreur J2 vaut N*G54 une fois pour tous ses c, incluant c=1 ; il ne s'ajoute pas à une erreur déjà facturée séparément sur ce même bloc. P6 est donc un majorant partiel cohérent pour N pair,3∤N. Pour 3|N, l'extraction n'est pas employée et le moment initial reste entier.

Le témoin conjoint d=1,p3167,q3169 garde le principal commun négatif et le bracket entier positif par son entropie. Le singleton d=1,p3167,q3191 a i=0,j=1 : sa vraie contribution est +log n3, et pas log(n3/n). La face d=7 reste seule lorsque3d>C_t ; aucun log positif de n3 hors domaine n'est inséré. Les falsificateurs ne sont pas des erreurs Lean. Le bas r<=alpha du point c=3 porte −log3 tandis que l'annulus est nul : son entropie n'est pas payée par la bande acquise.

Ni le crible des incidences conjointes, ni P1/P2, ni E_common ne paie H2, Delta_single, Delta_face, J0 ou J1. Aucun minorant de R_pair ou A_common,+ n'est supposé. Le ledger reste D_N=B_prime^a+B_pp^a+P_band+Z_face+I_alpha+2max(e,0). I, les properpowers et la face harmonique gardent leurs paiements une fois ; le seuil BV supplémentaire de P_band et le pont couvert e restent ouverts. Les quatre Möbius HH, les sélecteurs natifs et leur phase physique constante ne sont pas remplacés par cette extraction.

## 8. Compilation honnête et artefacts finaux

Un premier préflight a rencontré KeyError sur full_partitions, dict à deux entrées : corrigé avant tout appel Lean, puis enrichi de contrôles de partition/P2. Ce n'est pas une erreur du compilateur.

Les cinq vraies tentatives sont conservées avec leurs snapshots et logs :

| Tentative | Résultat |
|---|---|
| 1 | Erreurs techniques : orientation de Nat.coprime_of_lt_prime ; méthode mul_left absente ; inférence implicite du point dans P2 ; facteurs constants non extraits des sommes. Corrections par symétrie/mul_right, paramètres explicites et Finset.mul_sum. |
| 2 | U2/P1 locale, partition et P2 compilées. |
| 3 | Après assemblage de P1 sommée, omega n'a pas résolu trois égalités Nat.sub avec quotient opaque. Remplacement par Nat.sub_pos_iff_lt et Nat.sub_add_cancel. |
| 4 | P1 sommée et P2 compilées. |
| 5 | Source finale, domaines N pair/t unitaire explicites et toutes les déclarations inspectées : code de sortie0. |

Les candidats en erreur ont des sorryAx automatiques dans leurs sorties et ne sont pas des certificats. Aucune balise sorry/admit, déclaration axiom ou native_decide n'a été écrite. La sortie finale inspecte **19 théorèmes et15 définitions** : seuls propext, Classical.choice et Quot.sound apparaissent ; bulkCap n'a aucun axiome. Les erreurs réparées ne sont pas décrites comme des preuves d'un mur de la parité.

| Artefact final | SHA-256 |
|---|---|
| lean/ThreeAdicPrimePairing.lean | b3c22b714566b3d6e1fa864c4414201c9a2215c506350bdf1c8373a598d26f48 |
| role4_build/ThreeAdicPrimePairing.olean | 25cddc8edd9a9bd2b027846196faca5959664514cf67671671c08ce1d18ceac4 |
| role4_build/attempt05.log | fb630c246c30538e6375b952f4d3ff0da0caa4af47b1cd5df6a6ae96f9cce6e5 |
| role4_build_receipt.json | 3c66240216e4e5b3e985632618a3f92233a1445a2d7ae6aa955c75fd61639a4a |
| role4_build.py | bac7e7d516d426cffe749fac97b44a07b3372bfec4dfe7090ead7ef385c741e5 |
| copie source U1 | 25f38fcb6f84b73551bf9d4131745d5c234a3187dd3e92a8402f8e81b721b447 |
| U1 olean reconstruit neuf | 733128e14b663152143ea15a6939437691d0d3477837f10b686def852a56cc6b |

Verdict : COMPILED_ACTUAL_U2_P1_P2_WITH_GEOMETRIC_FACES; COMMON_MODEL_ONLY_PAYMENT_WRITTEN_VALID; SINGLETON_FACE_ENTROPY_COMPENSATION_OPEN; PHYSICAL_BAND_ONSET_UNEVALUATED; COVERED_E_UNPAID; VICTORY_FALSE. Source, build et présent rapport sont gelés à cette clôture ; le SHA du rapport est transmis séparément à root et au Juge.
