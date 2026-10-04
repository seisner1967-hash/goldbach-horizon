# Boucle 11 — préfixe bas, coefficients AP et compensation bilatérale

Agent 2. Seul ce rapport est écrit. Le PROBE11, le retour final10, les audits finaux `agent3_formalisation.md` et `agent4_formalisation.md`, le rapport1 final10 et les §§6,12.2 de la monographie ont été lus. Les fichiers antérieurs et Arbor restent inchangés. Aucun ancien banc PASS n'est rejoué.

**Résultat : compensation de parité non obtenue.** Le calcul explicite ci-dessous conserve le principal du préfixe ENTIER, y compris r<=alpha. Il donne un contrat arithmétique falsifiable pour les coefficients AP à lcm(r,d²), avec intersections et nonunités exactes. Le principal -S(N)N est celui de J_ref dans la source : il n'est pas une nouvelle découverte. Après son extraction, le véritable moment bilatéral avec les valeurs de Möbius reste impayé. Un minorant pointwise positif du poids couplé échoue sur les composites carrés-libres de parité impaire; cela ne prouve aucune impossibilité globale.

## 1. Quatre lignes et deux directions réellement examinées

Mechanism: Déplier le carré-diviseur du préfixe U_a entier avant l'estimation AP, conserver son principal -S(N)N, puis confronter ce principal au poids bilatéral réel mu(m)^2*Lambda(m)+S(N)*mu(m).

Hypothesis: Uniquement les coefficients Möbius/Mangoldt/totient usuels, lcm avec intersections, BV acquis de Lambda SEULE après expansion exacte, et Mertens ordinaire acquis pour un coefficient fixe; aucune petite énergie ni minoration de la compensation supposée.

Observable: Coefficient AP local réel A_N(r), tête+queue sans ajout de mu(m)^2 à la tête, préfixe bas séparé de l'annulus, et signe négatif exact du poids bilatéral sur un véritable triprime m avec N-m premier.

Conflicts: La référence et F_N source restent signés; le principal est acquis au §6, non un nouveau gain; Q demeure original, modèle k libre, raw properpowers, unités, +1 et quatre Möbius conservés; aucune extension BV à mu*Lambda.

La première direction cherche un coefficient estimable de la vraie référence, au lieu d'un transfert de norme du Gram nu. La seconde cherche à utiliser ce coefficient comme un minorant bilatéral du moment restant. La première fournit le raccord local ci-dessous; la seconde ne fournit pas la minoration requise. Ces deux résultats sont distingués jusqu'au verdict.

## 2. Route, conventions et préfixe entier

On conserve N pair, u=log N, ell=log u, alpha=ceil(N^(1/4)), Q=floor((N-1)/alpha), a=a9=ceil(N^(7/16)). Les deux fronts du bracket B^a sont a*k<m. Les conventions sont celles de boucle10 : W_kernel emploie log(k/m) et a le principal -S(nN); W_positive=-W_kernel a le principal +S(nN).

Avec n=N-m, Lambda_N(n)=Lambda(n)1_(n>1)1_(gcd(n,N)=1), définir

```
U_a(m)=sum_(r|m,r<=a)mu(r)*log r,
T_a^Lambda=sum_(1<=m<=N-2)Lambda_N(N-m)*mu(m)^2*U_a(m).
```

Le premier axe de T_a^Lambda garde les propres puissances premières unitaires. Le facteur mu(m)^2 est celui déjà justifié APRÈS construction du bracket entier U1. Il ne masque pas n, ni un facteur court de HH. Le préfixe est la somme DISJOINTE de r<=alpha et alpha<r<=a. L'estimation de l'annulus ne paie pas le premier morceau.

U1 et E3 sont certifiées; elles ne sont pas reprouvées ici. En particulier U1 donne pour le physique entier

```
P_a(m)=mu(m)^2[-Lambda(m)-U_a(m)].                  (B1)
```

Les masques physiques de k et le cap Q sont ceux certifiés dans U1. Le modèle conserve tous les k unitaires sous ce cap; il n'est pas une somme sur les seuls diviseurs de m. Le terme k=1 reste annulé conjointement au même point.

## 3. Expansion AP exacte avec queue explicite

Pour D>=1, posons

```
F_D(m)=sum_(d²|m,d<=D)mu(d),
R_D(m)=sum_(d²|m,d>D)mu(d).
mu(m)^2=F_D(m)+R_D(m).
```

La tête est F_D(m), et NON mu(m)^2*F_D(m). Cette dernière expression détruirait la cancellation nécessaire sur un m non carré-libre. La queue reste présente, même lorsque le produit final mu(m)^2 est zéro.

Avec X=N-1, noter la véritable progression

```
Psi_N(X;q,N)=sum_(n<=X,n congruent N modulo q)Lambda_N(n).
```

Les n=1 sont Mangoldt zéro. Le m=0 serait hors support parce que n<=N-1. Sur Lambda_N(n) non nulle, m=N-n est unitaire à N; tout r|m et tout d²|m sont donc unitaires à N. Il vient exactement

```
T_a^Lambda = H_a,D + Tail_a,D,
H_a,D=sum_(r<=a,(r,N)=1)mu(r)log r*
         sum_(d<=D,(d,N)=1)mu(d)*Psi_N(X;lcm(r,d²),N),
Tail_a,D=sum_m Lambda_N(N-m)*U_a(m)*R_D(m).         (B2)
```

Les r ou d non carrés-libres ont un coefficient mu nul. L'AP n'a pas été complétée à un intervalle réel : q|m est équivalent à n congruent N modulo q, avec le vrai cap entier X. Si une selection finie E des n est testée, LA MÊME E doit définir chaque Psi_E; une sélection ne remplace pas Psi_N globale.

### Regroupement exact des collisions

Pour r,d carrés-libres, écrire g=gcd(r,d), d=b, r=c*g. Alors gcd(b,c)=1 et

```
lcm(r,d²)=b²*c,
w_a,D(b²*c)=mu(b)mu(c)*
                 sum_(g|b,c*g<=a)mu(g)log(c*g), b<=D.  (B3)
```

La tête B2 est sum_q w_a,D(q)Psi_N(X;q,N). Les intersections g|b sont conservées. Aucun front inférieur alpha<c*g n'apparaît ici : B3 concerne le préfixe ENTIER. Le head de boucle8/9 avait cet annulus et des mêmes coefficients pondérés de taille <=u*tau(b); reprendre sa preuve de contrôle AP ne transforme pas son principal nul en celui du préfixe entier.

Les moduli vérifient q<=a*D², gcd(q,N)=1. L'AP incomplète et son +1 éventuel sont dans Psi_N et dans l'erreur AP exacte ci-dessous. Aucun +1 n'est supprimé par une densité heuristique de primes.

## 4. Coefficient de référence réel, local p-adique

Pour r>=1, définir le coefficient effectif de la référence

```
A_N(r)=1_(gcd(r,N)=1)*
       sum_(d>=1,(d,N)=1)mu(d)/phi(lcm(r,d²)).       (B4)
```

La série en d est absolument convergente pour r fixé. Le masque extérieur est indispensable : quand (r,N)>1, aucune fibre physique unitaire ne porte r. Employer la formule de produit sans ce masque donnerait une densité principale illégitime.

Pour r carré-libre et unitaire à N, poser

```
V_N=prod_(p prime,p nondivisor N)(1-1/[p(p-1)]).
```

Les facteurs sont positifs : N pair implique que p=2 est exclu. La somme locale sur l'exposant de d donne

```
p|r, p nondivisor N : 1/(p-1)-1/[p(p-1)]=1/p;
p nondivisor r*N   : 1-1/[p(p-1)];
p|N                : seul d-exposant0 est admissible.
```

Ainsi

```
A_N(r)=V_N*prod_(p|r)(p-1)/(p²-p-1).               (B5)
```

Pour p²|r et p nondivisor N, les deux choix d=1 ou d=p donnent le MÊME exposant >=2 de q, donc leur différence est zéro. A_N(r)=0 pour r non carré-libre. Le coefficient mu(r) l'aurait déjà éliminé dans B2; cette observation ne justifie pas d'étendre B5 à ces r.

### Premier lemme Lean réellement arithmétique proposé

Soit P un entier carré-libre unitaire à N et r|P. La variante FINIE est

```
sum_(d|P)mu(d)/phi(lcm(r,d²))
 = (1/r)*prod_(p|P,p nondivisor r)(1-1/[p(p-1)]).   (B6)
```

Elle a les vrais mu, phi, lcm et diviseurs, sans coefficient libre. Si r|P, r est carré-libre; le garde unitaire de la référence est annoncé séparément. La preuve doit partitionner les diviseurs d suivant p|d puis établir les deux valeurs locales ci-dessus. C'est un certificat auxiliaire de coefficient AP; il n'implique aucune victoire et n'est pas proposé comme une estimation de la compensation.

Le support d|P de B6 n'est PAS le support d<=D de la tête B2. Le certificat de produit fini peut justifier les facteurs de B5 après passage à la limite absolument convergent; il ne remplace pas la tête tronquée. Le passage du support d<=D à B4 garde précisément B9, et un produit fini numérique n'évalue pas la queue infinie.

## 5. Le principal ne disparaît pas

Le calcul confirme celui de la source. Écrire g_p=(p-1)/(p²-p-1). Le coefficient

```
c_N(r)=mu(r)*1_(r,N)=1*prod_(p|r)g_p
```

a la convolution exacte avec mu(r)/r, dont le facteur h'_N satisfait

```
h'_N(p^j)=p^(-j),                         p|N;
h'_N(p^j)=-p^(-j)/(p²-p-1), j>=1,        p nondivisor N.
```

Puisque p>=3 dans la seconde ligne, ses valeurs absolues sont dominées terme par terme par celles du h_N de §12.2, qui a dénominateur p-1. Les moments absolus et demi-moments acquis (50) s'appliquent donc par domination, et la preuve de transport (51)/(52) emploie le même Mertens ordinaire, sans poids prime mobile.

Le produit au principal donne exactement

```
V_N*sum_d h'_N(d)=S(N).
```

Localement, pour p nondivisor N,

```
(1-1/[p(p-1)])*(1-g_p)/(1-1/p)
   =p(p-2)/(p-1)^2=1-1/(p-1)^2.
```

Pour p|N, le facteur est p/(p-1); le p=2 donne 2. Ces produits recombinent S(N), avec TOUS les premiers du masque.

Le préfixe logarithmique est W'_(a)+log(a)A'_(a), pas seulement W'_(a). Son endpoint est présent. Avec a>=N^(1/5), a<N, u>=10^6, la même démonstration de l'enveloppe (54), appliquée à h'_N dominé, donne

```
|sum_(r<=a)mu(r)log r*A_N(r)+S(N)|<=G54/u,
G54=4*10^8*u^5*exp(-sqrt(u)/60)+160*u²*exp(-u/40).   (B7)
```

L'exposant source littéral demeure -sqrt(u/60), et celui affiché est un affaiblissement valide. Ce n'est pas une importation gratuite de la borne 1/phi au nouveau coefficient : le facteur de convolution et sa domination ont été indiqués. Aucune phase additive ou rough mask non autorisé n'est introduit.

En particulier le principal de T_a^Lambda est -S(N)*(N-1), et non zéro. Remplacer N-1 par N coûte explicitement S(N). Le §6 de la monographie définit déjà j_alpha=-U_alpha, J_ref et E_J=S(N)N-J_ref. B4–B7 retrouvent ce raccord de référence, à la face a; ils ne constituent pas une nouvelle preuve du contournement de parité.

## 6. Audit quantitatif avec les queues, les unités et l'onset

Les deux queues suivantes peuvent être majorées indépendamment, sans effacer la référence. Posons L_D=1+log D. Le comptage positif donne

```
|Tail_a,D|<=44*N*u²*(1+u)*L_D²/D.                  (B8)
```

Dérivation : |U_a(m)|<=u*tau(m), Lambda_N<=u. Pour d carré-libre, tau(d²)=3^omega(d)=d_3(d); tau(d²v)<=tau(d²)tau(v). La somme des tau(v), v<=N/d², est <=(N/d²)(1+u). La queue sum_(d>D)d_3(d)/d² est <=44L_D²/D, par dyades et sum_(d<=x)d_3(d)<=x(1+log x)^2. Les séries dyadiques employées sont sum2^(-j)=2, sum(j+1)2^(-j)=4 et sum(j+1)^2*2^(-j)=12; log2<=1 donne 4L_D²+16L_D+24<=44L_D². Ce compte utilise floor(N/d²)<=N/d², pas un retrait arbitraire du +1 d'une AP générale.

Le remplacement du coefficient tronqué en d par B4 a sa SECONDE queue principale, distincte :

```
X*sum_(r<=a)|mu(r)|log r*
       sum_(d>D,(d,N)=1)|mu(d)|/phi(lcm(r,d²))
 <=396*N*u*(1+u)*L_D²/D.                           (B9)
```

Pour r,d carrés-libres, phi(lcm(r,d²))=phi(r)*d*phi(d)/phi(gcd(r,d)). Reparamétrer r=g*h avec g|d donne sum_h1/phi(h)<=3(1+u), puis au plus tau(d) choix de g. Il reste sum_(d>D)tau(d)/(d*phi(d)); la borne d/phi(d)<=3(1+log d) et la même sommation dyadique la majorent par 132L_D²/D. Les facteurs 3 et 132 expliquent le 396. Les unités sont supprimées seulement dans ce majorant POSITIF.

L'erreur AP à garder est

```
E_AP^N(D,a)=sum_q |w_a,D(q)|*
             max_(y<=X)|Psi_N(y;q,N)-y/phi(q)|,      (B10)
```

sur les q unitaires de B3. Le BV acquis de Lambda ordinaire peut être utilisé APRÈS B2/B3 : les poids mu(r),mu(d) sont indépendants de n. Il ne fournit pas une borne de mu(m)Lambda(n). La différence entre Psi_N et la somme Lambda ordinaire garde les n=p^j à base p|N, et doit être chargée dans B10. Une expression exacte est sum_(p|N,p^j<=X)log p*sum_(q|N-p^j)|w_a,D(q)|. Par tau(z)<=2^2040*z^(1/8) déjà audité, elle est au plus 2^4080*N^(1/4)*u^3/log2 : le poids intérieur est <=u*tau(N-p^j)^2, et la masse de ces bases est <=u*omega(N)<=u²/log2. Les properpowers à base unitaire restent dans Psi_N; elles ne sont pas retirées ici.

Avec D=floor(N^(1/64)), q<=aD²<=2N^(15/32), les deux queues sont des puissances de N et le poids satisfait |w|<=u*tau(q). La preuve weighted-BV du head9 peut être reprise pour ces tailles : troncature de tau, moment d_4 et all-prefix BV. Elle implique une portée qualitative O_A(N/u^A) ÉVENTUELLEMENT, avec un seuil BV supplémentaire non évalué. Ni ce seuil ni ses constantes ne sont déduits automatiquement de u>=10^24. La face basse change le principal, mais pas ce diagnostic de seuil.

Une borne complète explicite du défaut de référence est donc

```
|T_a^Lambda+S(N)N|
 <= B8+B9+E_AP^N(D,a)+N*G54/u+S(N).                (B11)
```

B11 est une dérivation de la référence avec tous ses postes. Elle ne doit pas être annoncée comme un nouveau contrôle de D_N : c'est le type de E_J déjà prévu par la source. La sommation finie r<=alpha n'a jamais été effacée.

## 7. Direction bilatérale : poids réel, minorant et gap

Posons le véritable poids

```
G_N(m)=mu(m)^2*Lambda(m)+S(N)*mu(m).                (B12)
```

Le garde mu(m)^2 de la première partie est indispensable : écrire Lambda(m)+S(N)mu(m) sur tout le raw réintroduirait les propres puissances du SECOND axe, annihilées par le coefficient entier. Le premier axe conserve Lambda_N et ses propres puissances.

Journal avant gel : la formulation exploratoire Lambda(m)+S(N)mu(m), correcte seulement sur m carré-libre, a été remplacée par B12 avec son vrai garde mu(m)^2 pour le raw complet. Ce raccord a été signalé à root avant toute clôture ou tentative Lean. Ce n'est pas une erreur du compilateur et le faux poids non gardé n'est pas soumis à formalisation.

Ce poids vaut log m-S(N) pour m premier, +S(N) pour m composite carré-libre avec mu(m)=+1, -S(N) pour m composite carré-libre avec mu(m)=-1, et zéro pour m non carré-libre. Le m=1 donne S(N); il est dans le coin où le modèle réel est vide et où aucune extraction principale gratuite n'est permise.

L'idée du minorant était que la masse principale de la référence puisse être fournie par une somme positive de G_N, en gardant les primes favorables et les composites. Un minorant pointwise nonnégatif est FAUX sur tout composite carré-libre de parité impaire. Un poids positif de type crible ne paie donc pas gratuitement le terme négatif: il lui faudrait une information sur les véritables masses corrélées avec n premier. Aucun minorant bilatéral indépendant de ces masses n'a été obtenu.

### Objet précis qui reste impayé

Noter F_unit=sum_(n<N)Lambda_N(n)mu(N-n), et conserver F_N SOURCE entier, sans redéfinition :

```
F_N=sum_(1<=n<N)Lambda(n)mu(N-n)=F_unit+F_nonunit.
```

F_nonunit est la somme signée des véritables n à base première divisant N; elle ne disparaît pas d'une identité. R_unit=sum Lambda_N(n)mu(m)^2 Lambda(m) garde les retained properpowers du premier axe et les faces unitaires. Le moment bilatéral restant est

```
M_bilateral=R_unit+S(N)*F_unit-S(N)*N
           =sum_(n<N)Lambda_N(n)G_N(N-n)-S(N)*N.     (B13)
```

Après extraction du modèle harmonique, une majoration UNILATÉRALE de B^a demanderait une minoration de B13 avec le bon budget, les erreurs de B11, les coins et le modèle couplé restant. Cette minoration n'est pas prise comme hypothèse. Le BV employé dans B11 n'estime pas le second terme signé de B13 et ne minore pas R_unit.

Sur le bulk, la base première p de n=p^j unitaire donne S(nN)=S(N)(1+1/(p-2)); la version n-2 est réservée à n premier. Le coût de mobilité peut être conservé sur le raw en regroupant les exposants j : sum_(j,p^j<N)log p<=u pour chaque base p, puis sum_(p>=3,p<N)1/(p-2)<=1+u. Sa charge est donc <=S(N)u(1+u), mais elle ne change pas B13. Un coin ou un préfixe vide garde son modèle direct au lieu d'un principal ajouté. Ce petit poste n'est pas revendiqué comme le progrès recherché.

Le raccord source déjà acquis R_unit=R_sf+P_ret-T_pairs permet d'écrire le même moment avec R_sf et F_N, en conservant P_ret, T_pairs et F_nonunit SIGNÉS. Il ne justifie ni de supprimer F_N ni de le remplacer par une norme. C'est exactement la compensation autour de S(N)(N-F_N) de Proposition6.2; la présente piste n'en dérive pas une nouvelle minoration.

Les quatre Möbius d'un HH restent dans leurs coefficients lorsqu'on décompose B13; une estimation BV après B2 ne diagonalise pas ce HH. La phase native reste 1 sur q|k. Les secteurs petits/grands, les nonunités, les fibres tronquées et leurs +1 ne sont pas absorbés dans un prétendu reste petit.

## 8. Contrat numérique courant et falsificateurs

Le rôle6 de boucle11 a reçu B2–B6 avec N=100000000, a=3163, alpha=100, Q=999999. Le coefficient INFINI B4 ne doit pas être testé par un produit fini annoncé comme complet. La comparaison porte sur B6, avec un produit fini P contenant les bases de r et toutes les exclusions unitaires.

Ratios attendus sous ces gardes : A_P(3)/V_P=2/5, A_P(7)/V_P=6/41 et A_P(21)/V_P=12/205. L'intersection r=3,d=3 impose q=lcm(3,9)=9 et phi(q)=6, et non q=27,phi=18. r=5 donne zéro comme coefficient réel à N=10^8; r=9 donne zéro par cancellation locale, plutôt que la formule squarefree 2/5. Ces tests précèdent toute proposition Lean.

Les premiers neufs signalés par le rôle6 sont : m=11,n=99999989, où U_low=-log11 et l'annulus est zéro; m=411=3*137,n=99999589, où U_low=-log3 et U_annulus=+log3, donc U_a=0. Ils distinguent le bas, la bande et leur somme.

La queue possède un témoin indispensable : m=31047267=3*3217²,n=68952733 premier. U_a=-log3 tandis que mu(m)^2=0. Pour D<3217, la tête F_D=1 donne -log n log3 et la queue d=3217 donne +log n log3. Multiplier la tête par mu(m)^2 lui donnerait artificiellement zéro et détruirait la véritable identité tête+queue.

Le rôle6 a fourni le nouveau triprime m=483=3*7*23, n=99999517 premier. Le poids B12 vaut exactement G_N(483)/S(N)=-1 : le minorant G_N>=0 est rejeté AVANT compilation, sans signe numérique d'une série infinie à estimer; S(N)>0 est acquis. Il a aussi fourni m=927=3²*103,n=99999073 premier : pour r=3,d=3, lcm=9 divise m tandis que le faux modulus 27 ne le divise pas, donc l'erreur d'intersection est détectable dans la progression réelle, pas seulement dans un produit jouet.

Le reçu courant `round11/witnesses.json` porte VERIFIED_NEW_FINITE_WITNESSES_ONLY. Il confirme les points neufs et leurs axes premiers; il ne certifie pas B7–B11. À la clôture de ce rapport, le rôle6 prépare encore le banc local B6 et tête+queue : aucun PASS de ce banc complet n'est inventé ici. Root recevra son gate directement avant toute éventuelle compilation. Aucun ancien témoin PASS n'est rejoué, aucune Psi_N globale à N=10^8 ni D_N global n'est calculé par ce rapport.

## 9. Verdict et ledger conservé

La route unique demeure

```
D_N=B_prime^a+B_pp^a+P_band^{>=2}+Z_face^{>=2}
       +I_alpha+2max(e,0).
```

Le passage par B^a=B_prime^a+B_pp^a est exact; les properpowers du premier axe ne sont pas supprimées du raw pour obtenir B11/B13. Leur paiement de B_pp est appliqué une fois si l'on revient au ledger premier. La référence B11 n'ajoute pas une deuxième route ni une deuxième allowance B_H. Les fees de I, Z_face et properpowers restent ceux retenus, une seule fois. Le seuil BV supplémentaire physique et 2max(e,0) restent ouverts.

La candidature B6 est un certificat local possible, pas un contournement. Le principal de référence est conservé et raccordé au §6, pas effacé ni revendiqué comme nouveau. La direction bilatérale laisse exactement B13 non minoré; adopter cette minoration comme hypothèse serait circulaire. Aucune conclusion d'impossibilité globale n'est tirée de l'échec du minorant pointwise.

Statuts : EXACT_WEIGHTED_LCM_COEFFICIENT_CANDIDATE; LOW_PREFIX_AND_REFERENCE_PRINCIPAL_PRESERVED; SOURCE_REFERENCE_REDISCOVERY_NOT_PARITY_GAIN; WEIGHTED_BV_THRESHOLD_UNEVALUATED; BILATERAL_SIGNED_MOMENT_OPEN; VICTORY_FALSE.

TERMINÉ. Rapport mathématique définitif de ce rôle, avec statut numérique limité aux nouveaux témoins vérifiés et gate de coefficient annoncé séparément par le rôle6. Le SHA-256 est transmis à root hors du fichier pour éviter une empreinte autoréférente. Aucune victoire, minoration couplée ou estimation de D_N n'est revendiquée.
