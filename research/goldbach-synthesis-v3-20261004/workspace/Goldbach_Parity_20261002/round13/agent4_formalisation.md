# Rôle 4 — variation du vrai noyau harmonique et audit de l’échange

**FINAL — compilation réussie ; paiement écrit partiel audité ; victoire fausse.** `HarmonicKernelVariation.lean` prouve 16 théorèmes nouveaux et définit 5 objets, sur le vrai `GoldbachRound11.harmonicKernel`. Le module raccorde le masque, le front strict et la variation entière tête/queue. Il fournit aussi une borne absolue finie indépendante sur les coefficients réels de Möbius/totient. Le paiement en puissance `21N^(31/32)u²` est validé ci-dessous comme preuve écrite ; il n’est pas présenté comme un théorème Lean ni comme une compensation globale de D_N.

Le rôle4 réutilise le slot de l’idéateur2 sur instruction du coordinateur. Son rapport2 FINAL est conservé octet pour octet. Seuls `round13/lean/HarmonicKernelVariation.lean`, `round13/role4/**`, ce rapport et `role4_final_receipt.json` sont écrits. Aucune archive, source ancienne, banque numérique gelée ou ancien PASS n’est modifié/rejoué.

Entrées : FINAL1 `agent1_exchange.md`, SHA `2b64a5434c1dfde766436d5abd44b62a2714615992193a3f0e21bf90554d8c54` ; FINAL6, SHA `00e234c7543fbb77d41f3f7d297c15b6bb649b6d940179509f7d916e68bb6bc0` ; `numeric_manifest.json`, SHA `c8468f94a118555c842a47879772620bf9dca9d520a6b89cec54f2895a38f932`. Ses onze bindings sont recalculés, sans exécuter leurs producteurs. Le registre de 514 anciens artefacts et les PDF/ZIP originaux sont vérifiés par empreintes seulement, résultat PRESERVED. Une contre-lecture indépendante de X8–X17 par le rôle6, strictement en lecture seule, concorde avec le présent audit.

## 1. Ce qui est compilé exactement

Namespace `GoldbachRound13.HarmonicKernelVariation`, import `ThreeAdicPrimePairing`. Les deux dépendances sont reconstruites depuis des copies exactes sous `role4/dependencies`, avec Lean4.15.0 et les bibliothèques mathlib locales au commit fourni `9837ca9d65d9de6fad1ef4381750ca688774e608`. Aucun ancien olean Goldbach n’est utilisé. La source historique `ShortDivisorComplement.lean` garde SHA `25f38fcb6f84b73551bf9d4131745d5c234a3187dd3e92a8402f8e81b721b447` ; `ThreeAdicPrimePairing.lean` garde SHA `b3c22b714566b3d6e1fa864c4414201c9a2215c506350bdf1c8373a598d26f48`.

Les définitions nouvelles sont `unitCoefficient`, `unitPrefix`, `unitLogPrefix`, `unitLogTail`, `sourceFront`. Le coefficient est littéralement `if Coprime(k,N) then mu(k)/phi(k) else 0`, où mu vient de la fonction de Möbius de mathlib et phi est `Nat.totient`. Le front est `min Q ((m−1)/a)`.

| Conclusions nouvelles | Portée |
| --- | --- |
| `prime_above_cap_units`, `strict_front_iff`, `front_filter_eq` | Premier n>Q : masque `(k,nN)=1` exactement réduit à `(k,N)=1` ; front strict `ak<m` exactement `k≤(m−1)/a` |
| `actual_kernel_eq_prefix`, `source_front_mono`, `source_cap_inactive` | Raccord au vrai harmonicKernel ; monotonie des deux fronts ; cap original inactif sous alpha≤a et m≤N |
| `interval_split`, `interval_disjoint`, `prefix_split` | Partition entière disjointe tête et queue, sans omettre k1 ou un endpoint |
| `logarithm_change`, `prefix_log_change`, `actual_kernel_variation` | Identité X7 avec les deux dénominateurs logarithmiques réels |
| `coefficient_abs_le_reciprocal`, `prefix_abs_bound`, `tail_abs_bound`, `actual_kernel_abs_variation` | Borne absolue finie avec vrais mu/phi, sans hypothèse de petitesse du noyau ou de la cible |

Écrire

\[
R_i=\min(Q,\lfloor(m_i-1)/a\rfloor),\qquad
A_N(R)=\sum_{1\le k\le R,(k,N)=1}\mu(k)/\varphi(k).
\]

Le théorème `actual_kernel_variation` prend uniquement `a>0`, `m_i>0`, `m1≤m0`, les deux n_i réellement premiers et `n_i>Q`. Sa conclusion est exactement

\[
W_a(n_1,m_1)-W_a(n_0,m_0)
=\log(m_0/m_1)A_N(R_1)
-\sum_{R_1<k\le R_0,(k,N)=1}
\frac{\mu(k)}{\varphi(k)}\log(k/m_0).
\tag{F7}
\]

`W_a` est le vrai harmonicKernel importé, et non une variable libre. Primalité et n_i>Q donnent `k<n_i`, donc `(k,n_i)=1` pour chaque k du cap ; le masque N reste explicite. Les divisions et logarithmes sont ceux des entiers castés en réels. Le k1 reste dans la tête. Si n_i≤Q ou n_i composite, ce théorème n’est pas utilisé pour l’échange.

Le théorème quantitatif fini compilé donne

\[
|\Delta W|\le |\log(m_0/m_1)|
\sum_{k=1}^{R_1}\frac1{\varphi(k)}
+\sum_{k=R_1+1}^{R_0}\frac{|\log(k/m_0)|}{\varphi(k)}.
\tag{Fabs}
\]

Les majorants peuvent inclure des nonunités, mais l’identité F7 conserve le vrai masque. Fabs utilise le théorème mathlib `abs_moebius_le_one`, la positivité du totient sur les indices positifs et l’inégalité triangulaire finie. Il ne suppose aucune petite énergie centrée, densité Goldbach ou conclusion recherchée. La borne de totient X8 et les profils fractionnaires ci-dessous ne sont pas inclus dans la partie Lean ; ils sont audités comme preuve écrite.

## 2. Audit indépendant X8–X17

On conserve N pair, `u=log N`, alpha et Q originaux, `a=ceil(N^(7/16))` et `M=ceil(N^(3/4))`. Les gardes de l’échange sont celles du FINAL1 : cinq premiers distincts `c<r<s≤a<p<q`, `rs=p−2>a`, `cr,cs≤a<crs`, unités N, `m0=cpq`, `m1=crsq`, `M≤m_i≤N−2`, et deux vrais premiers `n_i=N−m_i>Q`. Le paiement élémentaire demande u≥16 ; l’usage des acquis de signe conserve u≥10^24.

**X8 et X9.** Pour k≥1, factoriser en puissances premières. Pour `p^e`, `phi(p^e)^2/p^e=p^(e−2)(p−1)^2`. Lorsque e≥2, ce rapport est ≥1. Lorsque e=1 et p impair, `(p−1)^2≥p` pour p≥3. Le seul rapport <1 possible est p=2,e=1, et il vaut 1/2 ; il n’apparaît qu’une fois dans la factorisation. Le produit donne `phi(k)^2≥k/2`, avec k1 traité par phi1=1. Par positivité,

\[
1/\varphi(k)\le\sqrt2/\sqrt k.
\]

La borne finie `sum_{k≤R}1/sqrt(k)≤2sqrt(R)` se démontre sans input premier : `sqrt(k)−sqrt(k−1)=1/(sqrt(k)+sqrt(k−1))≥1/(2sqrt(k))`, puis télescopage. Donc pour R≥1,

\[
\sum_{1\le k\le R}1/\varphi(k)\le2\sqrt2\sqrt R<3\sqrt R.
\]

**Ceil, cap et X10.** Pour u≥16, `N^(7/16)≤a≤2N^(7/16)`. La monotonie de ceil donne alpha≤a, donc le Q source satisfait `Q≥floor((N−1)/a)≥floor((m_i−1)/a)` : le cap est inactif sans être changé. Puis `N^(5/16)≥e^5>8`, d’où `M≥2a+2`. Pour m1≥M,

\[
R_1\ge(m_1-a-1)/a\ge m_1/(2a)
\ge N^{5/16}/4,\quad R_0\le N/a.
\]

L’usage de floor `(m−1)/a` est indispensable. La marge `m1≥2a+2` justifie son coût entier, plutôt qu’une comparaison de quotients seuls.

**X11 et X12.** La différence de floors est au plus la différence des quotients plus 1. Garder ce +1 donne

\[
R_0-R_1\le2cq/a+1\le2N/a^2+1\le2N^{1/8}+1.
\]

Ici cpq≤N−2 et p>a impliquent cq<N/a. Comme m0/m1=p/(p−2), p≥4 et `log(1+t)≤t` donnent

\[
0<\log(m_0/m_1)\le2/(p-2)\le4/p\le4/a.
\]

Dans la queue, k≤R0≤(m0−1)/a<m0, puisque a≥1. Ainsi `|log(k/m0)|=log(m0)−log(k)≤u` pour chaque k positif. Aucune face n’est éliminée pour obtenir ce majorant.

**X13 à X15.** Fabs et X9 donnent une tête au plus `12N^(−5/32)`. Sur la queue, k>R1≥N^(5/16)/4 donne

\[
1/\varphi(k)\le2\sqrt2N^{-5/32}<3N^{-5/32}.
\]

Il y a exactement R0−R1 indices avant restriction des unités ; X11 garde leur majorant avec +1. La queue coûte donc au plus

\[
6uN^{-1/32}+3uN^{-5/32}.
\]

Comme N≥1 et u≥16≥1, la somme est ≤`(12+9u)N^(−1/32)≤21uN^(−1/32)`. Les constantes et exposants de X15 sont corrects. Aucun terme principal, diagonal ou de conducteur n’est caché dans cette borne élémentaire.

**X16.** La factorisation canonique assure les injections écrites de FINAL1. Le parent retrouve son unique petit premier c et ses deux grands premiers ordonnés p<q ; rs=p−2 avec r<s détermine l’échange. L’image retrouve son unique grand premier q et ses trois petits premiers ordonnés c<r<s. Parents J2 et images J1 sont disjoints. Ce raisonnement est un audit écrit de la factorisation réelle, pas une hypothèse libre d’injectivité du module4. Chaque image correspond à un m1 entier distinct dans `[1,N−2]`, donc K≤N ; aucune borne inférieure de K n’est fournie. Avec log(n1)≤u,

\[
E_{\rm switch}=\sum_{\rm tuples}\log n_1|\Delta W|
\le21K u^2N^{-1/32}\le21N^{31/32}u^2.
\]

**X17, seuil effectif écrit.** Le coût normalisé est `F(u)=21u³log(u)exp(−u/32)`. À u0=10^24, `log21<4`, `log10<5/2`, `log60<5` donnent `log(21u0³log u0)<189<200`, tandis que u0/32>10^22. Ces trois comparaisons logarithmiques peuvent être obtenues par les premiers termes positifs des séries de exp4,exp(5/2),exp5. Ainsi F(u0)<10^(−12). Pour u≥u0,

\[
(\log F)'=3/u+1/(u\log u)-1/32
\le4/u-1/32<0.
\]

La validité écrite de `E_switch<10^(−12)N/(u log u)` est donc effective dès l’onset source. Ce seuil ne devient ni un onset Goldbach ni le seuil BV supplémentaire de la bande physique.

## 3. X18, signe, masse favorable et P5

U4 de `round10/agent1_prime_signed.md`, §5, est conservé dans son domaine : sur les bulk m≥M, n>Q, le vrai masque devient N et

\[
W_i=-S(N)+\delta_i,\quad
|\delta_i|\le\epsilon_W=4\cdot10^8u^4e^{-\sqrt u/60}+160u e^{-u/40}.
\]

Au source u≥10^24, epsilon_W≤1/4 et S(N)≥1. Les préfixes d’ici satisfont le domaine R≥N^(1/5) de cet acquis, avec toute sa marge d’onset ; aucun annulus n’efface leur bas. Donc `W_i≤−3/4`, `log c−W0>0`, et l’identité réelle X5, prouvée séparément par le rôle3, entraîne

\[
\sum B_{\rm pair}\le-A_{\rm real}+E_{\rm switch},\quad
A_{\rm real}=\sum(\log c-W_0)\log(n_1/n_0)\ge0.
\]

A_real est strictement positif seulement si le bloc est non vide. Il demeure une masse réelle ; aucune minoration de densité ou capacité n’est postulée. Le contrôle U4 utilisé pour son signe n’est pas ajouté comme second frais NG54 aux mêmes parents. La borne par deux erreurs U4 constitue une route alternative à X16, pas un coût supplémentaire.

Le reste de X19 demeure `B_J0+B_(J1\T)+B_(J2\P)`. Les parents sans image première et les gardes échouées restent non appariés. P5 porte toujours sur K2 **entier du J2 bulk**. Le retrait exact des parents est

\[
B_{J2,bulk\setminus P}=K_2-\sum_P\kappa_m+
(R_{J2,bulk}-\sum_P e_m),\quad
\kappa_m=(\log c+S(N))\log n_0,\quad e_m=-\delta_0\log n_0.
\]

La dernière parenthèse est une somme sur J2 bulk privé de P ; son coût U4 ne porte donc que sur ce support. Les parents/images appariés reçoivent uniquement X16. Les nonbulk, célibataires, faces, H2 et le crédit rough de P5 restent littéraux. Appliquer P5 à K2 tronqué sans son retrait ou sommer NG54 sur tout J2 et X16 sur ses mêmes parents serait une double charge ; aucune de ces opérations n’est effectuée ici.

Le registre unique reste `D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0)`. Raw properpowers, deux vrais noyaux, c1, principal bilatéral `−S(N)N`, complément long, I_alpha et frais acquis gardent leur compte unique. X16 paie seulement la variation des deux W sur le bloc apparié ; il ne paie pas sa couverture, J0/J1, J2 restant ou le terme couvert. L’onset BV effectif de la bande physique reste ouvert.

## 4. Tentatives réelles, axiomes et limites

Trois compilations du module ont eu lieu. Attempt1 a réellement échoué sur quatre réparations techniques : construction du masque coprime, paramètre implicite N, positivité exigée par l’inégalité de division, et emploi de l’inégalité triangulaire `abs_sub_le`. Son source snapshot et son log sont conservés sous role4 ; les `sorryAx` imprimés automatiquement dans ce log rejeté ne constituent pas une preuve acceptée. Attempt2 sort code0 avec uniquement les axiomes standards ; attempt3 remplace un diagnostic de tactique ring par ring_nf et sort code0 sans diagnostic, erreur ou avertissement. Les trois snapshots/logs sont liés par SHA dans le reçu.

Les 16 théorèmes et 5 définitions du module final ont tous leur `#print axioms`. Le contrôle de la source finale écarte les preuves incomplètes, déclarations d’axiome et décision native. Toutes les dépendances imprimées sont dans `propext`, `Classical.choice`, `Quot.sound`, ou un sous-ensemble. L’audit additionnel de dépendances reconstruites imprime aussi les 17 anciens théorèmes U1, les 19 anciens théorèmes P1/P2 et leurs 5+15 définitions. Ces 36 anciens théorèmes ne sont pas recomptés comme nouveaux.

Le banc numérique F1 à N=10^8 conserve une paire réelle positive malgré son principal négatif. Il réfute le promoteur nu sans commutateur ; il ne réfute ni F7 ni X16. N=10^8 est hors du domaine source de X18 et ne certifie aucun paiement asymptotique. Aucun producteur numérique gelé n’a été relancé par ce rôle.

Reproduction du module : exécuter `round13/role4/build.py` avec l’interpréteur Python fourni. L’audit final est `round13/role4/finalize.py`. Ces scripts écrivent uniquement les chemins autorisés role4 et son reçu. Les inputs gelés sont vérifiés avant tout build ; les fichiers .olean des dépendances dans role4 proviennent de leur reconstruction nouvelle. Le contrôle final des 514 archives et des onze bindings numériques passe en lecture seule.

| Production finale | SHA-256 |
| --- | --- |
| `lean/HarmonicKernelVariation.lean` | `7bc1ee92e0e9c6000fd31afdc05a0a827a254d60354d6519c145727e886b1e95` |
| `role4_final_receipt.json` | `59f2ed42f942d5daaf3c7b7d4d843eb26ae783de4d493c5f656ab504dbf6111c` |

Statut : `COMPILED_ACTUAL_KERNEL_FINITE_VARIATION_WITH_WRITTEN_POWER_PAYMENT`. `new_theorem_count=16`, `new_definition_count=5`, `score=0`, `victory=false`. La fermeture de la capacité globale, les restes réels, le principal bilatéral, l’onset BV supplémentaire et `2max(e,0)` restent ouverts. Le rôle4 est terminé ; source et reçu sont gelés pour le Juge indépendant.
