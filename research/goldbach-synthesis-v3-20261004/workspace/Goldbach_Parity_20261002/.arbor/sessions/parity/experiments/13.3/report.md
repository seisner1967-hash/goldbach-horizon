# Boucle 13 — jugement indépendant définitif

**Verdict : progrès partiel raccordé aux objets réels, aucune victoire.** Les deux nouveaux modules compilent fraîchement. Ils prouvent l'antisymétrie des préfixes incomplets, le raccord des deux vrais brackets, les canonicalités, puis la variation exacte et une borne absolue finie des noyaux harmoniques. Le paiement écrit `21N^(31/32)u²` est valide sur le sous-ensemble effectivement apparié. La couverture et la somme non appariée restent sans estimation suffisante.

`status=PARTIAL_ACTUAL_PRIME_SEMIPRIME_SWITCH_WITH_UNPAID_COMPLEMENT`, `lean_invoked=true`, `victory=false`, `score=0`.

## Gel, reproduction et conservation

Les rapports 1, 2, 3, 4 et 6, PROBE_BLOCK13, la sélection du coordinateur, les cinq scripts et auxiliaires numériques, les gates et le rejeu ont été lus. Le gel global a été effectué après les deux signaux `TERMINÉ` des formalistes et la vérification de leurs SHA prescrites. Le manifeste contient **64 fichiers** de production définitive, dont les cinq rapports, les deux nouvelles sources, les journaux et snapshots des producteurs et les deux copies numériques isolées. Les sources historiques requises sont liées séparément à leurs empreintes protégées.

Commande B_dev exécutée une fois avec succès :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round13\judge\audit-judge.ps1' -Python 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
```

L'audit vérifie les entrées gelées et les 514 fichiers protégés, contrôle les reçus numériques en lecture seule, puis compile séquentiellement les deux dépendances nécessaires et les deux modules neufs. Tout code non nul arrête les étapes dépendantes. Les codes finaux sont `0/0/0/0` ; la sortie affiche `Score: 0`. Ce score exprime l'absence du certificat de victoire, pas un échec des identités locales.

Les **514 artefacts antérieurs** sont conservés avant et après : 487 fichiers déjà protégés et 27 fichiers définitifs de la boucle 12. Le registre garde SHA `02c04c95e5348369b9c4577ac3a14e5b4b89e15f53e142e75a37e58b6bde7351` ; le contrôleur 12 garde `d84cca25948c6794764f3afbc7b6fa23d46faa4152fdad17f2f87da69929a400`. Les PDF/ZIP originaux, les anciens pixels, textes rendus, objets Lean, logs et rapports sont intacts. Les exclusions futures utilisent le numéro analysé de `roundNN≥13`, avec détection des suppressions et additions dans le périmètre ancien.

Aucun producteur numérique nouveau ou ancien n'a été relancé par le Juge. Aucun ancien module indépendant n'a été recompilé hors des deux imports nécessaires. Aucun rendu source n'a été refait. Les écritures du Juge sont limitées à `round13/judge/**` et au présent rapport ; aucun état Arbor ou rapport central n'est modifié.

## Audit numérique en lecture seule

Les **11 liaisons** du manifeste numérique sont exactes. Les deux JSON canoniques et leurs copies sous `isolated_output_probe` sont identiques sur **tous les champs et tous les octets**, sans exclusion. Les codes zéro et les SHA du rejeu existant concordent avec ces fichiers. Les imports historiques cités sont liés au registre protégé et ne sont pas exécutés par cet audit.

| Sortie | Statut conservé |
|---|---|
| `exchange.json` | `PASS_NEW_CROSS_KERNEL_EXCHANGE_IDENTITY_ONLY` |
| `operator.json` | `PASS_NEW_ACTUAL_OPERATOR_IDENTITIES_ONLY` |
| Sous-identité des deux fronts | `PASS_NEW_LITERAL_TWO_FRONT_W_IDENTITY_ONLY` |
| Rejeu existant | `PASS_NEW_ROUND13_BYTES_AND_FIELDS_REPLAY` |

Les huit `ERROR_FALSIFIER` restent distincts : quatre pour l'échange, quatre pour l'opérateur. L'audit compte **17 positions de certificat de signe**, y compris les reprises d'un certificat dans des sous-rapports ; il ne s'agit pas de 17 résultats nouveaux. Les fractions sont comparées exactement : bornes ordonnées, intervalle strictement positif ou négatif selon le signe, aucun flottant et aucun `UNRESOLVED`. Les flags numériques de paiement analytique, borne globale, asymptotique et victoire restent faux. Leur flag `Lean_called=false` décrit la production numérique ; la compilation indépendante ultérieure du Juge est enregistrée séparément.

À `N=10^8`, les paramètres restent `alpha=100`, `a=3163`, `Q=999999` et `M=1000000`. Le descendant conjoint conserve `U_a(m0)=−log3`, `U_a(m1)=+log3`, ainsi que les morceaux bas et la bande : `U_alpha(m0)=−log3`, `U_alpha(m1)=0`. Le préfixe entier ne peut être remplacé par l'annulus acquis.

## Reconstruction Lean indépendante

Lean **4.15.0**, commit de compilateur `11651562caae`, cache mathlib au commit exact **`9837ca9d65d9de6fad1ef4381750ca688774e608`**, huit paquets locaux. Les sources sont compilées dans le nouveau répertoire `judge/fresh_a1wb0tpm`. `LEAN_PATH` contient ce répertoire et les seuls objets des bibliothèques standards. Aucun objet personnalisé du producteur ou d'une ancienne boucle n'est emprunté.

| Source reconstruite | Théorèmes | Définitions propres | Code de sortie | Avertissements | Nouveau compte |
|---|---:|---:|---:|---:|---:|
| `ShortDivisorComplement` | 17 | 5 | 0 | 0 | 0 : dépendance |
| `ThreeAdicPrimePairing` | 19 | 15 | 0 | 0 | 0 : dépendance |
| `PrimeSemiprimeSwitch` | 23 | 0 | 0 | 0 | 23 |
| `HarmonicKernelVariation` | 16 | 5 | 0 | 0 | 16 |

Chaque théorème et chaque définition propre est inspecté par `#print axioms`. Les douze constantes importées imprimées par le module d'échange sont également auditées et restent séparées du compteur nouveau. Toutes les dépendances constatées sont dans `propext`, `Classical.choice`, `Quot.sound`, ou sont vides. Le scanner du code exécutable, après traitement des commentaires et chaînes, ne trouve aucune preuve incomplète, déclaration d'axiome ou décision native prohibée. Les journaux indépendants ne contiennent ni `sorryAx`, ni erreur, ni avertissement.

**39 nouvelles conclusions auxiliaires ; cumul confirmé de 15 modules et 208 conclusions.** Les 36 théorèmes de dépendance, leurs 20 définitions et les douze constantes importées ne sont pas ajoutés comme nouveaux résultats. Les cinq définitions nouvelles sont auditées sans être comptées comme théorèmes.

## Partie compilée : échange et vraie variation

Les gardes du sous-ensemble sont arithmétiques : cinq premiers distincts `c<r<s≤a<p<q`, `rs+2=p`, `cr,cs≤a<rs`, `crs>a`, unités N, deux premiers complémentaires, fronts et bulk source. Elles ne postulent ni l'existence de partenaires ni la petitesse d'une somme.

`PrimeSemiprimeSwitch` démontre les diviseurs courts du parent `{1,c}` et ceux de l'image `{1,c,r,s,cr,cs}`. Les égalités de préfixe sont dérivées des vrais Möbius, logarithmes et facteurs :

\[
U_a(cpq)=-\log c,\qquad U_a(crsq)=+\log c.
\]

Les signes `μ(cpq)=−1`, `μ(crsq)=+1`, la squarefreeness et le Mangoldt nul sont prouvés. Le module applique le complément physique acquis au vrai `sourceBracket` ; il ne prend pas deux coefficients libres comme hypothèses. Son wrapper conserve les points `n_i=N−m_i`, les unités et les deux gardes bulk/`n_i>Q`, même lorsque celles-ci ne sont pas nécessaires à l'algèbre finie.

Il prouve le déplacement `m0=m1+2cq`, `n1=n0+2cq`, ainsi que

\[
B_{\mathrm{pair}}=-(\log c-W_0)\log(n_1/n_0)
+\log n_1(W_1-W_0).
\]

Les deux W sont littéralement les deux noyaux source. Les preuves de canonicalité récupèrent tous les facteurs depuis le parent ou l'image par factorisation ordonnée. La disjonction des supports parent/image découle de leurs signes de Möbius. Aucun postulat d'injectivité ne remplace cette arithmétique ; aucune borne inférieure du nombre de tuples n'est prouvée.

`HarmonicKernelVariation` réduit le masque à `(k,N)=1` uniquement sous les deux primalités `n_i>Q`. Avec `R_i=min(Q,floor((m_i−1)/a))`, il prouve

\[
W_1-W_0=\log(m_0/m_1)A_N(R_1)
-\sum_{R_1<k\le R_0,(k,N)=1}
\frac{\mu(k)}{\varphi(k)}\log(k/m_0).
\]

Le cap Q, les faces strictes, `k=1` et tous les indices de queue restent présents. Le même module prouve une borne absolue **finie** par le vrai totient :

\[
|\Delta W|\le |\log(m_0/m_1)|\sum_{k=1}^{R_1}\frac1{\varphi(k)}
+\sum_{k=R_1+1}^{R_0}\frac{|\log(k/m_0)|}{\varphi(k)}.
\]

Cette inégalité utilise `|μ(k)|≤1`, la positivité du totient et les sommes finies. Elle ne suppose aucune faible énergie, masse Goldbach ou cible désirée. La réduction ultérieure aux puissances de N et à la constante 21 est une preuve écrite, pas une conclusion Lean de ces modules.

## Audit indépendant du coût écrit X8–X20

Pour `k≥1`, la factorisation en puissances premières donne `φ(k)²≥k/2` : seul le facteur `2^1` peut contribuer le rapport 1/2. Le cas k1 est inclus. Par télescopage des différences de racines, la somme des réciproques vérifie `Σ_{k≤R}1/φ(k)<3sqrt R` pour `R≥1`.

Pour `u≥16`, les ceil donnent `N^(7/16)≤a≤2N^(7/16)` et la marge `M≥2a+2`. La monotonie `alpha≤a` rend le cap Q inactif sans le modifier. Le floor strict et son coût entier donnent

\[
R_1\ge N^{5/16}/4,\quad R_0\le N/a,\quad
R_0-R_1\le2N^{1/8}+1.
\]

Le `+1` est conservé. La translation donne `0<log(m0/m1)≤4/a`, et chaque logarithme de queue est de valeur absolue au plus u. La tête coûte donc `12N^(−5/32)` ; la queue coûte `6uN^(−1/32)+3uN^(−5/32)`. Cela implique

\[
|\Delta W|\le21uN^{-1/32}.
\]

Les canonicalités prouvées justifient une injection réelle des tuples dans les images entières distinctes, donc `K≤N`. Avec `log n1≤u`, **sur le seul sous-ensemble effectivement apparié**,

\[
E_{\mathrm{switch}}\le21K u^2N^{-1/32}
\le21N^{31/32}u^2.
\]

Le coût normalisé est `21u³log(u)exp(−u/32)`. À `u=10^24`, le logarithme du facteur polynomial est inférieur à 200 et `u/32>10^22` ; sa dérivée logarithmique est négative ensuite. Le paiement écrit inférieur à `10^−12 N/(u log u)` est donc effectif au seuil source. Les preuves écrites de ces étapes sont correctes ; ni leurs exposants ni ce seuil ne sont certifiés par le compilateur ici.

X18 réutilise U4 acquis pour le signe réel `W_i≤−3/4` au domaine source. Il conserve `A_real≥0`, strictement positif seulement si le sous-ensemble est non vide, sans minoration de K ou d'une densité première. Le coût de signe U4 n'est pas ajouté comme second NG54 aux mêmes parents. Une route par deux erreurs U4 et la route par X16 sont alternatives.

Le retrait X20 doit garder **K2 entier du J2 bulk**, sur lequel P5 conserve ses incidences, entropies, célibataires, faces et crédit rough. Il retire exactement les principaux des parents et leurs erreurs ; la somme d'erreurs restante ne porte que sur `J2 bulk\P`. Les couples retirés sont payés par X16. Sommer NG54 sur tout J2 puis payer à nouveau leurs mêmes noyaux serait une double charge ; appliquer P5 à K2 tronqué sans ce retrait serait injustifié. Aucun de ces raccords fautifs n'est utilisé.

## Falsifications et erreurs de compilation réellement observées

Les quatre falsifications d'échange sont : queue omise, direction p+2 traitée comme p−2, couverture première universelle, paire réelle descendante déclarée non positive sans défaut. Sur le descendant F1, le principal est négatif mais la paire réelle finie est positive. Sa queue contient les vrais indices 10613 et 10617 ; elle est non nulle. Le parent F3 possède un complément image composite et reste non apparié.

Les quatre falsifications d'opérateur sont : petite commutation universelle en `1/u`, conservation du moment orienté par symétrisation, positivité complète du bon H, substitution de theta au raw sur une arête longue. Les cubes sont complets, de 8/12 et 16/32 sommets/arêtes. La symétrisation donne zéro tandis que le moment orienté est positif ; `x=e187−e561` donne une direction négative du vrai H. Le matching conserve `S(cN)`, et l'arête longue conserve `Λ_N(8017²)=log8017` alors que theta y est nul. Une nilpotence de l'opérateur orienté ne contrôle pas ce coefficient physique.

Ces rejets sont locaux ou portent sur leur assertion structurelle précise. Ils ne réfutent pas toute approche spectrale, toute autre couverture, ou une éventuelle estimation globale indépendante au domaine source.

| Traces des producteurs | Qualification |
|---|---|
| Rôle 3, essais 01 et 02 | Vrais échecs : branches de diviseurs, non-nullités, noms de lemmes et membres distincts ; erreurs techniques réparées |
| Rôle 3, essai 04 | Vrai échec : nom `Nat.divisors_prime` absent et réécriture requise des facteurs avant récupération de p |
| Rôle 3, essais 03, 05, 06 | Réussites ; version finale 06 sans erreur ni avertissement |
| Rôle 4, essai 01 | Vrai échec : masque coprime, paramètre N implicite, positivité d'une division et forme de l'inégalité triangulaire |
| Rôle 4, essais 02 et 03 | Réussites ; version finale 03 sans diagnostic |
| Reconstruction du Juge | Quatre codes zéro ; aucune erreur nouvelle |
| Estimation globale absente | Obligation analytique encore ouverte ; aucun message Lean fictif |

Les erreurs ont été lues dans les journaux gelés. Les `sorryAx` des essais rejetés ne sont pas des preuves acceptées et ne sont présents dans aucun log indépendant final. Le mur de la parité n'est pas identifié à une erreur de nom de lemme ou à une tactique arithmétique locale.

## Registre restant et condition de victoire

La partition disjointe conserve

\[
B_{\mathrm{prime}}^a=B_{J0}+B_{J1\setminus T}
+B_{J2\setminus P}+\sum B_{\mathrm{pair}}.
\]

Aucune couverture, existence générale d'une image première ou minoration de cardinal n'est acquise. Le coût apparié ne contrôle pas `B_J0+B_(J1\T)+B_(J2\P)`. Les nonbulk et gardes échouées gardent leurs contributions littérales. Le matching bilatéral, le secteur c1, la référence `−S(N)N`, tous les cofacteurs longs et les compléments des cubes restent dans l'autre route non estimée.

Le registre unique demeure

\[
D_N=B_{\mathrm{prime}}^a+B_{\mathrm{pp}}^a
+P_{\mathrm{bande}}^{\ge2}+Z_{\mathrm{face}}^{\ge2}
+I_\alpha+2\max(e,0).
\]

H2, les célibataires/faces, J0/J1 et les moments signés restants, le seuil effectif BV supplémentaire de la bande physique et `2max(e,0)` restent ouverts. Les crédits déjà acquis gardent leur compte unique.

Le domaine source est `u≥10^24`. Les témoins à `N=10^8` sont hors de ce domaine : le signe positif de F1 réfute la promotion nue, **pas** le paiement corrigé X18 au source. (54) garde l'exposant littéral `−sqrt(u/60)` et le majorant volontairement plus faible `−sqrt(u)/60`. Les unités, conducteurs, fronts, quatre signes de Möbius, points k1, `+1` et phase native égale à 1 sur les fibres physiques restent conservés.

Le nouveau contenu compilé est utile à un mécanisme partiel et dépasse une substitution de coefficients libres. Il ne fournit pas le contrôle quantitatif du résidu complet. La borne `D_N≤N/(256 log N log log N)` et la condition de victoire restent non démontrées.

## Empreintes définitives

| Artefact | SHA-256 |
|---|---|
| `judge/input_sha256.json` | `98ccb5777ef45aa9cfa053ccf314ab3013d973479693003f2ec812d715a7767f` |
| `judge/judge_receipt.json` | `493260cab76a5db944c0f85182368f0540c9d2cf0e973807cc1b0ac65f623527` |
| `judge/numerical_audit_receipt.json` | `079dbac93e3037db902b463f845e213c5f3c9e103530a26c49fdfca4efec3582` |
| `PrimeSemiprimeSwitch.lean` | `21462365bb2fe343015161fc67639ed7bbba1234cfbbd985c90bb3d591a84da4` |
| `HarmonicKernelVariation.lean` | `7bc1ee92e0e9c6000fd31afdc05a0a827a254d60354d6519c145727e886b1e95` |

Le reçu lie les cinq rapports, les sources et auxiliaires, les deux copies complètes, les huit falsifications, chaque position de signe, les snapshots et objets indépendants, les noms et axiomes de toutes les déclarations inspectées, les scripts et la conservation avant/après. Aucun test supplémentaire n'a été lancé après ce passage réussi.
